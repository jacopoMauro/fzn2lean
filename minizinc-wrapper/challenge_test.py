#!/usr/bin/env python3
"""End-to-end test of the MiniZinc integration on the MiniZinc Challenge.

Runs every (model, data) instance of minizinc-challenge/<year>mzn through
`minizinc --solver leanfzn`, then checks each run three ways:

1. Witness: every solution leanfzn printed is re-verified with
   `leanfzn check` against the FlatZinc MiniZinc generated (through the
   wrapper's FZN_LEANFZN_SAVE_DIR hook).
2. Challenge oracle (challengeResults<year>.csv): a claimed UNSAT must not
   contradict a solver that found a solution; a proved optimum must equal
   every complete (SC) result and must not be beaten by any found
   objective; an incumbent must not be better than a complete result.
3. End-to-end: the objective MiniZinc prints (`_objective`) equals the
   objective of the last solution in leanfzn's own output stream.

Dev tool, not a solver dependency. Usage:

    minizinc-wrapper/challenge_test.py [--years 2025 2026] [--time-limit 20000]
        [--jobs 3] [--out tmp/minizinc-wrapper/challenge] [--only PROBLEM ...]

Instances whose pre-compiled FlatZinc is larger than --big-mb run
afterwards one at a time with a larger memory cap (systemd user scopes).
"""

import argparse
import concurrent.futures as cf
import csv
import json
import os
import re
import shutil
import subprocess
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.realpath(__file__)))
CHALLENGE = os.path.join(ROOT, "minizinc-challenge")
LEANFZN = os.environ.get("LEANFZN_BIN", os.path.join(ROOT, ".lake", "build", "bin", "leanfzn"))
OBJ_RE = re.compile(r"^_objective\s*=\s*(-?\d+);", re.M)


def instances(years, only):
    for y in years:
        base = os.path.join(CHALLENGE, f"{y}mzn")
        for prob in sorted(os.listdir(base)):
            if only and prob not in only:
                continue
            d = os.path.join(base, prob)
            models = sorted(f for f in os.listdir(d) if f.endswith(".mzn"))
            if not models:
                continue
            for f in sorted(os.listdir(d)):
                if f.endswith((".dzn", ".json")):
                    inst = os.path.splitext(f)[0]
                    fzn = os.path.join(CHALLENGE, f"{y}fzn", prob, inst + ".fzn")
                    size = os.path.getsize(fzn) if os.path.exists(fzn) else 0
                    yield {"year": y, "problem": prob, "instance": inst,
                           "model": os.path.join(d, models[0]), "data": os.path.join(d, f),
                           "fzn_mb": size / 1e6}


def load_results(years):
    res = {}
    for y in years:
        with open(os.path.join(CHALLENGE, f"challengeResults{y}.csv")) as f:
            for r in csv.DictReader(f):
                # SAT problems have a blank (" ") objective.
                r["objective"] = r["objective"].strip()
                res.setdefault((r["challenge"], r["problem"], r["instance"]), []).append(r)
    return res


def classify(stdout, stderr, rc, timed_out):
    if timed_out:
        return "killed"  # outer safety timeout (compile did not finish)
    if "=====UNSATISFIABLE=====" in stdout:
        return "unsat"
    if "unsupported model" in stderr or "=====UNSUPPORTED=====" in stdout:
        return "unsupported"
    if "parse error" in stderr:
        return "unsupported"
    if "==========" in stdout:
        return "complete"
    if "----------" in stdout:
        return "solution"
    if rc != 0 or "=====ERROR=====" in stdout or "Error" in stderr:
        if re.search(r"out of memory|std::bad_alloc|Killed|oom", stderr, re.I) or rc in (-9, 137):
            return "oom"
        return "error"
    return "unknown"


def run_one(inst, args, mem):
    tag = f"{inst['year']}-{inst['problem']}-{inst['instance']}"
    work = os.path.join(args.out, "runs", tag)
    shutil.rmtree(work, ignore_errors=True)
    os.makedirs(work)
    env = dict(os.environ, FZN_LEANFZN_SAVE_DIR=work)
    cmd = ["systemd-run", "--user", "--scope", "--quiet", "-p", f"MemoryMax={mem}",
           "-p", "MemorySwapMax=0",
           "timeout", "-k", "10", str(args.outer_timeout),
           args.minizinc, "--solver", "leanfzn", inst["model"], inst["data"],
           "-t", str(args.time_limit), "--output-mode", "dzn", "--output-objective"]
    t0 = time.monotonic()
    p = subprocess.run(cmd, capture_output=True, text=True, env=env)
    wall = time.monotonic() - t0
    with open(os.path.join(work, "stdout.txt"), "w") as f:
        f.write(p.stdout)
    with open(os.path.join(work, "stderr.txt"), "w") as f:
        f.write(p.stderr)
    timed_out = p.returncode == 124
    row = dict(inst, wall_s=round(wall, 1), rc=p.returncode,
               outcome=classify(p.stdout, p.stderr, p.returncode, timed_out))
    objs = [int(x) for x in OBJ_RE.findall(p.stdout)]
    row["n_solutions"] = p.stdout.count("----------")
    row["objective"] = objs[-1] if objs else None
    row["reason"] = next((l.strip() for l in p.stderr.splitlines()
                          if "unsupported" in l or "error" in l.lower()), "")[:160]

    # Witness check on leanfzn's raw output.
    raw = os.path.join(work, "raw.sol")
    fzn = os.path.join(work, "model.fzn")
    row["check"] = "-"
    row["raw_objective"] = None
    if os.path.exists(raw) and "----------" in open(raw).read():
        # Drop a trailing partial block (run stopped mid-print).
        text = open(raw).read()
        text = text[: text.rfind("----------") + len("----------")] + "\n"
        with open(raw, "w") as f:
            f.write(text)
        c = subprocess.run([LEANFZN, "check", fzn, raw], capture_output=True, text=True)
        row["check"] = "ok" if c.returncode == 0 else f"FAIL({c.returncode}): {c.stdout.strip()[:120]}"
        obj_var = solve_objective(fzn)
        if obj_var:
            vals = re.findall(rf"^{re.escape(obj_var)} = (-?\d+);", text, re.M)
            if vals:
                row["raw_objective"] = int(vals[-1])
    if os.path.exists(fzn):
        os.remove(fzn)  # FlatZinc copies can be large
    return row


def solve_objective(fzn):
    """Objective variable name from the FlatZinc solve item."""
    try:
        with open(fzn, "rb") as f:
            f.seek(max(0, os.path.getsize(fzn) - 65536))
            tail = f.read().decode("utf-8", "replace")
    except OSError:
        return None
    m = re.search(r"solve\b[^;]*\b(?:minimize|maximize)\s+([A-Za-z_][A-Za-z0-9_]*)\s*;", tail)
    return m.group(1) if m else None


def oracle(row, results):
    rows = results.get((str(row["year"]), row["problem"], row["instance"]), [])
    if not rows:
        return "no-reference"
    kind = rows[0]["problem_kind"]
    better = (lambda a, b: a < b) if kind == "MIN" else (lambda a, b: a > b)
    found = [int(r["objective"]) for r in rows
             if r["status"] in ("S", "SC") and r["objective"]]
    complete = [int(r["objective"]) for r in rows
                if r["status"] == "SC" and r["objective"]]
    any_solution = any(r["status"] in ("S", "SC") for r in rows)
    o = row["outcome"]
    obj = row["objective"]
    if o == "unsat" and any_solution:
        return "FAIL: UNSAT but a challenge solver found a solution"
    if kind != "SAT" and obj is not None:
        if o == "complete":
            if any(c != obj for c in complete):
                return f"FAIL: proved {obj}, complete results {sorted(set(complete))}"
            if any(better(f, obj) for f in found):
                return f"FAIL: proved {obj}, but {min(found) if kind == 'MIN' else max(found)} was found"
        if any(better(obj, c) for c in complete):
            return f"FAIL: incumbent {obj} beats complete result {complete[0]}"
    if o == "complete" and kind == "SAT" and not any_solution and rows:
        if any(r["status"] == "C" for r in rows):
            return "FAIL: SAT but a challenge solver proved UNSAT"
    return "ok"


def safe_result(get, inst):
    try:
        return get()
    except Exception as e:
        return dict(inst, wall_s=0, rc=None, outcome="error", n_solutions=0, objective=None,
                    raw_objective=None, check="-", reason=f"harness error {e!r}"[:160])


def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--years", nargs="+", default=["2025", "2026"])
    ap.add_argument("--only", nargs="*", default=[])
    ap.add_argument("--time-limit", type=int, default=20000, help="solver time limit, ms (-t)")
    ap.add_argument("--outer-timeout", type=int, default=900, help="hard cap per run, s")
    ap.add_argument("--jobs", type=int, default=3)
    ap.add_argument("--mem", default="5G", help="memory cap per run")
    ap.add_argument("--big-mb", type=float, default=100.0)
    ap.add_argument("--big-mem", default="18G")
    ap.add_argument("--minizinc", default=shutil.which("minizinc") or "minizinc")
    ap.add_argument("--out", default=os.path.join(ROOT, "tmp", "minizinc-wrapper", "challenge"))
    args = ap.parse_args()
    args.out = os.path.abspath(args.out)
    os.makedirs(args.out, exist_ok=True)

    version = subprocess.run([args.minizinc, "--version"], capture_output=True, text=True).stdout.splitlines()[0]
    print(f"minizinc: {version}\nout: {args.out}", flush=True)
    insts = list(instances(args.years, set(args.only)))
    small = [i for i in insts if i["fzn_mb"] <= args.big_mb]
    big = [i for i in insts if i["fzn_mb"] > args.big_mb]
    results = load_results(args.years)
    rows = []
    jsonl = open(os.path.join(args.out, "results.jsonl"), "w")

    def done(row):
        try:
            row["oracle"] = oracle(row, results)
        except Exception as e:  # a harness bug must not stop the run
            row["oracle"] = f"FAIL: harness error {e!r}"
        if row["raw_objective"] is not None and row["objective"] is not None \
                and row["raw_objective"] != row["objective"]:
            row["oracle"] = f"FAIL: printed objective {row['objective']} != leanfzn {row['raw_objective']}"
        rows.append(row)
        jsonl.write(json.dumps(row) + "\n")
        jsonl.flush()
        flag = "" if row["oracle"] == "ok" and row["check"] in ("ok", "-") else "  <<<"
        print(f"[{len(rows):3}/{len(insts)}] {row['year']} {row['problem']}/{row['instance']}: "
              f"{row['outcome']} obj={row['objective']} sols={row['n_solutions']} "
              f"check={row['check']} oracle={row['oracle']} ({row['wall_s']} s){flag}", flush=True)

    with cf.ThreadPoolExecutor(max_workers=args.jobs) as ex:
        futs = {ex.submit(run_one, i, args, args.mem): i for i in small}
        for fut in cf.as_completed(futs):
            row = safe_result(fut.result, futs[fut])
            # Instances without a pre-compiled .fzn can still flatten to a huge
            # model and hit the small memory cap; rerun those like big ones.
            if row["outcome"] in ("error", "oom", "killed") and futs[fut]["fzn_mb"] == 0:
                print(f"retry under {args.big_mem}: {row['year']} {row['problem']}/{row['instance']} "
                      f"({row['outcome']}, rc={row['rc']})", flush=True)
                big.append(futs[fut])
            else:
                done(row)
    for i in big:
        done(safe_result(lambda: run_one(i, args, args.big_mem), i))

    # Summary
    from collections import Counter
    outcomes = Counter(r["outcome"] for r in rows)
    fails = [r for r in rows if r["oracle"].startswith("FAIL") or r["check"].startswith("FAIL")]
    checked = sum(1 for r in rows if r["check"] == "ok")
    lines = [f"minizinc: {version}", f"instances: {len(rows)}  time limit: {args.time_limit} ms",
             "outcomes: " + ", ".join(f"{k}={v}" for k, v in sorted(outcomes.items())),
             f"witness checks passed: {checked}  failures: {len(fails)}"]
    for r in fails:
        lines.append(f"  FAIL {r['year']} {r['problem']}/{r['instance']}: check={r['check']} oracle={r['oracle']}")
    for r in rows:
        if r["outcome"] in ("error", "oom", "killed", "unsupported"):
            lines.append(f"  {r['outcome']:11} {r['year']} {r['problem']}/{r['instance']}: {r['reason']}")
    summary = "\n".join(lines)
    with open(os.path.join(args.out, "summary.txt"), "w") as f:
        f.write(summary + "\n")
    print("\n" + summary)
    sys.exit(1 if fails else 0)


if __name__ == "__main__":
    main()
