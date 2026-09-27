#!/usr/bin/env python3
"""
Differential comparison runner: MiniZinc Challenge vs the Lean solver.

Reads the official challenge result CSVs (challengeResults2025.csv /
challengeResults2026.csv), selects every challenge instance on which BOTH
Gecode and OR-Tools CP-SAT finished in strictly less than --max-seconds
(default 20) seconds, and then runs the Lean solver (``leanfzn solve``)
on the corresponding FlatZinc file, recording wall time, CPU time, and
peak memory usage (ru_maxrss via resource, sampled RSS via /proc).

For every selected instance the script also reports the reference Gecode /
CP-SAT challenge numbers (time, objective, score) for side-by-side comparison.

Output: one CSV per challenge in  <script dir>/comparison/lean_vs_challenge2025.csv
                                   <script dir>/comparison/lean_vs_challenge2026.csv
plus a combined  comparison/lean_vs_challenge_all.csv.

Usage:
  python3 run_lean_comparison.py [--max-seconds S] [--solver-class ...]
                                 [--challenges 2025 2026] [--dry-run]
                                 [--lean-flag ...]  (repeatable)
"""
from __future__ import annotations

import argparse
import csv
import os
import resource
import subprocess
import sys
import time

CHALLENGE_DIR = os.path.dirname(os.path.abspath(__file__))
COMPARISON_DIR = os.path.join(CHALLENGE_DIR, "comparison")
LEAN_BIN = "/workspace/.lake/build/bin/leanfzn"

BASE_COLUMNS = [
    "challenge", "problem", "instance", "fzn_file",
    # reference numbers from the official challenge run
    "gecode_status", "gecode_time_ms", "gecode_objective", "gecode_score",
    "cpsat_status", "cpsat_time_ms", "cpsat_objective", "cpsat_score",
    # lean solver run
    "lean_exit", "lean_verdict", "lean_wall_time_s", "lean_cpu_time_s",
    "lean_cpu_util", "lean_peak_rss_mb", "lean_sampled_rss_mb",
    "lean_error",
]


def load_results(year: str) -> dict[str, list[dict]]:
    """Return problem -> list of per-solver rows for one challenge."""
    path = os.path.join(CHALLENGE_DIR, f"challengeResults{year}.csv")
    per_problem: dict[str, list[dict]] = {}
    with open(path, newline="") as f:
        for row in csv.DictReader(f):
            per_problem.setdefault(row["problem"], []).append(row)
    return per_problem


def to_float(s: str) -> float | None:
    try:
        return float(s)
    except (TypeError, ValueError):
        return None


def select_instances(year: str, max_seconds: float) -> list[dict]:
    """Pick instances where Gecode AND CP-SAT statuses are successful
    (S or SC) and both times are < max_seconds; attach reference rows."""
    per_problem = load_results(year)
    out: list[dict] = []
    for problem, rows in sorted(per_problem.items()):
        # one reference row per (instance, solver); index by instance
        by_instance: dict[str, dict[str, dict]] = {}
        for r in rows:
            by_instance.setdefault(r["instance"], {})[r["solver"]] = r
        for inst, solver_rows in sorted(by_instance.items()):
            refs: dict[str, dict] = {}
            ok = True
            for key, want in (("gecode-fd", "gecode"), ("or-tools_cp-sat-fd", "cpsat")):
                # prefer FD entry, fall back to free class entry
                r = solver_rows.get(key) or solver_rows.get(key.replace("-fd", "-free"))
                if r is None or r["status"] not in ("S", "SC"):
                    ok = False
                    break
                t = to_float(r["time_ms"])
                if t is None or t >= max_seconds * 1000.0:
                    ok = False
                    break
                refs[want] = r
            if not ok:
                continue
            fzn = os.path.join(CHALLENGE_DIR, f"{year}fzn", problem, f"{inst}.fzn")
            out.append({
                "challenge": year, "problem": problem, "instance": inst,
                "fzn": fzn, "refs": refs,
            })
    return out


def run_lean(fzn: str, lean_flags: list[str], wall_limit: float) -> dict:
    """Run the Lean solver with wall/CPU/peak-RSS accounting."""
    cmd = [LEAN_BIN, "solve", *lean_flags, fzn]
    err_path = "/tmp/lean_cmp_stderr.txt"
    with open(err_path, "w") as errf:
        t0 = time.perf_counter()
        proc = subprocess.Popen(  # noqa: S603 - fixed argv, no shell
            cmd, stdout=subprocess.DEVNULL, stderr=errf,
        )
        sampled_peak = 0
        while proc.poll() is None:
            try:
                with open(f"/proc/{proc.pid}/status") as sf:
                    for line in sf:
                        if line.startswith("VmHWM:"):
                            sampled_peak = max(sampled_peak, int(line.split()[1]))
                            break
            except (FileNotFoundError, ProcessLookupError):
                pass
            if time.perf_counter() - t0 > wall_limit:
                proc.kill()
                proc.wait()
                return {"exit": "timeout", "verdict": "timeout",
                        "wall": wall_limit, "cpu": None, "util": None,
                        "peak_rss": None, "sampled": None,
                        "err": f"killed after {wall_limit:.0f}s wall limit"}
            time.sleep(0.05)

    usage_after = resource.getrusage(resource.RUSAGE_CHILDREN)
    wall = time.perf_counter() - t0
    with open(err_path) as ef:
        err = ef.read().strip()

    exit_code = proc.returncode
    verdict = {0: "sat", 1: "unsat", 2: "unknown", 3: "unsupported"}.get(exit_code, "crash")
    # ru_maxrss of children is a max over all children ever reaped, so the
    # sampled value is the faithful per-run figure; keep both.
    child_rss_mb = usage_after.ru_maxrss / 1024.0
    cpu = usage_after.ru_utime + usage_after.ru_stime
    util = (cpu / wall * 100.0) if wall > 0 else None
    return {"exit": exit_code, "verdict": verdict, "wall": wall, "cpu": cpu,
            "util": util, "peak_rss": child_rss_mb,
            "sampled": sampled_peak / 1024.0 if sampled_peak else None,
            "err": err.strip()[:300]}


def fmt(v) -> str:
    if v is None:
        return ""
    if isinstance(v, float):
        return f"{v:.6f}"
    return str(v)


def process_year(year: str, args, rows_out: list[list[str]]) -> int:
    sel = select_instances(year, args.max_seconds)
    print(f"=== {year}: {len(sel)} instances with Gecode & CP-SAT both < {args.max_seconds}s ===")
    for entry in sel:
        if args.dry_run:
            print("  [dry-run]", entry["problem"], entry["instance"])
            continue
        if not os.path.exists(entry["fzn"]):
            print("  [missing fzn]", entry["problem"], entry["instance"])
            continue
        res = run_lean(entry["fzn"], args.lean_flag, args.timeout + 5.0)
        g, c = entry["refs"]["gecode"], entry["refs"]["cpsat"]
        rows_out.append([
            entry["challenge"], entry["problem"], entry["instance"], entry["fzn"],
            g["status"], g["time_ms"], g["objective"], g["score"],
            c["status"], c["time_ms"], c["objective"], c["score"],
            fmt(res["exit"]), res["verdict"], fmt(res["wall"]), fmt(res["cpu"]),
            fmt(res["util"]), fmt(res["peak_rss"]), fmt(res["sampled"]),
            res["err"],
        ])
        print(f"  {entry['problem']}/{entry['instance']}: lean={res['verdict']} "
              f"wall={res['wall']:.2f}s cpu={fmt(res['cpu'])}s "
              f"peakRSS={fmt(res['sampled'])}MB   "
              f"[gecode {g['time_ms']}ms cpsat {c['time_ms']}ms]")
    return len(sel)


def main() -> None:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--max-seconds", type=float, default=20.0,
                    help="both Gecode and CP-SAT must finish under this many seconds")
    ap.add_argument("--challenges", nargs="+", default=["2025", "2026"],
                    help="which challenge years to process")
    ap.add_argument("--timeout", type=float, default=300.0,
                    help="wall-clock limit for each Lean solver run (s)")
    ap.add_argument("--dry-run", action="store_true", help="only list selected instances")
    ap.add_argument("--lean-flag", action="append", default=["--prop", "--mrv"],
                    help="extra flags for `leanfzn solve` (repeatable)")
    args = ap.parse_args(sys.argv[1:])

    os.makedirs(COMPARISON_DIR, exist_ok=True)
    all_rows: list[list[str]] = []
    for year in args.challenges:
        before = len(all_rows)
        process_year(year, args, all_rows)
        year_rows = all_rows[before:]
        if year_rows:
            path = os.path.join(COMPARISON_DIR, f"lean_vs_challenge{year}.csv")
            with open(path, "w", newline="") as f:
                w = csv.writer(f)
                w.writerow(BASE_COLUMNS)
                w.writerows(year_rows)
            print(f"-> wrote {len(year_rows)} rows to {path}")
    if all_rows:
        path = os.path.join(COMPARISON_DIR, "lean_vs_challenge_all.csv")
        with open(path, "w", newline="") as f:
            w = csv.writer(f)
            w.writerow(BASE_COLUMNS)
            w.writerows(all_rows)
        print(f"-> wrote combined {len(all_rows)} rows to {path}")


if __name__ == "__main__":
    main()
