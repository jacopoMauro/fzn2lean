#!/usr/bin/env python3
"""Strategy matrix runner for LeanFzn.

Usage:
  audits/strategy_matrix.py --configs default --cohort audits/cohorts/T10.txt --cap 10

Each (file, config) pair runs once, sequentially, pinned with taskset and
wrapped in an external `timeout --signal=KILL`. The whole pass holds
`flock /tmp/fzn2lean-measure.lock`, so no other measurement or build interferes.

The per-instance TSV columns are
  file, config, outcome, wall_s, n_solutions, best_objective,
  first_solution_s, checked

outcome is one of proved / sat-incumbent / incomplete_with_incumbent / unknown /
timeout_with_incumbent / timeout / none / unsupported / error:
  * proved: a terminal marker agrees with the exit status and solution count;
  * sat-incumbent: a complete run (exit 0) printed at least one solution but
    no proof marker;
  * incomplete_with_incumbent: exit 4 after printing at least one solution
    (an incomplete optimization that retains its incumbents);
  * unknown: exit 4 with no solution (a give-up/unknown verdict);
  * timeout_with_incumbent / timeout: the external wall cap killed the run,
    with or without a printed solution;
  * none: a complete run (exit 0) with no output;
  * unsupported: exit 3;
  * error: any other unexpected exit code or a failed check.

Exit 4 is never folded into `none`: a give-up is a distinct outcome from a
timeout, and both differ from a completed run with no output.

The last printed solution is verified with `leanfzn check`. The per-config
summary reports proved count, incumbent count and the MiniZinc-style quality
score against `audits/cohorts/strategy_targets.tsv`.
"""

from __future__ import annotations

import argparse
import fcntl
import hashlib
import json
import re
import shutil
import subprocess
import sys
import time
from datetime import datetime, timezone
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DEFAULT_BIN = ROOT / ".lake/build/bin/leanfzn"
DEFAULT_TARGETS = ROOT / "audits/cohorts/strategy_targets.tsv"
MEASURE_LOCK = "/tmp/fzn2lean-measure.lock"
PRESETS = {"default", "annot"}
POLL_S = 0.02


def parse_args() -> argparse.Namespace:
    p = argparse.ArgumentParser(description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    p.add_argument("--configs", required=True,
                   help="comma-separated preset names or +-joined flags "
                        "(e.g. default,annot,var=annot+val=min)")
    p.add_argument("--cohort", action="append", required=True,
                   help="file with one model path per line; repeatable")
    p.add_argument("--cap", type=int, default=10,
                   help="external wall cap in seconds (1..300, default 10)")
    p.add_argument("--out", default=None,
                   help="output directory (default tmp/strategy_matrix/<UTC>)")
    p.add_argument("--binary", default=str(DEFAULT_BIN))
    p.add_argument("--targets", default=str(DEFAULT_TARGETS))
    p.add_argument("--core", type=int, default=5,
                   help="CPU core for taskset (default 5)")
    p.add_argument("--cores", default=None,
                   help="taskset CPU list or range (e.g. 0,2,4,6 or 0-7); "
                        "overrides --core, for multi-threaded configs")
    p.add_argument("--lock", default=MEASURE_LOCK)
    p.add_argument("--no-check", action="store_true",
                   help="skip `leanfzn check` verification")
    args = p.parse_args()
    if not 1 <= args.cap <= 300:
        p.error("--cap must be in 1..300")
    return args


def config_argv(config: str) -> list[str]:
    """Translate a matrix config label into CLI flags."""
    if config == "default":
        return []
    if config in PRESETS:
        return ["--strategy=" + config]
    flags = []
    for part in config.split("+"):
        part = part.strip()
        if not part:
            raise SystemExit(f"empty flag in config '{config}'")
        flags.append(part if part.startswith("--") else "--" + part)
    return flags


def read_cohort(paths: list[str]) -> list[str]:
    files: list[str] = []
    seen: set[str] = set()
    for path in paths:
        with open(path, encoding="utf-8") as f:
            for line in f:
                line = line.strip()
                if not line or line.startswith("#"):
                    continue
                if line in seen:
                    continue
                seen.add(line)
                files.append(line)
    return files


def model_info(path: Path) -> tuple[str | None, str | None]:
    """Return (objective variable, MIN/MAX) from the model's solve item."""
    try:
        text = path.read_text(errors="replace")
    except OSError:
        return None, None
    m = re.search(r"(?ms)^\s*solve\b[^;]*?\b(minimize|maximize)\s+"
                  r"([A-Za-z_][A-Za-z0-9_]*)\s*;", text)
    if not m:
        return None, None
    return m.group(2), "MIN" if m.group(1) == "minimize" else "MAX"


def objective_value(block: list[str], var: str | None) -> str:
    if not var:
        return "-"
    pat = re.compile(r"^\s*" + re.escape(var) + r"\s*=\s*(-?\d+)\s*;\s*$")
    for line in reversed(block):
        m = pat.match(line)
        if m:
            return m.group(1)
    return "-"


def load_targets(path: Path) -> dict[str, tuple[str | None, str | None]]:
    """file -> (kind, best known objective)."""
    targets: dict[str, tuple[str | None, str | None]] = {}
    if not path.exists():
        return targets
    with path.open(encoding="utf-8") as f:
        header = f.readline().rstrip("\n").split("\t")
        idx = {name: i for i, name in enumerate(header)}
        for line in f:
            parts = line.rstrip("\n").split("\t")
            if len(parts) <= idx.get("file", -1):
                continue
            file = parts[idx["file"]]
            kind = parts[idx["kind"]] if "kind" in idx else None
            obj = parts[idx["best_objective"]] if "best_objective" in idx else None
            targets[file] = (kind or None, obj or None)
    return targets


def run_pinned(argv: list[str], stdout_path: Path, stderr_path: Path,
               timeout_s: int, cores: str) -> tuple[int, float, float | None, bool]:
    """Run `argv` under timeout/taskset, polling stdout for the first solution."""
    cmd = ["timeout", "--signal=KILL", str(timeout_s)]
    if shutil.which("taskset"):
        cmd += ["taskset", "-c", cores]
    cmd += argv
    start = time.monotonic()
    first: float | None = None
    offset = 0
    tail = b""
    with stdout_path.open("wb") as out, stderr_path.open("wb") as err:
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=out, stderr=err,
                             start_new_session=False)
        while True:
            if first is None:
                try:
                    size = stdout_path.stat().st_size
                except OSError:
                    size = offset
                if size > offset:
                    with stdout_path.open("rb") as rf:
                        rf.seek(offset)
                        chunk = rf.read(size - offset)
                    offset = size
                    probe = tail + chunk
                    if b"----------" in probe:
                        first = time.monotonic() - start
                    tail = probe[-32:]
            if p.poll() is not None:
                break
            time.sleep(POLL_S)
        rc = p.wait()
    return rc, time.monotonic() - start, first, rc in (124, 137)


def check_solution(binary: str, model: str, block: list[str],
                   out_path: Path, cores: str) -> str:
    text = "\n".join(block)
    if text:
        text += "\n"
    text += "----------\n"
    out_path.write_text(text, encoding="utf-8")
    cmd = ["timeout", "--signal=KILL", "30"]
    if shutil.which("taskset"):
        cmd += ["taskset", "-c", cores]
    cmd += [binary, "check", str(ROOT / model), str(out_path)]
    p = subprocess.run(cmd, cwd=ROOT, stdout=subprocess.PIPE,
                       stderr=subprocess.PIPE, text=True)
    if p.returncode == 0:
        return "yes"
    return f"no(rc={p.returncode})"


def last_solution(stdout: str) -> list[str]:
    lines = stdout.splitlines()
    seps = [i for i, line in enumerate(lines) if line.strip() == "----------"]
    if not seps:
        return []
    end = seps[-1]
    start = seps[-2] + 1 if len(seps) >= 2 else 0
    return lines[start:end]


def outcome_of(rc: int, timed_out: bool, stdout: str, n_solutions: int) -> str:
    lines = set(stdout.splitlines())
    optimum = "==========" in lines
    unsat = "=====UNSATISFIABLE=====" in lines
    killed = timed_out and rc in (-9, 124, 137)
    if unsat:
        return "proved" if not optimum and not n_solutions and (rc == 1 or killed) else "error"
    if optimum:
        return "proved" if n_solutions > 0 and (rc == 0 or killed) else "error"
    if timed_out:
        return "timeout_with_incumbent" if n_solutions > 0 else "timeout"
    if rc == 4:
        return "incomplete_with_incumbent" if n_solutions > 0 else "unknown"
    if rc == 3:
        return "unsupported"
    if rc == 0 and n_solutions > 0:
        return "sat-incumbent"
    if rc == 0:
        return "none"
    return "error"


def quality_score(kind: str | None, target: str | None,
                  found: str | None) -> float | None:
    if not target:
        return None
    try:
        t = int(target)
    except ValueError:
        return None
    if found in (None, "-"):
        return 0.0
    try:
        v = int(found)
    except ValueError:
        return 0.0
    if kind == "MAX":
        if v >= t:
            return 1.0
        if t > 0 and v > 0:
            return max(0.0, v / t)
        return 0.0
    # MIN (also the fallback when the kind is missing)
    if v <= t:
        return 1.0
    if v > 0 and t > 0:
        return max(0.0, t / v)
    return 0.0


def sha256(path: Path) -> str:
    h = hashlib.sha256()
    with path.open("rb") as f:
        for chunk in iter(lambda: f.read(1 << 20), b""):
            h.update(chunk)
    return h.hexdigest()


def main() -> int:
    args = parse_args()
    configs = [c.strip() for c in args.configs.split(",") if c.strip()]
    if not configs:
        raise SystemExit("--configs is empty")
    for config in configs:
        config_argv(config)  # validate eagerly

    cores = args.cores if args.cores else str(args.core)
    binary = Path(args.binary)
    if not binary.is_absolute():
        binary = (ROOT / binary).resolve()
    if not binary.exists():
        raise SystemExit(f"binary not found: {binary}")

    files = read_cohort(args.cohort)
    if not files:
        raise SystemExit("cohort is empty")
    targets = load_targets(Path(args.targets))

    stamp = datetime.now(timezone.utc).strftime("%Y%m%dT%H%M%SZ")
    outdir = Path(args.out) if args.out else ROOT / "tmp/strategy_matrix" / stamp
    outdir.mkdir(parents=True, exist_ok=True)
    matrix_path = outdir / "matrix.tsv"
    summary_path = outdir / "summary.tsv"
    meta_path = outdir / "meta.json"

    git_head = subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT,
                              capture_output=True, text=True).stdout.strip()
    git_status = subprocess.run(["git", "status", "--porcelain"], cwd=ROOT,
                                capture_output=True, text=True).stdout
    meta = {
        "timestamp_utc": stamp,
        "git_head": git_head,
        "git_status": git_status,
        "binary": str(binary),
        "binary_sha256": sha256(binary),
        "cap_s": args.cap,
        "core": args.core,
        "cores": cores,
        "configs": configs,
        "cohorts": args.cohort,
        "files": len(files),
        "poll_s": POLL_S,
        "runner": "audits/strategy_matrix.py",
    }
    meta_path.write_text(json.dumps(meta, indent=1) + "\n", encoding="utf-8")

    lock_file = open(args.lock, "w")
    announced = False
    try:
        while True:
            try:
                fcntl.flock(lock_file, fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except BlockingIOError:
                if not announced:
                    print(f"waiting for measurement lock {args.lock}", flush=True)
                    announced = True
                time.sleep(1)
    except BaseException:
        lock_file.close()
        raise

    rows: list[dict] = []
    try:
        with matrix_path.open("w", encoding="utf-8") as mf:
            mf.write("file\tconfig\toutcome\twall_s\tn_solutions\tbest_objective\t"
                     "first_solution_s\tchecked\n")
            mf.flush()
            for config in configs:
                flags = config_argv(config)
                for index, model in enumerate(files, 1):
                    label = f"{config.replace('+', '_').replace('=', '-')}__" \
                            f"{Path(model).stem}__{index:03d}"
                    stdout_path = outdir / (label + ".stdout")
                    stderr_path = outdir / (label + ".stderr")
                    rc, wall, first, timed_out = run_pinned(
                        [str(binary), "solve", *flags, model],
                        stdout_path, stderr_path, args.cap, cores)
                    stdout = stdout_path.read_text(errors="replace")
                    n_solutions = sum(1 for line in stdout.splitlines()
                                      if line.strip() == "----------")
                    objective_var, model_kind = model_info(ROOT / model)
                    kind, target = targets.get(model, (model_kind, None))
                    block = last_solution(stdout)
                    best = objective_value(block, objective_var) if block else "-"
                    checked = "-"
                    if block and not args.no_check:
                        checked = check_solution(
                            str(binary), model, block,
                            outdir / (label + ".last-solution.txt"), cores)
                    outcome = outcome_of(rc, timed_out, stdout, n_solutions)
                    row = {
                        "file": model,
                        "config": config,
                        "outcome": outcome,
                        "wall_s": wall,
                        "n_solutions": n_solutions,
                        "best_objective": best,
                        "first_solution_s": first,
                        "checked": checked,
                        "_kind": kind,
                        "_target": target,
                        "_rc": rc,
                        "_timed_out": timed_out,
                    }
                    rows.append(row)
                    mf.write(
                        f"{model}\t{config}\t{outcome}\t{wall:.3f}\t{n_solutions}\t"
                        f"{best}\t"
                        f"{'-' if first is None else f'{first:.3f}'}\t{checked}\n")
                    mf.flush()
                    first_note = "-" if first is None else f"{first:.2f}s"
                    print(f"[{config}] {index}/{len(files)} {model}: {outcome} "
                          f"rc={rc} wall={wall:.2f}s first={first_note} "
                          f"sols={n_solutions} obj={best} check={checked}",
                          flush=True)
    finally:
        fcntl.flock(lock_file, fcntl.LOCK_UN)
        lock_file.close()

    with summary_path.open("w", encoding="utf-8") as sf:
        sf.write("config\tfiles\tproved\tincumbents\tincomplete\tunknown\t"
                 "timeouts\tquality\tquality_files\tchecked_fail\terrors\n")
        for config in configs:
            sub = [r for r in rows if r["config"] == config]
            proved = sum(1 for r in sub if r["outcome"] == "proved")
            incumbents = sum(1 for r in sub if r["n_solutions"] > 0)
            incomplete = sum(1 for r in sub
                             if r["outcome"] == "incomplete_with_incumbent")
            unknown = sum(1 for r in sub if r["outcome"] == "unknown")
            timeouts = sum(1 for r in sub
                           if r["outcome"] in ("timeout", "timeout_with_incumbent"))
            checked_fail = sum(1 for r in sub if r["checked"].startswith("no"))
            errors = sum(1 for r in sub if r["outcome"] == "error")
            scores = []
            for r in sub:
                score = quality_score(r["_kind"], r["_target"],
                                      r["best_objective"])
                if score is not None:
                    scores.append(score)
            quality = sum(scores) / len(scores) if scores else 0.0
            sf.write(f"{config}\t{len(sub)}\t{proved}\t{incumbents}\t"
                     f"{incomplete}\t{unknown}\t{timeouts}\t"
                     f"{quality:.6f}\t{len(scores)}\t{checked_fail}\t{errors}\n")
            print(f"SUMMARY {config}: files={len(sub)} proved={proved} "
                  f"incumbents={incumbents} incomplete={incomplete} "
                  f"unknown={unknown} timeouts={timeouts} "
                  f"quality={quality:.4f} "
                  f"(targets={len(scores)}) checked_fail={checked_fail} "
                  f"errors={errors}", flush=True)

    checked_fail = sum(1 for r in rows if r["checked"].startswith("no"))
    errors = sum(1 for r in rows if r["outcome"] == "error")
    print(f"matrix: {matrix_path}")
    print(f"summary: {summary_path}")
    print(f"meta: {meta_path}")
    if checked_fail or errors:
        print(f"WARNING: checked_fail={checked_fail} errors={errors}", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    sys.exit(main())
