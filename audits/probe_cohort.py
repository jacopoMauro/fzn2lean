#!/usr/bin/env python3
"""Run a cohort of FlatZinc files under one or more Core configurations (dev-only).

Each line reports exit code (0 SAT/optimum, 1 certified UNSAT, 2 usage/parse,
3 unsupported, 4 unknown/incomplete, TO = wall cap), wall time, number of emitted solutions, whether a terminal
marker was printed, and the `--stats` line. Witnesses are NOT checked here:
use benchmark_performance.py for witness-checked acceptance measurements.

Usage:
  python3 audits/probe_cohort.py --cohort audits/cohorts/T10.txt --limit 16 \
      --cap 10 --jobs 14 --config= --config=--var=minc [--out DIR]

Pass flags with `--config=...` (argparse rejects a separate value starting with --).
"""
import argparse
import concurrent.futures as cf
import os
import subprocess
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--cohort", required=True)
    ap.add_argument("--limit", type=int, default=0)
    ap.add_argument("--cap", type=float, default=10.0)
    ap.add_argument("--jobs", type=int, default=max(1, (os.cpu_count() or 2) - 2))
    ap.add_argument("--config", action="append", default=None,
                    help="space-separated solve flags; repeatable; '' = defaults")
    ap.add_argument("--binary", default=os.path.join(ROOT, ".lake/build/bin/leanfzn"))
    ap.add_argument("--out", help="directory for raw stdout/stderr")
    a = ap.parse_args()
    files = [l.strip() for l in open(a.cohort) if l.strip() and not l.startswith("#")]
    if a.limit:
        files = files[:a.limit]
    configs = [c.split() for c in (a.config or [""])]
    if a.out:
        os.makedirs(a.out, exist_ok=True)

    def run(job):
        f, cfg = job
        t0 = time.time()
        try:
            p = subprocess.run([a.binary, "solve", *cfg, "--stats", os.path.join(ROOT, f)],
                               capture_output=True, text=True, timeout=a.cap)
            rc, out, err = str(p.returncode), p.stdout, p.stderr
        except subprocess.TimeoutExpired as e:
            rc = "TO"
            out = (e.stdout or b"").decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
            err = (e.stderr or b"").decode() if isinstance(e.stderr, bytes) else (e.stderr or "")
        dt = time.time() - t0
        tag = " ".join(cfg) or "default"
        if a.out:
            stem = os.path.join(a.out, f.replace("/", "_") + "." + (tag.replace(" ", "_").replace("-", "") or "default"))
            open(stem + ".out", "w").write(out)
            open(stem + ".err", "w").write(err)
        sols = out.count("----------")
        done = "==========" in out or "=====UNSATISFIABLE=====" in out
        stats = " ".join(l for l in err.splitlines() if "stats:" in l)
        return f"{os.path.basename(f):42s} {tag:22s} rc={rc:3s} t={dt:6.2f} sols={sols:3d} done={done} | {stats[:200]}"

    jobs = [(f, c) for f in files for c in configs]
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for line in ex.map(run, jobs):
            print(line, flush=True)


if __name__ == "__main__":
    main()
