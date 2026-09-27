#!/usr/bin/env python3
"""
Extract MiniZinc Challenge results (solver, instance, status, time, objective,
score) from the official per-challenge results.json published on minizinc.org
and write them as CSV.

The results.json contains, for every benchmark instance i and every pair of
solvers (s, s2), the pairwise Borda score scores[s][s2][i] used by the official
scoring script (https://www.minizinc.org/challenge/scoring.js). The per-instance
score displayed in the "Individual results" table is the sum over s2 of all
SELECTED solvers; we export the score summed over all participating solvers,
which matches the "select all solvers" view of the official table.

Usage: extract_results_csv.py [YEAR ...]   (default: 2025 2026)
"""
import csv
import json
import os
import sys

HERE = os.path.dirname(os.path.abspath(__file__))


def status_sort_key(status: str) -> int:
    """Order statuses sensibly for readability."""
    return {"SC": 0, "S": 1, "UNK": 2, "ERR": 3}.get(status, 4)


def extract(year: str, json_path: str, out_path: str) -> None:
    with open(json_path) as f:
        data = json.load(f)

    r = data["results"]
    solvers = r["solvers"]
    problems = r["problems"]
    instances_per_problem = r["instances"]  # list of benchmark indices per problem
    kinds = r["kind"]                       # MIN/MAX/SAT per problem
    benchmarks = r["benchmarks"]            # instance (data file) name per benchmark index
    results = r["results"]                  # [solver][benchmark] status
    times = r["times"]                      # [solver][benchmark] ms
    objectives = r["objectives"]            # [solver][benchmark] objective (' ' if none)
    scores = r["scores"]                    # [solver][opponent][benchmark] pairwise score
    scores_loc = r.get("scores_loc")       # incomplete-scoring counterpart, if present
    n_solvers = len(solvers)
    n_bench = len(benchmarks)

    # benchmark index -> problem
    bench_problem = []
    for p_idx, bench_idxs in enumerate(instances_per_problem):
        bench_problem.extend([(i, p_idx) for i in bench_idxs])

    with open(out_path, "w", newline="") as f:
        w = csv.writer(f)
        header = [
            "challenge", "problem", "problem_kind", "instance", "solver",
            "solver_class", "status", "time_ms", "objective", "score",
        ]
        if scores_loc is not None:
            header.append("score_incomplete")
        w.writerow(header)

        # Iterate like the official script: problem, then its instances
        for p_idx, bench_idxs in enumerate(instances_per_problem):
            kind = kinds[p_idx]
            prob = problems[p_idx]
            for i in bench_idxs:
                # keep original challenge ordering of solvers, but put fully
                # solved instances first for readability (stable sort)
                order = sorted(range(n_solvers), key=lambda s: (status_sort_key(results[s][i]), solvers[s]))
                for s in order:
                    cls_bits = []
                    if r["fd_solvers"][s]:
                        cls_bits.append("FD")
                    if r["free_solvers"][s]:
                        cls_bits.append("free")
                    if r["par_solvers"][s]:
                        cls_bits.append("parallel")
                    if r.get("open_solvers", [False] * n_solvers)[s]:
                        cls_bits.append("open")
                    if r.get("local_solvers", [False] * n_solvers)[s]:
                        cls_bits.append("local")
                    row = [
                        year,
                        prob,
                        kind,
                        benchmarks[i],
                        solvers[s],
                        "+".join(cls_bits),
                        results[s][i],
                        times[s][i],
                        objectives[s][i],
                        round(sum(scores[s][s2][i] for s2 in range(n_solvers)), 6),
                    ]
                    if scores_loc is not None:
                        row.append(round(sum(scores_loc[s][s2][i] for s2 in range(n_solvers)), 6))
                    w.writerow(row)

    n_rows = sum(len(b) for b in instances_per_problem) * n_solvers
    print(f"{year}: wrote {n_rows} rows ({len(problems)} problems x "
          f"{sum(len(b) for b in instances_per_problem)} instances x {n_solvers} solvers) -> {out_path}")


def main() -> None:
    years = sys.argv[1:] or ["2025", "2026"]
    for year in years:
        json_path = os.path.join("/tmp", f"results{year}.json")
        if not os.path.exists(json_path):
            url = f"https://www.minizinc.org/challenge/{year}/results.json"
            print(f"downloading {url}")
            import urllib.request
            urllib.request.urlretrieve(url, json_path)
        out_path = os.path.join(HERE, f"challengeResults{year}.csv")
        extract(year, json_path, out_path)


if __name__ == "__main__":
    main()
