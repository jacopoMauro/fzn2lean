# MiniZinc Challenge inputs

`2025mzn/` and `2026mzn/` contain the challenge model/data bundles;
`2025fzn/` and `2026fzn/` contain precompiled FlatZinc. The original archives
and `results<year>.json` files support reproducing the inputs and official
result CSVs. Oversized FlatZinc inputs listed in the root `.gitignore` are
not retained in the repository.

`challengeResults2025.csv` and `challengeResults2026.csv` contain the official
per-solver statuses, times, objectives and scores extracted by
`extract_results_csv.py`. A status of `S` means a solution was found; `C`
means search completed; `SC` means both. A solution alone does not establish
an optimum. These external results are comparison data, not measurements of
the current LeanFzn build.

## Regenerating inputs

Run from this directory, with MiniZinc 2.10.1 on `PATH` (or set
`MINIZINC_BIN` to its executable):

```bash
./compile_fzn.sh                  # both years
./compile_fzn.sh 2025             # one year
python3 extract_results_csv.py    # uses cached official JSONs
```

Compilation uses `--solver Gecode -G std` and omits the output `.ozn` file.
The standard library keeps solver-neutral predicates rather than
Gecode-specific globals. Each compilation has a 300-second wall cap; failures
are logged, partial outputs are removed, and the script exits nonzero if any
compilation fails. Checker coverage is defined in
`LeanFzn/Semantics/Globals.lean` relative to the repository root. The solver
accepts a smaller fragment, documented in [README.md](../README.md).

## Measuring LeanFzn

Use the maintained [audit tools](../audits/README.md):
`benchmark_performance.py` for budgeted cases, `strategy_matrix.py` for
cohorts/configurations and `oracle_check.py` to check witnesses and compare
claims with the official results. The old comparison runner and its generated
CSVs used removed CLI flags and obsolete exit-code classifications and have
been removed. New reports belong under ignored `tmp/`, with their binary/source
snapshot and run budget recorded.
