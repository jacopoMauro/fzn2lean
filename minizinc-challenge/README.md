# MiniZinc Challenge Benchmark Directory

## Goal of this directory

This directory hosts the raw material for benchmarking the LeanFzn /
leanfzn solver stack against reference CP solvers on **real, competitively
representative instances**:

- `2025mzn/`, `2026mzn/` — the official problem bundles of the MiniZinc
  Challenge 2025 and 2026 (downloaded from
  `https://www.minizinc.org/challenge/<year>/mznc<year>_probs.tar.gz`).
  Each problem is a directory with one model (`.mzn`) and five data files
  (`.dzn` / `.json`) — the exact instances used in the challenge.
- `2025fzn/`, `2026fzn/` — those models compiled to FlatZinc, ready to be
  consumed directly by the LeanFlatZinc parser/solver without needing a
  MiniZinc installation.
- `challengeResults2025.csv`, `challengeResults2026.csv` — the complete
  official results of both challenges (extracted from the site's
  `results.json`): status, runtime (ms), objective and the official Borda
  score for every solver on every instance.
- `comparison/` — output of `run_lean_comparison.py`: per-instance runs of
  `leanfzn` (wall time, CPU time, peak RSS) next to the reference Gecode /
  OR-Tools CP-SAT challenge numbers.
- `compile_fzn.sh`, `extract_results_csv.py`, `run_lean_comparison.py` —
  the three scripts to regenerate everything from scratch.

## Key decisions and why

### 1. FlatZinc is compiled with `minizinc --solver Gecode -G std`

The Gecode *engine* sets the target architecture, but the default Gecode
globals library (`-G gecode`) decomposes globals into **Gecode-branded
predicates** (`gecode_int_element`, `gecode_table_int`,
`gecode_global_cardinality`, `gecode_circuit`, …) that exist only because
Gecode links dedicated propagators for them. The LeanFzn checker and solver
implement the **MiniZinc-declared standard FlatZinc predicates**
(`fzn_all_different_int`, `fzn_table_int`, `fzn_global_cardinality`,
`int_lin_eq`, `set_in_reif`, … — 218 checked names, 138 supported `fzn_*`
globals, see `LeanFzn/FznGlobals.lean`).

Compiling with `-G std` uses the solver-neutral standard globals library:
globals are kept as the standard `fzn_*` predicates, and everything else is
decomposed into plain `int_*`/`bool_*`/`set_*` builtins.

### 2. `--no-output-ozn` when compiling

Only FlatZinc itself is needed (the Lean solver produces its own verdicts
from the FZN). The `.ozn` output section is dropped to avoid carrying
dead weight and to make it obvious that these files are *inputs to a
solver*, not entries of a MiniZinc execution round-trip.

### 3. One `.fzn` per (model, data-file) pair

The challenge instances are fixed-model-plus-data; compiling each data file
separately gives exactly the instance granularity both the challenge and
the results CSVs use, so every measurement row is directly joinable with
`challengeResults<year>.csv` by `(challenge, problem, instance)`.

### 4. Compilation budgets

Each compilation gets a 300 s wall-clock timeout (`PER_FILE_TIMEOUT`). The
bundles recompile in a few minutes; a failing compile is logged to
`/tmp/fzn_<problem>_<instance>.log` and counted, not fatal.

### 5. The comparison runner filters before measuring

`run_lean_comparison.py` deliberately measures only instances on which
**both** reference engines (Gecode-fd, OR-Tools CP-SAT-fd) finished in
under `--max-seconds` (default 20 s). Rationale:

- a Lean run can only be compared meaningfully where the reference had a
  *completed* run (status `S`/`SC`),
- small instances keep the Lean runs finite (LeanFzn has explicit
  search-space and domain-size caps, e.g. a per-variable domain cap of
  10000 values and a complete-assignment cap of 10^6 for the checker
  stage), so the default timeout of 300 s is generous but bounded,
- the filter threshold is a single flag so stricter/looser cuts can be rerun
  without touching the code.

Resource measurement is per-run: wall time via monotonic clock, CPU time
via `getrusage(RUSAGE_CHILDREN)`, and peak RSS both via `ru_maxrss` and a
high-water mark sampled from `/proc/<pid>/status` (`VmHWM`), the latter
being the truthful per-run value because `ru_maxrss` for children is the
maximum over all children ever reaped.

### 6. Scores are taken from the official per-challenge data source

The results pages on minizinc.org are JavaScript-rendered; the underlying
data lives at `https://www.minizinc.org/challenge/<year>/results.json` and
the scoring semantics in the site's `scoring.js`. The CSVs preserve the
official pairwise-Borda scoring exactly as the website computes it (the
per-instance `score` column is the sum over all opponent solvers, i.e. the
"select-all" view of the official individual-results table). The raw
`results<year>.json` files are kept here so the extraction is reproducible
without network access.

## Regenerating everything

```bash
./compile_fzn.sh                     # recompile all FlatZinc (both years)
python3 extract_results_csv.py       # rebuild the two result CSVs (uses cached JSONs)
python3 run_lean_comparison.py       # rebuild comparison/ CSVs (default X = 20 s)
```
