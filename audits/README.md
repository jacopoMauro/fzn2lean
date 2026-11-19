# Audit tools and benchmark records

Run commands from the repository root. These files support development and CI;
they are not solver runtime dependencies.

## Proof and architecture checks

- `certified_axioms.lean`: selected theorem axiom queries, also used by CI.
- `run_axiom_audit.sh`: runs and checks every registered query; fails on Lean
  errors, missing profiles, `sorryAx`, or non-allowlisted axioms.
- `check_module_boundaries.py`: checks component/test import boundaries, cycles,
  active proof holes and user axiom declarations, ignoring comments and strings.

Build the relevant libraries before running the axiom audit:

```bash
lake build LeanFzn
bash audits/run_axiom_audit.sh
python3 audits/check_module_boundaries.py
```

## FlatZinc semantic conformance

The reviewed source-contract inventory covers every active `stdSig` and
`globalsSig` name, the published builtins/functions (including explicit
exclusions), and declaration/model rules. Read
[the review](../specification/minizinc-2.10.1/predicates_and_globals_report.md)
and [machine-readable evidence](../specification/minizinc-2.10.1/semantic_conformance.json).

```bash
python3 -B audits/check_semantic_inventory.py
python3 -B Tests/Audits/test_semantic_inventory.py
lake build +Tests.Semantics.Conformance
# Required review-freshness check; upstream equivalence is a separate obligation:
python3 -B audits/check_semantic_inventory.py --require-clean
```

The default check validates complete name coverage and exact reviewed-file
hashes; it does not prove semantics. A changed implementation/helper/reference
invalidates the review. Re-review changed contracts and update the inventory
explicitly; do not refresh hashes as an automatic approval step.
`--require-clean` currently passes: all 15 recorded findings are marked fixed.
Thirteen rows remain explicitly restricted. Passing checks review freshness and
recorded finding states; it does not establish upstream equivalence or enforce
every admissibility premise. These obligations cannot be discharged by a
Boolean/Prop agreement theorem or benchmark suite.

For a fresh download of the immutable libminizinc tree, use
`--upstream-root PATH` to check all recorded upstream source hashes; PATH must
contain `share/minizinc/std/` and `docs/en/fzn-spec.rst`. No network request is
made by the checker. Both gate runners require the clean semantic check; the
release runner checks
the frozen snapshot and preserves the review evidence. The PGO/non-PGO gate
alone does not establish semantic conformance.

## Public Core benchmarks

`benchmark_performance.py` uses `performance_manifest.json` with small Latin,
linear/hole, reified, optimization and wide-domain examples, generated
parameterized scales, plus opt-in real challenge diagnostics. Defaults: 2
seconds per solver call and 60 seconds total; short tier is 10 seconds.
Medium/long tiers require explicit cases and a suite budget. No solver
invocation may exceed 300 seconds. Raw output, witness checks, completion
status, hashes and incremental JSON go to a fresh directory under
`tmp/performance/` by default. Incomplete optimization incumbents are distinct
from certified optimum completion. Timeout is an observation, not a correctness
pass; this scaffold does not replace proof/fuzz validation.

```bash
lake build leanfzn
python3 audits/benchmark_performance.py --tier quick --suite-budget 60
python3 audits/benchmark_performance.py --tier short --case challenge_fbd4 --suite-budget 30
python3 audits/benchmark_performance.py --tier quick --case gen_latin3 --suite-budget 10
```

### Cost attribution fields (B0)

Per case the runner records `peak_rss_kib`/`peak_rss_source`, streamed solution
timestamps (`time_to_first_solution_s`, `time_to_last_solution_s`,
`time_to_optimum_s`), `objective_var`, the `objective_trajectory` (observation
time plus parsed objective value for every improving solution), and the raw
`solve`/`check` subprocess records including `solutions_stream`. The top-level
`selected_cases`, `repetitions`, `skipped` and `summary` fields record the
chosen denominator (outcome counts, complete count, expected agreement, witness
accepts, summed solve wall time, max peak RSS).

- Peak RSS is the maximum polled `/proc/<pid>/status` `VmHWM` sample while the
  child lives. If the process exits before a sample, the
  `RUSAGE_CHILDREN.ru_maxrss` high-water mark is recorded instead; it is exact
  when the mark grew during this child and an upper bound otherwise.
  `peak_rss_source` names the method.
- Solution timestamps are stdout-observation times at `--poll-interval`
  (default 0.02 s), so they upper-bound the solver's emission time. The solver
  flushes after every improving solution, so the slack is mostly the poll.

### Source snapshot reproducibility

`--source-snapshot` writes `source_snapshot.json` with path+sha256+size for
every `LeanFzn/**/*.lean`, `lakefile.toml`, `lean-toolchain` and
`lake-manifest.json`, plus git head/status, the binary hash, and the bounded
`lake env lean --version` probe record. It also copies those files into
`source_snapshot_files/` under the run directory. A full `git diff` is
deliberately not collected: it can take minutes in this repository, so the hash
manifest plus the copies are the snapshot.

### Generated fixtures (`generate_cases.py`)

`python3 audits/generate_cases.py [--register]` deterministically writes the B0
parameterized scales under `audits/benchmark_fixtures/generated/` together with
`generated_manifest.json` (generator, parameters, seed, expected result,
witness, and how the result was established). `--register` adds or updates the
generated entries in `performance_manifest.json` with `default: false`, so the
default quick suite is unchanged. Existing constructed witnesses are re-checked
with `leanfzn check` on every generation.

| Generator | Cases | Parameters | Seed | Expected | Independent check |
| --- | --- | --- | --- | --- | --- |
| `latin` | `gen_latin3/4/5` | `n=3/4/5` | none (construction) | sat | `x_ij = (i+j) mod n + 1`, `leanfzn check` |
| `domain_width` | `gen_domain64/256/1024` | `width` | none | sat | constructed witness, `leanfzn check` |
| `dense_clause` | `gen_bool_dense40/60` | vars/clauses | 20261017 / 20261018 | sat | planted assignment, `leanfzn check` |
| `pigeonhole_bool` | `gen_pigeonhole_bool3/4` | holes 3/4 | none (construction) | unsat | exhaustive pigeon-to-hole injection enumeration, cross-checked against all `2^k` assignments for `n_holes <= 3` |
| `linear_chain` | `gen_linear8/32` | `n` | none | sat | constructed witness, `leanfzn check` |
| `holes` | `gen_holes` | `width=40`, holes `0..10` | none | sat | constructed witness, `leanfzn check` |

`heldout_gcc_toy` is an opt-in challenge diagnostic. Do not assume its expected
outcome from an old coverage report; record the actual observation.

## Fixed-limit A/B

`fixed_k.py` runs two binaries (or two flag sets on one binary) over a cohort at
one `--conflict-limit=K` and compares the deterministic counters (decisions,
conflicts, learned, propagations, `learnedLitsBefore/After`, `maxLevel`, rounds)
and the auxiliary `reasonsTrimmed` trim counter, plus outcome and objective,
reporting wall ratios at the same limit. `reasonsTrimmed` is not a search-action
counter, but a Tier A change that preserves the search tree must leave it
unchanged as well. Same-binary
runs must be identical; a difference is a bug in the twin, not a result. It
holds the measurement lock and is the Tier A tool.

```bash
python3 audits/fixed_k.py --cohort audits/cohorts/T10.txt --limit 300 \
  --binary-a tmp/baseline/leanfzn-7e9c730e --out tmp/performance/my-ab
```

## Configuration comparisons

`strategy_matrix.py` runs selected public CLI configurations over input lists in
`cohorts/`, sequentially under a measurement lock and a wall cap. It checks the
last emitted solution and records objective quality against `strategy_targets.tsv`.
The label `default` means no search flags (Core `act/incumbent`, with Luby
restarts after the first incumbent); use `strategy=default` for the explicit
`minc/act` preset, and `var=act+val=min+restart=none` for the pre-A1/A2 policy. Other supported flags can be joined with `+`.
`--cores=LIST` passes a taskset CPU list or range (for example `0,2,4,6`)
instead of the single `--core`; use it when a config runs multiple workers.
`--conflict-limit=N` can be passed the same way: it caps each Core optimization
round and exits 4 with a `cause="conflict limit reached"` stats line, which lets
a triage run measure conflicts per second on cases that otherwise only time out.
It is a diagnostic conflict budget, not a wall-clock limit and never a verdict.

```bash
python3 audits/strategy_matrix.py --configs default,var=minc+val=min,annot --cohort audits/cohorts/T10.txt --cap 10
```

`probe_cohort.py` is a faster, parallel triage run over the same cohorts: it
records exit code, wall time, solution count and the `--stats` line per
configuration, without witness checking or a measurement lock. Use it to count
give-ups or spot regressions; use `strategy_matrix.py`/`benchmark_performance.py`
for accepted comparisons. Pass flags as `--config=--var=minc`.

```bash
python3 audits/probe_cohort.py --cohort audits/cohorts/T10.txt --limit 16 --cap 10 --config= --config=--var=minc
```

### Profiling

The devcontainer has no perf/gdb. `profile_sample.py` samples the busiest
`leanfzn` thread with ptrace and maps PCs to symbols (PIE base handled). Self
counts are exact samples; inclusive counts use a heuristic stack scan and are
approximate. Check suspicious hot spots in the generated C under
`.lake/build/ir/LeanFzn/`.

```bash
python3 audits/profile_sample.py --seconds 8 -- .lake/build/bin/leanfzn solve MODEL.fzn
```

### Cohort freezing rule

Before comparing two versions, freeze a cohort: fix the manifest
(`manifest_sha256`), every case `input_sha256`, the tier, suite budget, and
repetition count, and record both binaries' sha256 plus their `--source-snapshot`
manifests. Generated fixtures are deterministic, so regeneration must reproduce
the same file hashes; a changed fixture hash means the cohort changed and old
and new results are not comparable. Never mix cases, budgets, tiers, or
repetition counts across the two sides of a comparison, and treat timeouts and
incomplete optimization incumbents as censored observations rather than times.

## Oracle and coverage fuzz (O3)

`oracle_check.py` independently audits a `strategy_matrix.py` results directory,
and `coverage_fuzz.py` generates deterministic micro-models and compares Core
with `fzn-gecode`. Both are development-only, use only the Python standard
library, and are never imported by Lean or by `LeanFzn/`. Gecode is an
independent oracle, not a solver dependency: an `unsupported` result is honest
and is never counted as agreement.

```bash
python3 audits/oracle_check.py tmp/performance/o1-cov37-check
python3 audits/oracle_check.py RESULTS_DIR --binary .lake/build/bin/leanfzn \
  --targets audits/cohorts/strategy_targets.tsv --json /tmp/oracle.json
python3 audits/coverage_fuzz.py --seeds 50 --start 0 --out tmp/o3-fuzz-smoke
python3 audits/coverage_fuzz.py --seeds 200 --out tmp/o3-fuzz
```

`oracle_check.py` runs three oracles and exits non-zero on any failure:

- **witness**: every complete solution block in every `.stdout` and every
  captured `.last-solution.txt` is re-run through `leanfzn check` on the
  original model. A rejected witness is a hard failure; the report names the
  file, row and block, and keeps a copy under `oracle_failures/`.
- **challenge**: joins each model path to
  `minizinc-challenge/(\d{4})fzn/<problem>/<instance>.fzn` in
  `challengeResults2025.csv` / `challengeResults2026.csv`, and joins
  `strategy_targets.tsv` for kind and target. The official statuses are `S`
  (solution found), `C` (search complete), and `SC` (both), so `C` without `S`
  is a complete search that found no solution. It fails a proved UNSAT when any
  solver reports `S` or `SC`; a claimed solution when all reported statuses are
  `C`/`UNK` and at least one is `C`; a proved optimum that differs from an `SC`
  objective; an incumbent better than an `SC` objective; and an incumbent
  better than the target (MIN: lower, MAX: higher).
- **cross-run**: within the results directory, fails UNSAT versus a solution
  for the same model, two different proved optima, and an objective better
  than a proved optimum or target.

`unsupported` (exit 3), `unknown` (exit 4), timeout and missing output are
reported as observations, never as agreement. The machine-readable report goes
to `RESULTS_DIR/oracle_report.json` (or `--json`) and a short text summary to
`RESULTS_DIR/oracle_summary.txt`.

`coverage_fuzz.py` covers the O2 literal shapes, reified literal-result forms,
case-split `var int` patterns, finite bounds, constant sets and set variables
(empty/reversed/duplicate/out-of-range sets, `set_in`, `set_in_reif`,
`set_card`, `set_union`, `set_intersect`, `array_var_set_element`), ground
constraints, out-of-range element indices, and MIN/MAX micro-optimizations. It
runs `leanfzn solve` and `fzn-gecode -a` under a wall cap, compares SAT/UNSAT,
compares the MIN/MAX optimum exactly, and checks every emitted Core solution
block with `leanfzn check` on the original model. The summary prints the
`unsupported` rate, the explicit `comparisons` denominator, and
`wrong`/`boundEx`/`rejectedWitness` counts. `--extra-model` adds a specific
model, `--keep` retains passing run artifacts, and a simple line-deletion
reducer writes any smaller failing model under `OUT/failures/`.

Core's public CLI has no all-solutions mode: for satisfaction it prints one
solution, so Gecode's `-a` count is compared only directionally (Core must not
print more distinct solutions than Gecode enumerates); for optimization the
optimum is compared exactly. Gecode input is copied to a local temporary file
because some workspace filesystems do not support the `mmap` Gecode uses. If
`fzn-gecode` is absent the fuzzer prints `SKIP` and exits 0; the gate reports
that as a skip rather than a silent pass.

The gate runs both tools in section 7. `ORACLE_RESULTS=DIR` reuses an existing
matrix directory instead of generating the two-model micro directory, and
`O3_FUZZ_SEEDS=N` changes the default 200 gate seeds.

### Checking the oracles

Use synthetic false verdicts, incorrect optima and corrupted witnesses to
exercise the failure paths. Keep the synthetic models, altered outputs and
reports in a fresh directory under `tmp/`. A useful regression must assert a
nonzero exit and the expected diagnostic, rather than relying on a historical
report from another checkout.

## Full validation

```bash
bash audits/run_gates.sh
```

The gate stops immediately if the aggregate source build fails, so old
binaries cannot mask a broken checkout. It builds current libraries/test suites
and registered native executables, runs native/Python regressions (including
validation-script and wrapper failure paths), audits axioms/import boundaries,
and runs the public quick suite, witness oracles and optional Gecode coverage
fuzz. The Legacy comparison tool, battery and harness fuzz were retired with
the old implementation. Current compiler tests retain small exhaustive oracles.
See [Tests/README.md](../Tests/README.md) for focused test commands.

Generated reports belong under ignored `tmp/`. Superseded plan snapshots,
one-off profiling modules, old coverage/result tables and duplicate benchmark
runners have been removed. Keep reusable inputs/manifests and regression fixtures.

## Release certification

```bash
bash audits/run_release_gates.sh
```

This is the required release gate separate from `run_gates.sh`: it snapshots the
tracked and non-ignored untracked implementation source and semantic-review
evidence into `tmp/release/<id>/{pgo,nopgo}`, removes
exactly the package `moreLeancArgs` line from the non-PGO tree, checks the frozen
semantic inventory, builds both variants serially under `tmp/lake.lock` with `nice`, verifies build isolation
and distinct binary hashes, then runs `audits/release_cohort.tsv` through the
snapshot copies of `audits/release_compare.py` and `audits/fixed_k.py`. The
comparator is invoked with `--require-snapshot-harness`, so a byte-level
substitution of either harness is a setup error rather than a pass. It requires
identical deterministic single-worker counters and terminal classes, equal
objectives/optima where known, every witness accepted by both `leanfzn check`
front doors, and every fixed-k `model_sha256` equal to the frozen fixture; it
writes `manifest.json`, `comparison.json` and `summary.txt` and fails closed on
missing evidence. Exit 1 means a case/comparison/timeout/report failure and
exit 2 means setup/cohort/manifest/harness incompatibility. `--expected-manifest`
pins the cohort, source, toolchain, MiniZinc, binary provenance and the
`tooling.fixed_k`/`tooling.release_compare` hashes for reproducible reruns. The
finite cohort is behavioural evidence, not a proof of compiled-code
correctness; see [pgo/README.md](../pgo/README.md).

The [17 November repository review](STATUS.md) records the current assurance
boundaries, validation evidence, untracked inputs and remaining work.
