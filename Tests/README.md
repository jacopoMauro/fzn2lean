# Tests

Paths mirror the components under `LeanFzn/`. The retired Legacy solver and
its exclusive tests have been removed. The module-boundary audit rejects imports
that would reintroduce that dependency.

| Directory | Coverage |
| --- | --- |
| `Parser/` | Parsing and pretty-printing |
| `Semantics/` | Standard predicates, globals, typing, well-formedness and kernel-checked source-admission boundaries |
| `Checker/` | Solution parsing, acceptance, objectives and fast/reference agreement |
| `Compiler/` | Normalization, parameter arrays, literal folding, checked bounds, finite-set expansion, rank circuits, preprocessing and element forms |
| `Engine/` | Domains, literals, trail, clauses, queue, analysis, search and reduction |
| `Engine/Props/` | Generic, arithmetic, Boolean, linear, order, element and all-different propagators |
| `Integration/Public/` | Core-only source solving, partial optimization, seed reuse, incumbent policies, LNS and the parallel portfolio |
| `Cli/` | Python subprocess tests of exit codes, output, options and checked witnesses |
| `Architecture/` | Imports, cycles, active proof holes and public/test independence from Legacy |
| `Audits/` | Benchmark outcomes and strategy classifications (`test_performance_outcomes.py`, `test_strategy_outcomes.py`), oracle and release-gate failure paths (`test_oracle_gates.py`, `test_release_gates.py`), the semantic-inventory failure paths (`test_semantic_inventory.py`), the minimal-repository audit (`test_repo_minimal.py`), and MiniZinc wrapper streaming/flags (`test_validation_scripts.py`) |
| `Fixtures/Solver/` | Shared FlatZinc regressions used by current tests |

`Tests` is the maintained Lean test library. Python tests run separately.
`lakefile.toml` registers the current native executable targets.

## Registered test targets

Every module below is registered in `lakefile.toml` as a `lean_lib` glob
member or as a `lean_exe` root, so it is built by `lake build` and, for an
executable, run by `audits/run_gates.sh`.

`Tests/Compiler/`: `ArrayParams.lean`, `BoundsTest.lean`, `ChallengeScan.lean`, `LiteralFoldTest.lean`, `PreprocessTest.lean`, `RankCircuitTest.lean`, `SetEmitTest.lean`, `SetExpandTest.lean`, `SetShapeTest.lean`.

`Tests/Engine/`: `AnalyzeTest.lean`, `ClausesTest.lean`, `DomOpsTest.lean`, `DomTest.lean`, `DynamicTest.lean`, `LitTest.lean`, `QueueTest.lean`, `ReduceTest.lean`, `SearchTest.lean`, `TrailTest.lean`.

`Tests/Engine/Props/`: `AllDiffTest.lean`, `ArithTest.lean`, `BoolExtTest.lean`, `ElementTest.lean`, `LinearExtTest.lean`, `LinearTest.lean`, `OrderTest.lean`, `PropTest.lean`.

`Tests/Integration/Public/`: `CoreSeedTest.lean`, `GateTest.lean`, `IncumbentTest.lean`, `LnsTest.lean`, `PortfolioTest.lean`.

`Tests/Parser/`: `Smoke.lean`.

`Tests/Semantics/`: `ConformanceGraph.lean`, `ConformanceMatrix.lean`, `ConformanceT10PackSched.lean`, `ConformanceT10SchedRegular.lean`, `ConformanceT10SetLex.lean`, `Coverage.lean`, `WellFormed.lean`.

`Tests/Checker/Prof.lean` has no native `main`; `lakefile.toml` registers it
as the `Tests.Checker.Prof` library target (alongside the older `tests_prof`
executable) so `lake build Tests.Checker.Prof` checks its examples.

## Current tests

```bash
lake build Tests leanfzn tests_smoke tests_pretty tests_solution tests_check tests_fast tests_array_params tests_literal_fold tests_engine_search tests_engine_dynamic tests_engine_reduce tests_engine_incumbent tests_integration_core_seed tests_integration_portfolio tests_core_only
```

Run the relevant native executables in `.lake/build/bin/` after explicitly
building their targets. `lake build Tests` also checks the Lean-only test
modules, including their `example` proofs and `#eval` assertions, but does not
rebuild every native executable.

```bash
.lake/build/bin/tests_core_only
.lake/build/bin/tests_integration_core_seed
.lake/build/bin/tests_integration_portfolio
python3 -B Tests/Cli/test_admission.py
python3 -B Tests/Cli/test_solve.py
python3 -B Tests/Cli/test_protocol.py
python3 -B Tests/Cli/test_check_separators.py
python3 -B Tests/Cli/test_gate.py
python3 -B Tests/Audits/test_release_gates.py
python3 -B Tests/Audits/test_semantic_inventory.py
# `Tests/` is not a package: discover from the repository root, without -t.
python3 -B -m unittest discover -s Tests/Architecture
python3 -B -m unittest discover -s Tests/Audits
python3 -B audits/check_repo_minimal.py
python3 audits/check_module_boundaries.py
```

The compiler array suite compares Core with small exhaustive enumeration, then
checks rendered witnesses against the original source model. Public seed and
incumbent tests use `LeanFzn.Core` APIs, with no fallback adapters.

## Solution-format boundary

`Checker/Solution` checks parsed values for bare/wrapped arrays, sets before
other array elements, comments, empty arrays, malformed separators and
unterminated suffixes. `Checker/SolutionGrammar` constructs independent grammar
derivations for the original multi-element-set regression and derives parser
acceptance from completeness. `Compiler/SetEmitTest` covers normalized output,
set semantics, empty-array bounds and actual `solve` → file → `check` round trips.

```bash
lake build +Tests.Checker.SolutionGrammar tests_solution tests_set_emit tests_check tests_fast
.lake/build/bin/tests_solution
.lake/build/bin/tests_set_emit
.lake/build/bin/tests_check
.lake/build/bin/tests_fast
```

The independent grammar and the string-level emitter round-trip theorems are
included in `audits/certified_axioms.lean`. They cover non-float assignment
bodies. Stream separators use the exact `SolutionLine` classifier: only exact
marker lines after permitted padding are structural, status-only input is not a
candidate solution (exit 4), and malformed marker prefixes are rejected as
assignment content. `Tests/Cli/test_check_separators.py` exercises those exit
classes through the compiled CLI.

## Full validation

```bash
bash audits/run_gates.sh
```

The full gate builds current libraries and all registered executable targets,
runs applicable native/Python suites, proof/import audits, witness checks, the
public quick suite and optional independent Gecode coverage fuzz. The retired
Legacy battery, harness fuzz and Core/Legacy differential are removed; these
checks are not reported as passing. Small exhaustive comparisons remain in the
compiler array suite.

Put new regressions beside the component they exercise. Shared fixture data
belongs in `Fixtures/`. Store generated logs, profiles and benchmark reports
under ignored `tmp/`.

## FlatZinc conformance regressions

`Semantics/Conformance.lean` contains kernel-evaluated examples derived from
pinned native predicate contracts, including negative/zero durations,
asymmetric machine bounds and original machine-index offsets, all-false
conditional partiality, knapsack nonnegativity and duplicate set enumerations. Build it with
`lake build +Tests.Semantics.Conformance`. The inventory validator's failure
paths run with `python3 -B Tests/Audits/test_semantic_inventory.py`, and the
whole tree is checked by `python3 -B audits/check_repo_minimal.py`: every
landed support file must be used by a script, a Lake target, a test or a
maintained document.
Its independent `ConformanceGraph`, `ConformanceMatrix` and four
`ConformanceT10*` modules cover graph, matrix and additional native contracts.
These tests do not establish upstream equivalence or discharge the remaining
restricted-input premises. Python tests use managed system temporary
directories and do not require a machine-specific `/tmp/opencode` directory.
