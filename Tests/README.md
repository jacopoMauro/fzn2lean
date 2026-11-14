# Tests

Paths mirror the components under `LeanFzn/`. Current tests never import Legacy;
the module-boundary audit enforces that rule transitively.

| Directory | Coverage |
| --- | --- |
| `Parser/` | Parsing and pretty-printing |
| `Semantics/` | Standard predicates, globals, typing and well-formedness |
| `Checker/` | Solution parsing, acceptance, objectives and fast/reference agreement |
| `Compiler/` | Normalization, parameter arrays, literal folding, checked bounds, finite-set expansion, rank circuits, preprocessing and element forms |
| `Engine/` | Domains, literals, trail, clauses, queue, analysis, search and reduction |
| `Engine/Props/` | Generic, arithmetic, Boolean, linear, order, element and all-different propagators |
| `Integration/Public/` | Core-only source solving, partial optimization, seed reuse, incumbent policies, LNS and the parallel portfolio |
| `Cli/` | Python subprocess tests of exit codes, output, options and checked witnesses |
| `Architecture/` | Imports, cycles, active proof holes and public/test independence from Legacy |
| `Audits/` | Benchmark outcomes, incomplete allowances, validation failure paths and MiniZinc wrapper streaming/flags |
| `Fixtures/Solver/` | Shared FlatZinc regressions used by current tests and the Legacy oracle |
| `Legacy/Integration/` | Historical adapters, options, fallback behavior and the Core/Legacy differential tool |
| `Legacy/Solver/` | Chronological, propagation and UIP historical regressions/harnesses |
| `Legacy/Benchmarks/` | Retained diagnostic tools for the list-based solver |

`Tests` is the current Lean test library. `Tests.Legacy` is a separate explicit
library. Python tests are run separately. Existing executable names are retained
so scripts can keep calling the same Lake targets; their `root` entries in
`lakefile.toml` point to the new locations.

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
python3 -B Tests/Cli/test_solve.py
python3 -B -m unittest discover -s Tests/Architecture
python3 -B -m unittest discover -s Tests/Audits
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
bodies; stream separators are handled by their separate normalization lemmas.

## Historical tests and full validation

```bash
lake build LeanFzn.Legacy Tests.Legacy tests_lcg_harness
.lake/build/bin/tests_lcg_harness --fixtures
bash audits/run_gates.sh
```

The full gate builds both libraries and all registered executable targets,
runs the applicable native/Python suites, differential checks, proof/import
audits, the Legacy fuzz harness and the public quick suite. Argument-driven
profilers are not correctness suites and are skipped or run with dedicated
arguments. The differential tool deliberately imports Legacy; it remains a
development oracle, not a public solver path.

Put new regressions beside the component they exercise. Put a test under
`Legacy/` if its purpose requires historical solver APIs. Shared fixture data
belongs in `Fixtures/`, not in an old implementation's test directory. Store
generated logs, profiles and benchmark reports under ignored `tmp/`.
