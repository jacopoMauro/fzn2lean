# LeanFzn — verified FlatZinc tools in Lean 4

LeanFzn provides a parser, a solution checker and a certified finite-domain
solver for FlatZinc. Shared formal semantics connect parsed models, checked
solutions and solver results.

- **Parser:** soundness and completeness with respect to the project's
  declarative grammar.
- **Solution checker:** verified checking of integer, Boolean and set models
  using supported standard predicates and global constraints.
- **Core solver:** certified array-based finite-domain search with propagation,
  learned clauses, conflict analysis, backjumping and branch-and-bound.

The public `solve` command runs **Core only**. Its default CLI search is
`--var=act --val=min`. If Core gives up, satisfaction reports unknown and
optimization reports incomplete, both with exit code 4. Already streamed
incumbents remain valid; no UNSAT or optimality marker is emitted for an
incomplete run. Options Core does not implement are usage errors, with no
implicit engine switching.

The old list-based solver and its fallback adapters are preserved under
[LeanFzn/Legacy/](LeanFzn/Legacy/README.md) for explicit development use and
historical certified theorems. They are not imported by the public CLI or Core
API. Shared domain/constraint semantics and compiler proof foundations remain
outside Legacy. See [PLAN.md](PLAN.md) for the active work and historical runs.

The language reference is **MiniZinc 2.10.0**, pinned to commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea`. See the
[vendor reference](specification/minizinc-2.10.0/README.md) and
[formalization assumptions](specification/flatzinc_specification_assumptions.md).
Float syntax and semantics are outside the supported fragment; strings are
supported in annotations.

## Guarantees and supported scope

### Parser

`LeanFzn.Parser.parseModel_ok_iff_valid` states that parsing succeeds exactly
when the input satisfies `ValidFlatZinc`. Parser soundness and completeness
also identify the AST produced by a grammar derivation. The recursive-descent
parser's fuel bound is proved sufficient.

Recognition is relative to the grammar over tokens produced by the project's
lexer. Lexical conventions and differences from the reference grammar are
recorded in the formalization assumptions.

### Solution checker

`leanfzn check` checks supplied solutions against the model's domains,
initializers and constraints. It establishes static well-formedness, supported
predicate names and valid solution entries before checking satisfaction.
Solution entries must name declared variables, with no duplicate assignments
or parameter reassignment. Model parameters retain their declared values.

`LeanFzn.Checker.checkModelSolution_correct` characterizes acceptance in terms
of the formal model semantics. `checkModelSolution_accepted` additionally ties
that satisfying store to the values written in the solution and the model's
parameters. The executable fast entry is proved equivalent to the verified
entry by `checkModelSolutionFast_eq`.

Supported predicates have executable interpretations proved equivalent to their
declarative meanings. The checker covers standard arithmetic, Boolean and set
predicates and supported global constraints. Unknown or unsupported predicates
produce an explicit unsupported outcome. The predicate definitions and coverage
lists live in `LeanFzn.Semantics` and `LeanFzn.Checker.Globals`.

The checker accepts solver output containing several solutions separated by
`----------` and checks each solution. It reports the first failure.

### Certified solver

`leanfzn solve` compiles supported, statically well-formed satisfaction models
with finite nonempty integer/Boolean domains. It propagates constraints and
learns entailed clauses using an array-based trail and clause database.
Unsupported declaration or constraint forms are reported explicitly.
`solve minimize/maximize <int variable>` uses certified branch-and-bound;
the final `==========` marker is backed by UNSAT under the improving bound.

The accepted constraint families are `int_eq`, `int_ne`, `int_le`, `int_lt`,
`int_plus`, `int_times`, `int_min`, `int_max`, `array_int_minimum`, `array_int_maximum`
(including supported literal-operand shapes), `int_abs`, `int_div`, `int_mod`,
`int_lin_eq`, `int_lin_le`, `int_lin_ne`, `bool_not`, `bool_and`, `bool_or`,
`bool_eq`, `bool2int`, `bool_clause`, `array_bool_and`, `array_int_element`,
`array_var_int_element`, `array_var_bool_element`, the reified forms
`int_eq_reif`, `int_le_reif`, `int_ne_reif`, `int_lin_eq_reif`,
`int_lin_le_reif`, `int_lin_ne_reif`, and `all_different`. Constant-set `set_in` and supported `set_in_reif`
forms are also compiled; the front end can fold membership restrictions into
finite integer domains. See [SetIn.lean](LeanFzn/Compiler/SetIn.lean).
`int_gt` and `int_ge` are also accepted for variable–constant comparisons.
Variables must be initializer-free scalar Booleans or integers with an explicit
finite range or enumerated domain. Literal scalar and array parameters and the supported variable-array aliases
are normalized before scalar compilation. Objectives must name an integer slot.

Support also depends on the argument form. Linear constraints require inline
arrays of literal integer coefficients and scalar variable names, matching array
lengths, and a literal integer right-hand side. `all_different` requires an
inline array of scalar variable names. Supported parameter arrays and variable-array aliases may also supply these
arguments after normalization. Other predicates accept the variable/literal
forms implemented by the [constraint extractor](LeanFzn/Compiler/Extract.lean)
and [compiler](LeanFzn/Compiler/Compile.lean); arbitrary expressions and parameter
substitution are not supported uniformly. For example, `int_le(x, k)` can resolve
a scalar integer parameter `k`, whereas `int_eq(x, k)` currently cannot; an
integer literal in its place is accepted.

| Unsupported feature | Why it is outside the current solver fragment |
| --- | --- |
| General objective expressions | Certified optimization currently requires a plain integer variable objective. |
| Unbounded `var int` | Search enumerates finite domains; its termination argument needs a finite set of candidates. |
| Set-valued variables, including bounded sets | Solver slots represent scalar integer/Boolean values. Set-value domains and their certified compilation are not implemented. |
| General array variable declarations/indexing | The front end supports aliases of scalar integer/Boolean slots and the compiled element/array families; arbitrary array storage and general index expressions remain unsupported. |
| Variable initializers | The accepted declaration translation handles initializer-free variables. Initializer relationships are not compiled; express supported scalar relationships as constraints instead. |
| General parameter expressions | Literal integer/Boolean arrays and supported constant-set membership forms are supported; arbitrary expression evaluation remains outside compilation. |
| Predicate declaration items | The compiler rejects predicate items and translates only its built-in constraint families. |
| Empty variable domains | The public solver gate requires every domain to be nonempty. It does not currently turn an empty domain into a certified UNSAT result. |
| `bool_xor`, general set constraints and other globals | Only implemented argument patterns and constraint translations have a certified solver route. Constant-set membership is supported; set-valued search slots are not. |
| Propagation strength | Core registers dedicated propagators for selected arithmetic, linear, order, Boolean and element shapes, with a generic checking propagator for remaining shapes. The kernel has its own explained-propagator registration. Compilation support does not imply equally strong propagation in both engines. |
| Other argument forms of the listed predicates | Compilation only covers specific argument patterns; the predicate name alone does not guarantee acceptance. |

These are limits of the current compiler and certified Core implementation;
changing the search policy does not by itself remove them.
For parsed, well-formed models outside this fragment, `solve` reports an
unsupported reason and exits with code 3. Syntax outside the parser's language,
such as floating-point declarations, instead produces a parse error (exit 2).

`LeanFzn.Core.solveModel_sat_correct` and `solveModel_unsat_correct` connect
Core results to source-model semantics. Core stores entailed clauses with
erased proofs, checks SAT assignments with `fitsB && accepts`, and derives
UNSAT from an entailed empty clause. A failed domain conversion, exhausted
search fuel or internal analysis give-up returns unknown; it never invokes
the old solver.

Linear and seeded optimization retain solution soundness, strict improvement,
and optimality/UNSAT guarantees **when `run.complete = true`**. There is no
unconditional completion guarantee in the new public API. The shared
`PartialCertSolver` interface supplies SAT/UNSAT soundness without assuming
that every search decides. Its adapter uses the generic optimizer's false
completeness gate explicitly; the optimizer still runs and preserves partial
progress. The old completion theorems are unchanged in Legacy and apply only
to their preserved legacy definitions.

For example, `var {0,1000000}: x; solve satisfy;` currently passes compilation
but Core cannot convert that wide sparse domain. The public command returns
unknown (exit 4). Improving this Core coverage is future work; there is no
hidden fallback masking it. Certification supplies correctness guarantees for
returned claims, not practical running-time or decision-coverage guarantees.

## Repository structure

| Component | Responsibility |
| --- | --- |
| `Syntax/`, `Parser/` | AST, lexer, grammar, parser, printer and recognition proofs |
| `Semantics/` | Model/store meanings and predicate interpretations |
| `Checker/Runtime/`, `Checker/Proofs/` | Executable checking and correctness/equivalence proofs |
| `Compiler/`, `Compiler/Proofs/` | Normalization, constraint/domain/objective compilation and correspondence |
| `Solver/Core/`, `Solver/Propagation/` | Shared domains, assignments, constraint/literal semantics and proof foundations |
| `Engine/` | Production Core: arrays, compact domains, watches, propagators, trail, queue, analysis and search |
| `Integration/Optimization/{Basic,Partial}.lean` | Generic branch-and-bound and partial certified solver interface; no Legacy imports |
| `Integration/Public/` | Core-only source solving, linear/seeded optimization and CLI driver |
| `Integration/Config/`, `Integration/Emit/` | Shared options, source annotations and output rendering |
| `Legacy/` | Old list search, exclusive propagation machinery, old option drivers and fallback APIs |
| `Cli/` | Parser/checker I/O and the Core-only solve command |

Paths above are relative to `LeanFzn/`. The public `LeanFzn.lean` and
`Integration.lean` umbrellas expose Core APIs. Historical APIs require an
explicit `LeanFzn.Legacy...` import; their declaration namespaces and theorem
statements are preserved.

### Solver structure

```text
FlatZinc -> Parser -> Compiler -> Engine.Search / Engine.Incremental
                                      |
                       Integration.Public.Solve / Optimize / Seed
                                      |
                       Integration.Public.Driver -> Cli.Main

shared generic optimization ----^       no path to Legacy/
```

Read `Engine/Types` for `EClause` and engine state; `Dom`/`Proofs/Dom` for domain
operations and laws; `Clauses`, `Prop`, `Props/` and `Queue/Run` for propagation;
`Analyze`, `Reduce` and `Search` for learning, policies and search. Seeded
optimization carries the certified clause database across stronger bounds via
`Engine/Incremental` and `Integration/Public/Seed`.

Proofs are separated in Parser, Checker, Compiler and Engine's queue/domain
layers. Certified propagator constructors keep the entailment lemmas needed to
construct their outputs nearby. Other Engine and shared Semantics modules still
combine definitions and proofs. The legacy solver's proofs live with its
preserved implementation. [code-structure.md](code-structure.md) gives the DAG
and canonical reading paths.

## Building and running

Requires Lean 4.33.1; `elan` uses the version specified in `lean-toolchain`.

```sh
# Build the library and CLI.
lake build LeanFzn leanfzn

# Build individual components.
lake build LeanFzn.Parser LeanFzn.Checker
lake build LeanFzn.Engine
# Optional historical search and development comparisons.
lake build LeanFzn.Legacy

# Parse a model, printing its AST.
lake env leanfzn model.fzn
echo 'solve satisfy;' | lake env leanfzn -

# Check supplied solutions.
lake env leanfzn check model.fzn solution.txt

# Solve a supported satisfaction model.
lake env leanfzn solve model.fzn
lake env leanfzn solve --certified model.fzn
```

`--certified` is an alias for the same certified solve command. Solve input
can be a file, `-`, or stdin when the file argument is omitted.

#### Search options

The no-flag CLI path selects Core with `--var=act --val=min`. The record and
`default` preset retain `minc/act`; explicit variable/value policies and presets
suppress the CLI default override.

| Option | Public Core-only status |
| --- | --- |
| `--engine=core` | Accepted; Core is the sole public engine. `kernel` is rejected. |
| `--var=minc\|annot\|act\|domwdeg` | Implemented. `obj` is legacy-only and rejected. |
| `--val=act\|min\|max\|median\|annot\|incumbent` | Implemented; seeded optimization rejects `incumbent`. |
| `--opt=linear\|seeded` | Implemented; both preserve incumbents on give-up. `bisect` is rejected. |
| `--restart=none\|luby\|geom`, `--restart-base=N` | Native Core restart schedules; restarting requires a positive base. |
| `--strategy=default\|annot` | Accepted. Other presets must satisfy the Core compatibility checks. |
| `--stats` | Core counters and completion/give-up status on stderr. Unavailable counters are `-`. |
| `--time-limit`, `--portfolio`, `--primal`, legacy `--heur-*` toggles | Not implemented by Core; rejected rather than routed to Legacy. |
| `--prop`, `--presolve`, `--seed` | Only `prop=auto` and `presolve=none` are supported; randomized seeds are rejected. |

[Config/Parse.lean](LeanFzn/Integration/Config/Parse.lean) contains the public
`parseCoreSolveFlags`; a historical compatibility parser remains available to
explicit legacy APIs. [Public/Driver.lean](LeanFzn/Integration/Public/Driver.lean)
also validates programmatic calls. Unsupported or incompatible options fail
before loading the model. The public parser never selects the legacy engine.

| Command | Exit codes |
| --- | --- |
| Parse | 0: success; 1: parse error; 2: usage/IO error |
| Check | 0: all supplied solutions accepted; 1: unsatisfied condition; 2: malformed model or usage/IO error; 3: unsupported predicate; 4: malformed solution entries |
| Solve | 0: SAT or certified completed optimum; 1: certified UNSAT or infeasible completed optimization; 2: malformed model or usage/IO/parse error, including unsupported options; 3: unsupported compilation/domain gate; 4: Core unknown or incomplete optimization, with any streamed incumbents retained |

SAT output ends with `----------`; UNSAT is printed as
`=====UNSATISFIABLE=====`. Optimization prints improving solutions followed by
`==========` on proven completion. Each improving solution is printed and
flushed immediately; external timeouts can therefore retain partial progress.

## Tests and audits

For a focused parser/checker check:

```sh
lake build LeanFzn.Parser LeanFzn.Checker \
  tests_smoke tests_pretty tests_solution tests_check tests_fast
for t in tests_smoke tests_pretty tests_solution tests_check tests_fast; do
  ".lake/build/bin/$t" || exit 1
done
python3 audits/check_module_boundaries.py
```

For the full acceptance gate, use the maintained runner rather than a copied
list of test targets:

```sh
bash audits/run_gates.sh
```

The runner builds the libraries and registered executables, runs the applicable
tests, harness battery/crosscheck, axiom and boundary audits, fuzzing, a short
performance suite and Core differential checks. It writes logs under `tmp/`.
Some executables require arguments and have dedicated gate steps. The target
inventory is [lakefile.toml](lakefile.toml); audit usage and measurement
provenance are in [audits/README.md](audits/README.md).

The axiom audit rejects missing profiles, `sorryAx` and axioms outside the
standard allowlist (`propext`, `Classical.choice`, `Quot.sound`). The boundary
audit checks component dependencies and import cycles; it does not replace
Lean compilation or prove behavioral equivalence.

The 2026-11-03 full gate validated the earlier combined Core/kernel route.
Its 51 executables, 3,308 axiom profiles and 3,000 fuzz cases are historical
results, not a new Core-only performance baseline. The Core-only migration adds
`tests_core_only`, `audits/test_core_only_cli.py`, and architecture scanner
regressions under `Tests/Architecture/`. They cover explicit give-up, rejection
of legacy-only options, incumbent retention, min/max optimization, clause reuse,
checked witnesses and absence of Legacy imports from production.
The existing 200-case CLI optimization fuzz now verifies partial outcomes as
well as completed optima: the current fixed-seed run completes 186 cases and
reports 14 incomplete cases, with all 673 checks passing. Directed completion
cases still require completion, and a fixed-seed coverage floor prevents an
all-unknown regression from passing.
The quick suite likewise retains the known UNSAT `nonunit_jump` fixture while
reporting its current unknown outcome separately. Only that explicitly marked
migration case may remain incomplete; mathematical expectations are preserved,
and unexpected incomplete cases or invalid witnesses fail the gate.


The Core-only acceptance gate passed on 2026-11-04 (`tmp/gates/core-only-accept-20261104T081225Z/`):
52 runnable executables; a 52-instance battery and 45-instance cross-check;
all 3,331 theorem axiom profiles; Core/legacy differential checks; 453 modules
with no import cycles or production Legacy imports; 3,000 harness fuzz instances
with zero wrong/bound/witness failures; five CLI regression tests and ten import/
outcome regression tests. The quick suite reports 10 completed cases plus the
one explicitly allowed unknown, with all eight witness checks accepted.

For selective performance measurements, use
`python3 audits/benchmark_performance.py` (default: 2 seconds per case,
60 seconds total). Follow [PLAN.md](PLAN.md) for campaign budgets and
[audits/README.md](audits/README.md) for reproducibility requirements.
