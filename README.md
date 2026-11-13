# LeanFzn — verified FlatZinc tools in Lean 4

**This project is heavily LLM-generated.** Large language models (LLMs) have
been used extensively to develop the implementation, Lean proofs, and
documentation.

LeanFzn provides a parser, a solution checker and a certified finite-domain
solver for FlatZinc. Shared formal semantics connect parsed models, checked
solutions and solver results.

- **Parser:** soundness and completeness with respect to the project's
  declarative grammar.
- **Solution checker:** verified checking of integer, Boolean and set models
  using supported standard predicates and global constraints.
- **Core solver:** certified array-based finite-domain search with propagation,
  learned clauses, conflict analysis, backjumping and branch-and-bound.

By default, the public `solve` command prioritizes variables using
conflict-driven activity (`--var=act`). For optimization it tries each variable's
previous incumbent value first (`--val=incumbent`), falling back to the smallest
remaining value before the first incumbent, and enables Luby restarts after the
first incumbent; `--opt=seeded` defaults to the smallest value (`--val=min`)
instead. These options control search order; minimization or maximization is
specified by the model's `solve` item.

If Core gives up, satisfaction reports unknown with the recorded diagnostic
cause when available, and optimization reports incomplete; both use exit
code 4. Already streamed
incumbents remain valid; no UNSAT or optimality marker is emitted for an
incomplete run. Options Core does not implement are usage errors, with no
implicit engine switching.

The language reference is **MiniZinc 2.10.1**, pinned to commit
`c3448c48e7f05f13805616cfd1b9e94972eef58c`. See the
[vendor reference](specification/minizinc-2.10.1/README.md) and
[formalization assumptions](specification/flatzinc_specification_assumptions.md).
Float syntax and semantics are outside the supported fragment; strings are
supported in annotations.

## Implementation status

The public solver uses the Core engine; historical implementations are isolated
under `LeanFzn/Legacy/` for proofs and development comparisons. The compiler
includes literal folding, checked integer bounds and finite-set expansion.
The engine supports certified propagation, learned clauses, optimization,
LNS and parallel portfolios. Unsupported inputs and incomplete searches are
reported explicitly; see the scope and exit-code tables below.

Use [Tests/README.md](Tests/README.md) and [audits/README.md](audits/README.md)
for validation commands. Benchmark reports depend on their source snapshot and
run budget; generated logs under `tmp/` are local artifacts.

## Using LeanFzn from MiniZinc

[minizinc-wrapper/](minizinc-wrapper/README.md) registers LeanFzn as a MiniZinc
solver. The primary route is the Docker image (MiniZinc 2.10.1 with LeanFzn as
the default solver):

```bash
docker build -f minizinc-wrapper/Dockerfile -t leanfzn-minizinc .
docker run --rm -v "$PWD:/work" leanfzn-minizinc model.mzn data.dzn
```

To add it to an existing MiniZinc instead, run `minizinc-wrapper/install.sh`
(it also installs the pinned MiniZinc 2.10.1 if needed) or follow the manual
steps in that README, then `minizinc --solver leanfzn model.mzn`. The
wrapper is not part of the certified code: it translates flags and output and
passes on only the verdicts `leanfzn solve` prints.

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

The checker covers standard arithmetic, Boolean and set
predicates and supported global constraints. Unknown or unsupported predicates
produce an explicit unsupported outcome. The predicate definitions and coverage
lists live in `LeanFzn.Semantics` and `LeanFzn.Checker.Globals`.

The checker accepts solver output containing several solutions separated by
`----------` and checks each solution. It reports the first failure.

### Certified solver

`leanfzn solve` compiles supported, statically well-formed satisfaction models
with finite nonempty integer/Boolean domains. It propagates constraints and
learns entailed clauses using an array-based trail and clause database.
Conflict analysis tracks root entailment, so literals already false at the root
are discharged from the learned clause instead of being stored again. Learned
clauses carry packed-literal intern hints through that path; every hint is
revalidated against the live literal table before reuse, and a stale index
falls back to ordinary interning.
Unsupported declaration or constraint forms are reported explicitly.
`solve minimize/maximize <int variable>` uses certified branch-and-bound;
the final `==========` marker is backed by UNSAT under the improving bound.
A verified rank-decomposition checker replays Gecode's `circuit` flattening
for the `tsptw` family; its 2-cycle seed clauses are not registered by the
default engine. See
[RankCircuit.lean](LeanFzn/Compiler/RankCircuit.lean) and
[Proofs/RankCircuit.lean](LeanFzn/Engine/Proofs/RankCircuit.lean).

The accepted constraint families are `int_eq`, `int_ne`, `int_le`, `int_lt`,
`int_plus`, `int_times`, `int_min`, `int_max`, `array_int_minimum`, `array_int_maximum`
(including supported literal-operand shapes), `int_abs`, `int_div`, `int_mod`,
`int_lin_eq`, `int_lin_le`, `int_lin_ne`, `bool_not`, `bool_and`, `bool_or`,
`bool_eq`, `bool_xor`, `bool2int`, `bool_clause`, `array_bool_and`, `array_int_element`,
`array_var_int_element`, `array_var_bool_element`, the reified forms
`int_eq_reif`, `int_le_reif`, `int_ne_reif`, `int_lin_eq_reif`,
`int_lin_le_reif`, `int_lin_ne_reif`, and `all_different`. Constant-set `set_in` and supported `set_in_reif`
forms are also compiled; the front end can fold membership restrictions into
finite integer domains. Bounded scalar set variables (`var set of lo..hi` or
`var set of {...}`) used by `set_in(k,S)` or `set_in_reif(k,S,b)` with an
integer-literal `k` are expanded into one Boolean per universe value by a
certified pass; an out-of-universe member is false, so an unreified
out-of-universe membership compiles to certified UNSAT. A certified shape
pass first rewrites the finite set shapes `set_in_reif(x,S,b)` with a
variable integer `x`, unreified `set_in(x,S)`, `set_card(S,k)` for a declared
set `S` (variable or literal result), `set_union` over declared or literal
finite sets, `set_intersect` over declared or literal finite sets, and
`array_var_set_element(i,[S…],T)` over an explicit set array
and a declared finite target into scalar membership/equality bits, Boolean
conjunctions, `bool2int` aliases, clause rows, one `bool_and` row per value
for intersection, and one
`array_var_bool_element` row per value of the element/target universe;
unhandled set shapes are never dropped. See
[SetIn.lean](LeanFzn/Compiler/SetIn.lean),
[SetShape.lean](LeanFzn/Compiler/SetShape.lean) and
[SetExpand.lean](LeanFzn/Compiler/SetExpand.lean).

Ground constraints whose arguments are all literals are decided during
normalization by the executable semantics: a true constraint is removed and a
false one becomes an accepted always-false row, so it compiles to certified
UNSAT instead of being dropped. Reified integer predicates with a literal
Boolean result are rewritten to the plain predicate (`true`) or its checked
negation (`false`); this includes `int_lt_reif`, `int_ge_reif` and
`int_gt_reif`, whose variable-result forms remain unsupported. Linear
literal-`false` results stay unsupported because their length-mismatch
semantics does not match a naive `int_lin_ne` rewrite. `set_card(R,x)` with a
literal or range set `R` is rewritten to `int_eq(x, |R|)` using the distinct
cardinality of `R` (duplicates counted once, reversed ranges empty); parameter
sets and set variables are handled only by the separate supported set passes. See
[LiteralFold.lean](LeanFzn/Compiler/LiteralFold.lean).

`int_gt` and `int_ge` are also accepted for variable–constant comparisons.
Variables must be scalar Booleans or integers with an explicit finite range or
enumerated domain, except that a bare `var int` is accepted when the
constraints force a finite interval. An untrusted recognizer proposes a bound
certificate and a verified checker replays it from the declared bounds:
reified equalities under a two-sided clause split, a forced Boolean branch, or
a linear equality row whose other terms are bounded. The checked interval
replaces the declaration before compilation; every unbounded integer variable
must have one, so a bare `var int` with no derivation stays unsupported and no
default or invented range is ever used. Coefficients other than ±1 are handled
with exact integer inequalities (the recognizer's floor/ceiling division is
never trusted), and a zero coefficient is rejected. See
[Bounds.lean](LeanFzn/Compiler/Bounds.lean).

A scalar variable may carry a literal initializer, or an
initializer naming a scalar parameter; the front end turns it into an
equivalent fixed-value constraint (`int_eq` for integers, `bool_not` for
Booleans) before compilation. Identifier and set initializers remain
unsupported. Literal scalar and array parameters and the supported
variable-array aliases are normalized before scalar compilation; scalar
`int`/`bool` parameters are substituted by their declared values in constraint
arguments and initializers. Literal integer/Boolean parameter arrays are still
inlined as before, and set parameters remain limited to the supported
constant-set membership forms. Objectives must name an integer slot.

Support also depends on the argument form. Linear constraints require inline
arrays of literal integer coefficients and scalar variable names, matching array
lengths, and a literal integer right-hand side. `all_different` requires an
inline array of scalar variable names. Supported parameter arrays and variable-array aliases may also supply these
arguments after normalization. Other predicates accept the variable/literal
forms implemented by the [constraint extractor](LeanFzn/Compiler/Extract.lean)
and [compiler](LeanFzn/Compiler/Compile.lean). Scalar `int`/`bool` parameters
are substituted by their declared literal values before the literal folds and
compilation, so every constraint shape that accepts the corresponding literal
is reachable through a scalar parameter. Arbitrary parameter expressions and
array parameters in scalar positions remain outside the fragment; literal
parameter arrays are inlined as described above. See
[Fragment.lean](LeanFzn/Compiler/Fragment.lean).

| Unsupported feature | Why it is outside the current solver fragment |
| --- | --- |
| General objective expressions | Certified optimization currently requires a plain integer variable objective. |
| Unbounded `var int` without a proved bound derivation | Search enumerates finite domains. A bare `var int` is accepted only when a checked certificate (case split, forced branch, or linear row) bounds it; otherwise compilation reports unsupported. |
| Set variables outside the supported finite shapes | Bounded scalar set variables are supported through literal membership, variable-element `set_in(x,S)` and `set_in_reif(x,S,b)`, `set_card(S,k)` for a declared set `S`, `set_union` and `set_intersect` over declared or literal finite sets, and `array_var_set_element(i,[S…],T)` over an explicit array of declared finite sets or set literals with a declared finite target and a variable index. An in-range literal index of `array_var_set_element` stays unsupported (exit 3) because the downstream Boolean-element route requires an identifier index; it is never dropped. Difference/subset/superset/symmetric difference, the lexicographic `set_le`/`set_lt`, their reified forms, other element/array set constraints, general set-array uses and unbounded `var set of int` are not compiled. |
| General array variable declarations/indexing | The front end supports aliases of scalar integer/Boolean slots and the compiled element/array families; arbitrary array storage and general index expressions remain unsupported. |
| Variable initializers | Only literal scalar initializers and initializers naming a scalar parameter are expanded into fixed-value constraints. Identifier initializers and set initializers are not expanded; array initializers are handled only by the supported variable-array alias inlining above. Express other relationships as constraints. |
| General parameter expressions | Scalar `int`/`bool` parameters are substituted by their declared values. Literal integer/Boolean parameter arrays are inlined and supported constant-set membership remains available; arbitrary parameter expressions and array parameters in scalar positions remain outside compilation. |
| Predicate declaration items | The compiler rejects predicate items and translates only its built-in constraint families. |
| Empty variable domains | The MiniZinc 2.10 flattener does not emit an empty scalar domain (its Boolean contradictions are constraints, which the literal fold already decides), so this is not a produced shape. A raw FlatZinc empty range (`var 1..0: x`) is still rejected honestly with exit 3; the solver gate does not invent a certified UNSAT for it. |
| General set constraints and other globals | Only implemented argument patterns and constraint translations have a certified solver route. Constant-set membership, constant-set `set_card`, bounded-set literal membership, variable-element membership and reified membership, declared-set `set_card`, finite `set_union`, finite `set_intersect`, and `array_var_set_element` over explicit set arrays are supported; difference/subset/superset/symmetric difference, the lexicographic comparisons and other set-array uses are not. |
| Propagation strength | Core registers dedicated propagators for selected arithmetic, linear, order, Boolean and element shapes, with a generic checking propagator for remaining shapes. A compiled constraint may therefore be checked without strong domain pruning. |
| Other argument forms of the listed predicates | Compilation only covers specific argument patterns; the predicate name alone does not guarantee acceptance. |

For parsed, well-formed models outside this fragment, `solve` reports an
unsupported reason and exits with code 3. Syntax outside the parser's language,
such as floating-point declarations, instead produces a parse error (exit 2).

`LeanFzn.Core.solveModel_sat_correct` and `solveModel_unsat_correct` connect
Core results to source-model semantics. Core stores entailed clauses with
erased proofs, checks SAT assignments with `fitsB && accepts`, and derives
UNSAT from an entailed empty clause. A failed domain conversion, exhausted
search fuel or internal analysis give-up returns unknown; it never invokes
the old solver.

New optimization solutions are always valid and strictly improving. A completed run additionally proves that its final solution is optimal, or that the model is unsatisfiable if no solution was found. Core may stop incomplete, leaving the best solution found without an optimality guarantee.
Wide enumerated domains are represented directly as sparse domains. For
example, `var {0,1000000}: x; solve satisfy;` is solved by Core (and
`minimize x` completes at 0) without falling back to the old solver. A
conversion failure or an internal give-up still returns unknown (exit 4).
Certification supplies correctness guarantees for returned claims, not
practical running-time or decision-coverage guarantees.

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

```

Proofs are separated in Parser, Checker, Compiler and Engine's queue/domain
layers. Certified propagator constructors keep the entailment lemmas needed to
construct their outputs nearby. Other Engine and shared Semantics modules still
combine definitions and proofs.

[code-structure.md](code-structure.md) gives the DAG
and canonical reading paths.

## Building and running

Requires Lean 4.35.0; `elan` uses the version specified in `lean-toolchain`.
The package build applies the committed LLVM PGO profile in `pgo/`
(see `pgo/README.md` for provenance and regeneration).

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
```

Solve input can be a file, `-`, or stdin when the file argument is omitted.

#### Search options

With no search flags, a Core run uses `--var=act`. `--val` defaults to
`incumbent` for `--opt=linear` and to `min` for `--opt=seeded`; an explicit `incumbent` is also supported. The options below control variable selection, value selection,
optimization and restarts.

| Option | What it does |
| --- | --- |
| `--engine=core` | Use the array-based Core solver, which is already the default. |
| `--var=minc` | Choose an unfixed variable with the fewest remaining allowed values. |
| `--var=annot` | Prioritize variables using the model's search annotation groups; break equal priorities by smallest remaining domain. |
| `--var=act` | Prioritize variables involved in learned conflicts, using scores that decay over time. Break equal scores by smallest remaining domain. |
| `--var=domwdeg` | Use conflict activity with larger score increases for variables whose current domains are smaller. |
| `--var=wdeg` | Choose the variable with the smallest current domain divided by one plus the number of conflict explanations that mentioned it. Break ties by smallest domain, then lowest index. |
| `--val=min` | Try the selected variable's smallest remaining allowed value first. For Booleans, try `false` first. |
| `--val=max` | Try its largest remaining allowed value first. For Booleans, try `true` first. |
| `--val=median` | Try an allowed integer near the midpoint of the remaining lower and upper bounds; fall back to the minimum if none is found nearby. |
| `--val=act` | With `--var=act`, `domwdeg` or `wdeg`, reuse the last saved value if it is still allowed; otherwise try the minimum. With other variable policies, try the minimum. |
| `--val=annot` | Follow supported integer-value ordering annotations in the model. Split annotations are approximated by choosing the minimum or maximum. |
| `--val=incumbent` | During optimization, try each variable's value from the previous solution first, falling back to the minimum when needed. This is the default for `--opt=linear` and is also available with `--opt=seeded`; the seeded driver seeds each round's phases from the previous incumbent. |
| `--opt=linear` | Find a solution, require a strictly better objective, and repeat until the improving bound is proved infeasible or Core stops incomplete. This is the default optimization mode. |
| `--opt=seeded` | Perform the same improving-bound search while retaining certified learned clauses between optimization rounds. |
| `--primal=lns` | Run a bounded large-neighborhood search around each incumbent before the complete linear loop. The pre-phase only proposes checked incumbents; only the ordinary loop can prove optimality or UNSAT. Off by default. |
| `--primal-time=N` | Set the per-neighborhood step budget for `--primal=lns` (default `1000`). |
| `--restart=none` | Keep searching without scheduled restarts. This is the default for the first optimization round; the linear driver enables Luby restarts after the first incumbent. Pass `--restart=none` explicitly to disable restarts for the whole run. |
| `--restart=luby` | Restart at conflict thresholds determined by the Luby sequence from the first round, returning to root decisions while retaining learned clauses. |
| `--restart=geom` | Restart at geometrically increasing conflict thresholds from the first round, doubling the threshold after each restart while retaining learned clauses. |
| `--restart-base=N` | Set the base conflict threshold for `luby` or `geom` restarts, including the linear driver's automatic after-incumbent Luby schedule. The default is `100`; `N` must be positive. An explicit `--restart=none` rejects a non-default base. |
| `--conflict-limit=N` | Stop the Core search of each optimization round after `N` conflicts, then exit 4 with the counters and cause `conflict limit reached`. This is a diagnostic measurement cap, not a wall-clock limit; it never changes a completed verdict, and `N` must be positive. |
| `--threads=N` | Run an opt-in portfolio of `N` independent certified workers (`1..8`). For linear optimization each worker compiles its own problem and runs one of `act/incumbent`, `minc/incumbent`, `wdeg/incumbent` or `annot/annot`; workers 5–8 repeat those strategies with after-incumbent Luby base 50 instead of 100. Only strictly improving checker-accepted incumbents are printed, and the first completed proof is reported only when its optimum matches the best printed incumbent. For satisfaction models the strategies use `value=act` or `value=annot`, and the first completed SAT or UNSAT verdict wins; a SAT witness is printed only after the checker accepts it. `--threads=1` is the ordinary single-threaded driver. The option is rejected with a preset, `--var`/`--val`, `--opt=seeded` or `--primal`. |
| `--strategy=default` | Select a preset with `--var=minc --val=act`, linear optimization and no scheduled restarts. |
| `--strategy=annot` | Select both `--var=annot` and `--val=annot` to use the model's search annotations. |
| `--strategy=lns` | Select `--var=annot --val=incumbent --opt=linear --primal=lns`. |
| `--prop=auto` | Use Core's automatic event-driven propagation scheduling. This is the default. |
| `--presolve=none` | Skip a separate presolve phase. Normal Core propagation still runs during search. This is the default. |
| `--presolve=dedup` | Remove syntactically duplicate compiled constraints while preserving the search box, objective slot and source reconstruction. Rejected with `--opt=seeded`. |
| `--stats` | Print search counters (including the deepest decision level reached), linear-optimization compile/search timing, and completion/give-up status to stderr. Counters that are unavailable are shown as `-`. |
| `--phase-stats` | Dev diagnostic: print one stderr line per compiler/search phase with this phase's wall time, cumulative wall time, current `VmRSS` and peak `VmHWM`. It never changes stdout, exit codes or counters; specialized seeded/LNS/portfolio paths print a note and run the ordinary driver. |

Presets are applied first; explicit flags override their settings. Without a
preset or portfolio, a Core run fills `--var` and `--val` independently:
`--var` defaults to `act`, and `--val` defaults to `incumbent` for
`--opt=linear` or `min` otherwise. Setting only one flag leaves the other at
its default; set both flags to choose the pair explicitly.

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

[Tests/README.md](Tests/README.md) maps test suites to the source components. Current tests build with `lake build Tests`; historical
solver tests are isolated under `Tests/Legacy` and build with
`lake build Tests.Legacy`.

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
