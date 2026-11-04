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
conflict-driven activity and tries each selected variable's smallest remaining
allowed value first (`--var=act --val=min`). These options control search order;
minimization or maximization is specified by the model's `solve` item.

If Core gives up, satisfaction reports unknown and
optimization reports incomplete, both with exit code 4. Already streamed
incumbents remain valid; no UNSAT or optimality marker is emitted for an
incomplete run. Options Core does not implement are usage errors, with no
implicit engine switching.

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
Unsupported declaration or constraint forms are reported explicitly.
`solve minimize/maximize <int variable>` uses certified branch-and-bound;
the final `==========` marker is backed by UNSAT under the improving bound.

The accepted constraint families are `int_eq`, `int_ne`, `int_le`, `int_lt`,
`int_plus`, `int_times`, `int_min`, `int_max`, `array_int_minimum`, `array_int_maximum`
(including supported literal-operand shapes), `int_abs`, `int_div`, `int_mod`,
`int_lin_eq`, `int_lin_le`, `int_lin_ne`, `bool_not`, `bool_and`, `bool_or`,
`bool_eq`, `bool_xor`, `bool2int`, `bool_clause`, `array_bool_and`, `array_int_element`,
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
| General set constraints and other globals | Only implemented argument patterns and constraint translations have a certified solver route. Constant-set membership is supported; set-valued search slots are not. |
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
For example, `var {0,1000000}: x; solve satisfy;` currently passes compilation
but Core cannot convert that wide sparse domain. The public command returns
unknown (exit 4). Certification supplies correctness guarantees for
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

```

Proofs are separated in Parser, Checker, Compiler and Engine's queue/domain
layers. Certified propagator constructors keep the entailment lemmas needed to
construct their outputs nearby. Other Engine and shared Semantics modules still
combine definitions and proofs.

[code-structure.md](code-structure.md) gives the DAG
and canonical reading paths.

## Building and running

Requires Lean 4.35.0; `elan` uses the version specified in `lean-toolchain`.

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

With no search flags, the solver uses `--var=act --val=min`. The options below
control variable selection, value selection, optimization and restarts.

| Option | What it does |
| --- | --- |
| `--engine=core` | Use the array-based Core solver, which is already the default. |
| `--var=minc` | Choose an unfixed variable with the fewest remaining allowed values. |
| `--var=annot` | Prioritize variables using the model's search annotation groups; break equal priorities by smallest remaining domain. |
| `--var=act` | Prioritize variables involved in learned conflicts, using scores that decay over time. Break equal scores by smallest remaining domain. |
| `--var=domwdeg` | Use conflict activity with larger score increases for variables whose current domains are smaller. |
| `--val=min` | Try the selected variable's smallest remaining allowed value first. For Booleans, try `false` first. |
| `--val=max` | Try its largest remaining allowed value first. For Booleans, try `true` first. |
| `--val=median` | Try an allowed integer near the midpoint of the remaining lower and upper bounds; fall back to the minimum if none is found nearby. |
| `--val=act` | With `--var=act` or `domwdeg`, reuse the last saved value if it is still allowed; otherwise try the minimum. With other variable policies, try the minimum. |
| `--val=annot` | Follow supported integer-value ordering annotations in the model. Split annotations are approximated by choosing the minimum or maximum. |
| `--val=incumbent` | During linear optimization, try each variable's value from the previous solution first, falling back to the minimum when needed. Use with `--opt=linear`. |
| `--opt=linear` | Find a solution, require a strictly better objective, and repeat until the improving bound is proved infeasible or Core stops incomplete. This is the default optimization mode. |
| `--opt=seeded` | Perform the same improving-bound search while retaining certified learned clauses between optimization rounds. |
| `--restart=none` | Keep searching without scheduled restarts. This is the default. |
| `--restart=luby` | Restart at conflict thresholds determined by the Luby sequence, returning to root decisions while retaining learned clauses. |
| `--restart=geom` | Restart at geometrically increasing conflict thresholds, doubling the threshold after each restart while retaining learned clauses. |
| `--restart-base=N` | Set the base conflict threshold for `luby` or `geom` restarts. The default is `100`; `N` must be positive when restarts are enabled. |
| `--strategy=default` | Select a preset with `--var=minc --val=act`, linear optimization and no scheduled restarts. |
| `--strategy=annot` | Select both `--var=annot` and `--val=annot` to use the model's search annotations. |
| `--prop=auto` | Use Core's automatic event-driven propagation scheduling. This is the default. |
| `--presolve=none` | Skip a separate presolve phase. Normal Core propagation still runs during search. This is the default. |
| `--stats` | Print search counters and completion/give-up status to stderr. Counters that are unavailable are shown as `-`. |

Presets are applied first; explicit flags override their settings. Without a
preset, setting only `--var` leaves the value policy at `act`, while setting only
`--val` leaves the variable policy at `minc`. Set both flags to choose the pair
explicitly.

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

The ordered solver performance tasks and current status are in
[PLAN.md](PLAN.md). [Tests/README.md](Tests/README.md) maps test suites to the
source components. Current tests build with `lake build Tests`; historical
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
