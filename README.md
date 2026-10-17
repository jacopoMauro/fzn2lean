# LeanFzn — verified FlatZinc tools in Lean 4

LeanFzn provides a parser, a solution checker and a certified finite-domain
solver for FlatZinc. Shared formal semantics connect parsed models, checked
solutions and solver results.

- **Parser:** soundness and completeness with respect to the project's
  declarative grammar.
- **Solution checker:** verified checking of integer, Boolean and set models
  using supported standard predicates and global constraints.
- **Chronological solver:** certified propagation, learned-clause pruning,
  search and chronological backtracking for the supported finite integer/Boolean
  satisfaction fragment.
- **First-UIP solver:** fuel-free certified conflict analysis, backjumping and
  non-unit learning for the checked finite integer/Boolean LCG fragment (mixed
  shape-typed domains), with chronological fallback.

The public `solve` command uses certified first-UIP search when its family,
shape, domain and slot gates pass (integer or Boolean-uniform domains); it uses
certified chronological search otherwise. Optimization uses the same certified
routing and streams and flushes improving solutions as they are found. The CLI
currently uses the unseeded optimization driver; a separate certified seeded
driver supports clause reuse across tighter bounds. Remaining implementation
work is tracked in [PLAN.md](PLAN.md), with optional performance tasks and agent
coordination in [PLAN_PERFORMANCE.md](PLAN_PERFORMANCE.md).

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
with finite nonempty integer/Boolean domains. It propagates constraints, shares
entailed learned clauses between branches and searches an explicit frontier.
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
`int_lin_le_reif`, `int_lin_ne_reif`, and `all_different`.
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
| Set parameters and general parameter expressions | Literal integer/Boolean arrays are supported; arbitrary expression evaluation remains outside compilation. |
| Predicate declaration items | The compiler rejects predicate items and translates only its built-in constraint families. |
| Empty variable domains | The public solver gate requires every domain to be nonempty. It does not currently turn an empty domain into a certified UNSAT result. |
| `bool_xor`, set constraints and globals other than the supported `all_different`/element/array forms | These lack an accepted translation and the corresponding compiler/solver correctness route. Checker support alone does not supply that route. |
| Propagation strength | All constraint constructors pass the LCG family gate, but the other route gates still apply. Arithmetic and reified families have dedicated explained propagators, with strength depending on the family and reification direction. `bool_clause` seeds the clause database. `array_bool_and`, `bool2int`, `bool_eq`, and the three element families have no dedicated registered propagator and retain leaf checking. Residual literal-pair `minPair`/`maxPair` shapes use checking-only `propCheck`. |
| Other argument forms of the listed predicates | Compilation only covers specific argument patterns; the predicate name alone does not guarantee acceptance. |

These are limits of the current certified implementation, rather than inherent
limits of chronological search; adding UIP does not by itself remove them.
For parsed, well-formed models outside this fragment, `solve` reports an
unsupported reason and exits with code 3. Syntax outside the parser's language,
such as floating-point declarations, instead produces a parse error (exit 2).

The source-level theorems establish:

- A returned store satisfies the model:
  `LeanFzn.Integration.solveCertified_sat_correct`.
- An UNSAT verdict excludes every parameter-honest satisfying store:
  `LeanFzn.Integration.solveCertified_unsat_correct`.
- Accepted finite inputs terminate without a budget-exhaustion `unknown` verdict:
  `LeanFzn.Integration.solveCertified_total`.

Propagation preserves solutions and learned clauses are globally entailed.
LCG search termination follows a checked sorted phase rank; chronological
fallback uses a finite-frontier measure. Domains are materialized
eagerly, and search can take exponential time; certification establishes
correctness and termination rather than a performance bound. The scheduled
propagator dispatch is proved equivalent to the plain per-step rescan. The
public route also uses a proved-equivalent indexed database scan and fast route
gate. Static activity-based value ordering is certified by domain permutations;
variable ordering remains positional, and dynamic activity and restarts remain
future work. Huge domains remain impractical with eager lists; compact domains
are the owner-gated D1 task.

## Repository structure

| Component | Responsibility |
| --- | --- |
| `LeanFzn.Syntax`, `LeanFzn.Parser` | AST, lexer, grammar, parsing, printing and parser proofs |
| `LeanFzn.Semantics` | Stores, model meanings and predicate interpretations |
| `LeanFzn.Checker` | Solution parsing, completion and certified checking |
| `LeanFzn.Compiler` | Domain/constraint compilation and correspondence proofs |
| `LeanFzn.Solver.Core`, `LeanFzn.Solver.Propagation` | Shared problems, domains, clauses, propagation and explanation contracts |
| `LeanFzn.Solver.Chronological` | Certified frontier search and learned-clause pruning |
| `LeanFzn.Solver.UIP` | First-UIP scheduler, backjumping, learning and certification |
| `LeanFzn.Solver.Reference` | Exhaustive and diagnostic search |
| `LeanFzn.Integration`, `LeanFzn.Cli` | Source-level certification, fallback policy and commands |

Each component has a Lake library target and a root import module. Parser and
checker build independently of solving. The chronological and UIP components
share foundations and do not import each other. `Main.lean` delegates to the
CLI component; `LeanFzn.lean` is an optional full-stack library import.

Tests are grouped by component, including compiler and source-level integration
checks. [audits/README.md](audits/README.md) describes proof checks, benchmark
tools, and retained measurement provenance. The lowercase `solver/` tree is a
legacy implementation outside the current Lake library targets; active
`LeanFzn` modules must not import it.
See [code-structure.md](code-structure.md) for dependency details.

## Building and running

Requires Lean 4.33.1; `elan` uses the version specified in `lean-toolchain`.

```sh
# Build the library and CLI.
lake build LeanFzn leanfzn

# Build individual components.
lake build LeanFzn.Parser LeanFzn.Checker
lake build LeanFzn.Solver.Chronological LeanFzn.Solver.UIP

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

| Command | Exit codes |
| --- | --- |
| Parse | 0: success; 1: parse error; 2: usage/IO error |
| Check | 0: all supplied solutions accepted; 1: unsatisfied condition; 2: malformed model or usage/IO error; 3: unsupported predicate; 4: malformed solution entries |
| Solve | 0: solution found; 1: UNSAT; 2: malformed model or usage/IO/parse error; 3: unsupported model |

SAT output ends with `----------`; UNSAT is printed as
`=====UNSATISFIABLE=====`. Optimization prints improving solutions followed by
`==========` on proven completion. Each improving solution is printed and
flushed immediately; external timeouts can therefore retain partial progress.

## Tests and audits

Build and run every registered test executable:

```sh
lake build LeanFzn Tests leanfzn \
  tests_smoke tests_stdlib tests_solution tests_gecode tests_globals \
  tests_bench tests_coverage tests_wellformed tests_pretty tests_prof tests_check \
  tests_solver tests_prop tests_fast tests_lcg tests_lcg_analysis tests_oracle \
  tests_lcg_scheduler_fixtures tests_lcg_scheduler_activation \
  tests_scheduler_computability tests_lcg_public_fixtures \
  tests_lcg_harness tests_lcg_proto tests_array_params tests_optimize \
  tests_optimize_bnb tests_lcg_kernel tests_lcg_optimize tests_public_lcg \
  tests_dbscan tests_p3b_gate tests_lcg_heur

for t in tests_smoke tests_stdlib tests_solution tests_gecode tests_globals \
         tests_bench tests_coverage tests_wellformed tests_pretty tests_prof \
         tests_check tests_solver tests_prop tests_fast tests_lcg \
         tests_lcg_analysis tests_oracle tests_lcg_scheduler_fixtures \
         tests_lcg_scheduler_activation tests_scheduler_computability \
         tests_lcg_public_fixtures tests_lcg_harness tests_lcg_proto \
         tests_array_params tests_optimize tests_optimize_bnb tests_lcg_kernel \
         tests_lcg_optimize tests_public_lcg tests_dbscan tests_p3b_gate \
         tests_lcg_heur; do
  lake env "$t" || exit 1
done

lake env tests_p3b_gate --battery-crosscheck
lake env tests_lcg_harness --fuzz 3000 100000 --bound 50000 --no-chrono
bash audits/run_axiom_audit.sh
python3 audits/check_module_boundaries.py
```

The axiom audit requires the queried proofs to depend only on Lean's standard
allowlist (`propext`, `Classical.choice`, `Quot.sound`), rejecting missing
profiles and `sorryAx`. The boundary check rejects import cycles and forbidden
component dependencies.

Tests exercise parsing, checking, compilation, propagation, solver verdicts and
witnesses. `tests_public_lcg` exercises parsed-source routing; `tests_lcg_heur`
checks the activity-ordered entry. `tests_dbscan` and `tests_p3b_gate` cover the
scan and gate optimizations. `challenge_scan` is a separate file-driven tool,
not a no-argument test executable.

The last recorded full validation on 2026-10-17 reports 458 solver tests,
1040 allowlisted axiom profiles, 307 modules with no import cycles, all runnable
executables passing, a 50-case harness battery, and 3,000 fuzz instances without
wrong answers, bound failures, or rejected witnesses. These are saved results,
not a guarantee that a later checkout has been revalidated. The harness also
records 31 `c-sem` observations attributed to its trail-only tracker; resolving
that instrumentation limitation is tracked in the performance plan.

The latest retained challenge run completes 2/21 cases within 60 seconds.
There is no current full 300-second result or controlled comparison establishing
competitiveness with other solvers. Historical profiles and comparisons in the
benchmark JSON describe different implementation snapshots. See the audit README
for rerunning measurements; the fixed benchmark cohort is not a fresh compiler
coverage scan.
