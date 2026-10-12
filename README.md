# LeanFzn — FlatZinc, formalized in Lean 4

LeanFzn is a verified FlatZinc toolchain in Lean 4 for the
**integer/Boolean/set fragment** of the MiniZinc solver language. Its checker
covers that fragment. Its finite-domain solver is being rebuilt around a
direct correctness theorem rather than checker acceptance. Its main results
and active development target are:

- reusable finite-domain search, propagation, and refinement components, now
  being assembled into a directly verified solver;
- a solution checker covering 218 standard and global predicate names; and
- a parser proved to recognize exactly the declarative FlatZinc grammar.

The parser and declarative semantics remain the common foundation. The
solution checker is for external solutions and independent testing. The new
solver correctness argument will instead connect compiled constraints, solver
states, propagation, branching, and terminal results directly to
`Satisfies fullSig fullInterp`; output rendering happens only afterward.

**Status (2026-10-08):** the public finite-domain solver propagates before
branching and lazily generates globally entailed explanation and conflict
clauses. Learned clauses are shared with later branches and used for domain
unit propagation. Explicit pending siblings remember exhausted alternatives.
The solver is fuel-free, with kernel-checked coverage, completeness and
termination; the compiler has no arbitrary domain or product size caps.

The 4-variable/3-value pairwise-disequality pigeonhole regression now returns
UNSAT with 5 branching decisions, 24 propagations, 15 learned clauses and no
complete-assignment checks; 9 deductions reuse learned clauses. Search can
still take exponential time, and domains are materialized eagerly. The active
driver backtracks chronologically; first-UIP resolution and nonchronological
backjumping remain future refinements. See [PLAN.md](PLAN.md).

The normative reference is **MiniZinc 2.10.0**, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`). Float syntax and semantics are
deliberately excluded; strings remain supported in annotations.

## Repository components

The implementation uses one `LeanFzn` module hierarchy:

| Component | Responsibility |
| --- | --- |
| `Syntax`, `Parser` | FlatZinc AST, parsing/printing and parser proofs |
| `Semantics` | Stores, predicate interpretations and model meanings |
| `Checker` | External solution parsing, completion and certified checking |
| `Compiler` | FlatZinc-to-domain compilation and correspondence proofs |
| `Solver.Core`, `Solver.Propagation` | Shared problems, domains, clauses, propagation and explanation contracts |
| `Solver.Chronological` | Current certified frontier traversal and learned-clause pruning |
| `Solver.UIP` | First-UIP scheduler, backjumping and its developing certification |
| `Solver.Reference` | Exhaustive and historical diagnostic search |
| `Integration`, `Cli` | Source-level theorem composition, fallback and commands |

Each component has a Lake library target and root import. Parser and checker
build independently of solving; chronological and UIP strategies do not import
each other. Shared propagation includes explanation/analysis primitives used by
both diagnostics and scheduler proofs. The public command still uses the
chronological route; this reorganization does not activate unfinished UIP proofs.
`Main.lean` delegates to `LeanFzn.Cli.Main`. Executable names and CLI arguments
are unchanged. The old `solver.*` module names and LCG/Direct namespaces were
removed; downstream Lean imports must use the component names.

Run `python3 audits/check_module_boundaries.py` to verify component boundaries.
See `code-structure.md` for dependencies and `PLAN.md` for remaining proof work.

## Main results

### Directly verified finite-domain solver

`leanfzn solve MODEL.fzn` (also accepting the `--certified` alias) runs the
well-formedness check, the fragment compiler, the nonempty finite int/bool gate,
and the explicit frontier driver. It reports `sat`, `unsat` or
`unsupported` with exit codes 0/1/3 (a statically malformed model is a
usage-class exit 2).

- A `sat store` satisfies the source model (`LeanFzn.Integration.solveCertified_sat_correct`,
  composed with compiler exactness).
- `unsat` excludes every parameter-honest satisfying source store
  (`LeanFzn.Integration.solveCertified_unsat_correct`, composed with compiler coverage).
- The traversal is FUEL-FREE: termination is kernel-checked by the
  frontier-cost measure, so an accepted finite model always receives a
  verdict (`solveCertified_total`); there is no budget-exhaustion
  `unknown` outcome.

`LeanFzn/Solver/Chronological/Pruned.lean` implements the active frontier; `Pruning.lean`
implements finite-domain propagation closure and clause generation. Closure
terminates by strict domain-size reduction, and search terminates by the
proof-only pending-work measure. A repeated deduction that removes no value
does not trigger another round. `Proofs/Pruned.lean` proves coverage-based
verdict correctness and completeness; `Proofs/Pruning.lean` proves preservation
and global entailment. `DomPruning.lean` connects the existing per-family
propagator proofs to the public driver. Compiled gate-passing models enable
that kit (`compiled_domPruningOk`).

The public CLI and `solveDom` use the concrete proved kit. Generic `solve`
accepts a proof-carrying kit; its identity default and `frontierSolve` remain
reference traversals. Arbitrary callbacks do not acquire pruning authority
merely by being supplied as the legacy propagator argument. The historical
analysis/flip loop (`lcgSearch.go`) remains diagnostic and is not executed.

Current solver regressions exercise the public certified path on large finite
ranges, enumerated domains and products, emitted-solution checker round trips,
all 64 graph edge subsets, conflicts, stale deductions and learned-clause reuse.
Builds, tests and axiom audits are run locally; CI is out of scope.

### Exact parser recognition

The recognition theorem is proven with no `sorry` or user-declared `axiom`.

```lean
theorem parseModel_ok_iff_valid (s : String) :
    (∃ m, Parser.parseModel s = .ok m) ↔ ValidFlatZinc s
```

That is: the parser succeeds on a string if and only if that string is a valid
FlatZinc program (and by case analysis on the `Except` result, it fails
exactly on the invalid ones). This is the
combination of two directions, each proven independently:

- **Soundness** (`FznCorrectness.lean`): every successful parse yields a model
  that the declarative grammar derives — the parser never accepts garbage.
- **Completeness** (`FznCompleteness.lean`, `FznAssembled.lean`): every grammar
  derivation is accepted by the parser, producing exactly the derived AST —
  the parser never rejects, or mangles, a valid program.

The parser is a fuelled recursive-descent implementation; completeness
includes a proof that the fuel budget `8 * (tokens + 1)` always suffices.

`ValidFlatZinc` is defined over the tokens produced by the project's own
lexer (`FznLexer.lean`), so the theorem is a statement about the grammar
over tokens: lexical validity (comments, integer literals, keywords, string
escapes per assumption R11) is defined by the lexer, which is trusted. Where
the project's grammar knowingly departs from the vendored BNF (scalar
parameter declarations, nested annotation arrays, the spelling of the
index-set bound), the choice is recorded as R27–R29 in
`specification/flatzinc_specification_assumptions.md`.

### Verified solution checker

The store a solution describes (`completedStore`: the model's parameters,
overridden by the solution's entries, closed under variable initializers) is
an ordinary definition, so the theorems below speak about the actual store.
Its compiled code goes through `@[implemented_by]` twins with the same body
(a compilation safeguard against an O(n²) blow-up, see `FznSolution.lean`).

`checkSolutionFull` has a machine-checked correctness theorem for the
predicates in `fullCheckableNames`. That closed list currently contains
**218 names**:

- 61 non-extensional standard FlatZinc predicates;
- 19 extensional set predicates; and
- 138 supported `fzn_*` global constraints.

For each of those names, the executable Boolean interpretation is proved
equivalent to the corresponding declarative `Prop` interpretation. Subject
to the theorem's explicit predicate-name hypothesis,
`checkSolutionFull_correct` states that the checker accepts exactly when the
solution parses and its completed store satisfies all variable domains,
initializers, and constraints according to `fullInterp`.

This guarantee is relative to the semantics formalized in this repository.
MiniZinc leaves parts of the `fzn_*` predicate semantics to solver libraries,
so choices and corner cases that are not fixed literally by the reference
material are recorded in
`specification/flatzinc_specification_assumptions.md`. Tests against Gecode
provide useful cross-validation but are not part of the proof.

The checker does **not** support every predicate shipped with MiniZinc 2.10.0.
`Globals.globalsUnsupported` lists the intentionally unsupported globals —
currently the optional-variable pair `fzn_alternative`/`fzn_span` and the
float-dependent `fzn_neural_net`/`fzn_piecewise_linear*` (the `_reif`,
float, and opt variants of other names are outside the fragment too).
Unknown or unsupported constraints evaluate to `false`, so they are rejected
rather than assigned guessed semantics. Float syntax and semantics are
outside the project fragment entirely.

#### The verified front door (`FznCheck.lean`)

`checkSolutionFull` itself decides the dynamic part of satisfaction only;
its correctness theorem takes static well-formedness and predicate
checkability as explicit preconditions. The CLI therefore does not call
it directly: `LeanFzn/Checker/Check.lean` provides `checkModelSolution`, a
verified wrapper that establishes both preconditions itself and
classifies every failure mode. Its correctness theorem
`checkModelSolution_correct` is unconditional: acceptance is equivalent
to full `Satisfies fullSig fullInterp` (with the completed store of the
parsed entries), `WellFormed fullSig m`, and all-checkable constraint
names. `checkModelSolution_accepted` adds what the store is: for an
accepted solution, the completed store maps every assigned name to the
value written in the solution (`completedStore_entry`), gives every
parameter its declared value (`ParamHonest`, via
`completedStore_paramHonest`), and satisfies the model. The CLI runs
`checkModelSolutionFast`, which returns exactly the same outcome
(`checkModelSolutionFast_eq`). The wrapper consists of:

* `wellFormedFastB` — a hash-based fast twin of `wellFormedB`,
  proved equivalent by `wellFormedFastB_iff`. The naive checker is
  Θ(n²) (about 37 s at the benchmark's 32,000 variables); the fast
  twin is linear (~50 ms for the whole front door there).
* `firstUnsupported` — the predicate-name precondition, with
  `firstUnsupported_none_iff`.
* `entriesOkB` — entry well-formedness: a solution string assigns
  declared variables only, each at most once (A7/A10). This closed a
  hole where a cheating string could reassign a *parameter* (e.g.
  override `int: k = 3;` with `k = 5;`) and satisfy constraints its
  model-given values violate; the old checker accepted such strings.
  `Tests/Checker/Check.lean` pins the rejection.

Solver output with several solutions (each ended by a `----------` line) is
split by `splitSolutions`; `leanfzn check` checks every solution and reports
the first one that is not accepted.

## Project layout

```text
LeanFzn/
  Syntax/             AST and common syntax
  Parser/Proofs/      Parsing, printing and parser correspondence
  Semantics/Globals/  Model meanings and predicate interpretations
  Checker/            Solution parsing, completion and checking
  Compiler/Proofs/    Compilation and source correspondence
  Solver/
    Core/             Problems, domains and finite enumeration
    Propagation/      Shared filtering, explanation contracts and proofs
    Chronological/    Current certified frontier strategy
    UIP/              First-UIP scheduler and conditional certification
    Reference/        Diagnostic search
  Integration/        Source verdict proofs and fallback composition
  Cli/                Command adapters
Tests/                Parser, Checker, Semantics, Propagation,
                      Chronological, UIP and Integration (including compiler checks)
audits/               Axiom and component-boundary checks
specification/        Pinned FlatZinc reference
Main.lean             Stable executable wrapper
PLAN.md               Sole continuation plan
```

## Building and running

Requires Lean 4.33.1 (see `lean-toolchain`; `elan` installs it automatically).

```sh
# Build the complete library, test modules and every executable:
lake build LeanFzn Tests leanfzn \
  tests_smoke tests_stdlib tests_solution tests_gecode tests_globals \
  tests_bench tests_coverage tests_wellformed tests_pretty tests_prof tests_check \
  tests_solver tests_prop tests_fast tests_lcg tests_lcg_analysis tests_oracle \
  tests_lcg_scheduler_fixtures tests_lcg_scheduler_activation \
  tests_scheduler_computability tests_lcg_public_fixtures

# Components can also be built independently, for example:
lake build LeanFzn.Parser LeanFzn.Checker \
  LeanFzn.Solver.Chronological LeanFzn.Solver.UIP

# Run the listed test and benchmark suites; stop at the first failure:
for t in tests_smoke tests_stdlib tests_solution tests_gecode tests_globals \
         tests_bench tests_coverage tests_wellformed tests_pretty tests_prof \
         tests_check tests_solver tests_prop tests_fast tests_lcg \
         tests_lcg_analysis tests_oracle tests_lcg_scheduler_fixtures \
         tests_lcg_scheduler_activation tests_scheduler_computability \
         tests_lcg_public_fixtures; do
  lake env $t || exit 1
done

# Per-suite reference (each also runs standalone through `lake env`)
lake env tests_smoke      # 41 parser smoke tests
lake env tests_stdlib     # 64 standard-library tests (static + dynamic)
lake env tests_solution   # solution-checker end-to-end tests
lake env tests_globals    # 52 global-constraint tests (static + dynamic + e2e)
lake env tests_gecode     # 64 Gecode-derived solution-checker regression tests (15 models)
lake env tests_coverage   # 465 tests covering every checkable predicate and global
lake env tests_check     # 18 front-door tests (outcome classes + exit codes)
lake env tests_bench     # compiled perf regression suite (front door + checker + parser timings)
lake env tests_wellformed # 49 static well-formedness tests
lake env tests_pretty     # 39 pretty-printer round-trip tests
lake env tests_prof      # profiling driver (parser timing analysis)
lake env tests_fast      # 7 fast-path differential tests

# Solver suites
lake env tests_solver    # 36 certified-path tests (compiler, theorems, CLI command)
lake env tests_prop      # 89 propagator tests
lake env tests_lcg       # 37 LCG engine tests

# Parse a FlatZinc file (prints the AST), or pipe via stdin
lake env leanfzn model.fzn
echo 'solve satisfy;' | lake env leanfzn -

# Check a solution string against a model (verified front door:
# static validation + predicate checkability + dynamic checking)
lake env leanfzn check model.fzn solution.txt

# Solve with the certified LCG path (source-level SAT/UNSAT theorems;
# `-` or omitted file reads stdin; --certified is a temporary
# no-op alias). Multi-value finite domains are admitted: SAT results
# carry the theorem (decisions + backtracking); UNSAT is claimed
# through either certified front door — the singleton door
# (`solve_certified_unsat_real`, singleton domains) or the wide
# decision-descent door (`solve_certified_unsat_wide`, all registered
# families including linLe) — both composed into the source-level
# `solveCertified_unsat_correct`.
lake env leanfzn solve model.fzn
```

Exit codes of `leanfzn`:

* parse mode: 0 = success, 1 = parse error, 2 = usage/IO error;
* `check` (every solution in the input is checked; the first one not
  accepted decides): 0 = solution(s) accepted; 1 = rejected (a domain, initializer,
  or constraint condition is unsatisfied); 2 = malformed model (static
  well-formedness or model-parse failure); 3 = unsupported predicate
  (unknown name, model declaration, or an intentionally unsupported
  global — see `Globals.globalsUnsupported`); 4 = malformed solution
  string (parse failure, parameter/unknown reassignment, duplicate
  assignment);
* `solve`: 0 = solution found, ending with `----------`; 1 = UNSAT,
  rendered as `=====UNSATISFIABLE=====`; 2 = malformed model or usage/IO/parse
  error; 3 = unsupported model. Accepted finite models have no internal
  budget-exhaustion outcome.

The listed build targets run the libraries and all 15 retained suites. A plain
`lake build` has no default target. Audit profiles are checked locally with
`lake env lean -j2 audits/certified_axioms.lean` and the identity-checking audit
script on its captured output.

## Project status

The public command remains the certified chronological propagation/learning
route. The first-UIP scheduler and its proofs are separate, and its concrete
public activation is still unfinished. The repository reorganization preserves
CLI arguments, outputs and accepted source models; it does not claim that the
conditional UIP proof package is complete.

Validation after restructuring (2026-10-12): explicit aggregate build passed
(486 jobs), all 21 registered test executables passed, component boundaries and
cycles passed, and the axiom audit passed 323/323 profiles on the standard
allowlist with no sorryAx. Boolean, integer, sparse-domain, auxiliary arithmetic,
SAT/UNSAT and error-exit CLI cases preserve recorded baseline results; emitted
SAT witnesses pass the checker. The certified alias has the same behavior.

See [PLAN.md](PLAN.md) for the exact remaining obligations and
[code-structure.md](code-structure.md) for module dependencies.
