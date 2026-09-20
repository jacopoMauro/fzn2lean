# LeanFzn — FlatZinc, formalized in Lean 4

LeanFzn is a verified FlatZinc toolchain in Lean 4 for the
**integer/Boolean/set fragment** of the MiniZinc solver language. Its checker
covers that fragment, while its search engine solves models whose decision
variables have explicit finite integer or Boolean domains. Its three main
results are:

- a finite-domain solver that can decide satisfiability, enumerate solutions,
  and optimize objectives;
- a solution checker covering 218 standard and global predicate names; and
- a parser proved to recognize exactly the declarative FlatZinc grammar.

These are one connected development rather than three unrelated programs.
The CLI receives a FlatZinc source file, so it first uses the verified parser
to turn that text into the `Model` syntax tree on which both checking and
solving are defined. The checker is then reused inside the solver as the
predicate for complete candidate assignments: a search leaf succeeds exactly
when the emitted assignment is accepted by the checker. Thus the solver's SAT
proof composes two results—search returns only a successful leaf, and checker
acceptance implies declarative satisfaction. Reference search,
propagation, heuristics, learning, restarts, enumeration, and branch-and-bound
optimization all carry Lean theorems describing the results they may return.

The normative reference is **MiniZinc 2.10.0**, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`). Float syntax and semantics are
deliberately excluded; strings remain supported in annotations.

## Main results

### Verified finite-domain solver

The solver is a main result of this repository, not merely an application of
the parser.  It is available through `leanfzn solve`, `leanfzn enum`, and
`leanfzn optimize`, and its complete umbrella module is
`solver/Solver.lean`.

The current search fragment contains initializer-free Boolean variables and
bounded or explicitly enumerated integer variables. Unbounded integer
variables, set decision variables, domains above `domainCap`, and search
spaces above `leavesCap` are reported as unsupported rather than searched
incompletely. Variables determined by initializers—including array aliases—are
reconstructed by the solution checker's completion machinery instead of
becoming search slots.

For supported finite models, the proof-facing solver contract distinguishes:

- **SAT:** the returned assignment is accepted by the verified front door and
  therefore satisfies the model's declarative `fullInterp` semantics;
- **UNSAT:** no assignment drawn from the declared finite domains satisfies
  the model, subject to the documented round-trip licence for propagating
  entry points while P0 in `PLAN.md` remains open;
- **unknown:** a bounded run exhausted its resource budget and makes no SAT or
  UNSAT claim; and
- **unsupported:** the model or requested feature combination is outside the
  implemented solver interface.

The unbounded reference search terminates because each branch decreases a
finite-domain measure.  Its central results are exposed by
`solveModel_sat_sound` and `solveModel_unsat_sound`; the composed configurable
front door is covered by `solveModelWith_sat_sound`,
`solveModelWith_unsat_sound`, and
`solveModelWith_budget_never_falseUnsat`.

#### How the solver works

1. **Validate and extract the finite problem.** The FlatZinc model first
   passes the same static well-formedness and supported-predicate gates used by
   the checker. `modelSlots` extracts explicit finite domains for decision
   variables, while `extractConstraints` recognizes constraints supported by
   the propagation layer. The extraction bridge
   `extractConstraints_holds` connects those internal constraints back to the
   model semantics.
2. **Run a complete reference search.** `search` enumerates assignments over
   the extracted slots. Its leaf predicate pairs slot names with candidate
   values, emits that assignment in FlatZinc solution syntax, and calls the
   verified checker. The search returns an assignment only when this predicate
   is true. This makes `checkModelSolution_correct` the semantic bridge in the
   SAT proof, while reference search remains the simple, deterministic baseline
   for optimized variants.
3. **Prune with verified propagation.** A propagator returns narrowed domains
   or a contradiction. Every propagator implements the `Preserves` contract:
   narrowing retains every compatible satisfying assignment, while a reported
   contradiction excludes all satisfying extensions. A fuel-bounded fixpoint
   composes these local results before and during `prunedSearch`.
4. **Recognize useful constraint shapes.** The wired propagators include
   equality, disequality, order, constant equality, integer arithmetic and
   bounds, Boolean connectives, `all_different`, and linear equality/inequality.
   The linear propagators `propLinEq` and `propLinLe` have proved preservation
   theorems and are extracted from `int_lin_eq` and `int_lin_le` models.
5. **Change search order without changing coverage.** `mrvOrder` selects a
   minimum-remaining-values order. The branch-coverage and permutation lemmas
   show that MRV changes only exploration order, not the assignments covered.
   `solveModelPropMrv` composes propagation and MRV through the same proof
   boundary.
6. **Learn and restart safely.** Decision-trail NoGoods have a declarative
   clause semantics and scope-limited entailment proofs. `learnSearch` agrees
   with reference search. Budgeted `searchBudget` and `restartSearch`
   distinguish exhaustion from budget interruption; interrupted searches
   return `unknown`, and fair schedules recover completeness.
7. **Enumerate and optimize.** `enumModel` proves membership, completeness,
   distinctness, and UNSAT results for all-solutions enumeration.
   `optimizeModel` and `optimizeModelBb` prove solution soundness, optimality,
   UNSAT behavior, and objective-value agreement; the branch-and-bound result
   is related to the reference optimizer by `optimizeModelBb_agrees`.
8. **Connect search results to model satisfaction.** The text returned by a
   successful solve is the same text accepted by the leaf predicate; the CLI
   does not perform a second redundant check after solving. The theorem
   `solveModelWith_sat_sound` transports that recorded leaf acceptance through
   `checkModelSolution_correct`, yielding satisfaction of the declarative
   model semantics.

The implementation also contains a reversible sparse-set state and trail.
`sparseNarrow_spec`, `revBacktrack_recovers`, and `revPropPass_refines` prove
its domain view, restoration behavior, and one-pass agreement with the
functional propagator. Wiring that state into search, adding queued wake-up
propagation, and watched NoGoods are future performance work rather than
missing pieces of the reference solver.

The remaining emitter/parser round-trip work is isolated in
`solver/Emit/Roundtrip.lean`, which currently builds successfully. The honest
offset-transport and emitted token-segment layers are proved for Boolean,
nonnegative-integer, and negative-integer literals; the complete nonnegative
entry walk and the generic four-token entry walk are also proved. Next come
the Boolean/negative walk instances and scalar-entry `parseEntry` reduction,
followed by the list-level `parseSolution` theorem and a string-free leaf path.
See `PLAN.md` P0 for the authoritative checklist.

### Exact parser recognition

The recognition theorem is proven with no `sorry` or user-declared `axiom`.

```lean
theorem parseModel_ok_iff_valid (s : String) :
    (∃ m, Parser.parseModel s = .ok m) ↔ ValidFlatZinc s

theorem parseModel_error_iff_invalid (s : String) :
    (∃ e, Parser.parseModel s = .error e) ↔ ¬ ValidFlatZinc s
```

That is: the parser succeeds on a string if and only if that string is a valid
FlatZinc program, and it fails exactly on the invalid ones. This is the
combination of two directions, each proven independently:

- **Soundness** (`FznCorrectness.lean`): every successful parse yields a model
  that the declarative grammar derives — the parser never accepts garbage.
- **Completeness** (`FznCompleteness.lean`, `FznAssembled.lean`): every grammar
  derivation is accepted by the parser, producing exactly the derived AST —
  the parser never rejects, or mangles, a valid program.

The parser is a fuelled recursive-descent implementation; completeness
includes a proof that the fuel budget `8 * (tokens + 1)` always suffices.

### Verified solution checker

The executable checker uses a small number of `opaque` logical wrappers
paired with verified executable implementations.

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
it directly: `LeanFzn/FznCheck.lean` provides `checkModelSolution`, a
verified wrapper that establishes both preconditions itself and
classifies every failure mode. Its correctness theorem
`checkModelSolution_correct` is unconditional: acceptance is equivalent
to full `Satisfies fullSig fullInterp` (with the completed store of the
parsed entries), `WellFormed fullSig m`, and all-checkable constraint
names. The wrapper consists of:

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
  `Tests/Check.lean` pins the rejection.

## Project layout

```
leanfzn/
├── LeanFzn.lean              # Umbrella module — imports the whole library
├── Main.lean                  # CLI: parse a file/stdin, check a solution,
│                              #   or solve / enumerate / optimize
├── PLAN.md                    # Current status and prioritized future work
├── code-structure.md          # Direct-import dependency map and module layers
├── lakefile.toml              # Lake build configuration
├── lean-toolchain             # Lean 4.33.1
│
├── LeanFzn/                   # The formalization library
│   ├── FznAST.lean            #   AST: items, expressions, types, annotations
│   ├── FznLexer.lean           #   Total lexer: tokens, integers, strings
│   ├── FznParser.lean          #   Fuelled recursive-descent parser
│   ├── FznGrammar.lean         #   Independent declarative grammar (Gr* rules)
│   ├── FznSemantics.lean       #   Values, evaluation, constraint satisfaction
│   ├── FznSuffix.lean          #   Suffix/consumption lemmas (fuel bookkeeping)
│   ├── FznCorrectness.lean     #   Soundness: parse success ⇒ grammar validity
│   ├── FznCompleteness.lean    #   Component completeness: each Gr* rule is parsed
│   ├── FznAssembled.lean       #   Model-level completeness + recognition theorem
│   ├── FznPretty.lean          #   Canonical pretty-printer (round-trip tested)
│   ├── FznStdLib.lean          #   Standard predicate signatures + interpretations
│   ├── FznSolution.lean        #   Solution-string parser + verified checker
│   ├── FznGlobals.lean         #   Global constraints: signatures, twins, master theorem
│   ├── FznCheck.lean          #   Verified CLI front door: fast static twin,
│   │                          #     outcome classification, wrapper theorem
│   └── FznGlobals/             #   Global-constraint families (frozen, verified)
│       ├── Common.lean         #     Shared list/set helpers
│       ├── AllDiffCounting.lean #   all-different family (8 fzn_* names)
│       ├── LexSort.lean        #     lex/sort/value-precedence family (12 names)
│       ├── PackSched.lean      #     packing/scheduling family (17 names)
│       ├── Counting.lean       #     counting family (32 names)
│       ├── Channeling.lean     #     channeling family (11 names)
│       ├── SetMath.lean        #     set/mathematical family (14 names)
│       ├── LexChain.lean       #     reverse/2D lex family (10 names)
│       ├── Graph.lean          #     circuit/graph family (18 names)
│       ├── Regular.lean        #     regular/mdd family (6 names)
│       └── Sched2.lean         #     scheduling/remaining family (10 names)
│
├── Tests/
│   ├── Smoke.lean              # 30 parser smoke tests (valid + malformed input)
│   ├── WellFormed.lean         # static well-formedness tests (library-only)
│   ├── Pretty.lean             # 39 pretty-printer round-trip tests (library-only)
│   ├── StdLib.lean             # 64 standard-library tests (static + dynamic)
│   ├── Solution.lean           # solution-checker end-to-end tests
│   ├── Globals.lean            # 52 global-constraint tests (static + dynamic + e2e)
│   ├── Gecode.lean             # 64 Gecode-ported regression tests (15 models)
│   ├── Coverage.lean           # 465 tests covering ALL checkable predicates
│   ├── Check.lean             # 12 front-door tests: every outcome class + exit codes
│   └── Bench.lean              # compiled perf regression suite (front door + checker + parser)
│
├── solver/                    # The verified constraint solver (PLAN item 6)
│   ├── Search.lean            #   exhaustive reference search + master theorems
│   ├── Domain.lean            #   finite-domain extraction from a model
│   ├── Emit.lean              #   solution-text emission + round-trip proof work
│   ├── Solve.lean             #   entry points: solveModel / solveModelProp / solveModelHeur
│   ├── Propagators.lean       #   propagation contract + first propagators
│   ├── Fixpoint.lean          #   propagation fixpoint + pruning search
│   ├── Heuristic.lean         #   MRV branch ordering (permutation composition)
│   ├── Enum.lean              #   all-solutions enumeration
│   ├── Extract.lean           #   constraint extraction for propagation
│   ├── Optimize.lean          #   optimization (reference + branch and bound)
│   ├── RevState.lean          #   sparse-set reversible state + trail
│   ├── Learning.lean          #   decision-trail NoGood learning
│   ├── Restarts.lean          #   budgeted restarts with the `unknown` verdict
│   ├── Config.lean            #   composed front door: SolveConfig / solveModelWith
│   ├── Solver.lean            #   complete solver umbrella used by CLI/tests
│   └── Tests*.lean            #   test executables (unit + integration + bench)
│
├── solver.lean                # Core-only solver root (Search/Domain/Emit/Solve)
│
└── specification/
    ├── minizinc-2.10.0/        # The pinned normative reference
    │   ├── README.md           #   Provenance: commit, checksums, links
    │   ├── predicates_and_globals_report.md  # inventory of all builtin/global names
    │   └── fzn-grammar.mzn     #   Vendored official FlatZinc grammar
    └── flatzinc_specification_assumptions.md  # R/A/G-series: every assumption, incl.
                                  #   all predicate-semantics decisions (G-series)
```

### The proof pipeline

The modules form a deliberate chain, each layer building on the last:

1. **`FznAST`** defines the abstract syntax that both the parser and the
   grammar produce.
2. **`FznLexer`** turns a string into tokens, totally, with progress lemmas.
3. **`FznParser`** (implementation) and **`FznGrammar`** (specification) are
   kept strictly independent: the grammar is an inductive relation over token
   lists, not a transcription of the parser.
4. **`FznSuffix`** proves that every grammar rule consumes input, giving the
   fuel bookkeeping needed for termination of the completeness argument.
5. **`FznCorrectness`** proves the parser sound against the grammar.
6. **`FznCompleteness`** proves each grammar rule is matched by the parser,
   with the fuel invariant `2 * remaining + K ≤ fuel`.
7. **`FznAssembled`** chains the component lemmas into `parseModel_complete`
   and the recognition theorems above.
8. **`FznSemantics`** gives the dynamic meaning of models (evaluation,
   satisfaction, objectives), kept separate from the parsing story.
9. **`FznStdLib`** gives the builtins a Prop semantics (`stdInterp`) plus a
   computable twin (`stdInterpB`), proved equivalent per name.
10. **`FznSolution`** checks solution strings against a model; every check
    step is mirrored by a per-name `iff` theorem, capped by the master
    correctness theorem for the standard fragment.
11. **`FznGlobals/*`** (ten family modules, frozen) supply the same
    Prop/twin/agreement triple for the 138 `fzn_*` globals; **`FznGlobals`**
    assembles them into the combined interpretation, the master agreement
    `globalsInterpB_iff`, and the full-checker correctness theorem
    `checkSolutionFull_correct`.

### Where the predicate semantics come from

The FlatZinc specification assigns no meaning to `fzn_*` solver
predicates, and several builtin glosses are loose about corner cases.
Every interpretive decision — 1-based array positions, tie-breaking,
partiality, set-lexicographic order, closedness of global
cardinalities, cumulative event-point checking, … — is recorded with
its normative justification in
`specification/flatzinc_specification_assumptions.md` (**G-series**),
with per-predicate handbook quotations and `.mzn` decomposition
citations in the module docstrings (`FznStdLib.lean` and
`LeanFzn/FznGlobals/*.lean`). Reference-solver behavior (Gecode) pins
the two cases where the handbook was genuinely wrong-footing
(truncated division, clause negation). Every decision is executable:
`Tests/Coverage.lean` exercises all 218 checkable names in both truth
directions and fails the build if a name is untested.

## Building and running

Requires Lean 4.33.1 (see `lean-toolchain`; `elan` installs it automatically).

```sh
# The one documented clean-build command (the lakefile has no default
# target, so every target is named; `lake build LeanFzn` builds only
# the library, `lake build solver` only the solver library):
lake build leanfzn solver tests_smoke tests_stdlib tests_solution tests_globals \
      tests_gecode tests_coverage tests_check tests_bench tests_wellformed \
      tests_pretty tests_prof tests_fast tests_solver tests_prop \
      tests_heur tests_fix tests_enum tests_sbench tests_opt tests_rev \
      tests_learn tests_restart

# The one documented functional-test command (runs every suite and
# fails on the first failure):
for t in tests_smoke tests_stdlib tests_solution tests_globals tests_gecode \
         tests_coverage tests_check tests_bench tests_wellformed tests_pretty \
         tests_prof tests_fast tests_solver tests_prop tests_heur tests_fix \
         tests_enum tests_sbench tests_opt tests_rev tests_learn tests_restart; do
  lake env $t || exit 1
done

# Per-suite reference (each also runs standalone through `lake env`)
lake env tests_smoke      # 30 parser smoke tests
lake env tests_stdlib     # 64 standard-library tests (static + dynamic)
lake env tests_solution   # solution-checker end-to-end tests
lake env tests_globals    # 52 global-constraint tests (static + dynamic + e2e)
lake env tests_gecode     # 64 Gecode-derived solution-checker regression tests (15 models)
lake env tests_coverage   # 465 tests covering every checkable predicate and global
lake env tests_check     # 12 front-door tests (outcome classes + exit codes)
lake env tests_bench     # compiled perf regression suite (front door + checker + parser timings)
lake env tests_wellformed # 49 static well-formedness tests
lake env tests_pretty     # 39 pretty-printer round-trip tests
lake env tests_prof      # profiling driver (parser timing analysis)
lake env tests_fast      # 7 fast-path differential tests

# Solver suites
lake env tests_solver    # 198 solver tests (unit + e2e + config-matrix integration)
lake env tests_prop      # 109 propagator tests
lake env tests_heur      # 93 heuristic tests
lake env tests_fix       # 21 fixpoint tests
lake env tests_enum     # 31 enumeration tests
lake env tests_sbench    # 4 solver benchmark checks
lake env tests_opt       # 73 optimization tests
lake env tests_rev       # 26 reversible-state tests
lake env tests_learn     # 37 learning tests
lake env tests_restart   # 26 restart tests

# Parse a FlatZinc file (prints the AST), or pipe via stdin
lake env leanfzn model.fzn
echo 'solve satisfy;' | lake env leanfzn -

# Check a solution string against a model (verified front door:
# static validation + predicate checkability + dynamic checking)
lake env leanfzn check model.fzn solution.txt

# Solve a model (verified solver, reference search by default).
# Flags: --prop (fixpoint propagation), --mrv (MRV branch ordering),
# --budget N (budgeted restarts, may report `unknown`),
# --nogoods (NoGood learning); supported combos are each switch
# alone and --prop with --mrv together. `-` or omitted file reads
# stdin.
lake env leanfzn solve model.fzn
lake env leanfzn solve --prop --mrv model.fzn

# Enumerate all solutions (FlatZinc output convention: each solution
# text, then a final ========== separator)
lake env leanfzn enum model.fzn

# Optimize (branch and bound): prints the optimal solution text and
# the ========== separator, with the objective value on stderr
lake env leanfzn optimize model.fzn
```

Exit codes of `leanfzn`:

* parse mode: 0 = success, 1 = parse error, 2 = usage/IO error;
* `check`: 0 = solution accepted; 1 = rejected (a domain, initializer,
  or constraint condition is unsatisfied); 2 = malformed model (static
  well-formedness or model-parse failure); 3 = unsupported predicate
  (unknown name, model declaration, or an intentionally unsupported
  global — see `Globals.globalsUnsupported`); 4 = malformed solution
  string (parse failure, parameter/unknown reassignment, duplicate
  assignment);
* `solve`: 0 = solution found (printed as-is, ending with the
  `----------` separator); 1 = unsatisfiable
  (`=====UNSATISFIABLE=====` on stdout); 2 = `unknown` — no verdict
  (budget exhausted or statically refused; reason on stderr), also
  usage/IO/parse errors; 3 = unsupported model or configuration
  (reason on stderr);
* `enum`: 0 = all solutions enumerated (each text, then `==========`);
  1 = unsatisfiable (`=====UNSATISFIABLE=====` on stdout); 3 =
  unsupported model (reason on stderr); usage/IO/parse errors exit 2;
* `optimize`: 0 = optimal solution found (text + `==========` on
  stdout, `objective = VALUE` on stderr); 1 = unsatisfiable
  (`=====UNSATISFIABLE=====` on stdout); 3 = unsupported model or
  objective (reason on stderr); usage/IO/parse errors exit 2.

`Tests/WellFormed.lean` and `Tests/Pretty.lean` can also be run directly
with `lake env lean`; their `#eval`-based checks are compiled by the
corresponding executable targets above. The clean build completes with
**zero linter warnings** (the two split-heavy parser modules carry an explicit
`linter.unusedSimpArgs` suppression documented in their headers; scratch
and probe files live under `archive/` and are not part of any Lake target).

## Project status and roadmap

See [`PLAN.md`](PLAN.md) for the completed milestones, current limitations,
and prioritized correctness-preserving extensions and performance work.  See
[`code-structure.md`](code-structure.md) for the current dependency map;
candidate simplifications are recorded in `PLAN.md` P4 and have not yet been
applied to the source tree.
