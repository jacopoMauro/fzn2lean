# LeanFzn — FlatZinc, formalized in Lean 4

LeanFzn is a machine-checked formalization of the **integer/Boolean fragment
of FlatZinc**, the solver input language of the MiniZinc toolchain. It provides
a lexer, a parser, an independent declarative grammar, static and dynamic
semantics — and a machine-checked proof that the parser accepts **exactly** the
grammatically valid FlatZinc strings.

It can also be used to **check a solver-produced solution against a FlatZinc
model**. The checker parses the candidate assignments, completes aliases and
initializers, checks declared domains, and evaluates every supported standard
and global constraint. Its executable decision procedure is connected to the
declarative semantics by Lean proofs; the exact supported fragment and
preconditions are described below.

The normative reference is **MiniZinc 2.10.0**, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`). Float syntax and semantics are
deliberately excluded; strings remain supported in annotations.

## Main results

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

### The verified front door (`FznCheck.lean`)

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
│   ├── Emit.lean              #   solution-text emission
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
│   ├── Solver.lean            #   umbrella module (whole-stack overview)
│   └── Tests*.lean            #   test executables (unit + integration + bench)
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
# Build the library and all executables (the lakefile has no default
# target, so name them; `lake build LeanFzn` builds only the library)
lake build leanfzn tests_smoke tests_stdlib tests_solution tests_globals \
      tests_gecode tests_coverage tests_check tests_bench tests_wellformed \
      tests_pretty tests_prof tests_fast solver tests_solver tests_prop \
      tests_heur tests_fix tests_enum tests_sbench tests_opt tests_rev \
      tests_learn tests_restart

# Run the test suites
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

# Run the solver test suites
lake env tests_solver    # 198 solver tests (unit + e2e + config-matrix integration)
lake env tests_prop      # 38 propagator tests
lake env tests_heur      # 93 heuristic tests
lake env tests_fix       # 21 fixpoint tests
lake env tests_enum     # 31 enumeration tests
lake env tests_sbench    # 4 solver benchmark checks
lake env tests_opt       # 73 optimization tests
lake env tests_rev       # 26 reversible-state tests
lake env tests_learn     # 37 learning tests
lake env tests_restart   # 23 restart tests

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
corresponding executable targets above. The current Lean build succeeds but
still reports non-fatal linter warnings, primarily unused `simp` arguments in
proof scripts.

### The verified solver (`solver/`)

On top of the checker, the repository includes a verified
finite-domain satisfaction solver for the same fragment (PLAN.md item
6, phases 6.1–6.7), exposed through the `leanfzn solve`, `enum`, and
`optimize` subcommands (the composed front door `solveModelWith`;
see below). The stack: exhaustive reference search
(`solveModel`), fixpoint propagation with branch pruning
(`solveModelProp`), minimum-remaining-values branch ordering
(`solveModelHeur`), all-solutions enumeration (`enumModel`),
optimization in a reference and a branch-and-bound form
(`optimizeModel`, `optimizeModelBb`), a sparse-set reversible state
with a trail refining the propagation pass, decision-trail NoGood
learning, and budgeted restarts with an explicit `unknown` verdict
(`solveModelBounded`). All entry points share one architecture — every
candidate leaf is validated by the verified checker itself — and each
carries a Lean theorem: a returned solution text is always
checker-accepted (so it satisfies the full declarative semantics via
`checkModelSolution_correct`), and an `unsat` verdict excludes every
assignment of the declared finite domains — for the propagating
entry points under one documented hypothesis (the emitter round-trip
licence; see `solver/Solve.lean`).

The composed front door is `solveModelWith` (`solver/Config.lean`):
a `SolveConfig` (`useProp`, `useMrv`, `budget`, `nogoods`) selects the
features, and each supported combination — every switch alone, plus
propagation with MRV together — routes through the corresponding
proven entry point (the prop+MRV combination is composed by
permutation, with its own master theorems). `solveModelWith_sat_sound`
proves SAT soundness for the full supported configuration space;
budgeted runs report an interrupted search as `unknown`, never as
`unsat` (`solveModelWith_budget_never_falseUnsat`). Other feature
combinations are refused with an explicit reason.

## Project status and roadmap

See [`PLAN.md`](PLAN.md) for the completed milestones, current limitations,
and prioritized correctness-preserving extensions and performance work.
