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

**Status (2026-10-06):** the public finite-domain solver uses a certified,
fuel-bounded chronological frontier. Each pending frame stores a selected
assignment prefix and its remaining value alternatives. Exhausted alternatives
are consumed permanently, fixing the pairwise-disequality pigeonhole cycle.
The 4-variable/3-value UNSAT regression finishes with 241 frontier transitions.
The public SAT and parameter-honest UNSAT theorem contracts are unchanged.

This driver checks complete assignments against the original domains,
constraints and clauses. It currently does not prune with propagators or clause
learning; their executable primitives and proofs remain available for a future
coverage-preserving refinement. Exhaustive work can be exponential. The default
10,000-transition budget can still return `unknown` on larger finite models.
The compiler’s existing 1,000,000-assignment cap also applies.
See [PLAN.md](PLAN.md) for the current scope and remaining release gates.

The normative reference is **MiniZinc 2.10.0**, pinned to immutable commit
`c9f9b649b2a251a40aa427a84d7cce73a8807fea` (see
`specification/minizinc-2.10.0/README.md`). Float syntax and semantics are
deliberately excluded; strings remain supported in annotations.

## Main results

### Directly verified finite-domain solver

`leanfzn solve MODEL.fzn` (also accepting the `--certified` alias) runs the
well-formedness check, the fragment compiler, the nonempty finite int/bool gate,
and the explicit frontier driver. It reports `sat`, `unsat` or
`unsupported` with exit codes 0/1/3 (a statically malformed model is a
usage-class exit 2).

- A `sat store` satisfies the source model (`Direct.solveCertified_sat_correct`,
  composed with compiler exactness).
- `unsat` excludes every parameter-honest satisfying source store
  (`Direct.solveCertified_unsat_correct`, composed with compiler coverage).
- The traversal is FUEL-FREE: termination is kernel-checked by the
  frontier-cost measure, so an accepted finite model always receives a
  verdict (`solveCertified_total`); there is no budget-exhaustion
  `unknown` outcome.

`solver/LCG/Frontier.lean` implements the stack. `Proofs/Frontier.lean` proves
leaf soundness, coverage of pending alternatives, UNSAT exclusion and
completeness of the fuel-free `frontierSolve` (`frontierSolve_sat_leaf`,
`frontierSolve_sat_mem`, `frontierSolve_unsat_excludes`,
`frontierSolve_complete`, `chronological_total`). Its `branchCost` counts the
transitions needed to exhaust the original domain product; every expansion
consumes one unit of pending work, and the measure lives only in the
termination proof — the compiled executable never computes it.
This is a guarantee for the chronological driver; no completeness claim is made
for the retained historical analysis/flip loop (`lcgSearch.go`, now the
top-level `lcgSearchGo` with a compatibility alias).

The propagation, explanation and conflict-analysis modules are still checked.
They are not used to prune the current public frontier. Their earlier run-level
invariant theorems remain available for a later certified search refinement.
The unbounded exhaustive reference (`Direct.solve`) remains a small-model oracle.

Current checks: 85/85 solver tests, 117/117 LCG tests (including 64 graph edge
subsets checked against the exhaustive oracle and a beyond-budget UNSAT
acceptance case), 89/89 propagator tests, and all 66 audited theorem profiles
with standard Lean axioms only. The proof-hole scan
is clean. All 15 suites, including the checker benchmark, pass.

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
│                              #   or solve (certified LCG path)
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
├── solver/                    # Solver components; direct proof redesign in PLAN.md
│   ├── Core.lean              #   shared solver-core umbrella
│   ├── Core/                  #   architecture-neutral problem semantics
│   │   ├── Types.lean         #     problems, slots, domains, assignments
│   │   └── Semantics.lean     #     assignment/domain agreement
│   ├── LCG.lean               #   lazy-clause-generation umbrella
│   ├── LCG/                   #   literals, clauses, reasons, LCG state/proofs
│   ├── Direct.lean            #   direct-solver umbrella
│   ├── Direct/                #   replacement solver
│   │   ├── Types.lean         #     compiled data and result types
│   │   ├── Compile.lean       #     executable compiler and constraint evaluation
│   │   ├── Search.lean        #     executable exhaustive solver driver
│   │   ├── Proofs/Compile.lean#     exact compiler correspondence obligations
│   │   ├── Proofs/Search.lean #     finite-search correctness obligations
│   │   └── Correctness.lean   #     public direct SAT/UNSAT theorems
│   ├── Search.lean            #   exhaustive reference search + master theorems
│   ├── Domain.lean            #   finite-domain extraction from a model
│   ├── Emit.lean              #   output-only solution-text emission
│   ├── Propagators.lean       #   propagation contract + first propagators
│   ├── Extract.lean           #   constraint extraction for propagation
│   └── Tests*.lean            #   test executables (unit + integration)
│
├── solver.lean                # Solver library root (Search/Domain/Core/LCG/Direct)
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
      tests_lcg

# Run the listed test and benchmark suites; stop at the first failure:
for t in tests_smoke tests_stdlib tests_solution tests_globals tests_gecode \
         tests_coverage tests_check tests_bench tests_wellformed tests_pretty \
         tests_prof tests_fast tests_solver tests_prop tests_lcg; do
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
* `check`: 0 = solution accepted; 1 = rejected (a domain, initializer,
  or constraint condition is unsatisfied); 2 = malformed model (static
  well-formedness or model-parse failure); 3 = unsupported predicate
  (unknown name, model declaration, or an intentionally unsupported
  global — see `Globals.globalsUnsupported`); 4 = malformed solution
  string (parse failure, parameter/unknown reassignment, duplicate
  assignment);
* `solve`: 0 = solution found (printed as-is, ending with the
  `----------` separator; multi-value domains included); 1 =
  unsatisfiable (`=====UNSATISFIABLE=====` on stdout; claimed only
  through the certified singleton or wide decision-descent front
  door); 2 = `unknown`/not well-formed — no verdict (fuel exhausted,
  an engine search the engine cannot complete — notably a nonempty
  unanalyzable conflict, where the chronological fallback retreats
  WITHOUT learning and may exhaust fuel (see the engine limits
  below) — or a statically malformed model; reason on stderr), also
  usage/IO/parse errors; 3 = unsupported model (outside the certified
  gate; reason on stderr).

**Known engine limits (do not overclaim).** The engine learns nogoods
at the leaf-failure arm and at the chronological fallback only when the
reported conflict clause is empty (the propagator-origin shape); when
`analyzeConflict` fails on a nonempty conflict clause the branch
retreats without learning, so a search whose progress depends on that
branch can exhaust fuel and report `unknown` even when the model has a
definite verdict. The known instances are the 4-slot/3-value
`int_ne` pigeonhole (UNSAT, currently reported as `unknown`) and a
satisfiable value-removal engine case (see PLAN.md P3). The
`hconfraw` entitlement proof for that branch
(`solver/LCG/Proofs/FallbackRaw.lean`) is proved but NOT yet wired
into the engine's run proof.

`Tests/WellFormed.lean` and `Tests/Pretty.lean` can also be run directly
with `lake env lean`; their `#eval`-based checks are compiled by the
corresponding executable targets above. The listed build targets are the
intended aggregate check; a plain `lake build` currently has no default
target. On 2026-09-29, the aggregate build (179 jobs: LeanFzn, solver,
leanfzn, all 15 test executables) completed, all suites passed, and the
10-theorem axiom audit (`audits/certified_axioms.lean`) reported only
the three standard Lean axioms; the axiom audit is now run by the
fail-closed `audits/run_axiom_audit.sh` in CI. The retired legacy
suites (heur, fix, enum, sbench, opt, rev, learn, restart) and their
modules were removed in the 2026-09-29 cleanup; Git history keeps them.
The current `tests_solver` state (76/78 checks passing, the
pigeonhole pair failing as documented in PLAN.md P3) is a known
deficit tracked there, not a green baseline.

## Project status and roadmap

The compiler proof is restored and split (CompileCore/CompileAux1/
CompileAux2a/2b/2c with a re-export shell), and two-literal `int_times`
shapes (`int_times(x,2,6)`, `int_times(2,x,6)`, `int_times(2,3,x)`,
and the other literal-argument shapes) are supported through aux
slots. The remaining solver work is the P3 engine-repair track
(fallback-search progress on nonempty unanalyzable conflicts), then
search completeness and sufficient fuel — see [PLAN.md](PLAN.md) for
the task DAG and gates, and [`code-structure.md`](code-structure.md)
for module dependencies. The axiom audit is fail-closed in CI
(`audits/run_axiom_audit.sh`).
On 2026-09-29 the full aggregate build (179 jobs) and all 15 suites
passed, and the axiom audit is clean (see above).
