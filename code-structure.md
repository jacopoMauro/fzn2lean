# LeanFzn dependency structure

The public solver uses the certified chronological frontier through the LCG API (`leanfzn solve` →
`Direct.solveCertified`), with kernel-checked source-level SAT/UNSAT
theorems. The legacy checker-mediated solver stack (Config, Solve,
Fixpoint, Heuristic, Enum, Optimize, RevState, Learning, Restarts,
the `solver/Tree` reference layer, and the `solver/Solver` umbrella)
was retired in the 2026-09-29 cleanup (PLAN.md §1); Git history
keeps it.

The dependency root is `solver.Core`, which contains only shared
problem and assignment semantics; `solver.LCG` is the certified
solver layer and `solver.Direct` the compiler + exhaustive
reference. Operational state lives in `solver.LCG`.

This file records the current module dependency graph for LeanFzn.
Arrows written as `A ← B` mean that `A` directly imports `B`.  The numbered
layers are explanatory groupings, not enforced package boundaries; the direct
imports are the source of truth.

## Legend

- `★` marks shared/high-fan-out modules.
- Development scratch artifacts were removed from the live tree in
  the 2026-09-27 cleanup (history preserved in Git).
- Test executables are listed separately at the end.

---

## Library and solver layers

```
Layer 0 — Foundation (no project imports)
├── LeanFzn/FznAST.lean ★         AST types (Ident, Value, BaseType, VDecl, ConstraintItem, Model)
├── LeanFzn/FznLexer.lean ★       Tokenizer (Token type, tokenize)
└── solver/Search.lean ★          Generic exhaustive search (allAssigns, search_some/none)

Solver core — shared foundation
├── solver/Core/Types.lean         Generic Problem; Slot/Domain/Assignment;
│                                  SearchResult
│   └── ← FznSemantics
├── solver/Core/Semantics.lean     Architecture-independent assignment semantics
│   └── ← Core/Types
└── solver/Core.lean               Shared-core umbrella
    └── ← Core/Types, Core/Semantics

Lazy clause generation layer (the certified solver)
├── solver/LCG/Types.lean          Atoms, literals, clauses, reasons, LCG State
├── solver/LCG/TrailEval.lean      Trail queries, norm literals, 1-UIP analysis
├── solver/LCG/Operations.lean     Evaluation (intView), trail, learning, API
├── solver/LCG/Encoding.lean       L0.1 foundation: literal laws, order encoding,
│                                  WellFormed, assignment↔valuation carving
│   └── ← LCG/Operations, LCG/Invariants
├── solver/LCG/Invariants.lean     Entailment, representation, conflict meaning
├── solver/LCG/Propagate.lean      Explanation-carrying bound propagators
├── solver/LCG/Frontier.lean       Pending value alternatives and finite work cost
│   └── ← Core/Types
├── solver/LCG/Engine.lean         Clause/propagation primitives + chronological driver
│   └── ← LCG/Propagate, LCG/Frontier
├── solver/LCG/Proofs/Frontier.lean  Branch coverage, verdict soundness, sufficient fuel
│   └── ← LCG/Engine, LCG/Invariants, solver/Search
├── solver/LCG/Search.lean          Executable entry points (solve/solveDom)
├── solver/LCG/Proofs/Transitions.lean  Local transition obligations
├── solver/LCG/Proofs/Search.lean  Public contracts via Proofs/Frontier; historical go obligations
│   (go_sat_leaf, strengthened go_unsat_shape with retained leaf facts,
│    EngineSafe over terminal states, unsat_root_leaf_constructive;
│    item 7 scaffold: initialWithRoots_fields,
│    unsat_root_conflict_constructive)
├── solver/LCG/Proofs/Singleton.lean  Singleton characterization
│   (Step 2.E item 1: fits_allSingleton_eq)
├── solver/LCG/Proofs/Theory.lean  Constructive no-excluded-solution theory
│   (SolvedBy invariant threads, enqueueNorm branch algebra, opposing-fact
│    branch unreachable for justified enqueues, scan-arm exclusion
│    scanConflict_excludes, per-gate inverses, coherence bridges, leSlot
│    kernel, PropSafe packaging bridge; item 6: sweep_solvedBy fold and
│    the MASTER RESULT propagateLoop_excludes)
├── solver/LCG/Proofs/Run.lean   Run-level reachability + the DECISION-DESCENT
│   MASTER THEOREM go_unsat_entry_invariant (every .unsat arises at a
│   level-0 conflict-clear SolvedBy entry; both terminal shapes), the
│   RunInv bundle + per-transition preservation, Level0Solved algebra,
│   the empty-conflict non-analyzability lemmas; newDecisionLevel_runInv
│   and enqueueNorm_runInv_pos preserve fallback flips above level zero
├── solver/LCG/Proofs/ConstFamilies.lean  The five constant-bound families
│   (leConstHi/Lo, ltConstHi/Lo, constEq): views, hygiene, safe triples,
│   entitlement, reason-validity + the shared narrow inversions
├── solver/LCG/Proofs/Propagators.lean  The eleven-family registration +
│   propagatorsOfProved_safeUniv/_entitled front doors
├── solver/LCG/Proofs/Reason.lean  The master theorem's PREMISE-DISCHARGE
│   layer (2026-10-01): state-free reason-validity (two-case constraint
│   disjunctions; linLe excluded — machine-checked obstruction), the
│   rooted hjust, the cc≠[] conflict entitlement, the initial-state seeds
├── solver/LCG/Proofs/Obstructions.lean  Machine-checked obstructions and
│   counterexamples justifying the invariant gates (TrailDistinct,
│   TrailBoolPins, the run-relativized hconfent); extracted 2026-10-05
│   from the former tmp/ scratch deliverables; a leaf module with no
│   importers, kept as maintained regressions
└── solver/LCG.lean                LCG-layer umbrella

Layer 1 — Grammar, Parser, Semantics
├── LeanFzn/FznGrammar.lean        Derivability relation (GrModel, GrSepList, …)
│   └── ← FznAST, FznLexer
├── LeanFzn/FznParser.lean ★       Recursive-descent parser (parseModel)
│   └── ← FznAST, FznLexer
├── LeanFzn/FznPretty.lean         Pretty-printer (prettyModel, round-trip)
│   └── ← FznAST
├── LeanFzn/FznSemantics.lean ★    Types, values, stores, signatures, Satisfies
│   └── ← FznAST
└── solver/Propagators.lean ★      Propagation contract + propagators (Preserves, propEqSlot, …)
                                   + linear propagators (propLinEq/propLinLe, DomConstraint.linEq/linLe,
                                   dotSum_bounds, term_bound, proved preservation theorems)
    └── ← LeanFzn*, solver/Search

Layer 2 — Correctness, StdLib
├── LeanFzn/FznSuffix.lean         Grammar suffix/consumption bounds
│   └── ← FznGrammar
├── LeanFzn/FznCorrectness.lean    Parser soundness (parseModel → GrModel)
│   └── ← FznParser, FznGrammar, FznSemantics
└── LeanFzn/FznStdLib.lean ★       Standard predicate signatures + interpretations (stdSig, stdInterp)
    └── ← FznSemantics

Layer 3 — Completeness, Solution, Extraction
├── LeanFzn/FznCompleteness.lean   Parser completeness (GrModel → parseModel)
│   └── ← FznCorrectness, FznSuffix
├── LeanFzn/FznSolution.lean ★     Solution checker (checkSolution, checkSolution_correct)
│   └── ← FznParser, FznCorrectness, FznStdLib, Lean
├── solver/Extract.lean ★          Constraint extraction for propagation
│   └── ← LeanFzn*, solver/Search, solver/Domain, solver/Propagators
├── solver/Domain.lean ★           Finite-domain extraction from parsed models (modelSlots)
│   └── ← LeanFzn*
├── solver/Direct/Types.lean       Source wrapper over Core.Problem + result
│   └── ← Core/Types, FznGlobals
├── solver/Direct/Compile.lean     Executable compiler and leaf evaluation
│   └── ← Direct/Types, Domain, Extract, Propagators
├── solver/Direct/Search.lean      Executable exhaustive direct solver
│   └── ← solver/Search, Direct/Compile
├── solver/Direct/Proofs/CompileCore.lean  Core compilation proof obligations:
│   lookup, compiler inversion, store bridge, constraint exactness,
│   slot/typing chains, compile-list inversions, assembly ingredients,
│   bool typing chain (split from Compile.lean in the 2026-10-05 P1c
│   memory-driven split; statements unchanged)
│   └── ← solver/Core, Direct/Compile
├── solver/Direct/Proofs/CompileAux1.lean  Aux-slot expansion infrastructure:
│   name freshness, nameIndex append lemmas, expansion pre-pass
│   spec/membership inversions, emitted-slot properties, per-piece
│   compile inversions
│   └── ← Direct/Proofs/CompileCore
├── solver/Direct/Proofs/CompileAux2a.lean  Per-shape semantic bridges (SAT
│   and coverage), extended read chains, first argument inversions
│   └── ← Direct/Proofs/CompileAux1
├── solver/Direct/Proofs/CompileAux2b.lean  Remaining argument inversions
│   (two-literal times, and/or shapes), aux-slot linker premises
│   └── ← Direct/Proofs/CompileAux2a
├── solver/Direct/Proofs/CompileAux2c.lean  Per-shape name inversions and
│   per-piece successful-compile inversions
│   └── ← Direct/Proofs/CompileAux2b
├── solver/Direct/Proofs/Compile.lean  Re-export shell preserving the
│   module's public face for Exact/Fam.AllDiff/the reference solver
│   └── ← CompileCore, CompileAux1, CompileAux2a/2b/2c
├── solver/Direct/Proofs/Search.lean   Search proof obligations
│   └── ← Direct/Search, solver/Propagators
├── solver/Direct/Correctness.lean Public direct SAT/UNSAT theorem obligations
│   └── ← Direct/Proofs/Compile, Direct/Proofs/Search
├── solver/Direct.lean             Direct-solver public umbrella
│   └── ← all solver/Direct modules
├── solver/Emit/Basic.lean         Stable executable solution emission
│   └── ← Lean, solver/Domain
└── solver/Emit.lean               Output-only public emission re-export
    └── ← solver/Emit/Basic

Layer 4 — Assembly, Global Common
├── LeanFzn/FznAssembled.lean      Top-level recognition theorems (parseModelSpec)
│   └── ← FznParser, FznGrammar, FznSuffix, FznCompleteness
└── LeanFzn/FznGlobals/Common.lean ★  Shared global-constraint helpers (setMemB, arraySlice, iff lemmas)
    └── ← FznSolution

Layer 5 — Global Constraint Families
├── LeanFzn/FznGlobals/AllDiffCounting.lean   8 names (all_different, all_disjoint, …)
│   └── ← FznGlobals/Common
├── LeanFzn/FznGlobals/LexSort.lean           12 names (lex_less, sort, arg_sort, …)
│   └── ← FznGlobals/Common
├── LeanFzn/FznGlobals/PackSched.lean         17 names (bin_packing, diffn, cumulative, table, …)
│   └── ← FznGlobals/Common
├── LeanFzn/FznGlobals/Channeling.lean        11 names (inverse, member, arg_val, …)
│   └── ← FznGlobals/Common
├── LeanFzn/FznGlobals/Graph.lean             18 names (circuit, reachable, path, steiner, …)
│   └── ← FznGlobals/Common
├── LeanFzn/FznGlobals/Regular.lean            6 names (regular, mdd, cost_regular, …)
│   └── ← FznGlobals/Common
├── LeanFzn/FznGlobals/Sched2.lean            10 names (cumulatives, geost, diffn_k, …)
│   └── ← FznGlobals/Common
└── LeanFzn/FznGlobals/Counting.lean          32 names (nvalue, among, count_*, gcc, …)
    └── ← FznGlobals/AllDiffCounting

Layer 6 — Global Aggregation
└── LeanFzn/FznGlobals.lean ★       Aggregates all 10 families (globalsInterp, globalsInterpB_iff)
    └── ← all 10 FznGlobals/* family modules, FznStdLib, FznSolution

Layer 7 — Top-Level Modules
└── LeanFzn/FznCheck.lean ★        Verified front door (checkModelSolution_correct)
    └── ← FznGlobals

Layer 8 — Library Roots
├── LeanFzn.lean ★                 Library root: imports all 14 LeanFzn modules
└── solver.lean                    Solver root: imports Search, Domain, Core, Direct, LCG

Layer 9 — Executable
└── Main.lean                      CLI entry point (check/solve)
    └── ← LeanFzn, solver/Direct/Cli
```

**Notes:**

- `LeanFzn*` in solver dependencies means "imports `LeanFzn` (the root import file)
  or specific LeanFzn submodules like `LeanFzn.FznCheck`". The solver modules
  depend on the parser/semantics stack for types, values, and the solution checker.
- `FznGlobals/Common.lean` is the main shared dependency for all 10 global-constraint
  families; `AllDiffCounting` is additionally shared by `Counting` and `SetMath`.
- `solver/Domain.lean` and `solver/Search.lean` are the solver's foundational modules.
- The dependency chain from `FznAST` to `FznGlobals.lean` is 7 layers deep.
- The certified LCG layer (`solver/LCG`) builds on `solver.Core` and
  `solver/Propagators`; the `solver/LCG/Certified.lean` front door and the
  `solver/Direct/Cli.lean` composition are the public solve path.

## Test Executables

```
Tests/Smoke.lean         → FznParser
Tests/Solution.lean      → FznSolution, FznParser, FznStdLib
Tests/Pretty.lean        → FznPretty, FznParser
Tests/StdLib.lean         → FznStdLib, FznParser
Tests/WellFormed.lean     → LeanFzn (full library)
Tests/Check.lean          → LeanFzn
Tests/Fast.lean           → LeanFzn
Tests/Bench.lean          → LeanFzn
Tests/Prof.lean           → LeanFzn
Tests/Gecode.lean         → LeanFzn, FznGlobals
Tests/Globals.lean        → FznGlobals, FznParser
Tests/Coverage.lean       → FznGlobals, FznParser, FznStdLib
solver/Tests.lean         → solver/Direct/Correctness, Direct/Cli, LCG/Certified
solver/TestsProp.lean     → solver/Propagators, solver/Extract
solver/TestsLCG.lean     → solver/LCG
```

## Dependency fan-out (qualitative)

| Module | Main downstream users |
|--------|-----------------------|
| `FznAST` | grammar, parser, pretty-printer, semantics, and all downstream library modules |
| `FznParser` | correctness, assembled recognition, solution parsing, and parser-facing tests |
| `FznSemantics` | correctness, standard predicates, solution checking, and globals |
| `FznSolution` | global common utilities, global aggregation, and the verified front door |
| `FznGlobals/Common` | the base global-constraint family modules |
| `solver/Search` | heuristics, propagators, fixpoint search, learning, and solver composition |
| `solver/Domain` | executable emission, extraction, and FlatZinc-facing solving |
| `solver/Propagators` | fixpoint search, extraction, learning, and configuration |

Exact counts are intentionally omitted because transitive and direct fan-out
were previously mixed.  A generated direct-import inventory is proposed in
`PLAN.md` P4.

## Archived Development Artifacts

All former root-level scratch files and the `archive/` directory were
removed in the 2026-09-27 cleanup (PLAN item P4); their history is in
Git (the `archive/` tree of any earlier commit) rather than in the
live module space.

## The certified solve path (2026-09-27, first certified fragment)

```
source model (FlatZinc text)
  | Parser.parseModel
  v
Model --(WellFormed gate: Check.wellFormedFastB)
  | Direct.compileModel                        [solver/Direct/Compile.lean]
  v
CompiledProblem DomConstraint                 [solver/Direct/Types.lean]
  | Direct.toLCG (empty clause database)       [solver/Direct/Cli.lean]
  v
LCG.Problem DomConstraint Unit                 [solver/LCG/Types.lean]
  | LCG.fragmentOk gate (singleton domains)    [solver/LCG/Certified.lean]
  | LCG.solve (engine, empty propagators)
  v
sat store / unsat / unknown / unsupported
```

### The public certified theorems (axioms: propext, Classical.choice,
### Quot.sound — the three standard Lean axioms only)

| Theorem | File | Statement |
| --- | --- | --- |
| `Direct.compile_exact` | Direct/Proofs/Exact.lean | accepted assignment -> the store satisfies every source constraint + declaration |
| `Direct.compile_covers` | Direct/Proofs/Exact.lean | satisfying parameter-honest store -> accepted assignment |
| `Direct.solve_sat_correct` | Direct/Correctness.lean | `solve = .sat store -> Satisfies fullSig fullInterp` |
| `Direct.solve_unsat_correct` | Direct/Correctness.lean | `solve = .unsat -> not-exists store, Satisfies and ParamHonest` |
| `LCG.solve_certified_sat` | LCG/Certified.lean | LCG sat assignment satisfies every internal constraint (declarative) |
| `LCG.solve_certified_unsat` | LCG/Certified.lean | LCG unsat excludes every internal solution |
| `Direct.solveCertified_sat_correct` | Direct/Cli.lean | the composed source-level SAT theorem |
| `Direct.solveCertified_unsat_correct` | Direct/Cli.lean | the composed source-level UNSAT theorem |

### The trusted base

- the Lean kernel + the three standard axioms;
- the accepted fragment's checks are executable and theorem-backed:
  `wellFormedFastB_iff` (WF gate), `fragmentOk_iff` (fragment gate),
  `DomConstraint.satisfiedB_iff` (evaluator agreement);
- `ParamHonest` (the UNSAT conclusion's parameter-honesty condition)
  is the FlatZinc instance-level parameter fixing — the same
  convention as the reference checker's `candidateStore`
  (`FznSolution.lean`), which builds stores from the model's
  `paramMap`.

### New modules this session

- `solver/Direct/Proofs/Exact.lean` — the whole-model correspondence
  (compile_exact/compile_covers, both SAT linkers, all fallback
  family inversions, the store-extensionality transports);
- `solver/LCG/Certified.lean` — the first certified LCG fragment;
- `solver/Direct/Cli.lean` — `solveCertified` + the composed
  source-level theorems + the solution emitter;
- `.github/workflows/ci.yml` — the aggregate CI gate (build, tests,
  proof-hole audit, axiom-profile audit, user-axiom audit).

## Standalone runtime diagnostic

`audits/pigeonhole_trace.lean` imports `solver.Direct.Cli` and
`solver.Direct.Search` to replay the retained historical LCG pigeonhole failure against
the compiled public propagators and the exhaustive reference oracle. It is
a diagnostic leaf, outside production imports and Lake targets. Its copied
search transition is snapshot-specific; see the embedded engine hash and
`audits/pigeonhole_runtime.txt`.

The public call chain is `Direct.solveCertified -> LCG.solve -> lcgSearch ->
chronologicalSearch -> frontierSolve` — the FUEL-FREE traversal whose
termination is kernel-checked by the `frontierCost` measure (no search
budget; accepted finite models always receive SAT or UNSAT). The
historical `lcgSearch.go` (now the top-level `lcgSearchGo`, aliased as
`lcgSearch.go`) and the bounded `frontierSearch`/`chronologicalSearchBounded`/
`lcgSearchBounded`/`solveBounded` remain as explicitly named diagnostic
references for their retained proofs; public search never calls them.
Propagators and analysis are not currently used to prune frontier frames.
The source theorem signatures remain unchanged; their active proof chain
uses frontier coverage, and `solveCertified_total` establishes the
source-level total-verdict guarantee.
