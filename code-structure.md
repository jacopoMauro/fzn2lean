# LeanFzn dependency structure

The solver portion below records the current migration state. `solver/Solve`
and its higher adapters still implement the retired checker-mediated entry
points; `PLAN.md` specifies their direct-proof replacement.

The new intended dependency root is `solver.Core`, which contains only shared
problem and assignment semantics. Operational state is layered: `solver.Tree`
for classical CP tree search and `solver.LCG` for the top-priority lazy clause
generation solver. Other approaches receive their own state layer and prove a
connection to the common problem semantics.

This file records the current module dependency graph for LeanFzn.
Arrows written as `A ← B` mean that `A` directly imports `B`.  The numbered
layers are explanatory groupings, not enforced package boundaries; the direct
imports are the source of truth.

## Legend

- `★` marks shared/high-fan-out modules.
- Untracked development artifacts are now **archived** under `archive/`
  (see below); none of them is part of any build target.
- Test executables are listed separately at the end.

---

## Library and solver layers

```
Layer 0 — Foundation (no project imports)
├── LeanFzn/FznAST.lean ★         AST types (Ident, Value, BaseType, VDecl, ConstraintItem, Model)
├── LeanFzn/FznLexer.lean ★       Tokenizer (Token type, tokenize)
└── solver/Search.lean ★          Generic exhaustive search (allAssigns, search_some/none)

Solver core — new shared foundation
├── solver/Core/Types.lean         Generic Problem; Slot/Domain/Assignment;
│                                  SearchResult
│   └── ← FznSemantics
├── solver/Core/Semantics.lean     Architecture-independent assignment semantics
│   └── ← Core/Types
└── solver/Core.lean               Shared-core umbrella
    └── ← Core/Types, Core/Semantics

Classical tree-search layer
├── solver/Tree/Types.lean         Decision/NoGood/TrailEntry/reference State
│   └── ← Core/Types
├── solver/Tree/Operations.lean    Reference state operations
├── solver/Tree/Invariants.lean    Tree representation/preservation contracts
├── solver/Tree/Proofs.lean        Tree foundational proof scaffolds
└── solver/Tree.lean               Tree-layer umbrella

Lazy clause generation layer (top-priority solver)
├── solver/LCG/Types.lean          Atoms, literals, clauses, reasons, LCG State
├── solver/LCG/TrailEval.lean      Trail queries, norm literals, 1-UIP analysis
├── solver/LCG/Operations.lean     Evaluation (intView), trail, learning, API
├── solver/LCG/Encoding.lean       L0.1 foundation: literal laws, order encoding,
│                                  WellFormed, assignment↔valuation carving
│   └── ← LCG/Operations, LCG/Invariants
├── solver/LCG/Invariants.lean     Entailment, representation, conflict meaning
├── solver/LCG/Propagate.lean      Explanation-carrying bound propagators
├── solver/LCG/Engine.lean         Clause scanning, propagation, search loop
├── solver/LCG/Search.lean          Executable entry points (solve/solveDom)
├── solver/LCG/Proofs/Transitions.lean  Local transition obligations
├── solver/LCG/Proofs/Search.lean  Internal SAT/UNSAT obligations
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
├── solver/Heuristic.lean          MRV heuristic (mrvOrder, mrvSearch)
│   └── ← solver/Search
└── solver/Propagators.lean ★      Propagation contract + propagators (Preserves, propEqSlot, …)
                                   + linear propagators (propLinEq/propLinLe, DomConstraint.linEq/linLe,
                                   dotSum_bounds, term_bound, proved preservation theorems)
    └── ← LeanFzn*, solver/Search

Layer 2 — Correctness, StdLib, Fixpoint
├── LeanFzn/FznSuffix.lean         Grammar suffix/consumption bounds
│   └── ← FznGrammar
├── LeanFzn/FznCorrectness.lean    Parser soundness (parseModel → GrModel)
│   └── ← FznParser, FznGrammar, FznSemantics
├── LeanFzn/FznStdLib.lean ★       Standard predicate signatures + interpretations (stdSig, stdInterp)
│   └── ← FznSemantics
└── solver/Fixpoint.lean           Propagation fixpoint + pruning search
    └── ← LeanFzn*, solver/Search, solver/Propagators

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
│   └── ← Direct/Types
├── solver/Direct/Search.lean      Executable exhaustive direct solver
│   └── ← solver/Search, Direct/Compile
├── solver/Direct/Proofs/Compile.lean  Exact compilation proof obligations
│   └── ← solver/Search, Direct/Compile
├── solver/Direct/Proofs/Search.lean   Search proof obligations
│   └── ← Direct/Search
├── solver/Direct/Correctness.lean Public direct SAT/UNSAT theorem obligations
│   └── ← Direct/Proofs/Compile, Direct/Proofs/Search
├── solver/Direct.lean             Direct-solver public umbrella
│   └── ← all solver/Direct modules
├── solver/Emit/Basic.lean         Stable executable solution emission
│   └── ← Lean, solver/Domain
├── solver/Emit.lean               Output-only public emission re-export
│   └── ← solver/Emit/Basic
├── solver/Enum.lean               All-solutions enumeration (enumerateAll)
│   └── ← solver/Solve
├── solver/Optimize.lean           Branch-and-bound optimization (optimizeModelBb)
│   └── ← solver/Enum
├── solver/RevState.lean           Reversible sparse-set state (SparseDom, trail)
│   └── ← LeanFzn*, solver/Fixpoint
└── solver/Learning.lean           NoGood learning (learnSearch, EntailedOn)
    └── ← LeanFzn*, solver/Search, solver/Propagators, solver/Enum

Layer 4 — Assembly, Global Common, Solver Core
├── LeanFzn/FznAssembled.lean      Top-level recognition theorems (parseModelSpec)
│   └── ← FznParser, FznGrammar, FznSuffix, FznCompleteness
├── LeanFzn/FznGlobals/Common.lean ★  Shared global-constraint helpers (setMemB, arraySlice, iff lemmas)
│   └── ← FznSolution
└── solver/Solve.lean ★            FlatZinc-facing solver (solveModel, SolveResult,
                                   domPropagators incl. proved linEq/linLe wiring)
    └── ← solver/Search, solver/Emit/Basic, solver/Domain, solver/Heuristic,
         solver/Propagators, solver/Fixpoint, solver/Extract, LeanFzn/FznCheck

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
└── solver/Restarts.lean           Restart loop + budget (restartSearch, BoundedResult)
    └── ← solver/Solve

Layer 6 — Global Constraint Family Extensions + Config
├── LeanFzn/FznGlobals/Counting.lean          32 names (nvalue, among, count_*, gcc, …)
│   └── ← FznGlobals/AllDiffCounting
├── LeanFzn/FznGlobals/LexChain.lean          10 names (lex_greater, lex2, orbitope, …)
│   └── ← FznGlobals/LexSort
├── LeanFzn/FznGlobals/SetMath.lean           14 names (disjoint, set_member, range, …)
│   └── ← FznGlobals/AllDiffCounting, FznGlobals/Common
└── solver/Config.lean ★            Composed front door (SolveConfig, solveModelWith,
                                   permConstraint incl. linEq/linLe permutation cases)
    └── ← solver/Solve, solver/Heuristic, solver/Fixpoint, solver/Extract,
         solver/Learning, solver/Restarts

Layer 7 — Global Aggregation
└── LeanFzn/FznGlobals.lean ★       Aggregates all 10 families (globalsInterp, globalsInterpB_iff)
    └── ← all 10 FznGlobals/* family modules, FznStdLib, FznSolution

Layer 8 — Top-Level Modules
├── LeanFzn/FznCheck.lean ★        Verified front door (checkModelSolution_correct)
│   └── ← FznGlobals
└── solver/Solver.lean ★           Complete solver library (all 6.1–6.7)
    └── ← LeanFzn*, FznCheck, all solver/* modules

Layer 9 — Library Roots
├── LeanFzn.lean ★                 Library root: imports all 14 LeanFzn modules
└── solver.lean                    New root: imports Core, Direct, Search, Domain

Layer 10 — Executable
└── Main.lean                      CLI entry point (check/solve/enum/optimize)
    └── ← LeanFzn, solver/Solver
```

**Notes:**

- `LeanFzn*` in solver dependencies means "imports `LeanFzn` (the root import file)
  or specific LeanFzn submodules like `LeanFzn.FznCheck`". The solver modules
  depend on the parser/semantics stack for types, values, and the solution checker.
- `FznGlobals/Common.lean` is the main shared dependency for all 10 global-constraint
  families; `AllDiffCounting` is additionally shared by `Counting` and `SetMath`.
- `solver/Domain.lean` and `solver/Search.lean` are the solver's foundational modules.
- The dependency chain from `FznAST` to `FznGlobals.lean` is 7 layers deep.
- `solver.lean` and `solver/Solver.lean` are currently different roots; the
  former is core-only and the latter exposes the legacy complete stack. Their
  replacement is sequenced in `PLAN.md` D0–D3.
- Several solver modules directly import the broad `LeanFzn` umbrella. The
  graph above records that as `LeanFzn*`; imports will be narrowed as the new
  semantic and compiled-problem foundations are introduced.

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
solver/Tests.lean         → solver/Solver
solver/TestsProp.lean     → solver/Solver
solver/TestsHeur.lean     → solver/Solver
solver/TestsFix.lean      → solver/Solver
solver/TestsEnum.lean     → solver/Solver
solver/TestsBench.lean    → solver/Solver
solver/TestsOpt.lean      → solver/Optimize
solver/TestsRev.lean      → solver/Solver
solver/TestsLearn.lean    → solver/Solver
solver/TestsRestart.lean  → solver/Restarts
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

## Archived Development Artifacts (not part of any build target)

All former root-level scratch files live under `archive/` since the
2026-09-18 cleanup (PLAN item 1); the `bench_ab`/`test_enum_tmp` Lake
targets were removed with them:

```
probeC.lean, probeF.lean, probeG.lean, probeH.lean,
probeL.lean, probeL2–6.lean, probeR4–5.lean, probeS.lean, probeS2–4.lean
BenchAB.lean, TestEnumTmp.lean, axcheck_tmp.lean, mini.lean, testBX.lean
FznGlobals.lean.orig, probeTmp.lean, probeTmp2.lean
```
