# LeanFzn dependency structure

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
├── solver/Emit/Basic.lean         Stable executable solution emission
│   └── ← Lean, solver/Domain
├── solver/Emit/Roundtrip.lean     Buildable emitted-solution proof branch;
│                                  entry parsing/master round trip still open
│   └── ← solver/Emit/Basic
├── solver/Emit.lean               Stable public emission re-export
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
└── solver.lean                    Core solver root: imports Search, Domain, Emit/Basic, Solve

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
  former is core-only and the latter exposes the complete stack.  Consolidating
  or renaming them is tracked in `PLAN.md` P4.
- Several solver modules directly import the broad `LeanFzn` umbrella.  The
  graph above records that as `LeanFzn*`; narrowing those imports is also
  tracked in P4.

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
