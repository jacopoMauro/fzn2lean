# LeanFzn Dependency DAG

This file records the module dependency graph for the fzn2lean project.
Dependencies flow downward; roots are at the top, leaves at the bottom.

## Legend

- `★` marks shared/high-fan-out modules.
- Untracked development artifacts (`probe*.lean`, `BenchAB.lean`, `TestEnumTmp.lean`,
  `axcheck_tmp.lean`, `mini.lean`, `testBX.lean`) are excluded from the graph
  unless they are explicitly registered as Lake targets.
- Test executables are listed separately at the end.

---

## LeanFzn Library

```
Layer 0 — Foundation (no project imports)
├── LeanFzn/FznAST.lean ★         AST types (Ident, Value, BaseType, VDecl, ConstraintItem, Model)
├── LeanFzn/FznLexer.lean ★       Tokenizer (Token type, tokenize)
├── solver/Search.lean ★           Generic exhaustive search (allAssigns, search_some/none)
└── solver/Emit.lean               Solution text emission (emitSolution) +
                                   round-trip Layer A theorems (splitOn_intercalate_newline,
                                   splitOn_eq_list, splitOnAux_eq_splitAux, splitAux_spec,
                                   extract_ofList_seg, boundary/shift lemmas, repr_val)

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
                                   dotSum_bounds, term_bound, propIdSlot placeholder)
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
                                   domPropagators incl. linEq/linLe wiring via propIdSlot)
    └── ← solver/Search, solver/Emit, solver/Domain, solver/Heuristic,
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
└── solver.lean                    Library root: imports Search, Domain, Emit, Solve

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

## Dependency fan-out (most-imported modules)

| Module | Imported by |
|--------|-------------|
| `FznAST` | 6 (Grammar, Lexer-used-by-Parser, Parser, Pretty, Semantics, indirectly all) |
| `FznParser` | 8 (Correctness, Assembled, Solution, many tests) |
| `FznSemantics` | 3 (StdLib, Correctness, indirectly Solution) |
| `FznSolution` | 3 (Globals/Common, FznGlobals, indirectly FznCheck) |
| `FznGlobals/Common` | 8 (7 family modules + SetMath) |
| `solver/Search` | 6 (Propagators, Heuristic, Fixpoint, Extract, Learning, config chain) |
| `solver/Domain` | 4 (Emit→Solve, Extract, Solve, Domain itself) |
| `solver/Propagators` | 3 (Fixpoint, Extract, Learning) |

## Untracked Development Artifacts (not part of any build target)

```
probeL.lean, probeL2–6.lean, probeR4–5.lean, probeS.lean, probeS2–4.lean
BenchAB.lean, TestEnumTmp.lean, axcheck_tmp.lean, mini.lean, testBX.lean
solver.lean (root re-export)
```
