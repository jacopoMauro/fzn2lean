# Dependency-closure inventory (PLAN.md P1a)

Audit: 2026-10-05 (HEAD `2eb8ac0` on branch `lazySolver` + the uncommitted
working tree; `lakefile.toml` already carries the retired-target deletions).

Roots considered: `Main.lean`, the library roots `LeanFzn.lean` and
`solver.lean`, all 16 `lean_exe` roots in `lakefile.toml` (`leanfzn` + 15
test executables), and `audits/certified_axioms.lean`. Method: transitive
closure over `^import` lines, then per-declaration usage checks with
word-boundary grep over the reachable set plus `lakefile.toml`, `audits/`,
`README.md`, `PLAN.md`, `code-structure.md`, distinguishing code references
from prose. `tmp/` (180 scratch files) was excluded from the closure; four
live proof modules cite tmp files in *prose comments* only (Run.lean,
Reason.lean, Fam/Lin.lean, Fallback.lean) — P1d must re-home or drop those
citations.

Totals: 116 in-scope `.lean` files → **93 reachable, 23 unreachable**.

## A. The reachable closure (93 modules)

### A1. Certified path from `Main.lean` (70 modules)

`Main.lean` imports only `LeanFzn` and `solver.Direct.Cli` — the legacy
`solver.Solver` dispatch (`SolveConfig`/`solveModelWith`/`enumModel`/
`optimizeModelBb`) is fully gone; `runSolve` calls only
`solveCertified`/`emitCertifiedSolution` behind the `wellFormedFastB` gate.

- **LeanFzn library (26):** the `LeanFzn` root + `FznAST, FznLexer,
  FznSemantics, FznGrammar, FznSuffix, FznParser, FznCorrectness,
  FznCompleteness, FznAssembled, FznPretty, FznStdLib, FznSolution,
  FznGlobals` and `FznGlobals/{Common, AllDiffCounting, Counting, LexSort,
  LexChain, PackSched, Channeling, SetMath, Graph, Regular, Sched2}`.
- **Shared solver support (9):** `solver.Core` (+ `Core.Types`,
  `Core.Semantics`), `solver.Search`, `solver.Domain`, `solver.Extract`,
  `solver.Propagators`, `solver.Emit` (+ `Emit.Basic`).
- **Direct compiler layer (5):** `Direct.Cli`, `Direct.Types`,
  `Direct.Compile`, `Direct.Proofs.Compile`, `Direct.Proofs.Exact`.
- **LCG layer (29):** `LCG.Certified` + `LCG.{Types, TrailEval, Operations,
  Encoding, Invariants, Propagate, Engine, Search}` + proof modules
  `LCG.Proofs.{Transitions, Analyze, EngDup, Engine, Lift, Reachability,
  Singleton, Theory, ConstFamilies, Propagators, Reason, Run, Search,
  Fallback, FallbackFit}` and `LCG.Proofs.Fam/{Bool, Arith, Lin, Times,
  AllDiff}`.

Key import chains: `Main → Direct.Cli → LCG.Certified → {LCG.Proofs.Search,
Proofs.Propagators, Proofs.Reason, Proofs.FallbackFit, Direct.Proofs.Exact,
Propagators}`; the `Fam/*` modules feed `LCG.Proofs.Propagators`.

### A2. Reached only by test roots (19 modules beyond Main)

- The 12 `Tests/*.lean` roots (`Smoke, StdLib, Solution, Gecode, Globals,
  Bench, Coverage, WellFormed, Pretty, Prof, Check, Fast`).
- The 3 retained solver test files: `solver.Tests` (`tests_solver`),
  `solver.TestsProp` (`tests_prop`), `solver.TestsLCG` (`tests_lcg`).
- **The direct exhaustive reference solver**, reached only via
  `solver.Tests → Direct.Correctness → Direct.Proofs.Search →
  Direct.Search` (which itself imports `solver.Search` + `Direct.Compile`).
- `solver.LCG` (the LCG umbrella), imported only by `solver/TestsLCG.lean`.

### A3. Reached only by the audit root (beyond Main + tests)

- `audits/certified_axioms.lean` itself, and
- **`solver.LCG.Proofs.FallbackRaw`** — imported only by the audit file.
  Watch item: if the audit drops `propagatorsOfProved_conflictraw`, the
  module becomes fully dead.

### A4. Reached only by the `solver` library root

- `solver.lean` (no file does `import solver`) and the `solver.Direct`
  umbrella it pulls in.

## B. Unreachable files — 23, all dead from every functional root

Zero module-name references from the reachable set, `lakefile.toml`,
`audits/`, `README.md`, `PLAN.md` or `code-structure.md` (prose mentions of
"retired" modules only). All still git-tracked; no pending working-tree
changes.

| Group | Files | Status |
| --- | --- | --- |
| Legacy solver stack | `solver/Solver.lean`, `Config`, `Solve`, `Enum`, `Optimize`, `RevState`, `Learning`, `Restarts`, `Fixpoint`, `Heuristic` (10) | dead; Lake targets for their tests already removed from `lakefile.toml` |
| Tree family | `solver/Tree.lean` + `Tree/{Types, Operations, Invariants, Proofs}.lean` (5) | dead — working-tree `solver.lean` no longer imports `solver.Tree` |
| Legacy test orphans | `solver/Tests{Bench, Enum, Fix, Heur, Learn, Opt, Restart, Rev}.lean` (8) | dead — targets removed in the working tree |

The legacy CLI declarations (`SolveConfig`, `solveModelWith`, `enumModel`,
`optimizeModelBb`) now appear only inside these unreachable files.

## C. Shared-declaration ledger

"Certified" = reachable from `Main.lean`; "legacy/test-only" = reachable
only from test/audit roots or unreachable.

| Declaration | Defined in | Certified users | Legacy/test-only users |
| --- | --- | --- | --- |
| `allAssigns`, `mem_allAssigns_singleton` | `solver/Search.lean` | Propagators, Direct.Cli, Direct.Proofs.Compile/Exact, LCG.Proofs.Fam.AllDiff | dead Config/Enum/Fixpoint/…; tests solver.Tests*, TestsLCG |
| `slotsMeasure` | `solver/Search.lean:50` | — | dead Enum/Learning/Restarts → deletable with P1b |
| `search`, `search_some`, `search_none`, `searchGo_search` | `solver/Search.lean` | — | only `Direct.Search` / `Direct.Proofs.Search` (test-root) + dead files → couples to the Direct-reference decision |
| `slotsChecked`, `varDomain`, `leavesProduct`, `leavesCap`, `declSlots` | `solver/Domain.lean` | Direct.Compile/Proofs, LCG.Certified, LCG.Proofs.Reason, Extract, Emit.Basic | dead Solve/Enum/Optimize/… only |
| `extractConstraint` (+inv), `nameIndex` | `solver/Extract.lean` | Direct.Compile, all Direct proofs, LCG.Certified, LCG.Propagate | solver.TestsProp (test root) |
| `DomConstraint`, `satisfiedB(_iff)`, `SatisfiedBy` | `solver/Propagators.lean` | all Direct.*, all LCG.*, Extract, solver.lean root | dead Config/Fixpoint/RevState/Solve/Tree; tests TestsFix/TestsLCG/TestsProp |
| `emitSolution` (+fast twin) | `solver/Emit/Basic.lean` | Direct.Cli (`emitCertifiedSolution`) | dead Solve/Solver only |
| `checkModelSolutionFast_eq`, `checkPreparedSolution_eq` | `LeanFzn/FznCheck.lean` | — | dead Solve/Config/Restarts/Enum/Optimize only → deletable with P1b (or re-pin first) |

## D. Verdicts driving P1b

1. **Main is clean** — no legacy dispatch remains.
2. **Legacy stack + Tree + 8 legacy test orphans (23 files): deletable
   wholesale.** No reachable file imports them.
3. **`solver/Search.lean` split:** only the `allAssigns` trio is
   certified-used. `search`/`search_some`/`search_none`/`slotsMeasure`/
   `searchGo_search` have no Main-reachable users; `search*` survive only
   through `Direct.Search`/`Direct.Proofs.Search` (the reference solver),
   `slotsMeasure` through nothing live.
4. **Direct reference chain decision (PLAN P1b):** `Direct.Search →
   Direct.Proofs.Search → Direct.Correctness` is pinned **solely** by
   `solver/Tests.lean` nonvacuity checks (Tests.lean:196, 228 use
   `solve_sat_correct`/`solve_unsat_correct` of `Direct.Correctness`, plus
   `solve`/`solveCompiled` at Tests.lean:108–192). The audit file does NOT
   pin Direct.Correctness: its unqualified `#print axioms
   solve_sat_correct` resolves to the *LCG* theorem in
   `LCG/Proofs/Search.lean` (the audit imports no Direct.Correctness).
   Options: (a) keep a slim reference; (b) replace the test uses with LCG
   equivalents and delete the chain. PLAN.md asks to keep a small useful
   reference or replace those uses first — the LCG engine already has
   source-level SAT/UNSAT theorems, so replacement is viable.
5. **`solver.lean` root / `solver.Direct` umbrella:** the lib root still
   has value as a one-import face for library users; `solver.Direct`
   umbrella is pulled only by it and by the `solver.Tests` root.
6. **`FznCheck.lean` legacy rewrites** (`checkModelSolutionFast_eq`,
   `checkPreparedSolution_eq`): no live users left.

## E. Changes since the 2026-09-29 inventory

1. Main's legacy dispatch is gone → the legacy stack dropped out of the
   closure entirely (was "in-closure via `import solver.Solver`").
2. `solver.lean` no longer imports `solver.Tree` → Tree family now fully
   dead.
3. Test targets pruned from 23 to 15 test executables (8 legacy
   `solver.Tests*` targets deleted in the working tree).
4. New LCG proof modules: `Analyze, EngDup, Fallback, FallbackFit,
   FallbackRaw, Lift, Reachability, Engine` + `Fam/{Bool, Arith, Lin,
   Times, AllDiff}` — the proof layer is now 22 modules.
5. New LeanFzn module `FznGlobals/LexChain.lean`.
6. `solver.Emit` umbrella is now certified-path (only user `Direct.Cli`).
7. `checkModelSolutionFast_eq`/`checkPreparedSolution_eq` lost their last
   live users.
8. `solver.Tests` slimmed as previously recommended (imports
   `Direct.Correctness + Direct.Cli + LCG.Certified`).
9. The audit file grew to 50 `#print axioms` lines and directly imports
   `LCG.Proofs.Run` + `LCG.Proofs.FallbackRaw`.

## F. Lake targets and retained suites

`lakefile.toml` (working tree): 2 `lean_lib` (`LeanFzn`, `solver`) + 16
`lean_exe` = `leanfzn` + **15 test executables** — `tests_smoke`,
`tests_stdlib`, `tests_solution`, `tests_gecode`, `tests_globals`,
`tests_bench`, `tests_coverage`, `tests_wellformed`, `tests_pretty`,
`tests_prof`, `tests_check`, `tests_fast`, `tests_solver`, `tests_prop`,
`tests_lcg`. This matches PLAN.md's "15 retained test suites" and
README.md's run loop. Test `.lean` files on disk: 23 (12 wired under
`Tests/`, 3 wired `solver/Tests{,Prop,LCG}`, 8 unwired legacy orphans).

CI (`.github/workflows/ci.yml`) builds only `LeanFzn solver leanfzn
tests_solver tests_lcg`, runs only `tests_solver`/`tests_lcg`, and does
the three audits (proof-hole grep, axiom-profile print, user-axiom grep —
the profile step prints but does not fail on unexpected axioms). 13 of 15
suites are not exercised by CI; P2/P1e must decide coverage and make the
axiom audit fail on unexpected axioms.
