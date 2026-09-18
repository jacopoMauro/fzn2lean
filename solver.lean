/-
File: solver.lean

Purpose:
  Library root for the verified constraint solver: re-exports the core
  solver modules so clients depend on the solver as one library.

Dependencies:
  solver.Search (exhaustive search), solver.Domain (domain extraction),
  solver.Emit (solution emission), solver.Solve (FlatZinc-facing solver).

Why:
  `solveModel` and `SolveResult` in `solver/Solve.lean` are the solver's
  public face against the LeanFzn semantics; the root file groups the
  import set. The full solver (heuristics, learning, restarts, config)
  lives behind `solver/Solver.lean`.

DAG:
  solver.Search/Domain/Emit -> solver.Solve -> solver.lean -> Main
-/

import solver.Search
import solver.Domain
import solver.Emit
import solver.Solve
