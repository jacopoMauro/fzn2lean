/-
File: solver.lean

Purpose:
  Library root for the certified solver: exports the shared semantic
  problem representation, the finite slot machinery, and the two
  solver stacks (direct exhaustive reference and LCG).

Dependencies:
  solver.Core (shared semantic problem representation),
  solver.Search + solver.Domain (finite exhaustive search and slot
  extraction), solver.Propagators (DomConstraint and its Boolean
  twin), solver.Extract (constraint-shape extraction), solver.Emit
  (solution-text rendering), solver.Direct (the direct compiler,
  exhaustive reference solver, and its correctness proofs),
  solver.LCG (the lazy-clause-generation engine, its proofs, and the
  certified front door).

Why:
  One import gives library users the full certified stack.  The
  legacy checker-mediated solver (Config/Solve/Fixpoint/Heuristic/
  Enum/Optimize/RevState/Learning/Restarts) was retired (PLAN.md §1);
  Git history keeps it.

DAG:
  LeanFzn semantics -> solver.Core
  solver.Search / solver.Domain / solver.Propagators / solver.Extract /
    solver.Emit (shared support)
  solver.Core + support -> solver.Direct (compiler, reference search,
    correctness proofs)
  solver.Core + support -> solver.LCG (engine, proofs, certified door)
  all of the above -> solver.lean
-/

import solver.Search
import solver.Domain
import solver.Core
import solver.Direct
import solver.LCG
