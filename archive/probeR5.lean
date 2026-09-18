/-
File: probeR5.lean

Purpose:
  Scratch file testing `rcases` interaction with hypotheses in
  `solver/Search.lean` correctness proofs.

Dependencies:
  LeanFzn, solver.Search.

Why:
  Development-time exploration for PLAN.md item 6.2 search proofs.
  Not part of any build target.

DAG:
  LeanFzn + solver.Search -> probeR5.lean (standalone, no dependents)
-/

import LeanFzn
import solver.Search
open LeanFzn LeanFzn.Solution LeanFzn.Solver
-- rcases hc with hcl | hcr then `hc` disappears? error says hc unknown at line with `rw [if_pos hc]`.
-- That's because rcases consumes hc. Restructure: don't rcases; use .1/.2
example (b m : Int) (hc : b = 0 ∨ m = 0) : b = 0 ∨ m = 0 := by
  rcases hc with hcl | hcr
  · exact Or.inl hcl
  · exact Or.inr hcr
