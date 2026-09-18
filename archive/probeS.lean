/-
File: probeS.lean

Purpose:
  Scratch file testing `subst` behavior with `Option` values in the
  solver correctness proofs.

Dependencies:
  LeanFzn, solver.Search.

Why:
  Development-time exploration for PLAN.md item 6.2. Not part of any
  build target.

DAG:
  LeanFzn + solver.Search -> probeS.lean (standalone, no dependents)
-/

import LeanFzn
import solver.Search
open LeanFzn LeanFzn.Solution LeanFzn.Solver

-- after subst hvy where hvy : v = y — which is eliminated?
example (v y : Value) (hy : some v = some y) : v = y := by
  subst hy  -- hy : some v = some y? not directly subst-able
  sorry
