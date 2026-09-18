/-
File: probeS4.lean

Purpose:
  Scratch file testing `obtain`-then-`subst` vs `rw` strategies in
  the solver correctness proofs.

Dependencies:
  LeanFzn, solver.Search.

Why:
  Development-time exploration for PLAN.md item 6.2. Not part of any
  build target.

DAG:
  LeanFzn + solver.Search -> probeS4.lean (standalone, no dependents)
-/

import LeanFzn
import solver.Search
open LeanFzn LeanFzn.Solution LeanFzn.Solver

-- both directions work standalone. In the real proof, `y` appears in hy : a[j]? = some y (from obtain)
-- so subst hvy (v = y) would eliminate v (appears only in hv). Actually error says `y` unknown — so it
-- eliminated y. Why? Because `v` also appears in `hv` which mentions... hmm.
-- Robust fix: instead of subst, rewrite the specific memberships:
example (x y z : Value) (hx : x = y) (hP : z ∈ [x]) : z ∈ [y] := by
  rw [← hx]; exact hP
