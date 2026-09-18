/-
File: probeS3.lean

Purpose:
  Scratch file testing `subst` in the reverse direction (substituting
  a hypothesis used by the goal) in the solver correctness proofs.

Dependencies:
  LeanFzn, solver.Search.

Why:
  Development-time exploration for PLAN.md item 6.2. Not part of any
  build target.

DAG:
  LeanFzn + solver.Search -> probeS3.lean (standalone, no dependents)
-/

import LeanFzn
import solver.Search
open LeanFzn LeanFzn.Solution LeanFzn.Solver

-- In that probe, subst hy with hy : v = y eliminated... which? Test the reverse usage:
example (v y : Value) (hy : v = y) (P : Value → Prop) (hp : P v) : P y := by
  subst hy
  exact hp
