/-
File: probeS2.lean

Purpose:
  Scratch file testing `subst` with simple equality hypotheses and
  function application goals.

Dependencies:
  LeanFzn, solver.Search.

Why:
  Development-time exploration for PLAN.md item 6.2. Not part of any
  build target.

DAG:
  LeanFzn + solver.Search -> probeS2.lean (standalone, no dependents)
-/

import LeanFzn
import solver.Search
open LeanFzn LeanFzn.Solution LeanFzn.Solver

example (v y : Value) (hy : v = y) (P : Value → Prop) (hpy : P y) : P v := by
  subst hy
  exact hpy
