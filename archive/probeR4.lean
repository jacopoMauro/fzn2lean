/-
File: probeR4.lean

Purpose:
  Scratch file debugging `subst` vs `rw` disambiguation in the
  `solver/Search.lean` correctness proofs.

Dependencies:
  LeanFzn, solver.Search.

Why:
  Development-time exploration for PLAN.md item 6.2 search proofs.
  Not part of any build target.

DAG:
  LeanFzn + solver.Search -> probeR4.lean (standalone, no dependents)
-/

import LeanFzn
import solver.Search
open LeanFzn LeanFzn.Solution LeanFzn.Solver
-- subst hbb where hbb : b' = b — b' is obtain'd (inner), b is from `cases hb : ...` (also inner-ish,
-- bound by the `some b` alternative). Which gets eliminated? Error says `b` unknown → subst
-- eliminated b, replacing b by b'. So after subst, references to `b` break. Fix: use rw [hbb] to
-- rewrite b' → b in goal... but goal contains b (from hc/if). Instead obtain with flipped names:
-- have hbb : b = b' := Option.some.inj hb'; subst hbb eliminates b'... or rewrite hc etc.
-- Simplest robust: rw [hbb] at h (the if-condition mentions b).
example (b b' : Int) (hbb : b' = b) (P : Int → Prop) (hc : P b') : P b := by
  rw [← hbb]; exact hc
