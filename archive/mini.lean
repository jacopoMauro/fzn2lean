/-
File: mini.lean

Purpose:
  Scratch file prototyping the sparse-domain narrowing pass that
  later became `solver/RevState.lean`. Contains an unfinished
  preservation proof sketch.

Dependencies:
  LeanFzn (Value type).

Why:
  Development-time scratch for the reversible-state work (PLAN.md 6.4).
  Not part of any build target.

DAG:
  LeanFzn -> mini.lean (standalone, no dependents)
-/

import LeanFzn
open LeanFzn LeanFzn.Solution

structure SparseDomX where
  vals : Array Value
  size : Nat
  deriving Repr

private def narrowPass (keep : Value → Bool) (A : Array Value) (p w n : Nat) : SparseDomX :=
  if p < n then
    if keep (A.getD p default) then
      if w < p then
        narrowPass keep
          ((A.setIfInBounds w (A.getD p default)).setIfInBounds p (A.getD w default))
          (p + 1) (w + 1) n
      else
        narrowPass keep A (p + 1) (w + 1) n
    else
      narrowPass keep A (p + 1) w n
  else ⟨A, w⟩
termination_by n - p
decreasing_by all_goals omega

-- Aha — maybe the issue: `n ≤ A.size` uses `Array.size` as a FUNCTION — in the goal it's
-- `n ≤ A.size` where the motive abstracted A. The `→` shown might be `∀ (_ : n ≤ A.size), ...`
-- which IS intro-able. Unless — the goal is an `Iff` in `Prop` and `intro` works only on
-- implications... the goal IS `n ≤ A.size → (iff)`. intro should work!
-- DESPERATE: use `apply ih` after intro? Try full different approach — maybe `case1`'s goal
-- after pattern is CLOSED by providing 7th name that consumed the implication? The pattern
-- `| case1 A p w hpn hkeep hwp ih` — 6 names. But earlier "8 provided 7 expected" with 8 names.
-- So expected 7: (A p w hpn hkeep hwp ih) is 6... +1 = 7. What's the 7th? Perhaps the
-- implication hypothesis is auto-named in the case binders! So `| case1 A p w hpn hkeep hwp hnle ih`
-- — no wait "7 expected" when I gave 8 (A p w v hpn hkeep hwp ih). So the case takes 7:
-- (A p w hpn hkeep hwp X) where X is... the ih? Then no room for both. OR the motive arg...
-- Test: give exactly 7 names including a name where the implication auto-appears:
example (keep : Value → Bool) (n k : Nat) (hkn : n ≤ k) (v : Value) :
    ∀ (A : Array Value) (p w : Nat),
      n ≤ A.size →
      v ∈ (narrowPass keep A p w n).vals.toList.take k ↔ v ∈ A.toList.take k := by
  intro A p w
  induction A, p, w using narrowPass.induct (keep := keep) (n := n) with
  | case1 A p w hpn hkeep hwp ih =>
      intro hnle
      sorry
  | _ => sorry
