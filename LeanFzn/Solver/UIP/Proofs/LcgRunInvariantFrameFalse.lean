/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantFrameFalse.lean
U1c finding (now RESOLVED by R3): before the orig-aware `impliesP`, `FrameExplainedFull` was
refuted on the one-Boolean box: the pin `posBool 0 false` could not imply the int-form bound
`¬(s ≤ 0)`, because `impliesP` had a kind guard. R3 makes `impliesP orig` let a Boolean literal
imply an int-form literal on a slot that is Boolean-only in `orig` (`slotBoolB`).
This file is the regression: the pin now implies the bound, along a real supported run.
-/
import LeanFzn.Solver.UIP.Proofs.LcgFamiliesRun
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies

namespace LeanFzn.Solver.UIP.LcgRunInv

/-- The branch state right after deciding `posBool 0 false` on the box `[[false, true]]`
(the real first decision, see `first_step_bool_decision`). -/
def boolDecidedState (leaf : Assignment → Bool) : BranchState leaf :=
  { frame := ([], [Value.bool false])
    trail := [⟨posBool 0 false, 1, none⟩]
    level := 1
    learned := [] }

/-- **Regression (R3):** on the Boolean box `[[false, true]]`, the pin `posBool 0 false`
implies the int-form bound `¬(0 ≥ 1)`-side literal `(negLe 0 0).negate.norm`. -/
theorem boolPin_implies_bound :
    impliesP [[Value.bool false, Value.bool true]] (posBool 0 false)
      (negLe 0 0).negate.norm = true := by
  unfold impliesP impliesBase slotBoolB
  decide

/-- The REAL first scheduler step from the root of the one-Boolean problem is a decision
whose successor branch is exactly the state with the pin `posBool 0 false`. -/
def boolLeaf : Assignment → Bool := fun _ => false

theorem first_step_bool_decision :
    ((schedulerNext (SchedulerConfig.init (leaf := boolLeaf)
        [[Value.bool false, Value.bool true]] [] [])).successor.map
        (fun c => (c.branch.frame, c.branch.trail))) =
      some (([], [Value.bool false]),
        [⟨posBool 0 false, 1, none⟩]) := by
  rfl

/-- **Regression (R3): the Boolean pin implies the int-form bound along a real supported run.**
The first step of the one-Boolean problem reaches a supported configuration whose trail
contains the pin, and that pin implies `(negLe 0 0).negate.norm` through `impliesP` (the
old refutation `¬FrameExplainedFull` is withdrawn). -/
theorem boolPin_witness_on_run :
    ∃ cfg : SchedulerConfig boolLeaf,
      SupportedReach [[Value.bool false, Value.bool true]] [] [] cfg ∧
      ∃ e, e ∈ cfg.branch.trail ∧
        impliesP [[Value.bool false, Value.bool true]] e.literal (negLe 0 0).negate.norm = true := by
  have h := first_step_bool_decision
  cases hs : (schedulerNext (SchedulerConfig.init (leaf := boolLeaf)
      [[Value.bool false, Value.bool true]] [] [])).successor with
  | none => rw [hs] at h; cases h
  | some c =>
      rw [hs] at h
      simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
      have ht : c.branch.trail = [⟨posBool 0 false, 1, none⟩] := h.2
      refine ⟨c, SupportedReach.step (SupportedReach.init (fun _ h => absurd h (by simp))) hs,
        ⟨⟨posBool 0 false, 1, none⟩, by rw [ht]; simp, boolPin_implies_bound⟩⟩

end LeanFzn.Solver.UIP.LcgRunInv
