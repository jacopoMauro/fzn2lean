import solver.LCG.Engine
import solver.LCG.Encoding
import solver.LCG.Invariants

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

-- Probe: negOnTrail falsifies, entry-level.
theorem negOnTrail_falsifies_entry {st : State} {l : Literal} {a : Assignment}
    (hneg : st.negOnTrail l = true)
    (hsat : st.TrailSatisfied a) :
    l.eval a = some false := by
  unfold State.negOnTrail at hneg
  rw [List.any_eq_true] at hneg
  obtain ⟨e, hem, heb⟩ := hneg
  have hlit : e.literal = l.negate.norm := by
    simpa only [litEqB, decide_eq_true_eq] using heb
  have hev : e.literal.eval a = some true := hsat e hem
  rw [hlit, Literal.norm_eval (l.negate) a, Literal.eval_negate l a] at hev
  cases h : l.eval a with
  | none => rw [h] at hev; simp at hev
  | some b =>
      rw [h] at hev
      cases b <;> simp at hev <;> rfl

-- KEY INSIGHT probe: the opposing-fact branch of enqueueNorm is
-- unreachable under represented-solution soundness: whenever it fires
-- (negOnTrail l = true), the trail-satisfying represented solution a
-- makes l FALSE at a; but PropSafe says the propagator's implied l is
-- TRUE at a — contradiction. So the branch never fires for enqueues of
-- implied literals of sound propagators.
example (st : State) (l : Literal) (a : Assignment)
    (hsat : st.TrailSatisfied a)
    (hneg : st.negOnTrail l = true) :
    l.eval a = some false :=
  negOnTrail_falsifies_entry hneg hsat

end LeanFzn.Solver.LCG
