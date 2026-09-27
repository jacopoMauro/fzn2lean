import solver.LCG.Engine
import solver.LCG.Encoding
import solver.LCG.Invariants
import solver.LCG.Proofs.Lift
import solver.LCG.Proofs.Reachability

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

theorem enqueueNorm_fresh_solvedBy
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnew : st.litOnTrail l0.norm = false)
    (hneg : st.negOnTrail l0.norm = false)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true)
    (hsol : ∀ a, ProblemSolution problem constraintHolds a →
      st.Represents a) :
    ∀ a, ProblemSolution problem constraintHolds a →
      (enqueueNorm st l0 reason).Represents a := by
  intro a ha
  have hrep := hsol a ha
  obtain ⟨hfit, htrail, hclauses, hlearned⟩ := hrep
  have hal : l0.norm.eval a = some true := hlit a ha
  have hinrange : l0.norm.atom.slot < a.length :=
    eval_lit_some_slot_lt (l := l0.norm) hal
  have hfitN : a.Fits (domOfLit st.domains l0.norm) :=
    firing (doms := st.domains) (l := l0.norm) (a := a) hfit hinrange hal
  have htrailN : (enqueueNorm st l0 reason).TrailSatisfied a :=
    enqueueNorm_fresh_trailSat (st := st) (l0 := l0)
      (reason := reason) hnew hneg ha htrail hal
  unfold enqueueNorm at htrailN ⊢
  simp only [hnew, hneg, Bool.false_eq_true, if_false] at htrailN ⊢
  refine ⟨?_, htrailN, hclauses, hlearned⟩
  have : (enqueue st l0.norm reason).domains = st.domains := rfl
  rw [this]; exact hfitN

/-- negOnTrail falsifies at a trail-satisfying assignment (entry level). -/
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

/-- THE SWEEP TRANSFER: folding sound conflict-free-running propagators
    over a solved-by state either (i) never reports a conflict and the
    final state again solves-by, or the conflict that appears excludes
    every internal solution. Stated as the disjunction the loop needs. -/
theorem sweep_solvedBy
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {props : List Propagator} {st0 : State}
    (hsafe : PropSafe problem constraintHolds props)
    (hsol : SolvedBy problem constraintHolds st0)
    (hnone : st0.conflict = none) :
    ((runPropagators props st0).conflict = none ∧
      SolvedBy problem constraintHolds (runPropagators props st0)) ∨
    (∃ c, (runPropagators props st0).conflict = some c ∧
      ∀ a, ProblemSolution problem constraintHolds a →
        ¬ c.SatisfiedBy a) := by
  sorry

end LeanFzn.Solver.LCG
