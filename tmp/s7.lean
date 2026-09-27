import solver.LCG.Engine
import solver.LCG.Encoding
import solver.LCG.Invariants
import solver.LCG.Proofs.Lift

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

structure PropSafe (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (props : List Propagator) (st : State) : Prop where
  impliedTrueAt : ∀ p ∈ props, ∀ l r,
    p.run st = .implied l r →
    ∀ a, (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      l.eval a = some true
  conflictExcludes : ∀ p ∈ props, ∀ c,
    p.run st = .conflict c →
    ∀ a, (ProblemSolution problem constraintHolds a ∧ st.Represents a) →
      ¬ c.SatisfiedBy a

def SolvedBy (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (st : State) : Prop :=
  ∀ a, ProblemSolution problem constraintHolds a → st.Represents a

theorem negOnTrail_falsifies_entry {st : State} {l : Literal}
    {a : Assignment}
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

/-- The opposing-fact branch of `enqueueNorm` is unreachable for a
    justified enqueue: if `l0.norm` is true at some internal solution
    represented by `st`, then `st.negOnTrail l0.norm` is false. -/
theorem enqueueNorm_no_opposing
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {a : Assignment}
    (hsol : ProblemSolution problem constraintHolds a)
    (hrep : st.Represents a)
    (halt : l0.norm.eval a = some true)
    (hneg : st.negOnTrail l0.norm = true) :
    False := by
  obtain ⟨_, htrail, _, _⟩ := hrep
  have hf : l0.norm.eval a = some false :=
    negOnTrail_falsifies_entry hneg htrail
  rw [halt] at hf
  exact absurd hf (by simp)

/-- The fresh branch of `enqueueNorm` preserves `SolvedBy`. -/
theorem enqueueNorm_fresh_solvedBy
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnew : st.litOnTrail l0.norm = false)
    (hneg : st.negOnTrail l0.norm = false)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true)
    (hsol : SolvedBy problem constraintHolds st) :
    SolvedBy problem constraintHolds
      (enqueueNorm st l0 reason) := by
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
  have hdom : (enqueue st l0.norm reason).domains = st.domains := rfl
  rw [hdom]; exact hfitN

/-- CONFLICT-HALF of the enqueue step: for a justified literal (true at
    every internal solution), the enqueue output's conflict slot is
    still clear — the opposing branch would contradict the
    justification (given ANY internal solution exists), and the skip
    and fresh branches never write the slot. -/
theorem enqueueNorm_conflictNone_of_justified
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hnone : st.conflict = none)
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hrep : SolvedBy problem constraintHolds st)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    (enqueueNorm st l0 reason).conflict = none := by
  obtain ⟨b, hb⟩ := hsolvable
  unfold enqueueNorm
  show ((if st.litOnTrail l0.norm = true then st
    else if st.negOnTrail l0.norm = true then
      { st with conflict := some [l0.norm, l0.norm.negate] }
    else
      let st' := enqueue st l0.norm reason
      { st' with domains := domOfLit st'.domains l0.norm }) : State).conflict
    = none
  split
  · exact hnone
  · split
    · exfalso
      rename_i hneg
      exact enqueueNorm_no_opposing (problem := problem)
        (constraintHolds := constraintHolds) (st := st) (l0 := l0)
        (a := b) hb (hrep b hb) (hlit b hb) hneg
    · rename_i h1 h2
      show ((let st' := enqueue st l0.norm reason
        { st' with domains := domOfLit st'.domains l0.norm }) : State).conflict
          = none
      have hdom : (enqueue st l0.norm reason).conflict = st.conflict := rfl
      rw [hdom]; exact hnone

/-- SOLVEDBY-HALF of the enqueue step: for a justified literal (true at
    every internal solution), the enqueue output again solves-by — the
    skip branch is the identity, the fresh branch transfers by the
    firing lemma, and the opposing branch is unreachable. -/
theorem enqueueNorm_solvedBy_of_justified
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {st : State} {l0 : Literal} {reason : Option Reason}
    (hsolvable : ∃ b, ProblemSolution problem constraintHolds b)
    (hrep : SolvedBy problem constraintHolds st)
    (hlit : ∀ a, ProblemSolution problem constraintHolds a →
      l0.norm.eval a = some true) :
    SolvedBy problem constraintHolds
      (enqueueNorm st l0 reason) := by
  obtain ⟨b, hb⟩ := hsolvable
  unfold enqueueNorm SolvedBy
  intro a ha
  show ((if st.litOnTrail l0.norm = true then st
    else if st.negOnTrail l0.norm = true then
      { st with conflict := some [l0.norm, l0.norm.negate] }
    else
      let st' := enqueue st l0.norm reason
      { st' with domains := domOfLit st'.domains l0.norm })).Represents a
  split
  · exact hrep a ha
  · split
    · exfalso
      rename_i hneg
      exact enqueueNorm_no_opposing (problem := problem)
        (constraintHolds := constraintHolds) (st := st) (l0 := l0)
        (a := b) hb (hrep b hb) (hlit b hb) hneg
    · rename_i hnew hneg
      have hnew' : st.litOnTrail l0.norm = false := by
        cases hb2 : st.litOnTrail l0.norm with
        | true => exact absurd hb2 hnew
        | false => rfl
      have hneg' : st.negOnTrail l0.norm = false := by
        cases hb2 : st.negOnTrail l0.norm with
        | true => exact absurd hb2 hneg
        | false => rfl
      show ((let st' := enqueue st l0.norm reason
        { st' with domains := domOfLit st'.domains l0.norm })).Represents a
      have conv : ((let st' := enqueue st l0.norm reason
          { st' with domains := domOfLit st'.domains l0.norm }) : State)
          = (enqueueNorm st l0 reason) := by
        simp only [enqueueNorm, hnew', hneg', Bool.false_eq_true, if_false]
      rw [conv]
      exact enqueueNorm_fresh_solvedBy (st := st) (l0 := l0)
        (reason := reason) hnew' hneg' hlit hrep a ha

end LeanFzn.Solver.LCG
