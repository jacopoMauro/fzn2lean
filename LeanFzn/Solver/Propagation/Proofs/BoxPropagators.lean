/-
File: LeanFzn/Solver/Propagation/Proofs/BoxPropagators.lean
Purpose: Package proved propagators for finite-domain boxes without trail invariants.
Dependencies: Propagators supplies local-domain deduction and conflict safety;
Reason supplies globally entailed explanations for every registered family.
DAG: Proofs.Propagators + Proofs.Reason -> BoxPropagators -> box-search certification.
-/
import LeanFzn.Solver.Propagation.Proofs.Propagators
import LeanFzn.Solver.Propagation.Proofs.Reason
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-- Registered propagators preserve every solution fitting the current box;
reported conflicts exclude the box, including conflicts with empty explanations. -/
theorem boxPropagators_safe
    {problem : Problem DomConstraint Unit}
    (_hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    -- the compiled shape: every linLe constraint has equal-length
    -- coefficient/index lists (the extractor's gate)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length) :
    ∀ st, IntViewedDoms st.domains →
    (∀ p ∈ props, ∀ l r, p.run st = .implied l r →
      ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
        a.Fits st.domains → l.eval a = some true) ∧
    (∀ p ∈ props, ∀ c, p.run st = .conflict c →
      ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
        a.Fits st.domains → False) := by
  intro st hviewst
  refine ⟨?_, ?_⟩
  · intro p hp l r hrun a hsol hfit
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProved_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
      ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
      ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
      ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
      ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
      ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
      ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
      ⟨lc, li, lb2, ldca, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
      ⟨ais, hadca, hrunad⟩
    · rw [hdc2] at hdc
      exact (propLe_safe st i j).1 l r hrun2 a hfit (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLt_safe st i j).1 l r hrun2 a hfit (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propEq_safe st i j hviewst).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propNe_safe st i j hviewst).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propPlus_safe st i j k).1 l r hrun2 a hfit (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      -- linLe needs equal lengths (the compiled shape):
      have hlen : coeffs.length = is.length :=
        hlin _ hdc coeffs is b2 rfl
      exact (propLinLe2_safe st coeffs is b2 hlen).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLeConstHi_safe st i c).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLeConstLo_safe st i c).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLtConstHi_safe st i c).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLtConstLo_safe st i c).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propConstEq_safe st i v).1 l r hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdca] at hdc
      exact (propBoolNot_safe st ia ja).1 l r hruna a hfit
        (hsol.2 _ hdc)
    · rw [hdcb] at hdc
      exact (propBoolAnd_safe st ib jb kb).1 l r hrunb a hfit
        (hsol.2 _ hdc)
    · rw [hdcc] at hdc
      exact (propBoolOr_safe st ic jc kc).1 l r hrunc a hfit
        (hsol.2 _ hdc)
    · rw [hdcd] at hdc
      exact (propMin_safe st id jd kd).1 l r hrund a hfit
        (hsol.2 _ hdc)
    · rw [hdce] at hdc
      exact (propMax_safe st ie je ke).1 l r hrune a hfit
        (hsol.2 _ hdc)
    · rw [hdcg] at hdc
      exact (propAbs_safe st ig kg).1 l r hrung a hfit
        (hsol.2 _ hdc)
    · rw [ldca] at hdc
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      exact (propLinEq2_safe st lc li lb2 hlenL).1 l r hrunl a hfit
        (hsol.2 _ hdc)
    · rw [hdct] at hdc
      exact (propTimes_safe st ti tj tk2).1 l r hrunt a hfit
        (hsol.2 _ hdc)
    · rw [hadca] at hdc
      exact (propAllDiffLCG_safe st ais).1 l r hrunad a hfit
        (hsol.2 _ hdc)
  · intro p hp c hrun a hsol hfit
    obtain ⟨dc, hdc, hprop⟩ := hprops p hp
    rcases propagatorOfProved_run hprop hrun with
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
      ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
      ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, k, hdc2, hrun2⟩ |
      ⟨i, k, hdc2, hrun2⟩ | ⟨i, k, hdc2, hrun2⟩ |
      ⟨i, k, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
      ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
      ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
      ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
      ⟨lc, li, lb2, ldca, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
      ⟨ais, hadca, hrunad⟩
    · rw [hdc2] at hdc
      exact (propLe_safe st i j).2.1 c hrun2 a hfit (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLt_safe st i j).2.1 c hrun2 a hfit (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propEq_safe st i j hviewst).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propNe_safe st i j hviewst).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propPlus_safe st i j k).2.1 c hrun2 a hfit (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      have hlen : coeffs.length = is.length :=
        hlin _ hdc coeffs is b2 rfl
      exact (propLinLe2_safe st coeffs is b2 hlen).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLeConstHi_safe st i k).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLeConstLo_safe st i k).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLtConstHi_safe st i k).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propLtConstLo_safe st i k).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdc2] at hdc
      exact (propConstEq_safe st i v).2.1 c hrun2 a hfit
        (hsol.2 _ hdc)
    · rw [hdca] at hdc
      exact (propBoolNot_safe st ia ja).2.1 c hruna a hfit
        (hsol.2 _ hdc)
    · rw [hdcb] at hdc
      exact (propBoolAnd_safe st ib jb kb).2.1 c hrunb a hfit
        (hsol.2 _ hdc)
    · rw [hdcc] at hdc
      exact (propBoolOr_safe st ic jc kc).2.1 c hrunc a hfit
        (hsol.2 _ hdc)
    · rw [hdcd] at hdc
      exact (propMin_safe st id jd kd).2.1 c hrund a hfit
        (hsol.2 _ hdc)
    · rw [hdce] at hdc
      exact (propMax_safe st ie je ke).2.1 c hrune a hfit
        (hsol.2 _ hdc)
    · rw [hdcg] at hdc
      exact (propAbs_safe st ig kg).2.1 c hrung a hfit
        (hsol.2 _ hdc)
    · rw [ldca] at hdc
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      exact (propLinEq2_safe st lc li lb2 hlenL).2.1 c hrunl a hfit
        (hsol.2 _ hdc)
    · rw [hdct] at hdc
      exact (propTimes_safe st ti tj tk2).2.1 c hrunt a hfit
        (hsol.2 _ hdc)
    · rw [hadca] at hdc
      exact (propAllDiffLCG_safe st ais).2.1 c hrunad a hfit
        (hsol.2 _ hdc)


/-- Implication reasons are globally entailed, independently of the observation trail. -/
theorem boxPropagators_reasons
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length) :
    ∀ st, ∀ p ∈ props, ∀ l r, p.run st = .implied l r →
      Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
        (∀ q ∈ r.clause, q = q.norm) := by
  intro st p hp l r hrun
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, c, hdc2, hrun2⟩ |
    ⟨i, c, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
    ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
    ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
    ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
    ⟨ais, hdcai, hrunad⟩
  · rw [hdc2] at hdc
    exact propLe_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLt_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propEq_reason_valid hview hdc hrun2
  · rw [hdc2] at hdc
    exact propNe_reason_valid hview hdc hrun2
  · rw [hdc2] at hdc
    exact propPlus_reason_valid hdc hrun2
  · -- linLe: the FIXED propagator's reasons are state-free valid
    rw [hdc2] at hdc
    have hlenL : coeffs.length = is.length :=
      hlin _ hdc coeffs is b2 rfl
    exact propLinLe2_reason_valid hdc hlenL hrun2
  · rw [hdc2] at hdc
    exact propLeConstHi_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLeConstLo_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLtConstHi_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propLtConstLo_reason_valid hdc hrun2
  · rw [hdc2] at hdc
    exact propConstEq_reason_valid hdc hrun2
  · rw [hdca] at hdc
    exact propBoolNot_reason_safe_sat hdc hruna
  · rw [hdcb] at hdc
    exact propBoolAnd_reason_safe_sat hdc hrunb
  · rw [hdcc] at hdc
    exact propBoolOr_reason_safe_sat hdc hrunc
  · rw [hdcd] at hdc
    exact propMin_reason_valid hdc hrund
  · rw [hdce] at hdc
    exact propMax_reason_valid hdc hrune
  · rw [hdcg] at hdc
    exact propAbs_reason_valid hdc hrung
  · rw [hdcl] at hdc
    have hlenL : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact propLinEq2_reason_valid hdc hlenL hrunl
  · rw [hdct] at hdc
    exact propTimes_reason_valid hdc hrunt
  · rw [hdcai] at hdc
    exact propAllDiffLCG_reason_valid hrunad


/-- Every nonempty raw propagator conflict is globally entailed. Empty
explanations certify only local exclusion and are deliberately excluded. -/
theorem boxPropagators_conflicts
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (st : State) (p : Propagator) (hp : p ∈ props) (cc : Clause)
    (hrun : p.run st = .conflict cc) (hne0 : cc ≠ []) :
    cc.EntailedBy problem DomConstraint.SatisfiedBy := by
  intro a ha
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
      ⟨i, c2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
      ⟨i, c2, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
    ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
    ⟨ic, jc, kc, hdcc, hrunc⟩ | ⟨id, jd, kd, hdcd, hrund⟩ |
    ⟨ie, je, ke, hdce, hrune⟩ | ⟨ig, kg, hdcg, hrung⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ | ⟨ti, tj, tk2, hdct, hrunt⟩ |
    ⟨ais, hdcai, hrunad⟩
  · rw [hdc2] at hdc
    exact propLe_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLt_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propEq_conflict_entitled hview hdc hrun2 a ha
  · -- neSlot: its conflict clause is EMPTY, contradicting cc ≠ []
    exact absurd rfl (propNe_conflict_clause_empty hrun2 ▸ hne0)
  · rw [hdc2] at hdc
    exact propPlus_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    have hlenL : coeffs.length = is.length :=
      hlin _ hdc coeffs is b2 rfl
    exact propLinLe2_entitled hdc hlenL hrun2 a ha
  · rw [hdc2] at hdc
    exact propLeConstHi_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLeConstLo_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLtConstHi_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLtConstLo_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propConstEq_conflict_entitled hdc hrun2 a ha
  · rw [hdca] at hdc
    exact propBoolNot_entitled hdc hruna a ha
  · rw [hdcb] at hdc
    exact propBoolAnd_entitled hdc hrunb a ha
  · rw [hdcc] at hdc
    exact propBoolOr_entitled hdc hrunc a ha
  · rw [hdcd] at hdc
    exact propMin_entitled hdc hrund a ha
  · rw [hdce] at hdc
    exact propMax_entitled hdc hrune a ha
  · rw [hdcg] at hdc
    exact propAbs_entitled hdc hrung a ha
  · rw [hdcl] at hdc
    have hlenL : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact propLinEq2_entitled hdc hlenL hrunl a ha
  · rw [hdct] at hdc
    exact propTimes_entitled hdc hrunt a ha
  · -- allDiff: its conflict clause is EMPTY, contradicting cc ≠ []
    exact absurd rfl (propAllDiffLCG_conflict_clause_empty hrunad ▸ hne0)

end LeanFzn.Solver.Propagation
