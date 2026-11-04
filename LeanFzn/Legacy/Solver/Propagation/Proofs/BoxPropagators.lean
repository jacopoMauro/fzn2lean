/-
File: LeanFzn/Solver/Propagation/Proofs/BoxPropagators.lean
Purpose: Package proved propagators for finite-domain boxes without trail invariants.
Dependencies: Propagators supplies local-domain deduction and conflict safety;
Reason supplies globally entailed explanations for every registered family.
DAG: Proofs.Propagators + Proofs.Reason -> BoxPropagators -> box-search certification.
-/
import LeanFzn.Legacy.Solver.Propagation.Proofs.Propagators
import LeanFzn.Legacy.Solver.Propagation.Proofs.Reason
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
      ⟨ic, jc, kc, hdcc, hrunc⟩ |
      ⟨lc, li, lb2, ldca, hrunl⟩ |
      ⟨ais, hadca, hrunad⟩ | ⟨lre, lri, lrb, lrr, hdcR, hrunR⟩ |
      ⟨lnc, lni, lnb, hdcN, hrunN⟩ | ⟨imn, jmn, kmn, hdcMn, hrunMn⟩ | ⟨imx, jmx, kmx, hdcMx, hrunMx⟩ |
      ⟨ilr, jlr, rlr, hdcLR, hrunLR⟩ |
      ⟨ieq, jeq, req, hdcE, hrunE⟩ | ⟨ine, jne, rne, hdcNE, hrunNE⟩ |
      ⟨lq1, leqs, leqb, leqr, hdcEqR, hrunEqR⟩ |
      ⟨lq2, lnis, lnib, lnir, hdcNeR, hrunNeR⟩ |
      ⟨itt, jtt, ktt, hdcTt, hrunTt⟩ |
      ⟨iab, kab, hdcAb, hrunAb⟩ |
      ⟨od1, od2, od3, hdcD, hrunD⟩ | ⟨om1, om2, om3, hdcM, hrunM⟩ |
      ⟨_, hrunLn⟩ | ⟨osG, rG, hdcG, hrunG⟩ | ⟨osH, rH, hdcH, hrunH⟩ | ⟨iB, kB, hdcB, hrunB⟩ |
      ⟨xsE, iE, kE, hdcElem, hrunElem⟩ |
      ⟨isAnd, kAnd, hdcAnd, hrunAnd⟩ |
      ⟨isV, iV, kV, hdcV, hrunV⟩ |
      ⟨isW, iW, kW, hdcW, hrunW⟩
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
    · rw [ldca] at hdc
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      exact (propLinEq2_safe st lc li lb2 hlenL).1 l r hrunl a hfit
        (hsol.2 _ hdc)
    · rw [hadca] at hdc
      exact (propAllDiffLCG_safe st ais).1 l r hrunad a hfit
        (hsol.2 _ hdc)
    · rw [hdcR] at hdc
      exact (propLinLeReif_safe st lre lri lrb lrr).1 l r hrunR a hfit
        (hsol.2 _ hdc)
    · rw [hdcN] at hdc
      exact (propLinNe_safe st lnc lni lnb).1 l r hrunN a hfit
        (hsol.2 _ hdc)
    · exact (propMin_safe st imn jmn kmn).1 l r hrunMn a hfit
        (hdcMn _ (hsol.2 _ hdc))
    · exact (propMax_safe st imx jmx kmx).1 l r hrunMx a hfit
        (hdcMx _ (hsol.2 _ hdc))
    · rw [hdcLR] at hdc
      exact (propLeReifSlotB_safe st ilr jlr rlr).1 l r hrunLR a hfit
        (hsol.2 _ hdc)
    · rw [hdcE] at hdc
      exact (propEqReifSlot_safe st ieq jeq req hviewst).1 l r hrunE a hfit
        (hsol.2 _ hdc)
    · rw [hdcNE] at hdc
      exact (propNeReifSlot_safe st ine jne rne hviewst).1 l r hrunNE a hfit
        (hsol.2 _ hdc)
    · rw [hdcEqR] at hdc
      exact (propLinEqReif_safe st lq1 leqs leqb leqr).1 l r hrunEqR a hfit
        (hsol.2 _ hdc)
    · rw [hdcNeR] at hdc
      exact (propLinNeReif_safe st lq2 lnis lnib lnir).1 l r hrunNeR a hfit
        (hsol.2 _ hdc)
    · rw [hdcTt] at hdc
      exact (propTimes_safe st itt jtt ktt).1 l r hrunTt a hfit
        (hsol.2 _ hdc)
    · rw [hdcAb] at hdc
      exact (propAbs_safe st iab kab).1 l r hrunAb a hfit (hsol.2 _ hdc)
    · rw [hdcD] at hdc
      exact (propDiv_safe st od1 od2 od3).1 l r hrunD a hfit (hsol.2 _ hdc)
    · rw [hdcM] at hdc
      exact (propMod_safe st om1 om2 om3).1 l r hrunM a hfit (hsol.2 _ hdc)
    · exact (propCheck_implied_elim hrunLn).elim
    · rw [hdcG] at hdc
      exact (propMaxGen_safe st osG rG).1 l r hrunG a hfit (hsol.2 _ hdc)
    · rw [hdcH] at hdc
      exact (propMinGen_safe st osH rH).1 l r hrunH a hfit (hsol.2 _ hdc)
    · rw [hdcB] at hdc
      exact (propBool2intSlot_safe st iB kB).1 l r hrunB a hfit (hsol.2 _ hdc)
    · rw [hdcElem] at hdc
      exact (propArrayIntElement_safe st xsE iE kE).1 l r hrunElem a hfit
        (hsol.2 _ hdc)
    · rw [hdcAnd] at hdc
      exact (propArrayBoolAnd_safe st isAnd kAnd).1 l r hrunAnd a hfit
        (hsol.2 _ hdc)
    · rw [hdcV] at hdc
      exact (propArrayVarIntElement_safe st isV iV kV).1 l r hrunV a hfit
        (hsol.2 _ hdc)
    · rw [hdcW] at hdc
      exact (propArrayVarBoolElement_safe st isW iW kW).1 l r hrunW a hfit
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
      ⟨ic, jc, kc, hdcc, hrunc⟩ |
      ⟨lc, li, lb2, ldca, hrunl⟩ |
      ⟨ais, hadca, hrunad⟩ | ⟨lre, lri, lrb, lrr, hdcR, hrunR⟩ |
      ⟨lnc, lni, lnb, hdcN, hrunN⟩ | ⟨imn, jmn, kmn, hdcMn, hrunMn⟩ | ⟨imx, jmx, kmx, hdcMx, hrunMx⟩ |
      ⟨ilr, jlr, rlr, hdcLR, hrunLR⟩ |
      ⟨ieq, jeq, req, hdcE, hrunE⟩ | ⟨ine, jne, rne, hdcNE, hrunNE⟩ |
      ⟨lq1, leqs, leqb, leqr, hdcEqR, hrunEqR⟩ |
      ⟨lq2, lnis, lnib, lnir, hdcNeR, hrunNeR⟩ |
      ⟨itt, jtt, ktt, hdcTt, hrunTt⟩ |
      ⟨iab, kab, hdcAb, hrunAb⟩ |
      ⟨od1, od2, od3, hdcD, hrunD⟩ | ⟨om1, om2, om3, hdcM, hrunM⟩ |
      ⟨_, hrunLn⟩ | ⟨osG, rG, hdcG, hrunG⟩ | ⟨osH, rH, hdcH, hrunH⟩ | ⟨iB, kB, hdcB, hrunB⟩ |
      ⟨xsE, iE, kE, hdcElem, hrunElem⟩ |
      ⟨isAnd, kAnd, hdcAnd, hrunAnd⟩ |
      ⟨isV, iV, kV, hdcV, hrunV⟩ |
      ⟨isW, iW, kW, hdcW, hrunW⟩
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
    · rw [ldca] at hdc
      have hlenL : lc.length = li.length :=
        hlinE _ hdc lc li lb2 rfl
      exact (propLinEq2_safe st lc li lb2 hlenL).2.1 c hrunl a hfit
        (hsol.2 _ hdc)
    · rw [hadca] at hdc
      exact (propAllDiffLCG_safe st ais).2.1 c hrunad a hfit
        (hsol.2 _ hdc)
    · rw [hdcR] at hdc
      exact (propLinLeReif_safe st lre lri lrb lrr).2.1 c hrunR a hfit
        (hsol.2 _ hdc)
    · rw [hdcN] at hdc
      exact (propLinNe_safe st lnc lni lnb).2.1 c hrunN a hfit
        (hsol.2 _ hdc)
    · exact (propMin_safe st imn jmn kmn).2.1 c hrunMn a hfit
        (hdcMn _ (hsol.2 _ hdc))
    · exact (propMax_safe st imx jmx kmx).2.1 c hrunMx a hfit
        (hdcMx _ (hsol.2 _ hdc))
    · rw [hdcLR] at hdc
      exact (propLeReifSlotB_safe st ilr jlr rlr).2.1 c hrunLR a hfit
        (hsol.2 _ hdc)
    · rw [hdcE] at hdc
      exact (propEqReifSlot_safe st ieq jeq req hviewst).2.1 c hrunE a hfit
        (hsol.2 _ hdc)
    · rw [hdcNE] at hdc
      exact (propNeReifSlot_safe st ine jne rne hviewst).2.1 c hrunNE a hfit
        (hsol.2 _ hdc)
    · rw [hdcEqR] at hdc
      exact (propLinEqReif_safe st lq1 leqs leqb leqr).2.1 c hrunEqR a hfit
        (hsol.2 _ hdc)
    · rw [hdcNeR] at hdc
      exact (propLinNeReif_safe st lq2 lnis lnib lnir).2.1 c hrunNeR a hfit
        (hsol.2 _ hdc)
    · rw [hdcTt] at hdc
      exact (propTimes_safe st itt jtt ktt).2.1 c hrunTt a hfit
        (hsol.2 _ hdc)
    · rw [hdcAb] at hdc
      exact (propAbs_safe st iab kab).2.1 c hrunAb a hfit (hsol.2 _ hdc)
    · rw [hdcD] at hdc
      exact (propDiv_safe st od1 od2 od3).2.1 c hrunD a hfit (hsol.2 _ hdc)
    · rw [hdcM] at hdc
      exact (propMod_safe st om1 om2 om3).2.1 c hrunM a hfit (hsol.2 _ hdc)
    · exact propCheck_conflict_false hrunLn hfit (hsol.2 _ hdc)
    · rw [hdcG] at hdc
      exact (propMaxGen_safe st osG rG).2.1 c hrunG a hfit (hsol.2 _ hdc)
    · rw [hdcH] at hdc
      exact (propMinGen_safe st osH rH).2.1 c hrunH a hfit (hsol.2 _ hdc)
    · rw [hdcB] at hdc
      exact (propBool2intSlot_safe st iB kB).2.1 c hrunB a hfit (hsol.2 _ hdc)
    · rw [hdcElem] at hdc
      exact (propArrayIntElement_safe st xsE iE kE).2.1 c hrunElem a hfit
        (hsol.2 _ hdc)
    · rw [hdcAnd] at hdc
      exact (propArrayBoolAnd_safe st isAnd kAnd).2.1 c hrunAnd a hfit
        (hsol.2 _ hdc)
    · rw [hdcV] at hdc
      exact (propArrayVarIntElement_safe st isV iV kV).2.1 c hrunV a hfit
        (hsol.2 _ hdc)
    · rw [hdcW] at hdc
      exact (propArrayVarBoolElement_safe st isW iW kW).2.1 c hrunW a hfit
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
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (hlreif : ∀ dc ∈ problem.constraints, ∀ coeffs is b r,
      dc = .linLeReif coeffs is b r →
        ∀ i ∈ is, i < problem.domains.length)
    (hlad : ∀ dc ∈ problem.constraints, ∀ is, dc = .allDiff is →
        ∀ i ∈ is, i < problem.domains.length)
    (haba : ∀ dc ∈ problem.constraints, ∀ is k,
      dc = .arrayBoolAndSlot is k → BoolDomsAt problem is) :
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
    ⟨ic, jc, kc, hdcc, hrunc⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ |
    ⟨ais, hdcai, hrunad⟩ | ⟨lre, lri, lrb, lrr, hdcR, hrunR⟩ |
    ⟨lnc, lni, lnb, hdcN, hrunN⟩ | ⟨imn, jmn, kmn, hdcMn, hrunMn⟩ | ⟨imx, jmx, kmx, hdcMx, hrunMx⟩ |
    ⟨ilr, jlr, rlr, hdcLR, hrunLR⟩ |
    ⟨ieq, jeq, req, hdcE, hrunE⟩ | ⟨ine, jne, rne, hdcNE, hrunNE⟩ |
    ⟨lq1, leqs, leqb, leqr, hdcEqR, hrunEqR⟩ |
    ⟨lq2, lnis, lnib, lnir, hdcNeR, hrunNeR⟩ |
    ⟨itt, jtt, ktt, hdcTt, hrunTt⟩ |
    ⟨iab, kab, hdcAb, hrunAb⟩ |
    ⟨od1, od2, od3, hdcD, hrunD⟩ | ⟨om1, om2, om3, hdcM, hrunM⟩ |
    ⟨_, hrunLn⟩ | ⟨osG, rG, hdcG, hrunG⟩ | ⟨osH, rH, hdcH, hrunH⟩ | ⟨iB, kB, hdcB, hrunB⟩ |
    ⟨xsE, iE, kE, hdcElem, hrunElem⟩ |
    ⟨isAnd, kAnd, hdcAnd, hrunAnd⟩ |
    ⟨isV, iV, kV, hdcV, hrunV⟩ |
    ⟨isW, iW, kW, hdcW, hrunW⟩
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
  · rw [hdcl] at hdc
    have hlenL : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact propLinEq2_reason_valid hdc hlenL hrunl
  · -- allDiff: the value eliminations' state-free reason validity (the
    -- problem-level operand-range gate pins the fixed and the target
    -- slot in range)
    have hlad' : ∀ i ∈ ais, i < problem.domains.length :=
      fun i hi => hlad dc hdc ais hdcai i hi
    rw [hdcai] at hdc
    exact propAllDiffLCG_reason_valid hview hdc hlad' hrunad
  · rw [hdcR] at hdc
    exact propLinLeReif_reason_valid hview hdc hlreif hrunR
  · rw [hdcN] at hdc
    exact propLinNe_reason_valid hdc hrunN
  · exact propMin_reason_valid (fun a ha => hdcMn _ (ha.2 _ hdc)) hrunMn
  · exact propMax_reason_valid (fun a ha => hdcMx _ (ha.2 _ hdc)) hrunMx
  · rw [hdcLR] at hdc
    exact propLeReifSlotB_reason_valid hdc hrunLR
  · rw [hdcE] at hdc
    exact propEqReifSlot_reason_valid hview hdc hrunE
  · rw [hdcNE] at hdc
    exact propNeReifSlot_reason_valid hview hdc hrunNE
  · rw [hdcEqR] at hdc
    exact propLinEqReif_reason_valid hdc hrunEqR
  · rw [hdcNeR] at hdc
    exact propLinNeReif_reason_valid hdc hrunNeR
  · rw [hdcTt] at hdc
    exact propTimes_reason_valid hdc hrunTt
  · rw [hdcAb] at hdc
    exact propAbs_reason_valid hdc hrunAb
  · rw [hdcD] at hdc
    exact propDiv_reason_valid hdc hrunD
  · rw [hdcM] at hdc
    exact propMod_reason_valid hdc hrunM
  · exact (propCheck_implied_elim hrunLn).elim
  · rw [hdcG] at hdc
    exact propMaxGen_reason_valid (fun a ha => ha.2 _ hdc) hrunG
  · rw [hdcH] at hdc
    exact propMinGen_reason_valid (fun a ha => ha.2 _ hdc) hrunH
  · rw [hdcB] at hdc
    exact propBool2intSlot_reason_valid hdc hrunB
  · rw [hdcElem] at hdc
    exact propArrayIntElement_reason_valid hdc hrunElem
  · exact propArrayBoolAnd_reason_valid (hdcAnd ▸ hdc)
      (haba dc hdc isAnd kAnd hdcAnd) hrunAnd
  · rw [hdcV] at hdc
    exact propArrayVarIntElement_reason_valid hdc hrunV
  · rw [hdcW] at hdc
    exact propArrayVarBoolElement_reason_valid hdc hrunW

/-- Every nonempty raw propagator conflict is entailed at every internal
solution that is FAITHFUL to the state the propagator read (`FrameFaithful`:
the solution reads, at every slot, a value of the sort of the slot's current
domain values - automatic when the state's domains are sub-domains of a
shape-typed int-viewed problem box, `frameFaithful_of_domSub`). The premise is
consumed only by the `neSlot`, `allDiff` and `propCheck` arms (their
explained clauses); every other family is state-free. Empty explanations certify only local
exclusion and are deliberately excluded. -/
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
    ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      FrameFaithful st.domains a → cc.SatisfiedBy a := by
  intro a ha hfaith
  obtain ⟨dc, hdc, hprop⟩ := hprops p hp
  rcases propagatorOfProved_run hprop hrun with
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, hdc2, hrun2⟩ |
    ⟨i, j, hdc2, hrun2⟩ | ⟨i, j, k, hdc2, hrun2⟩ |
    ⟨coeffs, is, b2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
      ⟨i, c2, hdc2, hrun2⟩ | ⟨i, c2, hdc2, hrun2⟩ |
      ⟨i, c2, hdc2, hrun2⟩ | ⟨i, v, hdc2, hrun2⟩ |
    ⟨ia, ja, hdca, hruna⟩ | ⟨ib, jb, kb, hdcb, hrunb⟩ |
    ⟨ic, jc, kc, hdcc, hrunc⟩ |
    ⟨lc, li, lb2, hdcl, hrunl⟩ |
    ⟨ais, hdcai, hrunad⟩ | ⟨lre, lri, lrb, lrr, hdcR, hrunR⟩ |
    ⟨lnc, lni, lnb, hdcN, hrunN⟩ | ⟨imn, jmn, kmn, hdcMn, hrunMn⟩ | ⟨imx, jmx, kmx, hdcMx, hrunMx⟩ |
    ⟨ilr, jlr, rlr, hdcLR, hrunLR⟩ |
    ⟨ieq, jeq, req, hdcE, hrunE⟩ | ⟨ine, jne, rne, hdcNE, hrunNE⟩ |
    ⟨lq1, leqs, leqb, leqr, hdcEqR, hrunEqR⟩ |
    ⟨lq2, lnis, lnib, lnir, hdcNeR, hrunNeR⟩ |
    ⟨itt, jtt, ktt, hdcTt, hrunTt⟩ |
    ⟨iab, kab, hdcAb, hrunAb⟩ |
    ⟨od1, od2, od3, hdcD, hrunD⟩ | ⟨om1, om2, om3, hdcM, hrunM⟩ |
    ⟨_, hrunLn⟩ | ⟨osG, rG, hdcG, hrunG⟩ | ⟨osH, rH, hdcH, hrunH⟩ | ⟨iB, kB, hdcB, hrunB⟩ |
    ⟨xsE, iE, kE, hdcElem, hrunElem⟩ |
    ⟨isAnd, kAnd, hdcAnd, hrunAnd⟩ |
    ⟨isV, iV, kV, hdcV, hrunV⟩ |
    ⟨isW, iW, kW, hdcW, hrunW⟩
  · rw [hdc2] at hdc
    exact propLe_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propLt_conflict_entitled hdc hrun2 a ha
  · rw [hdc2] at hdc
    exact propEq_conflict_entitled hview hdc hrun2 a ha
  · -- neSlot: the explained clause `[x ≠ c, y ≠ c]` / `[x = ¬b, y = ¬b]`
    rw [hdc2] at hdc
    exact propNe_conflict_entailed hrun2 hne0 (ha.2 _ hdc) hfaith
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
  · rw [hdcl] at hdc
    have hlenL : lc.length = li.length :=
      hlinE _ hdc lc li lb2 rfl
    exact propLinEq2_entitled hdc hlenL hrunl a ha
  · -- allDiff: the explained Hall clause
    rw [hdcai] at hdc
    exact propAllDiffLCG_conflict_entailed hrunad hne0 (ha.2 _ hdc) hfaith
  · -- linLeReif: the pinned delegation's conflict entitlement
    rw [hdcR] at hdc
    exact propLinLeReif_entitled hrunR hfaith (ha.2 _ hdc)
  · rw [hdcN] at hdc
    exact propLinNe_entitled hrunN (ha.2 _ hdc)
  · exact propMin_entitled (fun a ha => hdcMn _ (ha.2 _ hdc)) hrunMn a ha
  · exact propMax_entitled (fun a ha => hdcMx _ (ha.2 _ hdc)) hrunMx a ha
  · rw [hdcLR] at hdc
    exact propLeReifSlotB_entitled hdc hrunLR a ha
  · rw [hdcE] at hdc
    exact propEqReifSlot_entitled hview hdc hrunE a hfaith ha
  · rw [hdcNE] at hdc
    exact propNeReifSlot_entitled hview hdc hrunNE a hfaith ha
  · rw [hdcEqR] at hdc
    exact propLinEqReif_entitled hrunEqR hfaith (ha.2 _ hdc)
  · rw [hdcNeR] at hdc
    exact propLinNeReif_entitled hrunNeR hfaith (ha.2 _ hdc)
  · rw [hdcTt] at hdc
    exact propTimes_entitled hdc hrunTt a ha
  · rw [hdcAb] at hdc
    exact propAbs_entitled hdc hrunAb a ha
  · rw [hdcD] at hdc
    exact propDiv_entitled hdc hrunD a ha
  · rw [hdcM] at hdc
    exact propMod_entitled hdc hrunM a ha
  · -- `propCheck`: the faithful solution differs from the forced assignment
    exact propCheck_conflict_faithful hrunLn hfaith (ha.2 _ hdc)
  · rw [hdcG] at hdc
    exact propMaxGen_entitled (fun a ha => ha.2 _ hdc) hrunG a ha
  · rw [hdcH] at hdc
    exact propMinGen_entitled (fun a ha => ha.2 _ hdc) hrunH a ha
  · rw [hdcB] at hdc
    exact propBool2intSlot_entitled hdc hrunB a ha
  · rw [hdcElem] at hdc
    exact propArrayIntElement_entitled hdc hrunElem a ha
  · rw [hdcAnd] at hdc
    exact propArrayBoolAnd_entitled hrunAnd hfaith (ha.2 _ hdc)
  · rw [hdcV] at hdc
    exact propArrayVarIntElement_entitled hdc hrunV a ha
  · rw [hdcW] at hdc
    exact propArrayVarBoolElement_entitled hdc hrunW a ha

end LeanFzn.Solver.Propagation
