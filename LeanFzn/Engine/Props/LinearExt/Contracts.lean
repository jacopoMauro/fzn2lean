/-
Purpose: LinearExt propagators: contracts definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.LinearExt.Reified
DAG: LeanFzn.Engine.Props.LinearExt.Reified -> LeanFzn.Engine.Props.LinearExt.Contracts.
-/
import LeanFzn.Engine.Props.LinearExt.Reified

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Reification contract helpers -/

theorem domC_evalLit_posBool_compl {d : DomC} {r : Nat} {b : Bool}
    (h : d.evalLit (posBool r true) = some b) :
    d.evalLit (posBool r (!b)) = some false := by
  cases b with
  | true =>
      rw [domC_evalLit_posBool_false_iff]
      exact domC_evalLit_posBool_true_iff.mp h
  | false =>
      simpa using h

theorem domC_evalLit_posBool_none_of_not {d : DomC} {r : Nat}
    (h1 : d.evalLit (posBool r true) ≠ some true)
    (h2 : d.evalLit (posBool r true) ≠ some false) :
    d.evalLit (posBool r true) = none := by
  cases h : d.evalLit (posBool r true) with
  | none => rfl
  | some b => cases b <;> simp_all

theorem domC_evalLit_posBool_none_of_none {d : DomC} {r : Nat} {b : Bool}
    (h : d.evalLit (posBool r true) = none) :
    d.evalLit (posBool r b) = none := by
  rw [domC_evalLit_posBool_none_iff] at h ⊢
  exact h

/-! ### Case lemmas for the inequality plans -/

theorem linLePlan_conflict_cases {terms : List LinTerm} {b : Int} {ls : List Literal}
    (h : (linLePlan terms b).conflict? = some ls) :
    b < linTotalMin terms ∧ ls = linConflictLits terms := by
  unfold linLePlan at h
  split at h
  · rename_i hconf
    exact ⟨hconf, (Option.some.inj h).symm⟩
  · simp at h

theorem linLePlan_conflict_none_cases {terms : List LinTerm} {b : Int}
    (h : (linLePlan terms b).conflict? = none) : ¬ b < linTotalMin terms := by
  unfold linLePlan at h
  split at h
  · simp at h
  · omega

theorem linGePlan_conflict_cases {terms : List LinTerm} {b : Int} {ls : List Literal}
    (h : (linGePlan terms b).conflict? = some ls) :
    linTotalMax terms < b ∧ ls = linMaxLits terms := by
  unfold linGePlan at h
  split at h
  · rename_i hconf
    exact ⟨hconf, (Option.some.inj h).symm⟩
  · simp at h

theorem linGePlan_conflict_none_cases {terms : List LinTerm} {b : Int}
    (h : (linGePlan terms b).conflict? = none) : ¬ linTotalMax terms < b := by
  unfold linGePlan at h
  split at h
  · simp at h
  · omega

/-! ### Case lemmas for the reification decision plans -/

theorem linLeReifDecidePlan_prunes_cases {r : Nat} {terms : List LinTerm} {b : Int}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linLeReifDecidePlan r terms b).prunes) :
    (linTotalMax terms ≤ b ∧ l = posBool r true ∧
      reason = linMaxLits terms ++ [posBool r true]) ∨
    (b < linTotalMin terms ∧ l = posBool r false ∧
      reason = linConflictLits terms ++ [posBool r false]) := by
  unfold linLeReifDecidePlan at h
  split at h
  · rename_i hmax
    obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
    exact Or.inl ⟨hmax, hl, hr⟩
  · split at h
    · rename_i hmin
      obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
      exact Or.inr ⟨hmin, hl, hr⟩
    · simp [linPlanEmpty] at h

theorem linEqReifDecidePlan_prunes_cases {r : Nat} {terms : List LinTerm} {b : Int}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linEqReifDecidePlan r terms b).prunes) :
    (linTotalMin terms = b ∧ linTotalMax terms = b ∧ l = posBool r true ∧
      reason = linConflictLits terms ++ linMaxLits terms ++ [posBool r true]) ∨
    (b < linTotalMin terms ∧ l = posBool r false ∧
      reason = linConflictLits terms ++ [posBool r false]) ∨
    (linTotalMax terms < b ∧ l = posBool r false ∧
      reason = linMaxLits terms ++ [posBool r false]) := by
  unfold linEqReifDecidePlan at h
  split at h
  · rename_i hboth
    obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
    exact Or.inl ⟨hboth.1, hboth.2, hl, hr⟩
  · split at h
    · rename_i hmin
      obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
      exact Or.inr (Or.inl ⟨hmin, hl, hr⟩)
    · split at h
      · rename_i hmax
        obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
        exact Or.inr (Or.inr ⟨hmax, hl, hr⟩)
      · simp [linPlanEmpty] at h

theorem linNeReifDecidePlan_prunes_cases {r : Nat} {terms : List LinTerm} {b : Int}
    {l : Literal} {reason : Clause}
    (h : (l, reason) ∈ (linNeReifDecidePlan r terms b).prunes) :
    (b < linTotalMin terms ∧ l = posBool r true ∧
      reason = linConflictLits terms ++ [posBool r true]) ∨
    (linTotalMax terms < b ∧ l = posBool r true ∧
      reason = linMaxLits terms ++ [posBool r true]) ∨
    (linTotalMin terms = b ∧ linTotalMax terms = b ∧ l = posBool r false ∧
      reason = linConflictLits terms ++ linMaxLits terms ++ [posBool r false]) := by
  unfold linNeReifDecidePlan at h
  split at h
  · rename_i hmin
    obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
    exact Or.inl ⟨hmin, hl, hr⟩
  · split at h
    · rename_i hmax
      obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
      exact Or.inr (Or.inl ⟨hmax, hl, hr⟩)
    · split at h
      · rename_i hboth
        obtain ⟨hl, hr⟩ := linPlanSingle_prunes h
        exact Or.inr (Or.inr ⟨hboth.1, hboth.2, hl, hr⟩)
      · simp [linPlanEmpty] at h

/-! ### `linLeReif` output contracts -/

theorem linLeReifOutWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : linLeReifOutWith p T coeffs is b r view hmem hsize bds hbds hslots = .conflict ec) :
    ∃ rb : Bool,
      (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
      (∃ ls0,
        (if rb then linLePlan (linTerms coeffs.toArray is.toArray bds) b
         else linGePlan (linTerms coeffs.toArray is.toArray bds) (b + 1)).conflict? =
          some ls0 ∧
        T.decodeClause ec.lits = ls0 ++ [posBool r (!rb)] ∧
        Entailed p (T.decodeClause ec.lits) ∧
        (∀ l ∈ T.decodeClause ec.lits,
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false)) := by
  unfold linLeReifOutWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · rename_i htrue
      obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
      obtain ⟨ls0, h0, hlsEq⟩ := linPlanAppendLit_conf_mem hls
      have h0' : (linLePlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          some ls0 := by simpa using h0
      obtain ⟨hconf, hls0⟩ := linLePlan_conflict_cases h0'
      refine ⟨true, htrue, ls0, by simpa using h0', ?_, ?_, ?_⟩
      · rw [hdec, hlsEq]; simp
      · rw [hdec]; exact hent
      · intro l hl
        rw [hdec, hlsEq] at hl
        rcases List.mem_append.mp hl with hl0 | hlLit
        · rw [hls0] at hl0
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
          simpa [atomSlot_linMinNegLit] using
            linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
        · rw [List.mem_singleton.mp hlLit]
          simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
            (d := view.doms.getD r DomC.empty) htrue
    · split at h
      · rename_i hfalse
        obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
        obtain ⟨ls0, h0, hlsEq⟩ := linPlanAppendLit_conf_mem hls
        have h0' : (linGePlan (linTerms coeffs.toArray is.toArray bds) (b + 1)).conflict? =
            some ls0 := by simpa using h0
        obtain ⟨hconf, hls0⟩ := linGePlan_conflict_cases h0'
        refine ⟨false, hfalse, ls0, by simpa using h0', ?_, ?_, ?_⟩
        · rw [hdec, hlsEq]; simp
        · rw [hdec]; exact hent
        · intro l hl
          rw [hdec, hlsEq] at hl
          rcases List.mem_append.mp hl with hl0 | hlLit
          · rw [hls0] at hl0
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
            simpa [atomSlot_linMaxNegLit] using
              linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · rw [List.mem_singleton.mp hlLit]
            simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
              (d := view.doms.getD r DomC.empty) hfalse
      · exfalso
        obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
        rw [linLeReifDecidePlan_conflict_none r
          (linTerms coeffs.toArray is.toArray bds) b] at hls
        cases hls

theorem linPlanAppendLit_conflict_none {plan : LinPlan} {l : Literal}
    (h : (linPlanAppendLit plan l).conflict? = none) : plan.conflict? = none := by
  cases hc : plan.conflict? with
  | none => rfl
  | some ls =>
      rw [linPlanAppendLit, hc] at h
      simp at h

theorem linLeReifOutWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : linLeReifOutWith p T coeffs is b r view hmem hsize bds hbds hslots = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        ((∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
            ∃ (l0 : Literal) (reason0 : Clause),
              (l0, reason0) ∈
                (if rb then linLePlan terms b else linGePlan terms (b + 1)).prunes ∧
              l = l0 ∧ reason = reason0 ++ [posBool r (!rb)]) ∨
          ((view.doms.getD r DomC.empty).evalLit (posBool r true) = none ∧
            (l, reason) ∈ (linLeReifDecidePlan r terms b).prunes)) ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linLeReifOutWith at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · rename_i htrue
      obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
      have hconfInner : (linLePlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          none := linPlanAppendLit_conflict_none hconf
      have hnot := linLePlan_conflict_none_cases hconfInner
      have hb : linTotalMin (linTerms coeffs.toArray is.toArray bds) ≤ b := by omega
      refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
      intro q hq
      obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
      obtain ⟨reason0, hpr0, hreason⟩ := linPlanAppendLit_prunes_mem hpr
      have hpr0' : (l, reason0) ∈ linPrunes (linTerms coeffs.toArray is.toArray bds) b := by
        unfold linLePlan at hpr0
        split at hpr0
        · simp at hpr0
        · exact hpr0
      refine ⟨l, reason, Or.inl ⟨true, htrue, l, reason0, hpr0, rfl, hreason⟩,
        hlit, hdec, hent, ?_, ?_⟩
      · exact linPrune_lit_evalLit_none p coeffs is b view hsize bds hbds hWF hb hpr0'
      · intro q' hq' hne
        rw [hreason] at hq'
        rcases List.mem_append.mp hq' with hq0 | hqlit
        · exact linPrune_other_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
            hpr0' q' hq0 hne
        · rw [List.mem_singleton.mp hqlit]
          simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
            (d := view.doms.getD r DomC.empty) htrue
    · split at h
      · rename_i hfalse
        obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
        have hconfInner :
            (linGePlan (linTerms coeffs.toArray is.toArray bds) (b + 1)).conflict? = none :=
          linPlanAppendLit_conflict_none hconf
        have hnot := linGePlan_conflict_none_cases hconfInner
        have hb : b + 1 ≤ linTotalMax (linTerms coeffs.toArray is.toArray bds) := by omega
        refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
        intro q hq
        obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
        obtain ⟨reason0, hpr0, hreason⟩ := linPlanAppendLit_prunes_mem hpr
        have hpr0' : (l, reason0) ∈
            linPrunesGe (linTerms coeffs.toArray is.toArray bds) (b + 1) := by
          unfold linGePlan at hpr0
          split at hpr0
          · simp at hpr0
          · exact hpr0
        refine ⟨l, reason, Or.inl ⟨false, hfalse, l, reason0, hpr0, rfl, hreason⟩,
          hlit, hdec, hent, ?_, ?_⟩
        · exact linPruneGe_lit_evalLit_none p coeffs is (b + 1) view hsize bds hbds hWF hb hpr0'
        · intro q' hq' hne
          rw [hreason] at hq'
          rcases List.mem_append.mp hq' with hq0 | hqlit
          · exact linPruneGe_other_lits_evalLit_false p coeffs is (b + 1) view hsize bds hbds hWF
              hpr0' q' hq0 hne
          · rw [List.mem_singleton.mp hqlit]
            simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
              (d := view.doms.getD r DomC.empty) hfalse
      · have hdNone : (view.doms.getD r DomC.empty).evalLit (posBool r true) = none :=
          domC_evalLit_posBool_none_of_not (by assumption) (by assumption)
        obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
        refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
        intro q hq
        obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
        rcases linLeReifDecidePlan_prunes_cases hpr with
          ⟨hmax, hl, hr⟩ | ⟨hmin, hl, hr⟩
        · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
          · rw [hl]
            exact domC_evalLit_posBool_none_of_none hdNone (b := true)
          · intro q' hq' hne
            rw [hr] at hq'
            rcases List.mem_append.mp hq' with hq0 | hqlit
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq0
              simpa [atomSlot_linMaxNegLit] using
                linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
            · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)
        · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
          · rw [hl]
            exact domC_evalLit_posBool_none_of_none hdNone (b := false)
          · intro q' hq' hne
            rw [hr] at hq'
            rcases List.mem_append.mp hq' with hq0 | hqlit
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq0
              simpa [atomSlot_linMinNegLit] using
                linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
            · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)

theorem linEqReifOutWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : linEqReifOutWith p T coeffs is b r view hmem hsize bds hbds hslots = .conflict ec) :
    ∃ rb : Bool,
      (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
      (∃ ls0,
        (if rb then linEqPlan (linTerms coeffs.toArray is.toArray bds) b
         else linNePlan (linTerms coeffs.toArray is.toArray bds) b
           (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? =
          some ls0 ∧
        T.decodeClause ec.lits = ls0 ++ [posBool r (!rb)] ∧
        Entailed p (T.decodeClause ec.lits) ∧
        (∀ l ∈ T.decodeClause ec.lits,
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false)) := by
  unfold linEqReifOutWith at h
  dsimp only at h
  split at h
  · rename_i htrue
    obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
    obtain ⟨ls0, h0, hlsEq⟩ := linPlanAppendLit_conf_mem hls
    have h0' : (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
        some ls0 := by simpa using h0
    refine ⟨true, htrue, ls0, by simpa using h0', ?_, ?_, ?_⟩
    · rw [hdec, hlsEq]; simp
    · rw [hdec]; exact hent
    · intro l hl
      rw [hdec, hlsEq] at hl
      rcases List.mem_append.mp hl with hl0 | hlLit
      · rcases linEqPlan_conflict_cases h0' with ⟨hconf, hls0⟩ | ⟨hconf, hls0⟩
        · rw [hls0] at hl0
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
          simpa [atomSlot_linMinNegLit] using
            linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
        · rw [hls0] at hl0
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
          simpa [atomSlot_linMaxNegLit] using
            linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
      · rw [List.mem_singleton.mp hlLit]
        simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
          (d := view.doms.getD r DomC.empty) htrue
  · split at h
    · rename_i hfalse
      obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
      obtain ⟨ls0, h0, hlsEq⟩ := linPlanAppendLit_conf_mem hls
      have h0' : (linNePlan (linTerms coeffs.toArray is.toArray bds) b
          (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? =
          some ls0 := by simpa using h0
      obtain ⟨hall, hdotlo, hls0⟩ := linNePlan_conflict_cases h0'
      refine ⟨false, hfalse, ls0, by simpa using h0', ?_, ?_, ?_⟩
      · rw [hdec, hlsEq]; simp
      · rw [hdec]; exact hent
      · intro l hl
        rw [hdec, hlsEq] at hl
        rcases List.mem_append.mp hl with hl0 | hlLit
        · rw [hls0] at hl0
          obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
          have htmem : t.s ∈ is.toArray.toList := by
            have := linTerms_slot_mem_is hsize hbds ht
            simpa using this
          have hkind := viewIntKindB_spec hguard htmem
          have hwf := hWF.dom_wf htmem
          obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds ht
          have hfix := linNonFixedIndices_nil_spec hall t ht
          simpa [posNe, atomSlot] using DomC.evalLit_posNe_intKind hwf hkind hlo hhi hfix
        · rw [List.mem_singleton.mp hlLit]
          simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
            (d := view.doms.getD r DomC.empty) hfalse
    · exfalso
      obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
      rw [linEqReifDecidePlan_conflict_none r
        (linTerms coeffs.toArray is.toArray bds) b] at hls
      cases hls

theorem linEqReifOutWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : linEqReifOutWith p T coeffs is b r view hmem hsize bds hbds hslots = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        ((∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
            ∃ (l0 : Literal) (reason0 : Clause),
              (l0, reason0) ∈
                (if rb then linEqPlan terms b
                 else linNePlan terms b
                   (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).prunes ∧
              l = l0 ∧ reason = reason0 ++ [posBool r (!rb)]) ∨
          ((view.doms.getD r DomC.empty).evalLit (posBool r true) = none ∧
            (l, reason) ∈ (linEqReifDecidePlan r terms b).prunes)) ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linEqReifOutWith at h
  dsimp only at h
  split at h
  · rename_i htrue
    obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
    have hconfInner : (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
        none := linPlanAppendLit_conflict_none hconf
    obtain ⟨hnotmin, hnotmax⟩ := linEqPlan_conflict_none_cases hconfInner
    refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
    intro q hq
    obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
    obtain ⟨reason0, hpr0, hreason⟩ := linPlanAppendLit_prunes_mem hpr
    have hcases := linEqPlan_prunes_cases hpr0
    refine ⟨l, reason, Or.inl ⟨true, htrue, l, reason0, hpr0, rfl, hreason⟩,
      hlit, hdec, hent, ?_, ?_⟩
    · rcases hcases with hprMin | hprGe
      · exact linPrune_lit_evalLit_none p coeffs is b view hsize bds hbds hWF
          (by omega) hprMin
      · exact linPruneGe_lit_evalLit_none p coeffs is b view hsize bds hbds hWF
          (by omega) hprGe
    · intro q' hq' hne
      rw [hreason] at hq'
      rcases List.mem_append.mp hq' with hq0 | hqlit
      · rcases hcases with hprMin | hprGe
        · exact linPrune_other_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
            hprMin q' hq0 hne
        · exact linPruneGe_other_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
            hprGe q' hq0 hne
      · rw [List.mem_singleton.mp hqlit]
        simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
          (d := view.doms.getD r DomC.empty) htrue
  · split at h
    · rename_i hfalse
      obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
      refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
      intro q hq
      obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
      obtain ⟨reason0, hpr0, hreason⟩ := linPlanAppendLit_prunes_mem hpr
      have hpr0' : (l, reason0) ∈
          (linNePlan (linTerms coeffs.toArray is.toArray bds) b
            (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).prunes := by
        simpa using hpr0
      obtain ⟨i, t, hnf, hterm, hc, hl, heq, hev, hr⟩ :=
        linNePlan_prunes_cases hpr0'
      have hr' : reason0 =
          linFixedLits ((linTerms coeffs.toArray is.toArray bds).eraseIdx i) ++ [l] := by
        simpa using hr
      refine ⟨l, reason, Or.inl ⟨false, hfalse, l, reason0, by simpa using hpr0, rfl, hreason⟩,
        hlit, hdec, hent, ?_, ?_⟩
      · have hev' : (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none := by
          simpa [hl] using hev
        exact hev'
      · intro q' hq' hne
        rw [hreason] at hq'
        rcases List.mem_append.mp hq' with hq0 | hqlit
        · rw [hr'] at hq0
          rcases List.mem_append.mp hq0 with hqfixed | hql
          · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hqfixed
            have hu' : u ∈ linTerms coeffs.toArray is.toArray bds :=
              List.mem_of_mem_eraseIdx hu
            have humem : u.s ∈ is.toArray.toList := by
              have := linTerms_slot_mem_is hsize hbds hu'
              simpa using this
            have hkind := viewIntKindB_spec hguard humem
            have hwf := hWF.dom_wf humem
            obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds hu'
            have hfix := linNonFixedIndices_singleton_fixed_erase hnf u hu
            simpa [posNe, atomSlot] using DomC.evalLit_posNe_intKind hwf hkind hlo hhi hfix
          · exact absurd (List.mem_singleton.mp hql) hne
        · rw [List.mem_singleton.mp hqlit]
          simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
            (d := view.doms.getD r DomC.empty) hfalse
    · have hdNone : (view.doms.getD r DomC.empty).evalLit (posBool r true) = none :=
        domC_evalLit_posBool_none_of_not (by assumption) (by assumption)
      obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
      refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
      intro q hq
      obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
      rcases linEqReifDecidePlan_prunes_cases hpr with
        ⟨hmin, hmax, hl, hr⟩ | ⟨hmin, hl, hr⟩ | ⟨hmax, hl, hr⟩
      · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
        · rw [hl]
          exact domC_evalLit_posBool_none_of_none hdNone (b := true)
        · intro q' hq' hne
          rw [hr] at hq'
          rcases List.mem_append.mp hq' with hq0 | hqlit
          · rcases List.mem_append.mp hq0 with hqc | hqm
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hqc
              simpa [atomSlot_linMinNegLit] using
                linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hqm
              simpa [atomSlot_linMaxNegLit] using
                linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)
      · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
        · rw [hl]
          exact domC_evalLit_posBool_none_of_none hdNone (b := false)
        · intro q' hq' hne
          rw [hr] at hq'
          rcases List.mem_append.mp hq' with hq0 | hqlit
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq0
            simpa [atomSlot_linMinNegLit] using
              linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)
      · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
        · rw [hl]
          exact domC_evalLit_posBool_none_of_none hdNone (b := false)
        · intro q' hq' hne
          rw [hr] at hq'
          rcases List.mem_append.mp hq' with hq0 | hqlit
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq0
            simpa [atomSlot_linMaxNegLit] using
              linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)

theorem linNeReifOutWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : linNeReifOutWith p T coeffs is b r view hmem hsize bds hbds hslots = .conflict ec) :
    ∃ rb : Bool,
      (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
      (∃ ls0,
        (if rb then linNePlan (linTerms coeffs.toArray is.toArray bds) b
           (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)
         else linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          some ls0 ∧
        T.decodeClause ec.lits = ls0 ++ [posBool r (!rb)] ∧
        Entailed p (T.decodeClause ec.lits) ∧
        (∀ l ∈ T.decodeClause ec.lits,
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false)) := by
  unfold linNeReifOutWith at h
  dsimp only at h
  split at h
  · rename_i htrue
    obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
    obtain ⟨ls0, h0, hlsEq⟩ := linPlanAppendLit_conf_mem hls
    have h0' : (linNePlan (linTerms coeffs.toArray is.toArray bds) b
        (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? =
        some ls0 := by simpa using h0
    obtain ⟨hall, hdotlo, hls0⟩ := linNePlan_conflict_cases h0'
    refine ⟨true, htrue, ls0, by simpa using h0', ?_, ?_, ?_⟩
    · rw [hdec, hlsEq]; simp
    · rw [hdec]; exact hent
    · intro l hl
      rw [hdec, hlsEq] at hl
      rcases List.mem_append.mp hl with hl0 | hlLit
      · rw [hls0] at hl0
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
        have htmem : t.s ∈ is.toArray.toList := by
          have := linTerms_slot_mem_is hsize hbds ht
          simpa using this
        have hkind := viewIntKindB_spec hguard htmem
        have hwf := hWF.dom_wf htmem
        obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds ht
        have hfix := linNonFixedIndices_nil_spec hall t ht
        simpa [posNe, atomSlot] using DomC.evalLit_posNe_intKind hwf hkind hlo hhi hfix
      · rw [List.mem_singleton.mp hlLit]
        simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
          (d := view.doms.getD r DomC.empty) htrue
  · split at h
    · rename_i hfalse
      obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
      obtain ⟨ls0, h0, hlsEq⟩ := linPlanAppendLit_conf_mem hls
      have h0' : (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          some ls0 := by simpa using h0
      refine ⟨false, hfalse, ls0, by simpa using h0', ?_, ?_, ?_⟩
      · rw [hdec, hlsEq]; simp
      · rw [hdec]; exact hent
      · intro l hl
        rw [hdec, hlsEq] at hl
        rcases List.mem_append.mp hl with hl0 | hlLit
        · rcases linEqPlan_conflict_cases h0' with ⟨hconf, hls0⟩ | ⟨hconf, hls0⟩
          · rw [hls0] at hl0
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
            simpa [atomSlot_linMinNegLit] using
              linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · rw [hls0] at hl0
            obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl0
            simpa [atomSlot_linMaxNegLit] using
              linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
        · rw [List.mem_singleton.mp hlLit]
          simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
            (d := view.doms.getD r DomC.empty) hfalse
    · exfalso
      obtain ⟨ls, hls, hdec, hent⟩ := linPlanOut_run_conflict p T _ _ _ h
      rw [linNeReifDecidePlan_conflict_none r
        (linTerms coeffs.toArray is.toArray bds) b] at hls
      cases hls

theorem linNeReifOutWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hslots : slotsIntB p is = true)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : linNeReifOutWith p T coeffs is b r view hmem hsize bds hbds hslots = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        ((∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
            ∃ (l0 : Literal) (reason0 : Clause),
              (l0, reason0) ∈
                (if rb then linNePlan terms b
                   (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)
                 else linEqPlan terms b).prunes ∧
              l = l0 ∧ reason = reason0 ++ [posBool r (!rb)]) ∨
          ((view.doms.getD r DomC.empty).evalLit (posBool r true) = none ∧
            (l, reason) ∈ (linNeReifDecidePlan r terms b).prunes)) ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linNeReifOutWith at h
  dsimp only at h
  split at h
  · rename_i htrue
    obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
    refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
    intro q hq
    obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
    obtain ⟨reason0, hpr0, hreason⟩ := linPlanAppendLit_prunes_mem hpr
    have hpr0' : (l, reason0) ∈
        (linNePlan (linTerms coeffs.toArray is.toArray bds) b
          (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).prunes := by
      simpa using hpr0
    obtain ⟨i, t, hnf, hterm, hc, hl, heq, hev, hr⟩ :=
      linNePlan_prunes_cases hpr0'
    have hr' : reason0 =
        linFixedLits ((linTerms coeffs.toArray is.toArray bds).eraseIdx i) ++ [l] := by
      simpa using hr
    refine ⟨l, reason, Or.inl ⟨true, htrue, l, reason0, by simpa using hpr0, rfl, hreason⟩,
      hlit, hdec, hent, ?_, ?_⟩
    · simpa [hl] using hev
    · intro q' hq' hne
      rw [hreason] at hq'
      rcases List.mem_append.mp hq' with hq0 | hqlit
      · rw [hr'] at hq0
        rcases List.mem_append.mp hq0 with hqfixed | hql
        · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hqfixed
          have hu' : u ∈ linTerms coeffs.toArray is.toArray bds :=
            List.mem_of_mem_eraseIdx hu
          have humem : u.s ∈ is.toArray.toList := by
            have := linTerms_slot_mem_is hsize hbds hu'
            simpa using this
          have hkind := viewIntKindB_spec hguard humem
          have hwf := hWF.dom_wf humem
          obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds hu'
          have hfix := linNonFixedIndices_singleton_fixed_erase hnf u hu
          simpa [posNe, atomSlot] using DomC.evalLit_posNe_intKind hwf hkind hlo hhi hfix
        · exact absurd (List.mem_singleton.mp hql) hne
      · rw [List.mem_singleton.mp hqlit]
        simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
          (d := view.doms.getD r DomC.empty) htrue
  · split at h
    · rename_i hfalse
      obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
      have hconfInner : (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? =
          none := linPlanAppendLit_conflict_none hconf
      obtain ⟨hnotmin, hnotmax⟩ := linEqPlan_conflict_none_cases hconfInner
      refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
      intro q hq
      obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
      obtain ⟨reason0, hpr0, hreason⟩ := linPlanAppendLit_prunes_mem hpr
      have hcases := linEqPlan_prunes_cases hpr0
      refine ⟨l, reason, Or.inl ⟨false, hfalse, l, reason0, hpr0, rfl, hreason⟩,
        hlit, hdec, hent, ?_, ?_⟩
      · rcases hcases with hprMin | hprGe
        · exact linPrune_lit_evalLit_none p coeffs is b view hsize bds hbds hWF
            (by omega) hprMin
        · exact linPruneGe_lit_evalLit_none p coeffs is b view hsize bds hbds hWF
            (by omega) hprGe
      · intro q' hq' hne
        rw [hreason] at hq'
        rcases List.mem_append.mp hq' with hq0 | hqlit
        · rcases hcases with hprMin | hprGe
          · exact linPrune_other_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
              hprMin q' hq0 hne
          · exact linPruneGe_other_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
              hprGe q' hq0 hne
        · rw [List.mem_singleton.mp hqlit]
          simpa [atomSlot, posBool] using domC_evalLit_posBool_compl
            (d := view.doms.getD r DomC.empty) hfalse
    · have hdNone : (view.doms.getD r DomC.empty).evalLit (posBool r true) = none :=
        domC_evalLit_posBool_none_of_not (by assumption) (by assumption)
      obtain ⟨hconf, _hne, hqfacts⟩ := linPlanOut_run_prune p T _ _ _ h
      refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
      intro q hq
      obtain ⟨l, reason, hpr, hlit, hdec, hent⟩ := hqfacts q hq
      rcases linNeReifDecidePlan_prunes_cases hpr with
        ⟨hmin, hl, hr⟩ | ⟨hmax, hl, hr⟩ | ⟨hminboth, hmaxboth, hl, hr⟩
      · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
        · rw [hl]
          exact domC_evalLit_posBool_none_of_none hdNone (b := true)
        · intro q' hq' hne
          rw [hr] at hq'
          rcases List.mem_append.mp hq' with hq0 | hqlit
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq0
            simpa [atomSlot_linMinNegLit] using
              linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)
      · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
        · rw [hl]
          exact domC_evalLit_posBool_none_of_none hdNone (b := true)
        · intro q' hq' hne
          rw [hr] at hq'
          rcases List.mem_append.mp hq' with hq0 | hqlit
          · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hq0
            simpa [atomSlot_linMaxNegLit] using
              linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)
      · refine ⟨l, reason, Or.inr ⟨hdNone, hpr⟩, hlit, hdec, hent, ?_, ?_⟩
        · rw [hl]
          exact domC_evalLit_posBool_none_of_none hdNone (b := false)
        · intro q' hq' hne
          rw [hr] at hq'
          rcases List.mem_append.mp hq' with hq0 | hqlit
          · rcases List.mem_append.mp hq0 with hqc | hqm
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hqc
              simpa [atomSlot_linMinNegLit] using
                linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
            · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hqm
              simpa [atomSlot_linMaxNegLit] using
                linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF t ht
          · exact absurd (List.mem_singleton.mp hqlit) (by rw [hl] at hne; exact hne)

/-- Membership-explicit bounded linear equality reification propagator. -/
def linEqReifPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints) : PropV2 p T :=
  let dc := DomConstraint.linEqReif coeffs is b r
  let cs := coeffs.toArray
  let slots := is.toArray
  let hslots := slotsIntB p is
  { vars := (dcSlotsFull dc).toArray
    events := slots.flatMap (fun s => #[(s, .bounds), (s, .fix)]) ++ #[(r, .fix)]
    run := fun view =>
      if hsize : cs.size = slots.size then
        match hbds : linExtractBounds view.doms slots with
        | none => .fix
        | some bds =>
            if _hslots : hslots = true then
              if _hguard : viewIntKindB view slots = true then
                linEqReifOutWith p T coeffs is b r view hmem hsize bds hbds _hslots
              else .fix
            else .fix
      else
        .fix }

theorem linEqReifPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linEqReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
        (∃ ls0,
          (if rb then linEqPlan terms b
           else linNePlan terms b
             (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? =
            some ls0 ∧
          T.decodeClause ec.lits = ls0 ++ [posBool r (!rb)]) ∧
        Entailed p (T.decodeClause ec.lits) ∧
        (∀ l ∈ T.decodeClause ec.lits,
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false)) := by
  unfold linEqReifPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      by_cases hslots' : slotsIntB p is = true
      · rw [dif_pos hslots'] at h
        by_cases hguard' : viewIntKindB view is.toArray = true
        · rw [dif_pos hguard'] at h
          obtain ⟨rb, hrb, hls0⟩ :=
            linEqReifOutWith_run_conflict p T coeffs is b r view hmem hsize' bds hbds
              hslots' hWF hguard' h
          obtain ⟨ls0, hls, hdec, hent, hfalse⟩ := hls0
          exact ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, rb, hrb,
            ⟨⟨ls0, hls, hdec⟩, hent, hfalse⟩⟩
        · rw [dif_neg hguard'] at h
          cases h
      · rw [dif_neg hslots'] at h
        cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linEqReifPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linEqReifPropWith p T coeffs is b r hmem).run view = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        ((∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
            ∃ (l0 : Literal) (reason0 : Clause),
              (l0, reason0) ∈
                (if rb then linEqPlan terms b
                 else linNePlan terms b
                   (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).prunes ∧
              l = l0 ∧ reason = reason0 ++ [posBool r (!rb)]) ∨
          ((view.doms.getD r DomC.empty).evalLit (posBool r true) = none ∧
            (l, reason) ∈ (linEqReifDecidePlan r terms b).prunes)) ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linEqReifPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      by_cases hslots' : slotsIntB p is = true
      · rw [dif_pos hslots'] at h
        by_cases hguard' : viewIntKindB view is.toArray = true
        · rw [dif_pos hguard'] at h
          obtain ⟨bds', terms, hbds', hterms, hq⟩ :=
            linEqReifOutWith_run_prune p T coeffs is b r view hmem hsize' bds hbds
              hslots' hWF hguard' h
          exact ⟨bds', terms, hbds', hterms, hq⟩
        · rw [dif_neg hguard'] at h
          cases h
      · rw [dif_neg hslots'] at h
        cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linEqReifPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linEqReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨bds, terms, hbds, hterms, rb, hrb, hls0, hent, hfalse⟩ :=
    linEqReifPropWith_run_conflict p T coeffs is b r view hmem hsize hWF hslots hguard h
  exact hent

theorem linEqReifPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linEqReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨bds, terms, hbds, hterms, rb, hrb, hls0, hent, hfalse⟩ :=
    linEqReifPropWith_run_conflict p T coeffs is b r view hmem hsize hWF hslots hguard h
  exact hfalse

theorem linEqReifPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linEqReifPropWith p T coeffs is b r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linEqReifPropWith_run_prune p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨l, reason, hsrc, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  rwa [hdec]

theorem linEqReifPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linEqReifPropWith p T coeffs is b r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linEqReifPropWith_run_prune p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨l, reason, hsrc, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

theorem linEqReifPropWith_run_fix_of_size_ne (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (_hmem : DomConstraint.linEqReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.length ≠ is.length) :
    (linEqReifPropWith p T coeffs is b r _hmem).run view = .fix := by
  unfold linEqReifPropWith
  dsimp only
  have hne : coeffs.toArray.size ≠ is.toArray.size := by
    simpa using hsize
  rw [dif_neg hne]

/-- Membership-explicit bounded linear inequality reification propagator. -/
def linLeReifPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints) : PropV2 p T :=
  let dc := DomConstraint.linLeReif coeffs is b r
  let cs := coeffs.toArray
  let slots := is.toArray
  let hslots := slotsIntB p is
  { vars := (dcSlotsFull dc).toArray
    events := slots.map (fun s => (s, .bounds)) ++ #[(r, .fix)]
    run := fun view =>
      if hsize : cs.size = slots.size then
        let d := view.doms.getD r DomC.empty
        match linTotals view.doms cs slots with
        | none => .fix
        | some (tmin, tmax) =>
          if linRowSkipTotalsB d r tmin tmax b then .fix
          else
            match hbds : linExtractBounds view.doms slots with
            | none => .fix
            | some bds =>
                if _hslots : hslots = true then
                  if _hguard : viewIntKindB view slots = true then
                    linLeReifOutWith p T coeffs is b r view hmem hsize bds hbds _hslots
                  else .fix
                else .fix
      else
        .fix }

theorem linLeReifPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linLeReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
        (∃ ls0,
          (if rb then linLePlan terms b else linGePlan terms (b + 1)).conflict? =
            some ls0 ∧
          T.decodeClause ec.lits = ls0 ++ [posBool r (!rb)] ∧
          Entailed p (T.decodeClause ec.lits) ∧
          (∀ l ∈ T.decodeClause ec.lits,
            (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false))) := by
  unfold linLeReifPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i tmin tmax htot
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i bds hbds
          obtain ⟨rb, hrb, hls0⟩ :=
            linLeReifOutWith_run_conflict p T coeffs is b r view hmem hsize' bds hbds
              hslots hWF hguard h
          obtain ⟨ls0, hls, hdec, hent, hfalse⟩ := hls0
          exact ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, rb, hrb,
            ⟨ls0, hls, hdec, hent, hfalse⟩⟩
  · rw [dif_neg hsize'] at h
    cases h

theorem linLeReifPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linLeReifPropWith p T coeffs is b r hmem).run view = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        ((∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
            ∃ (l0 : Literal) (reason0 : Clause),
              (l0, reason0) ∈
                (if rb then linLePlan terms b else linGePlan terms (b + 1)).prunes ∧
              l = l0 ∧ reason = reason0 ++ [posBool r (!rb)]) ∨
          ((view.doms.getD r DomC.empty).evalLit (posBool r true) = none ∧
            (l, reason) ∈ (linLeReifDecidePlan r terms b).prunes)) ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linLeReifPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i tmin tmax htot
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i bds hbds
          obtain ⟨bds', terms, hbds', hterms, hq⟩ :=
            linLeReifOutWith_run_prune p T coeffs is b r view hmem hsize' bds hbds
              hslots hWF hguard h
          exact ⟨bds', terms, hbds', hterms, hq⟩
  · rw [dif_neg hsize'] at h
    cases h

theorem linLeReifPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linLeReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨bds, terms, hbds, hterms, rb, hrb, hls0⟩ :=
    linLeReifPropWith_run_conflict p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨ls0, hls, hdec, hent, hfalse⟩ := hls0
  exact hent

theorem linLeReifPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linLeReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨bds, terms, hbds, hterms, rb, hrb, hls0⟩ :=
    linLeReifPropWith_run_conflict p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨ls0, hls, hdec, hent, hfalse⟩ := hls0
  exact hfalse

theorem linLeReifPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linLeReifPropWith p T coeffs is b r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linLeReifPropWith_run_prune p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨l, reason, hsrc, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  rwa [hdec]

theorem linLeReifPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linLeReifPropWith p T coeffs is b r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linLeReifPropWith_run_prune p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨l, reason, hsrc, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

theorem linLeReifPropWith_run_fix_of_size_ne (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (_hmem : DomConstraint.linLeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.length ≠ is.length) :
    (linLeReifPropWith p T coeffs is b r _hmem).run view = .fix := by
  unfold linLeReifPropWith
  dsimp only
  have hne : coeffs.toArray.size ≠ is.toArray.size := by
    simpa using hsize
  rw [dif_neg hne]

/-- Membership-explicit bounded linear disequality reification propagator. -/
def linNeReifPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints) : PropV2 p T :=
  let dc := DomConstraint.linNeReif coeffs is b r
  let cs := coeffs.toArray
  let slots := is.toArray
  let hslots := slotsIntB p is
  { vars := (dcSlotsFull dc).toArray
    events := slots.flatMap (fun s => #[(s, .bounds), (s, .fix)]) ++ #[(r, .fix)]
    run := fun view =>
      if hsize : cs.size = slots.size then
        match hbds : linExtractBounds view.doms slots with
        | none => .fix
        | some bds =>
            if _hslots : hslots = true then
              if _hguard : viewIntKindB view slots = true then
                linNeReifOutWith p T coeffs is b r view hmem hsize bds hbds _hslots
              else .fix
            else .fix
      else
        .fix }

theorem linNeReifPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linNeReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
        (∃ ls0,
          (if rb then linNePlan terms b
             (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)
           else linEqPlan terms b).conflict? = some ls0 ∧
          T.decodeClause ec.lits = ls0 ++ [posBool r (!rb)] ∧
          Entailed p (T.decodeClause ec.lits) ∧
          (∀ l ∈ T.decodeClause ec.lits,
            (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false))) := by
  unfold linNeReifPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      by_cases hslots' : slotsIntB p is = true
      · rw [dif_pos hslots'] at h
        by_cases hguard' : viewIntKindB view is.toArray = true
        · rw [dif_pos hguard'] at h
          obtain ⟨rb, hrb, hls0⟩ :=
            linNeReifOutWith_run_conflict p T coeffs is b r view hmem hsize' bds hbds
              hslots' hWF hguard' h
          obtain ⟨ls0, hls, hdec, hent, hfalse⟩ := hls0
          exact ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, rb, hrb,
            ⟨ls0, hls, hdec, hent, hfalse⟩⟩
        · rw [dif_neg hguard'] at h
          cases h
      · rw [dif_neg hslots'] at h
        cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linNeReifPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linNeReifPropWith p T coeffs is b r hmem).run view = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        ((∃ rb, (view.doms.getD r DomC.empty).evalLit (posBool r true) = some rb ∧
            ∃ (l0 : Literal) (reason0 : Clause),
              (l0, reason0) ∈
                (if rb then linNePlan terms b
                   (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)
                 else linEqPlan terms b).prunes ∧
              l = l0 ∧ reason = reason0 ++ [posBool r (!rb)]) ∨
          ((view.doms.getD r DomC.empty).evalLit (posBool r true) = none ∧
            (l, reason) ∈ (linNeReifDecidePlan r terms b).prunes)) ∧
        q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason ∧
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
        (∀ q' ∈ reason, q' ≠ l →
          (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linNeReifPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      by_cases hslots' : slotsIntB p is = true
      · rw [dif_pos hslots'] at h
        by_cases hguard' : viewIntKindB view is.toArray = true
        · rw [dif_pos hguard'] at h
          obtain ⟨bds', terms, hbds', hterms, hq⟩ :=
            linNeReifOutWith_run_prune p T coeffs is b r view hmem hsize' bds hbds
              hslots' hWF hguard' h
          exact ⟨bds', terms, hbds', hterms, hq⟩
        · rw [dif_neg hguard'] at h
          cases h
      · rw [dif_neg hslots'] at h
        cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linNeReifPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linNeReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨bds, terms, hbds, hterms, rb, hrb, ls0⟩ :=
    linNeReifPropWith_run_conflict p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨ls, hls, hdec, hent, hfalse⟩ := ls0
  exact hent

theorem linNeReifPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linNeReifPropWith p T coeffs is b r hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨bds, terms, hbds, hterms, rb, hrb, ls0⟩ :=
    linNeReifPropWith_run_conflict p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨ls, hls, hdec, hent, hfalse⟩ := ls0
  exact hfalse

theorem linNeReifPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linNeReifPropWith p T coeffs is b r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linNeReifPropWith_run_prune p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨l, reason, hsrc, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  rwa [hdec]

theorem linNeReifPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hslots : slotsIntB p is = true)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linNeReifPropWith p T coeffs is b r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linNeReifPropWith_run_prune p T coeffs is b r view hmem hsize hWF hslots hguard h
  obtain ⟨l, reason, hsrc, hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

theorem linNeReifPropWith_run_fix_of_size_ne (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat) (view : EngineView)
    (_hmem : DomConstraint.linNeReif coeffs is b r ∈ p.constraints)
    (hsize : coeffs.length ≠ is.length) :
    (linNeReifPropWith p T coeffs is b r _hmem).run view = .fix := by
  unfold linNeReifPropWith
  dsimp only
  have hne : coeffs.toArray.size ≠ is.toArray.size := by
    simpa using hsize
  rw [dif_neg hne]


end LeanFzn.Engine
