/-
Postscript: Generic set-membership propagator for `setInReifSlot`.

`propsOf` routed `setInReifSlot` to the generic checker, a sound no-op, so
`set_in_reif(x, S, b)` could not force `b` when `x` was fixed outside `S`
nor prune `x` when `b` was true.  This module adds a partial but sound
propagator: fixed-value rules for arbitrary constant sets, plus semantic
lemmas for interval sets that are not yet wired into `run`.

Dependencies: LeanFzn.Engine.Props.Order (literal/domain lemmas),
LeanFzn.Engine.Prop (`Entailed`, `EClause`).
DAG: LeanFzn.Engine.Props.Order -> LeanFzn.Engine.Props.SetIn.
-/
import LeanFzn.Engine.Props.Order
import LeanFzn.Engine.Proofs.PruneSound

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Semantic content of the reified membership -/

/-- Every accepted assignment reads the integer slot `i` and Boolean slot
`r`, and `r` holds exactly the membership truth value. -/
theorem setInReif_sem (p : CompiledProblem DomConstraint) {i : Nat}
    {s : IntSetValue} {r : Nat}
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints) :
    ∀ a, a ∈ allAssigns p.domains → accepts p a = true →
      ∃ (pv : Int) (rb : Bool), a[i]? = some (.int pv) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ s.Contains pv) := by
  intro a _ha hacc
  have hall : DomConstraint.satisfiedB (DomConstraint.setInReifSlot i s r) a = true := by
    unfold accepts at hacc
    exact List.all_eq_true.mp hacc _ hmem
  exact (DomConstraint.satisfiedB_iff _ a).mp hall

theorem setInReif_rTrue_of_fixed_contains (p : CompiledProblem DomConstraint)
    {i : Nat} {s : IntSetValue} {r : Nat} {pv : Int}
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (hpv : s.Contains pv) :
    Entailed p [posBool r true, posNe i pv] := by
  intro a ha hacc
  obtain ⟨p', rb, hi, hr, hiff⟩ := setInReif_sem p hmem a ha hacc
  by_cases hp : p' = pv
  · have hc : s.Contains p' := by rw [hp]; exact hpv
    have hrb : rb = true := hiff.mpr hc
    exact ⟨posBool r true, by simp,
      (eval_posBool_iff a r true).mpr (by rw [hr, hrb])⟩
  · exact ⟨posNe i pv, by simp,
      (eval_posNe_iff a i pv).mpr ⟨p', by simp [slotInt, hi, Value.intView], hp⟩⟩

theorem setInReif_rFalse_of_fixed_not_contains
    (p : CompiledProblem DomConstraint) {i : Nat} {s : IntSetValue}
    {r : Nat} {pv : Int}
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (hpv : ¬ s.Contains pv) :
    Entailed p [posBool r false, posNe i pv] := by
  intro a ha hacc
  obtain ⟨p', rb, hi, hr, hiff⟩ := setInReif_sem p hmem a ha hacc
  by_cases hp : p' = pv
  · have hnot : ¬ s.Contains p' := by rw [hp]; exact hpv
    have hrb : rb = false := by
      cases rb with
      | false => rfl
      | true => exact False.elim (hnot (hiff.mp rfl))
    exact ⟨posBool r false, by simp,
      (eval_posBool_iff a r false).mpr (by rw [hr, hrb])⟩
  · exact ⟨posNe i pv, by simp,
      (eval_posNe_iff a i pv).mpr ⟨p', by simp [slotInt, hi, Value.intView], hp⟩⟩

/-- Interval membership, activated `r = true`, excludes values below `lo`. -/
theorem setInReif_rFalse_of_interval_below
    (p : CompiledProblem DomConstraint) {i : Nat} {lo hi : Int} {r : Nat}
    {k : Int}
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (hk : k < lo) :
    Entailed p [posBool r false, negLe i k] := by
  intro a ha hacc
  obtain ⟨p', rb, hslot, hr, hiff⟩ :=
    setInReif_sem p hmem a ha hacc
  cases rb with
  | false =>
      exact ⟨posBool r false, by simp,
        (eval_posBool_iff a r false).mpr (by rw [hr])⟩
  | true =>
      have hc : (IntSetValue.interval lo hi).Contains p' := hiff.mp rfl
      have hge : lo ≤ p' := hc.1
      exact ⟨negLe i k, by simp,
        (eval_negLe_iff a i k).mpr
          ⟨p', by simp [slotInt, hslot, Value.intView], by omega⟩⟩

/-- Interval membership, activated `r = true`, excludes values above `hi`. -/
theorem setInReif_rFalse_of_interval_above
    (p : CompiledProblem DomConstraint) {i : Nat} {lo hi : Int} {r : Nat}
    {k : Int}
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (hk : hi ≤ k) :
    Entailed p [posBool r false, posLe i k] := by
  intro a ha hacc
  obtain ⟨p', rb, hi', hr, hiff⟩ :=
    setInReif_sem p hmem a ha hacc
  cases rb with
  | false =>
      exact ⟨posBool r false, by simp,
        (eval_posBool_iff a r false).mpr (by rw [hr])⟩
  | true =>
      have hc : (IntSetValue.interval lo hi).Contains p' := hiff.mp rfl
      have hle : p' ≤ hi := hc.2
      exact ⟨posLe i k, by simp,
        (eval_posLe_iff a i k).mpr
          ⟨p', by simp [slotInt, hi', Value.intView], by omega⟩⟩

/-- A domain known to lie inside an interval forces `r = true`. -/
theorem setInReif_rTrue_of_interval_inside
    (p : CompiledProblem DomConstraint) {i : Nat} {lo hi : Int} {r : Nat}
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints) :
    Entailed p [posBool r true, posLe i (lo - 1), negLe i hi] := by
  intro a ha hacc
  obtain ⟨p', rb, hi', hr, hiff⟩ :=
    setInReif_sem p hmem a ha hacc
  cases rb with
  | true =>
      exact ⟨posBool r true, by simp,
        (eval_posBool_iff a r true).mpr (by rw [hr])⟩
  | false =>
      have hnot : ¬ (IntSetValue.interval lo hi).Contains p' := by
        intro hc
        have : (false : Bool) = true := hiff.mpr hc
        exact Bool.noConfusion this
      simp only [IntSetValue.Contains] at hnot
      by_cases hlt : p' < lo
      · exact ⟨posLe i (lo - 1), by simp,
          (eval_posLe_iff a i (lo - 1)).mpr
            ⟨p', by simp [slotInt, hi', Value.intView], by omega⟩⟩
      · exact ⟨negLe i hi, by simp,
          (eval_negLe_iff a i hi).mpr
            ⟨p', by simp [slotInt, hi', Value.intView], by omega⟩⟩

/-! ## The propagator -/

/-- Reified membership with partial propagation.  The fixed-value rules
work for every constant set.  The interval lemmas below are available but
not yet called by `run`. -/
def setInReifFixedPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints) :
    PropV2 p T :=
  { vars := (dcSlotsFull (DomConstraint.setInReifSlot i s r)).toArray
    events := #[(i, .bounds), (i, .fix), (r, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dr := view.doms.getD r DomC.empty
      match di.fixedValue with
      | some (.int pv) =>
          match dr.fixedValue with
          | some (.bool true) =>
              if hc : s.Contains pv then .fix
              else .conflict (EClause.ofLiterals p T
                [posBool r false, posNe i pv]
                (setInReif_rFalse_of_fixed_not_contains p hmem hc))
          | some (.bool false) =>
              if hc : s.Contains pv then
                .conflict (EClause.ofLiterals p T
                  [posBool r true, posNe i pv]
                  (setInReif_rTrue_of_fixed_contains p hmem hc))
              else .fix
          | some (.int _) => .fix
          | some (.setOfInt _) => .fix
          | some (.array _) => .fix
          | none =>
              if hc : s.Contains pv then
                .prune #[(pLit (posBool r true), EClause.ofLiterals p T
                  [posBool r true, posNe i pv]
                  (setInReif_rTrue_of_fixed_contains p hmem hc))]
              else
                .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                  [posBool r false, posNe i pv]
                  (setInReif_rFalse_of_fixed_not_contains p hmem hc))]
      | _ => .fix }

theorem setInReifFixedPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (setInReifFixedPropWith p T i s r hmem).run view = .prune ps) :
    ∃ pv,
      (view.doms.getD i DomC.empty).fixedValue = some (.int pv) ∧
      (view.doms.getD r DomC.empty).fixedValue = none ∧
      ((s.Contains pv ∧
          PruneFacts p T ps (posBool r true)
            [posBool r true, posNe i pv]) ∨
        (¬ s.Contains pv ∧
          PruneFacts p T ps (posBool r false)
            [posBool r false, posNe i pv])) := by
  unfold setInReifFixedPropWith at h
  dsimp only at h
  split at h
  · rename_i pv hfix
    refine ⟨pv, hfix, ?_⟩
    split at h
    · rename_i hrt
      by_cases hc : s.Contains pv
      · rw [dif_pos hc] at h
        cases h
      · rw [dif_neg hc] at h
        cases h
    · rename_i hrf
      by_cases hc : s.Contains pv
      · rw [dif_pos hc] at h
        cases h
      · rw [dif_neg hc] at h
        cases h
    · cases h
    · cases h
    · cases h
    · rename_i hnone
      by_cases hc : s.Contains pv
      · rw [dif_pos hc] at h
        injection h with hps
        subst hps
        refine ⟨hnone, Or.inl ⟨hc, ?_⟩⟩
        intro q hq
        have hq' : q = (pLit (posBool r true), EClause.ofLiterals p T
            [posBool r true, posNe i pv]
            (setInReif_rTrue_of_fixed_contains p hmem hc)) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_, setInReif_rTrue_of_fixed_contains p hmem hc⟩
        change T.decodeClause
          ([posBool r true, posNe i pv].toArray.map pLit) =
          [posBool r true, posNe i pv]
        exact LitTable.decodeClause_map_pLit T _
      · rw [dif_neg hc] at h
        injection h with hps
        subst hps
        refine ⟨hnone, Or.inr ⟨hc, ?_⟩⟩
        intro q hq
        have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
            [posBool r false, posNe i pv]
            (setInReif_rFalse_of_fixed_not_contains p hmem hc)) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_, setInReif_rFalse_of_fixed_not_contains p hmem hc⟩
        change T.decodeClause
          ([posBool r false, posNe i pv].toArray.map pLit) =
          [posBool r false, posNe i pv]
        exact LitTable.decodeClause_map_pLit T _
  · cases h

theorem setInReifFixedPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (setInReifFixedPropWith p T i s r hmem).run view = .conflict ec) :
    ∃ pv,
      (view.doms.getD i DomC.empty).fixedValue = some (.int pv) ∧
      ((s.Contains pv ∧
          (view.doms.getD r DomC.empty).fixedValue = some (.bool false) ∧
          T.decodeClause ec.lits = [posBool r true, posNe i pv] ∧
          Entailed p [posBool r true, posNe i pv]) ∨
        (¬ s.Contains pv ∧
          (view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          T.decodeClause ec.lits = [posBool r false, posNe i pv] ∧
          Entailed p [posBool r false, posNe i pv])) := by
  unfold setInReifFixedPropWith at h
  dsimp only at h
  split at h
  · rename_i pv hfix
    refine ⟨pv, hfix, ?_⟩
    split at h
    · rename_i hrt
      by_cases hc : s.Contains pv
      · rw [dif_pos hc] at h
        cases h
      · rw [dif_neg hc] at h
        injection h with hec
        subst hec
        refine Or.inr ⟨hc, hrt, ?_, ?_⟩
        · change T.decodeClause
            ([posBool r false, posNe i pv].toArray.map pLit) =
            [posBool r false, posNe i pv]
          exact LitTable.decodeClause_map_pLit T _
        · exact setInReif_rFalse_of_fixed_not_contains p hmem hc
    · rename_i hrf
      by_cases hc : s.Contains pv
      · rw [dif_pos hc] at h
        injection h with hec
        subst hec
        refine Or.inl ⟨hc, hrf, ?_, ?_⟩
        · change T.decodeClause
            ([posBool r true, posNe i pv].toArray.map pLit) =
            [posBool r true, posNe i pv]
          exact LitTable.decodeClause_map_pLit T _
        · exact setInReif_rTrue_of_fixed_contains p hmem hc
      · rw [dif_neg hc] at h
        cases h
    · cases h
    · cases h
    · cases h
    · rename_i hnone
      by_cases hc : s.Contains pv
      · rw [dif_pos hc] at h
        cases h
      · rw [dif_neg hc] at h
        cases h
  · cases h

theorem setInReifFixedPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (setInReifFixedPropWith p T i s r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, hbranch⟩ :=
    setInReifFixedPropWith_run_conflict p T i s r hmem view h
  rcases hbranch with ⟨_, _, hdec, hent⟩ | ⟨_, _, hdec, hent⟩
  · rwa [hdec]
  · rwa [hdec]

theorem setInReifFixedPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ec : EClause p T}
    (h : (setInReifFixedPropWith p T i s r hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨pv, hfix, hbranch⟩ :=
    setInReifFixedPropWith_run_conflict p T i s r hmem view h
  rcases hbranch with ⟨hc, hrf, hdec, _⟩ | ⟨hc, hrt, hdec, _⟩
  · have hrf' : (view.doms[r]?.getD DomC.empty).fixedValue = some (.bool false) := by
      simpa [Array.getD_eq_getD_getElem?] using hrf
    rw [hdec]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simpa [atomSlot, posBool, DomC.evalLit, hrf']
    · simpa [atomSlot, posNe] using
        DomC.evalLit_posNe_false_of_fixed_intView hWFi hfix rfl
  · have hrt' : (view.doms[r]?.getD DomC.empty).fixedValue = some (.bool true) := by
      simpa [Array.getD_eq_getD_getElem?] using hrt
    rw [hdec]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · simpa [atomSlot, posBool, DomC.evalLit, hrt']
    · simpa [atomSlot, posNe] using
        DomC.evalLit_posNe_false_of_fixed_intView hWFi hfix rfl

theorem setInReifFixedPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (setInReifFixedPropWith p T i s r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨pv, _, _, hbranch⟩ :=
    setInReifFixedPropWith_run_prune p T i s r hmem view h
  rcases hbranch with ⟨hc, hfacts⟩ | ⟨hc, hfacts⟩
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem setInReifFixedPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (setInReifFixedPropWith p T i s r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨pv, hfix, hrnone, hbranch⟩ :=
    setInReifFixedPropWith_run_prune p T i s r hmem view h
  rcases hbranch with ⟨hc, hfacts⟩ | ⟨hc, hfacts⟩
  · obtain ⟨hlit, hdec, _⟩ := hfacts q hq
    constructor
    · rw [hlit]
      simpa [atomSlot, posBool] using
        DomC.evalLit_posBool_none_of_not_fixed
          (d := view.doms.getD r DomC.empty) (s := r) (b := true) hrnone
    · intro q' hq' hne
      rw [hlit] at hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd rfl hne
      · simpa [atomSlot, posNe] using
          DomC.evalLit_posNe_false_of_fixed_intView hWFi hfix rfl
  · obtain ⟨hlit, hdec, _⟩ := hfacts q hq
    constructor
    · rw [hlit]
      simpa [atomSlot, posBool] using
        DomC.evalLit_posBool_none_of_not_fixed
          (d := view.doms.getD r DomC.empty) (s := r) (b := false) hrnone
    · intro q' hq' hne
      rw [hlit] at hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd rfl hne
      · simpa [atomSlot, posNe] using
          DomC.evalLit_posNe_false_of_fixed_intView hWFi hfix rfl

theorem setInReifFixedPropWith_pruneSound (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints) :
    (setInReifFixedPropWith p T i s r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWFi : (view.doms.getD i DomC.empty).WF :=
    hWF.dom_wf (s := i) (by simp [setInReifFixedPropWith, dcSlotsFull])
  have hWFr : (view.doms.getD r DomC.empty).WF :=
    hWF.dom_wf (s := r) (by simp [setInReifFixedPropWith, dcSlotsFull])
  exact ⟨(setInReifFixedPropWith_prune_lit_none p T i s r hmem view hWFi hWFr hrun hq).1,
    (setInReifFixedPropWith_prune_lit_none p T i s r hmem view hWFi hWFr hrun hq).2⟩

/-! ## Interval rules

The fixed-value rules above handle every set when `x` is fixed.  For an
interval set they also let the propagator act on bounds: a domain disjoint
from the interval forces `r = false`, a domain inside it forces `r = true`,
and `r = true` prunes the two bounds of `x`. -/

/-- Interval membership with `r = true` implies the lower bound `x ≥ lo`. -/
theorem setInReif_interval_lower
    (p : CompiledProblem DomConstraint) {i : Nat} {lo hi : Int} {r : Nat}
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints) :
    Entailed p [negLe i (lo - 1), posBool r false] := by
  intro a ha hacc
  obtain ⟨p', rb, hslot, hr, hiff⟩ := setInReif_sem p hmem a ha hacc
  cases rb with
  | false =>
      exact ⟨posBool r false, by simp,
        (eval_posBool_iff a r false).mpr (by rw [hr])⟩
  | true =>
      have hc : (IntSetValue.interval lo hi).Contains p' := hiff.mp rfl
      have hge : lo ≤ p' := hc.1
      exact ⟨negLe i (lo - 1), by simp,
        (eval_negLe_iff a i (lo - 1)).mpr
          ⟨p', by simp [slotInt, hslot, Value.intView], by omega⟩⟩

/-- Interval membership with `r = true` implies the upper bound `x ≤ hi`. -/
theorem setInReif_interval_upper
    (p : CompiledProblem DomConstraint) {i : Nat} {lo hi : Int} {r : Nat}
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints) :
    Entailed p [posLe i hi, posBool r false] := by
  intro a ha hacc
  obtain ⟨p', rb, hi', hr, hiff⟩ := setInReif_sem p hmem a ha hacc
  cases rb with
  | false =>
      exact ⟨posBool r false, by simp,
        (eval_posBool_iff a r false).mpr (by rw [hr])⟩
  | true =>
      have hc : (IntSetValue.interval lo hi).Contains p' := hiff.mp rfl
      exact ⟨posLe i hi, by simp,
        (eval_posLe_iff a i hi).mpr
          ⟨p', by simp [slotInt, hi', Value.intView], hc.2⟩⟩

/-- The interval propagator: `r = true` bounds are intersected with `lo..hi`,
and the two Boolean truth values are forced when the domain is disjoint or
contained. -/
def setInReifIntervalPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints) :
    PropV2 p T :=
  { vars := (dcSlotsFull (DomConstraint.setInReifSlot i (.interval lo hi) r)).toArray
    events := #[(i, .bounds), (i, .fix), (r, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dr := view.doms.getD r DomC.empty
      match dr.fixedValue with
      | some (.bool true) =>
          match domBounds di with
          | some (l, h) =>
              if hlt : h < lo then
                .conflict (EClause.ofLiterals p T
                  [posBool r false, negLe i h]
                  (setInReif_rFalse_of_interval_below p hmem hlt))
              else if hgt : hi < l then
                .conflict (EClause.ofLiterals p T
                  [posBool r false, posLe i (l - 1)]
                  (setInReif_rFalse_of_interval_above p hmem (by omega)))
              else if hlow : l < lo then
                .prune #[(pLit (negLe i (lo - 1)), EClause.ofLiterals p T
                  [negLe i (lo - 1), posBool r false]
                  (setInReif_interval_lower p hmem))]
              else if hhigh : hi < h then
                .prune #[(pLit (posLe i hi), EClause.ofLiterals p T
                  [posLe i hi, posBool r false]
                  (setInReif_interval_upper p hmem))]
              else .fix
          | none => .fix
      | none =>
          match domBounds di with
          | some (l, h) =>
              if hlt : h < lo then
                .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                  [posBool r false, negLe i h]
                  (setInReif_rFalse_of_interval_below p hmem hlt))]
              else if hgt : hi < l then
                .prune #[(pLit (posBool r false), EClause.ofLiterals p T
                  [posBool r false, posLe i (l - 1)]
                  (setInReif_rFalse_of_interval_above p hmem (by omega)))]
              else if hin : lo ≤ l ∧ h ≤ hi then
                .prune #[(pLit (posBool r true), EClause.ofLiterals p T
                  [posBool r true, posLe i (lo - 1), negLe i hi]
                  (setInReif_rTrue_of_interval_inside p hmem))]
              else .fix
          | none => .fix
      | some (.bool false) => .fix
      | some (.int _) => .fix
      | some (.setOfInt _) => .fix
      | some (.array _) => .fix }

theorem setInReifIntervalPropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (setInReifIntervalPropWith p T i lo hi r hmem).run view = .prune ps) :
    ∃ l hgt : Int,
      domBounds (view.doms.getD i DomC.empty) = some (l, hgt) ∧
      (((view.doms.getD r DomC.empty).fixedValue = none ∧ hgt < lo ∧
          PruneFacts p T ps (posBool r false)
            [posBool r false, negLe i hgt]) ∨
        ((view.doms.getD r DomC.empty).fixedValue = none ∧ ¬ hgt < lo ∧ hi < l ∧
          PruneFacts p T ps (posBool r false)
            [posBool r false, posLe i (l - 1)]) ∨
        ((view.doms.getD r DomC.empty).fixedValue = none ∧ ¬ hgt < lo ∧ ¬ hi < l ∧
          lo ≤ l ∧ hgt ≤ hi ∧
          PruneFacts p T ps (posBool r true)
            [posBool r true, posLe i (lo - 1), negLe i hi]) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          ¬ hgt < lo ∧ ¬ hi < l ∧ l < lo ∧
          PruneFacts p T ps (negLe i (lo - 1))
            [negLe i (lo - 1), posBool r false]) ∨
        ((view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
          ¬ hgt < lo ∧ ¬ hi < l ∧ ¬ l < lo ∧ hi < hgt ∧
          PruneFacts p T ps (posLe i hi)
            [posLe i hi, posBool r false])) := by
  unfold setInReifIntervalPropWith at h
  dsimp only at h
  split at h
  · rename_i hrt
    split at h
    · rename_i l hgt hb
      by_cases hlt : hgt < lo
      · rw [dif_pos hlt] at h
        cases h
      · rw [dif_neg hlt] at h
        by_cases hgtc : hi < l
        · rw [dif_pos hgtc] at h
          cases h
        · rw [dif_neg hgtc] at h
          by_cases hlow : l < lo
          · rw [dif_pos hlow] at h
            injection h with hps
            subst hps
            refine ⟨l, hgt, hb, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
            refine ⟨hrt, hlt, hgtc, hlow, ?_⟩
            intro q hq
            have hq' : q = (pLit (negLe i (lo - 1)), EClause.ofLiterals p T
                [negLe i (lo - 1), posBool r false]
                (setInReif_interval_lower p hmem)) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_, setInReif_interval_lower p hmem⟩
            change T.decodeClause
              ([negLe i (lo - 1), posBool r false].toArray.map pLit) =
              [negLe i (lo - 1), posBool r false]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg hlow] at h
            by_cases hhigh : hi < hgt
            · rw [dif_pos hhigh] at h
              injection h with hps
              subst hps
              refine ⟨l, hgt, hb, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
              refine ⟨hrt, hlt, hgtc, hlow, hhigh, ?_⟩
              intro q hq
              have hq' : q = (pLit (posLe i hi), EClause.ofLiterals p T
                  [posLe i hi, posBool r false]
                  (setInReif_interval_upper p hmem)) := by
                simpa using hq
              subst hq'
              refine ⟨rfl, ?_, setInReif_interval_upper p hmem⟩
              change T.decodeClause
                ([posLe i hi, posBool r false].toArray.map pLit) =
                [posLe i hi, posBool r false]
              exact LitTable.decodeClause_map_pLit T _
            · rw [dif_neg hhigh] at h
              cases h
    · cases h
  · rename_i hrnone
    split at h
    · rename_i l hgt hb
      by_cases hlt : hgt < lo
      · rw [dif_pos hlt] at h
        injection h with hps
        subst hps
        refine ⟨l, hgt, hb, Or.inl ?_⟩
        refine ⟨hrnone, hlt, ?_⟩
        intro q hq
        have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
            [posBool r false, negLe i hgt]
            (setInReif_rFalse_of_interval_below p hmem hlt)) := by
          simpa using hq
        subst hq'
        refine ⟨rfl, ?_, setInReif_rFalse_of_interval_below p hmem hlt⟩
        change T.decodeClause
          ([posBool r false, negLe i hgt].toArray.map pLit) =
          [posBool r false, negLe i hgt]
        exact LitTable.decodeClause_map_pLit T _
      · rw [dif_neg hlt] at h
        by_cases hgtc : hi < l
        · rw [dif_pos hgtc] at h
          injection h with hps
          subst hps
          refine ⟨l, hgt, hb, Or.inr (Or.inl ?_)⟩
          refine ⟨hrnone, hlt, hgtc, ?_⟩
          intro q hq
          have hq' : q = (pLit (posBool r false), EClause.ofLiterals p T
              [posBool r false, posLe i (l - 1)]
              (setInReif_rFalse_of_interval_above p hmem (by omega))) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_,
            setInReif_rFalse_of_interval_above p hmem (by omega)⟩
          change T.decodeClause
            ([posBool r false, posLe i (l - 1)].toArray.map pLit) =
            [posBool r false, posLe i (l - 1)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hgtc] at h
          by_cases hin : lo ≤ l ∧ hgt ≤ hi
          · rw [dif_pos hin] at h
            injection h with hps
            subst hps
            refine ⟨l, hgt, hb, Or.inr (Or.inr (Or.inl ?_))⟩
            refine ⟨hrnone, hlt, hgtc, hin.1, hin.2, ?_⟩
            intro q hq
            have hq' : q = (pLit (posBool r true), EClause.ofLiterals p T
                [posBool r true, posLe i (lo - 1), negLe i hi]
                (setInReif_rTrue_of_interval_inside p hmem)) := by
              simpa using hq
            subst hq'
            refine ⟨rfl, ?_, setInReif_rTrue_of_interval_inside p hmem⟩
            change T.decodeClause
              ([posBool r true, posLe i (lo - 1), negLe i hi].toArray.map pLit) =
              [posBool r true, posLe i (lo - 1), negLe i hi]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg hin] at h
            cases h
    · cases h
  · cases h
  · cases h
  · cases h
  · cases h

theorem setInReifIntervalPropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (setInReifIntervalPropWith p T i lo hi r hmem).run view = .conflict ec) :
    (view.doms.getD r DomC.empty).fixedValue = some (.bool true) ∧
      ∃ l hgt : Int,
        domBounds (view.doms.getD i DomC.empty) = some (l, hgt) ∧
        ((hgt < lo ∧
            T.decodeClause ec.lits = [posBool r false, negLe i hgt]) ∨
          (¬ hgt < lo ∧ hi < l ∧
            T.decodeClause ec.lits = [posBool r false, posLe i (l - 1)])) := by
  unfold setInReifIntervalPropWith at h
  dsimp only at h
  split at h
  · rename_i hrt
    split at h
    · rename_i l hgt hb
      by_cases hlt : hgt < lo
      · rw [dif_pos hlt] at h
        injection h with hec
        subst hec
        refine ⟨hrt, l, hgt, hb, Or.inl ⟨hlt, ?_⟩⟩
        change T.decodeClause
          ([posBool r false, negLe i hgt].toArray.map pLit) =
          [posBool r false, negLe i hgt]
        exact LitTable.decodeClause_map_pLit T _
      · rw [dif_neg hlt] at h
        by_cases hgtc : hi < l
        · rw [dif_pos hgtc] at h
          injection h with hec
          subst hec
          refine ⟨hrt, l, hgt, hb, Or.inr ⟨hlt, hgtc, ?_⟩⟩
          change T.decodeClause
            ([posBool r false, posLe i (l - 1)].toArray.map pLit) =
            [posBool r false, posLe i (l - 1)]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hgtc] at h
          by_cases hlow : l < lo
          · rw [dif_pos hlow] at h
            cases h
          · rw [dif_neg hlow] at h
            by_cases hhigh : hi < hgt
            · rw [dif_pos hhigh] at h
              cases h
            · rw [dif_neg hhigh] at h
              cases h
    · cases h
  · split at h
    · rename_i l hgt hb
      by_cases hlt : hgt < lo
      · rw [dif_pos hlt] at h
        cases h
      · rw [dif_neg hlt] at h
        by_cases hgtc : hi < l
        · rw [dif_pos hgtc] at h
          cases h
        · rw [dif_neg hgtc] at h
          by_cases hin : lo ≤ l ∧ hgt ≤ hi
          · rw [dif_pos hin] at h
            cases h
          · rw [dif_neg hin] at h
            cases h
    · cases h
  · cases h
  · cases h
  · cases h
  · cases h

theorem setInReifIntervalPropWith_conflict_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (setInReifIntervalPropWith p T i lo hi r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨_, _, _, hb, hbranch⟩ :=
    setInReifIntervalPropWith_run_conflict p T i lo hi r hmem view h
  rcases hbranch with ⟨hlt, hdec⟩ | ⟨_, hgt, hdec⟩
  · rw [hdec]
    exact setInReif_rFalse_of_interval_below p hmem hlt
  · rw [hdec]
    exact setInReif_rFalse_of_interval_above p hmem (by omega)

theorem setInReifIntervalPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    {ec : EClause p T}
    (h : (setInReifIntervalPropWith p T i lo hi r hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  obtain ⟨hrt, l, hgt, hb, hbranch⟩ :=
    setInReifIntervalPropWith_run_conflict p T i lo hi r hmem view h
  obtain ⟨hlo, hhi⟩ := domBounds_spec hb
  have hle : l ≤ hgt :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hlo hhi
  rcases hbranch with ⟨hlt, hdec⟩ | ⟨hlt, hgtc, hdec⟩
  · rw [hdec]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simpa [atomSlot, posBool] using
        DomC.evalLit_posBool_false_of_fixed_other (d := view.doms.getD r DomC.empty)
          (s := r) (b := false) (c := true) hrt (by decide)
    · simpa [atomSlot, negLe] using
        evalLit_negLe_false_of_hi_le (d := view.doms.getD i DomC.empty)
          (s := i) (k := hgt) hlo hhi (Int.le_refl hgt) (by omega)
  · rw [hdec]
    intro q hq
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · simpa [atomSlot, posBool] using
        DomC.evalLit_posBool_false_of_fixed_other (d := view.doms.getD r DomC.empty)
          (s := r) (b := false) (c := true) hrt (by decide)
    · simpa [atomSlot, posLe] using
        evalLit_posLe_false_of_lo_gt (d := view.doms.getD i DomC.empty)
          (s := i) (k := l - 1) hlo hhi (by omega) (by omega)

theorem setInReifIntervalPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (setInReifIntervalPropWith p T i lo hi r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨_, _, _, hbranch⟩ :=
    setInReifIntervalPropWith_run_prune p T i lo hi r hmem view h
  rcases hbranch with ⟨_, _, hfacts⟩ | ⟨_, _, _, hfacts⟩ |
    ⟨_, _, _, _, _, hfacts⟩ | ⟨_, _, _, _, hfacts⟩ | ⟨_, _, _, _, _, hfacts⟩
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem setInReifIntervalPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints)
    (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (setInReifIntervalPropWith p T i lo hi r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨l, hgt, hb, hbranch⟩ :=
    setInReifIntervalPropWith_run_prune p T i lo hi r hmem view h
  obtain ⟨hlo, hhi⟩ := domBounds_spec hb
  have hle : l ≤ hgt :=
    DomC.lo?_le_hi? (view.doms.getD i DomC.empty) hWFi hlo hhi
  rcases hbranch with
    ⟨hrnone, hlt, hfacts⟩ |
    ⟨hrnone, hlt, hgtc, hfacts⟩ |
    ⟨hrnone, hlt, hgtc, hlin, hhin, hfacts⟩ |
    ⟨hrt, hlt, hgtc, hlow, hfacts⟩ |
    ⟨hrt, hlt, hgtc, hlow, hhigh, hfacts⟩
  · obtain ⟨hlit, hdec, _⟩ := hfacts q hq
    constructor
    · rw [hlit]
      simpa [atomSlot, posBool] using
        DomC.evalLit_posBool_none_of_not_fixed
          (d := view.doms.getD r DomC.empty) (s := r) (b := false) hrnone
    · intro q' hq' hne
      rw [hlit] at hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd rfl hne
      · simpa [atomSlot, negLe] using
          evalLit_negLe_false_of_hi_le (d := view.doms.getD i DomC.empty)
            (s := i) (k := hgt) hlo hhi (Int.le_refl hgt) (by omega)
  · obtain ⟨hlit, hdec, _⟩ := hfacts q hq
    constructor
    · rw [hlit]
      simpa [atomSlot, posBool] using
        DomC.evalLit_posBool_none_of_not_fixed
          (d := view.doms.getD r DomC.empty) (s := r) (b := false) hrnone
    · intro q' hq' hne
      rw [hlit] at hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd rfl hne
      · simpa [atomSlot, posLe] using
          evalLit_posLe_false_of_lo_gt (d := view.doms.getD i DomC.empty)
            (s := i) (k := l - 1) hlo hhi (by omega) (by omega)
  · obtain ⟨hlit, hdec, _⟩ := hfacts q hq
    constructor
    · rw [hlit]
      simpa [atomSlot, posBool] using
        DomC.evalLit_posBool_none_of_not_fixed
          (d := view.doms.getD r DomC.empty) (s := r) (b := true) hrnone
    · intro q' hq' hne
      rw [hlit] at hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl | rfl
      · exact absurd rfl hne
      · simpa [atomSlot, posLe] using
          evalLit_posLe_false_of_lo_gt (d := view.doms.getD i DomC.empty)
            (s := i) (k := lo - 1) hlo hhi (by omega) (by omega)
      · simpa [atomSlot, negLe] using
          evalLit_negLe_false_of_hi_le (d := view.doms.getD i DomC.empty)
            (s := i) (k := hi) hlo hhi (by omega) (by omega)
  · obtain ⟨hlit, hdec, _⟩ := hfacts q hq
    constructor
    · rw [hlit]
      simpa [atomSlot, negLe] using
        evalLit_negLe_none (d := view.doms.getD i DomC.empty)
          (s := i) (k := lo - 1) hlo hhi (by omega) (by omega)
    · intro q' hq' hne
      rw [hlit] at hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd rfl hne
      · simpa [atomSlot, posBool] using
          DomC.evalLit_posBool_false_of_fixed_other
            (d := view.doms.getD r DomC.empty) (s := r) (b := false) (c := true)
            hrt (by decide)
  · obtain ⟨hlit, hdec, _⟩ := hfacts q hq
    constructor
    · rw [hlit]
      simpa [atomSlot, posLe] using
        evalLit_posLe_none (d := view.doms.getD i DomC.empty)
          (s := i) (k := hi) hlo hhi (by omega) (by omega)
    · intro q' hq' hne
      rw [hlit] at hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · exact absurd rfl hne
      · simpa [atomSlot, posBool] using
          DomC.evalLit_posBool_false_of_fixed_other
            (d := view.doms.getD r DomC.empty) (s := r) (b := false) (c := true)
            hrt (by decide)

theorem setInReifIntervalPropWith_pruneSound (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (lo hi : Int) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i (.interval lo hi) r ∈ p.constraints) :
    (setInReifIntervalPropWith p T i lo hi r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWFi : (view.doms.getD i DomC.empty).WF :=
    hWF.dom_wf (s := i) (by simp [setInReifIntervalPropWith, dcSlotsFull])
  exact ⟨(setInReifIntervalPropWith_prune_lit_none p T i lo hi r hmem view
      hWFi hrun hq).1,
    (setInReifIntervalPropWith_prune_lit_none p T i lo hi r hmem view
      hWFi hrun hq).2⟩

/-! ## Combined propagator -/

/-- Fixed-value rules first; when they say `.fix` on an interval set, the
interval rules run. -/
def setInReifPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints) :
    PropV2 p T :=
  { vars := (dcSlotsFull (DomConstraint.setInReifSlot i s r)).toArray
    events := #[(i, .bounds), (i, .fix), (r, .fix)]
    run := fun view =>
      match hs : s with
      | .interval lo hi =>
          match (setInReifFixedPropWith p T i s r (by
            simpa [← hs] using hmem)).run view with
          | .fix =>
              (setInReifIntervalPropWith p T i lo hi r (by
                simpa [hs] using hmem)).run view
          | .prune ps => .prune ps
          | .conflict ec => .conflict ec
      | .enumeration _ =>
          (setInReifFixedPropWith p T i s r (by
            simpa [← hs] using hmem)).run view }

theorem setInReifPropWith_run_prune
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (setInReifPropWith p T i s r hmem).run view = .prune ps) :
    ((∃ (lo hi : Int) (hs : s = .interval lo hi),
        (setInReifFixedPropWith p T i s r hmem).run view = .fix ∧
        (setInReifIntervalPropWith p T i lo hi r (by
          simpa [hs] using hmem)).run view = .prune ps) ∨
      (setInReifFixedPropWith p T i s r hmem).run view = .prune ps) := by
  unfold setInReifPropWith at h
  dsimp only at h
  split at h
  · rename_i lo1 hi1 hmem2 heq2
    split at h
    · rename_i hfix
      exact Or.inl ⟨lo1, hi1, rfl, hfix, h⟩
    · rename_i hprune
      injection h with hps
      subst hps
      exact Or.inr hprune
    · cases h
  · rename_i values hs
    exact Or.inr h

theorem setInReifPropWith_run_conflict
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (setInReifPropWith p T i s r hmem).run view = .conflict ec) :
    ((∃ (lo hi : Int) (hs : s = .interval lo hi),
        (setInReifFixedPropWith p T i s r hmem).run view = .fix ∧
        (setInReifIntervalPropWith p T i lo hi r (by
          simpa [hs] using hmem)).run view = .conflict ec) ∨
      (setInReifFixedPropWith p T i s r hmem).run view = .conflict ec) := by
  unfold setInReifPropWith at h
  dsimp only at h
  split at h
  · rename_i lo1 hi1 hmem2 heq2
    split at h
    · rename_i hfix
      exact Or.inl ⟨lo1, hi1, rfl, hfix, h⟩
    · cases h
    · rename_i hconf
      injection h with hec
      subst hec
      exact Or.inr hconf
  · rename_i values hs
    exact Or.inr h

theorem setInReifPropWith_prune_reason_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ps : Array (PLit × EClause p T)}
    (h : (setInReifPropWith p T i s r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  rcases setInReifPropWith_run_prune p T i s r hmem view h with
    ⟨lo, hi, hs, _, hrun⟩ | hrun
  · exact setInReifIntervalPropWith_prune_reason_entailed p T i lo hi r
      (by simpa [hs] using hmem) view hrun hq
  · exact setInReifFixedPropWith_prune_reason_entailed p T i s r hmem view hrun hq

theorem setInReifPropWith_conflict_entailed
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView) {ec : EClause p T}
    (h : (setInReifPropWith p T i s r hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  rcases setInReifPropWith_run_conflict p T i s r hmem view h with
    ⟨lo, hi, hs, _, hrun⟩ | hrun
  · exact setInReifIntervalPropWith_conflict_entailed p T i lo hi r
      (by simpa [hs] using hmem) view hrun
  · exact setInReifFixedPropWith_conflict_entailed p T i s r hmem view hrun

theorem setInReifPropWith_prune_lit_none
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (setInReifPropWith p T i s r hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  rcases setInReifPropWith_run_prune p T i s r hmem view h with
    ⟨lo, hi, hs, _, hrun⟩ | hrun
  · exact setInReifIntervalPropWith_prune_lit_none p T i lo hi r
      (by simpa [hs] using hmem) view hWFi hrun hq
  · exact setInReifFixedPropWith_prune_lit_none p T i s r hmem view
      hWFi hWFr hrun hq

theorem setInReifPropWith_conflict_lits_false
    (p : CompiledProblem DomConstraint) (T : LitTable)
    (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints)
    (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFr : (view.doms.getD r DomC.empty).WF)
    {ec : EClause p T}
    (h : (setInReifPropWith p T i s r hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  rcases setInReifPropWith_run_conflict p T i s r hmem view h with
    ⟨lo, hi, hs, _, hrun⟩ | hrun
  · exact setInReifIntervalPropWith_conflict_lits_false p T i lo hi r
      (by simpa [hs] using hmem) view hWFi hrun
  · exact setInReifFixedPropWith_conflict_lits_false p T i s r hmem view
      hWFi hWFr hrun

theorem setInReifPropWith_pruneSound (p : CompiledProblem DomConstraint)
    (T : LitTable) (i : Nat) (s : IntSetValue) (r : Nat)
    (hmem : DomConstraint.setInReifSlot i s r ∈ p.constraints) :
    (setInReifPropWith p T i s r hmem).PruneSound := by
  intro view ps hWF hrun q hq
  have hWFi : (view.doms.getD i DomC.empty).WF :=
    hWF.dom_wf (s := i) (by simp [setInReifPropWith, dcSlotsFull])
  have hWFr : (view.doms.getD r DomC.empty).WF :=
    hWF.dom_wf (s := r) (by simp [setInReifPropWith, dcSlotsFull])
  exact ⟨(setInReifPropWith_prune_lit_none p T i s r hmem view hWFi hWFr hrun hq).1,
    (setInReifPropWith_prune_lit_none p T i s r hmem view hWFi hWFr hrun hq).2⟩

end LeanFzn.Engine
