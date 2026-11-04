/-
Purpose: LinearExt propagators: plans definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.LinearExt.Bounds
DAG: LeanFzn.Engine.Props.LinearExt.Bounds -> LeanFzn.Engine.Props.LinearExt.Plans.
-/
import LeanFzn.Engine.Props.LinearExt.Bounds

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Generic plans and their `PropOut` wrapper -/

/-- A view-independent propagation plan: at most one conflict clause and a
finite list of value prunings with decoded reasons. -/
structure LinPlan where
  conflict? : Option (List Literal)
  prunes : List (Literal × Clause)

/-- Turn a plan into a `PropOut`, attaching the supplied entailment proofs. -/
def linPlanOut (p : CompiledProblem DomConstraint) (T : LitTable) (plan : LinPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ l r, (l, r) ∈ plan.prunes → Entailed p r) : PropOut p T :=
  match hc : plan.conflict? with
  | some ls => .conflict (EClause.ofLiterals p T ls (hconf ls hc))
  | none =>
      match _hp : plan.prunes with
      | [] => .fix
      | _ :: _ =>
          .prune ((plan.prunes.attach.map fun q =>
            (pLit q.1.1,
              EClause.ofLiterals p T q.1.2
                (hprune q.1.1 q.1.2 q.2))).toArray)

theorem linPlanOut_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (plan : LinPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ l r, (l, r) ∈ plan.prunes → Entailed p r)
    {ec : EClause p T}
    (h : linPlanOut p T plan hconf hprune = .conflict ec) :
    ∃ ls, plan.conflict? = some ls ∧ T.decodeClause ec.lits = ls ∧
      Entailed p ls := by
  unfold linPlanOut at h
  split at h
  · rename_i ls hls
    injection h with hec
    subst hec
    exact ⟨ls, hls, LitTable.decodeClause_map_pLit T ls, hconf ls hls⟩
  · split at h <;> cases h

theorem linPlanOut_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (plan : LinPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ l r, (l, r) ∈ plan.prunes → Entailed p r)
    {ps : Array (PLit × EClause p T)}
    (h : linPlanOut p T plan hconf hprune = .prune ps) :
    plan.conflict? = none ∧ plan.prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (r : Clause),
        (l, r) ∈ plan.prunes ∧ q.1.lit = l ∧
          T.decodeClause q.2.lits = r ∧ Entailed p r) := by
  unfold linPlanOut at h
  split at h
  · cases h
  · rename_i hc
    split at h
    · cases h
    · rename_i ps0 hps0
      injection h with hps
      subst hps
      refine ⟨hc, by simp [hps0], ?_⟩
      intro q hq
      rw [Array.mem_toList_iff, List.mem_toArray, List.mem_map] at hq
      obtain ⟨y, hy, rfl⟩ := hq
      refine ⟨y.1.1, y.1.2, y.2, rfl, ?_, ?_⟩
      · change T.decodeClause (Array.map pLit y.1.2.toArray) = y.1.2
        exact LitTable.decodeClause_map_pLit T y.1.2
      · change Entailed p y.1.2
        rw [← LitTable.decodeClause_map_pLit T y.1.2]
        exact (EClause.ofLiterals p T y.1.2
          (hprune y.1.1 y.1.2 y.2)).ent

theorem linPlanOut_run_fix_of_no_prunes (p : CompiledProblem DomConstraint) (T : LitTable)
    (plan : LinPlan)
    (hconf : ∀ ls, plan.conflict? = some ls → Entailed p ls)
    (hprune : ∀ l r, (l, r) ∈ plan.prunes → Entailed p r)
    (hc : plan.conflict? = none) (hp : plan.prunes = []) :
    linPlanOut p T plan hconf hprune = .fix := by
  unfold linPlanOut
  split
  · rename_i ls hls
    rw [hc] at hls
    cases hls
  · split
    · rfl
    · rename_i ps0 hps0
      rw [hp] at hps0
      cases hps0

/-! ## The inequality plans -/

def linLePlan (terms : List LinTerm) (b : Int) : LinPlan :=
  if b < linTotalMin terms then
    { conflict? := some (linConflictLits terms), prunes := [] }
  else
    { conflict? := none, prunes := linPrunes terms b }

def linGePlan (terms : List LinTerm) (b : Int) : LinPlan :=
  if linTotalMax terms < b then
    { conflict? := some (linMaxLits terms), prunes := [] }
  else
    { conflict? := none, prunes := linPrunesGe terms b }

theorem linLePlan_conf_entailed {terms : List LinTerm} {b : Int} {ls : List Literal}
    (h : (linLePlan terms b).conflict? = some ls) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hle : linDotSum terms a ≤ b) : Clause.SatisfiedBy ls a := by
  unfold linLePlan at h
  split at h
  · rename_i hconf
    injection h with hls
    subst hls
    exact linLeConflict_satisfied hint hle hconf
  · simp at h

theorem linLePlan_prunes_entailed {terms : List LinTerm} {b : Int}
    {l : Literal} {r : Clause}
    (h : (l, r) ∈ (linLePlan terms b).prunes) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hle : linDotSum terms a ≤ b) : Clause.SatisfiedBy r a := by
  unfold linLePlan at h
  split at h
  · simp at h
  · exact linPrunes_reason_satisfied hint hle h

theorem linGePlan_conf_entailed {terms : List LinTerm} {b : Int} {ls : List Literal}
    (h : (linGePlan terms b).conflict? = some ls) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hge : b ≤ linDotSum terms a) : Clause.SatisfiedBy ls a := by
  unfold linGePlan at h
  split at h
  · rename_i hconf
    injection h with hls
    subst hls
    exact linMaxConflict_satisfied_of_ge hint hge hconf
  · simp at h

theorem linGePlan_prunes_entailed {terms : List LinTerm} {b : Int}
    {l : Literal} {r : Clause}
    (h : (l, r) ∈ (linGePlan terms b).prunes) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hge : b ≤ linDotSum terms a) : Clause.SatisfiedBy r a := by
  unfold linGePlan at h
  split at h
  · simp at h
  · exact linPrunesGe_reason_satisfied hint hge h

/-! ## View-level facts for the maximum-side clauses -/

theorem linMaxConflict_lits_evalLit_false (_p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (_b : Int) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hWF : ViewWF view is.toArray) :
    ∀ t ∈ linTerms coeffs.toArray is.toArray bds,
      (view.doms.getD t.s DomC.empty).evalLit
        (linMaxNegLit t.s t.c t.lo t.hi) = some false := by
  intro t ht
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  have htmem : t.s ∈ is.toArray.toList :=
    linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
      (bds := bds) hsize hbdsize ht
  have hwf : (view.doms.getD t.s DomC.empty).WF := hWF.dom_wf htmem
  obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds ht
  exact linMaxNegLit_evalLit_false hwf hlo hhi

theorem linPruneGe_lit_evalLit_none (_p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hWF : ViewWF view is.toArray)
    (hb : b ≤ linTotalMax (linTerms coeffs.toArray is.toArray bds))
    {l : Literal} {reason : Clause}
    (hprune : (l, reason) ∈ linPrunesGe (linTerms coeffs.toArray is.toArray bds) b) :
    (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none := by
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  obtain ⟨i, t, hterm, hbranch⟩ := linPrunesGe_mem hprune
  have ht : t ∈ linTerms coeffs.toArray is.toArray bds := by
    obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hterm
    exact List.mem_iff_getElem.mpr ⟨i, hlt, hget⟩
  have htmem : t.s ∈ is.toArray.toList :=
    linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
      (bds := bds) hsize hbdsize ht
  have hwf : (view.doms.getD t.s DomC.empty).WF := hWF.dom_wf htmem
  obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds ht
  rcases hbranch with ⟨hpos, hl, hlt, _⟩ | ⟨_, hneg, hl, hlt, _⟩
  · subst hl
    have hnew := linPruneGePos_newLo_le_hi
      (terms := linTerms coeffs.toArray is.toArray bds) (i := i) (t := t)
      (b := b) hterm hpos hb
    have hklo : t.lo ≤
        -((linOtherMax (linTerms coeffs.toArray is.toArray bds) i - b) / t.c) - 1 := by
      omega
    have hkhi : -((linOtherMax (linTerms coeffs.toArray is.toArray bds) i - b) / t.c) - 1 < t.hi := by
      omega
    simpa [atomSlot, negLe] using
      (evalLit_negLe_none (d := view.doms.getD t.s DomC.empty) hlo hhi hklo hkhi)
  · subst hl
    have hnew := linPruneGeNeg_newHi_ge_lo
      (terms := linTerms coeffs.toArray is.toArray bds) (i := i) (t := t)
      (b := b) hterm hneg hb
    have hkhi : (b - linOtherMax (linTerms coeffs.toArray is.toArray bds) i) / t.c < t.hi := hlt
    simpa [atomSlot, posLe] using
      (evalLit_posLe_none (d := view.doms.getD t.s DomC.empty) hlo hhi hnew hkhi)

theorem linPruneGe_other_lits_evalLit_false (_p : CompiledProblem DomConstraint)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    (hWF : ViewWF view is.toArray)
    {l : Literal} {reason : Clause}
    (hprune : (l, reason) ∈ linPrunesGe (linTerms coeffs.toArray is.toArray bds) b) :
    ∀ q ∈ reason, q ≠ l →
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  let terms := linTerms coeffs.toArray is.toArray bds
  have hbdsize : bds.size = is.toArray.size := (linExtractBounds_spec hbds).1
  obtain ⟨i, t, hterm, hbranch⟩ := linPrunesGe_mem hprune
  have hreason : reason = linOtherMaxLits terms i ++ [l] := by
    rcases hbranch with ⟨_, _, _, hr⟩ | ⟨_, _, _, _, hr⟩ <;> exact hr
  intro q hq hne
  have hqOther : q ∈ linOtherMaxLits terms i := by
    rw [hreason] at hq
    rcases List.mem_append.mp hq with h | h
    · exact h
    · exact absurd (List.mem_singleton.mp h) hne
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp (by
    simpa [linOtherMaxLits, linMaxLits] using hqOther)
  have hu' : u ∈ terms := List.mem_of_mem_eraseIdx hu
  have humem : u.s ∈ is.toArray.toList :=
    linTerms_slot_mem (cs := coeffs.toArray) (slots := is.toArray)
      (bds := bds) hsize hbdsize hu'
  have hwf : (view.doms.getD u.s DomC.empty).WF := hWF.dom_wf humem
  obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds hu'
  simpa [atomSlot_linMaxNegLit] using linMaxNegLit_evalLit_false hwf hlo hhi

/-! ## The equality plan -/

def linEqPlan (terms : List LinTerm) (b : Int) : LinPlan :=
  if b < linTotalMin terms then
    { conflict? := some (linConflictLits terms), prunes := [] }
  else if linTotalMax terms < b then
    { conflict? := some (linMaxLits terms), prunes := [] }
  else
    { conflict? := none, prunes := linPrunes terms b ++ linPrunesGe terms b }

theorem linEqPlan_conflict_cases {terms : List LinTerm} {b : Int} {ls : List Literal}
    (h : (linEqPlan terms b).conflict? = some ls) :
    (b < linTotalMin terms ∧ ls = linConflictLits terms) ∨
      (linTotalMax terms < b ∧ ls = linMaxLits terms) := by
  unfold linEqPlan at h
  split at h
  · rename_i hmin
    left
    exact ⟨hmin, (Option.some.inj h).symm⟩
  · split at h
    · rename_i hmax
      right
      exact ⟨hmax, (Option.some.inj h).symm⟩
    · simp at h

theorem linEqPlan_conflict_none_cases {terms : List LinTerm} {b : Int}
    (h : (linEqPlan terms b).conflict? = none) :
    ¬ b < linTotalMin terms ∧ ¬ linTotalMax terms < b := by
  unfold linEqPlan at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · constructor <;> omega

theorem linEqPlan_prunes_cases {terms : List LinTerm} {b : Int}
    {l : Literal} {r : Clause}
    (h : (l, r) ∈ (linEqPlan terms b).prunes) :
    (l, r) ∈ linPrunes terms b ∨ (l, r) ∈ linPrunesGe terms b := by
  unfold linEqPlan at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · exact List.mem_append.mp h

theorem linEqPlan_conf_entailed {terms : List LinTerm} {b : Int} {ls : List Literal}
    (h : (linEqPlan terms b).conflict? = some ls) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hdot : linDotSum terms a = b) : Clause.SatisfiedBy ls a := by
  rcases linEqPlan_conflict_cases h with ⟨hconf, rfl⟩ | ⟨hconf, rfl⟩
  · exact linConflict_satisfied hint hdot hconf
  · exact linMaxConflict_satisfied hint hdot hconf

theorem linEqPlan_prunes_entailed {terms : List LinTerm} {b : Int}
    {l : Literal} {r : Clause}
    (h : (l, r) ∈ (linEqPlan terms b).prunes) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hdot : linDotSum terms a = b) : Clause.SatisfiedBy r a := by
  rcases linEqPlan_prunes_cases h with h | h
  · exact linPrunes_reason_satisfied hint (by omega) h
  · exact linPrunesGe_reason_satisfied hint (by omega) h

def linEqOutWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds) : PropOut p T :=
  linPlanOut p T (linEqPlan (linTerms coeffs.toArray is.toArray bds) b)
    (fun ls hls a ha hacc => by
      obtain ⟨hint, hdot⟩ :=
        linEq_accepts_facts p coeffs is b view hmem hsize bds hbds hacc
      exact linEqPlan_conf_entailed hls hint hdot)
    (fun l r hpr a ha hacc => by
      obtain ⟨hint, hdot⟩ :=
        linEq_accepts_facts p coeffs is b view hmem hsize bds hbds hacc
      exact linEqPlan_prunes_entailed hpr hint hdot)

theorem linEqOutWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {ec : EClause p T}
    (h : linEqOutWith p T coeffs is b view hmem hsize bds hbds = .conflict ec) :
    ∃ ls, (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? = some ls ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls := by
  unfold linEqOutWith at h
  exact linPlanOut_run_conflict p T _ _ _ h

theorem linEqOutWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {ps : Array (PLit × EClause p T)}
    (h : linEqOutWith p T coeffs is b view hmem hsize bds hbds = .prune ps) :
    (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).conflict? = none ∧
      (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).prunes ≠ [] ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (r : Clause),
        (l, r) ∈ (linEqPlan (linTerms coeffs.toArray is.toArray bds) b).prunes ∧
          q.1.lit = l ∧ T.decodeClause q.2.lits = r ∧ Entailed p r) := by
  unfold linEqOutWith at h
  exact linPlanOut_run_prune p T _ _ _ h

/-- Membership-explicit bounded linear equality propagator. -/
def linEqPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints) : PropV2 p T :=
  let dc := DomConstraint.linEq coeffs is b
  let cs := coeffs.toArray
  let slots := is.toArray
  { vars := (dcSlotsFull dc).toArray
    events := slots.map fun s => (s, .bounds)
    run := fun view =>
      if hsize : cs.size = slots.size then
        match hbds : linExtractBounds view.doms slots with
        | none => .fix
        | some bds =>
            linEqOutWith p T coeffs is b view hmem hsize bds hbds
      else
        .fix }

theorem linEqPropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linEqPropWith p T coeffs is b hmem).run view = .conflict ec) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      ((b < linTotalMin terms ∧ T.decodeClause ec.lits = linConflictLits terms) ∨
        (linTotalMax terms < b ∧ T.decodeClause ec.lits = linMaxLits terms)) ∧
      Entailed p (T.decodeClause ec.lits) ∧
      (∀ l ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold linEqPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      obtain ⟨ls, hls, hdec, hent⟩ :=
        linEqOutWith_run_conflict p T coeffs is b view hmem hsize' bds hbds h
      rcases linEqPlan_conflict_cases hls with ⟨hconf, hlsEq⟩ | ⟨hconf, hlsEq⟩
      · have hdec' : T.decodeClause ec.lits =
            linConflictLits (linTerms coeffs.toArray is.toArray bds) := hdec.trans hlsEq
        have hent' : Entailed p (T.decodeClause ec.lits) := by
          rw [hdec', ← hlsEq]
          exact hent
        have hfalse := linConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
        refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl,
          Or.inl ⟨hconf, hdec'⟩, hent', ?_⟩
        intro l hl
        rw [hdec'] at hl
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
        simpa [atomSlot_linMinNegLit] using hfalse t ht
      · have hdec' : T.decodeClause ec.lits =
            linMaxLits (linTerms coeffs.toArray is.toArray bds) := hdec.trans hlsEq
        have hent' : Entailed p (T.decodeClause ec.lits) := by
          rw [hdec', ← hlsEq]
          exact hent
        have hfalse := linMaxConflict_lits_evalLit_false p coeffs is b view hsize bds hbds hWF
        refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl,
          Or.inr ⟨hconf, hdec'⟩, hent', ?_⟩
        intro l hl
        rw [hdec'] at hl
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
        simpa [atomSlot_linMaxNegLit] using hfalse t ht
  · rw [dif_neg hsize'] at h
    cases h

theorem linEqPropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linEqPropWith p T coeffs is b hmem).run view = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      ¬ b < linTotalMin terms ∧ ¬ linTotalMax terms < b ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (reason : Clause),
        ((l, reason) ∈ linPrunes terms b ∨ (l, reason) ∈ linPrunesGe terms b) ∧
          q.1.lit = l ∧ T.decodeClause q.2.lits = reason ∧ Entailed p reason ∧
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
          (∀ q' ∈ reason, q' ≠ l →
            (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linEqPropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      obtain ⟨hconf, _hne, hqfacts⟩ :=
        linEqOutWith_run_prune p T coeffs is b view hmem hsize' bds hbds h
      have hnone := linEqPlan_conflict_none_cases (terms := linTerms coeffs.toArray is.toArray bds) hconf
      refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, hnone.1, hnone.2, ?_⟩
      intro q hq
      obtain ⟨l, r, hpr, hlit, hdec, hent⟩ := hqfacts q hq
      have hmem' : (l, r) ∈ linPrunes (linTerms coeffs.toArray is.toArray bds) b ∨
          (l, r) ∈ linPrunesGe (linTerms coeffs.toArray is.toArray bds) b :=
        linEqPlan_prunes_cases hpr
      refine ⟨l, r, hmem', hlit, hdec, hent, ?_, ?_⟩
      · rcases hmem' with h | h
        · exact linPrune_lit_evalLit_none p coeffs is b view hsize bds hbds hWF
            (by omega) h
        · exact linPruneGe_lit_evalLit_none p coeffs is b view hsize bds hbds hWF
            (by omega) h
      · rcases hmem' with h | h
        · exact linPrune_other_lits_evalLit_false p coeffs is b view hsize bds hbds hWF h
        · exact linPruneGe_other_lits_evalLit_false p coeffs is b view hsize bds hbds hWF h
  · rw [dif_neg hsize'] at h
    cases h

theorem linEqPropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linEqPropWith p T coeffs is b hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hcases, hent, hfalse⟩ :=
    linEqPropWith_run_conflict p T coeffs is b view hmem hsize hWF h
  exact hent

theorem linEqPropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ec : EClause p T}
    (h : (linEqPropWith p T coeffs is b hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨bds, terms, hbds, hterms, hcases, hent, hfalse⟩ :=
    linEqPropWith_run_conflict p T coeffs is b view hmem hsize hWF h
  exact hfalse

theorem linEqPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linEqPropWith p T coeffs is b hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hnotmin, hnotmax, hqfacts⟩ :=
    linEqPropWith_run_prune p T coeffs is b view hmem hsize hWF h
  obtain ⟨l, reason, hmem', hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  rwa [hdec]

theorem linEqPropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    {ps : Array (PLit × EClause p T)}
    (h : (linEqPropWith p T coeffs is b hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨bds, terms, hbds, hterms, hnotmin, hnotmax, hqfacts⟩ :=
    linEqPropWith_run_prune p T coeffs is b view hmem hsize hWF h
  obtain ⟨l, reason, hmem', hlit, hdec, hent, hnone, hother⟩ := hqfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

theorem linEqPropWith_run_fix_of_size_ne (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (_hmem : DomConstraint.linEq coeffs is b ∈ p.constraints)
    (hsize : coeffs.length ≠ is.length) :
    (linEqPropWith p T coeffs is b _hmem).run view = .fix := by
  unfold linEqPropWith
  dsimp only
  have hne : coeffs.toArray.size ≠ is.toArray.size := by
    simpa using hsize
  rw [dif_neg hne]

/-! ## The disequality plan -/

def linDotLo : List LinTerm → Int
  | [] => 0
  | t :: ts => linDotLo ts + t.c * t.lo

theorem linDotSum_eq_linDotLo_of_posNe_false (terms : List LinTerm) (a : Assignment)
    (h : ∀ t ∈ terms, (posNe t.s t.lo).eval a = some false) :
    linDotSum terms a = linDotLo terms := by
  induction terms with
  | nil => simp [linDotSum, linDotLo]
  | cons t ts ih =>
      have hhead := h t (by simp)
      have htail : ∀ u ∈ ts, (posNe u.s u.lo).eval a = some false := by
        intro u hu
        exact h u (by simp [hu])
      obtain ⟨x, hx, hxv⟩ := (eval_posNe_false_iff a t.s t.lo).mp hhead
      have hxlo : slotInt a t.s = some t.lo := by rw [hx, hxv]
      have iht := ih htail
      simp [linDotSum, linDotLo, hxlo, iht]

theorem linNeConflict_satisfied_of_dotLo {terms : List LinTerm} {b : Int} {a : Assignment}
    (hdotlo : linDotLo terms = b)
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hne : linDotSum terms a ≠ b) :
    Clause.SatisfiedBy (linNeConflictLits terms) a := by
  apply Classical.byContradiction
  intro hno
  have hnotTrue : ∀ l ∈ linNeConflictLits terms, l.eval a ≠ some true := by
    intro l hl htrue
    exact hno ⟨l, hl, htrue⟩
  have hfalse : ∀ t ∈ terms, (posNe t.s t.lo).eval a = some false := by
    intro t ht
    have hl : posNe t.s t.lo ∈ linNeConflictLits terms := List.mem_map.mpr ⟨t, ht, rfl⟩
    obtain ⟨x, hx⟩ := hint t ht
    cases he : (posNe t.s t.lo).eval a with
    | none =>
        rw [eval_posNe, hx] at he
        simp at he
    | some bb =>
        cases bb with
        | false => rfl
        | true => exact absurd he (hnotTrue _ hl)
  have hdot := linDotSum_eq_linDotLo_of_posNe_false terms a hfalse
  exact hne (by rw [hdot, hdotlo])

def linNePruneFor (terms : List LinTerm) (b : Int) (i : Nat)
    (ev : Literal → Option Bool) : Option (Literal × Clause) :=
  match terms[i]? with
  | none => none
  | some t =>
      if t.c = 0 then none
      else
        let v := (b - linOtherMin terms i) / t.c
        if t.c * v = b - linOtherMin terms i then
          if ev (posNe t.s v) = none then
            some (posNe t.s v, linFixedLits (terms.eraseIdx i) ++ [posNe t.s v])
          else none
        else none

theorem linNePruneFor_mem {terms : List LinTerm} {b : Int} {i : Nat}
    {ev : Literal → Option Bool} {q : Literal × Clause}
    (h : linNePruneFor terms b i ev = some q) :
    ∃ t, terms[i]? = some t ∧ t.c ≠ 0 ∧
      q.1 = posNe t.s ((b - linOtherMin terms i) / t.c) ∧
      t.c * ((b - linOtherMin terms i) / t.c) = b - linOtherMin terms i ∧
      ev q.1 = none ∧
      q.2 = linFixedLits (terms.eraseIdx i) ++ [q.1] := by
  unfold linNePruneFor at h
  cases hterm : terms[i]? with
  | none => simp [hterm] at h
  | some t =>
      simp only [hterm] at h
      split at h
      · simp at h
      · rename_i hc
        split at h
        · rename_i heq
          split at h
          · rename_i hev
            have hq : (posNe t.s ((b - linOtherMin terms i) / t.c),
                linFixedLits (terms.eraseIdx i) ++
                  [posNe t.s ((b - linOtherMin terms i) / t.c)]) = q :=
              Option.some.inj h
            subst hq
            exact ⟨t, rfl, hc, rfl, heq, hev, rfl⟩
          · simp at h
        · simp at h

def linNePlan (terms : List LinTerm) (b : Int)
    (ev : Literal → Option Bool) : LinPlan :=
  if linNonFixedIndices terms = [] then
    if linDotLo terms = b then
      { conflict? := some (linNeConflictLits terms), prunes := [] }
    else
      { conflict? := none, prunes := [] }
  else
    match linNonFixedIndices terms with
    | [i] =>
        match linNePruneFor terms b i ev with
        | some q => { conflict? := none, prunes := [q] }
        | none => { conflict? := none, prunes := [] }
    | _ => { conflict? := none, prunes := [] }

theorem linNePlan_conflict_cases {terms : List LinTerm} {b : Int}
    {ev : Literal → Option Bool} {ls : List Literal}
    (h : (linNePlan terms b ev).conflict? = some ls) :
    linNonFixedIndices terms = [] ∧ linDotLo terms = b ∧
      ls = linNeConflictLits terms := by
  unfold linNePlan at h
  split at h
  · rename_i hall
    split at h
    · rename_i hlo
      exact ⟨hall, hlo, (Option.some.inj h).symm⟩
    · simp at h
  · rename_i hall
    cases hnf : linNonFixedIndices terms with
    | nil => rw [hnf] at hall; simp at hall
    | cons x xs =>
        cases xs with
        | nil =>
            rw [hnf] at h
            simp only at h
            cases hp : linNePruneFor terms b x ev with
            | none => simp [hp] at h
            | some q => simp [hp] at h
        | cons y ys =>
            rw [hnf] at h
            simp at h

theorem linNePlan_prunes_cases {terms : List LinTerm} {b : Int}
    {ev : Literal → Option Bool} {q : Literal × Clause}
    (h : q ∈ (linNePlan terms b ev).prunes) :
    ∃ i t, linNonFixedIndices terms = [i] ∧ terms[i]? = some t ∧
      t.c ≠ 0 ∧
      q.1 = posNe t.s ((b - linOtherMin terms i) / t.c) ∧
      t.c * ((b - linOtherMin terms i) / t.c) = b - linOtherMin terms i ∧
      ev q.1 = none ∧
      q.2 = linFixedLits (terms.eraseIdx i) ++ [q.1] := by
  unfold linNePlan at h
  split at h
  · split at h <;> simp at h
  · rename_i hall
    cases hnf : linNonFixedIndices terms with
    | nil => rw [hnf] at hall; simp at hall
    | cons x xs =>
        cases xs with
        | nil =>
            rw [hnf] at h
            simp only at h
            cases hp : linNePruneFor terms b x ev with
            | none => simp [hp] at h
            | some q0 =>
                simp [hp] at h
                have hq : q = q0 := by simpa using h
                subst hq
                obtain ⟨t, hterm, hc, hl, heq, hev, hr⟩ := linNePruneFor_mem hp
                exact ⟨x, t, rfl, hterm, hc, hl, heq, hev, hr⟩
        | cons y ys =>
            rw [hnf] at h
            simp at h

theorem linNePlan_conf_entailed {terms : List LinTerm} {b : Int}
    {ev : Literal → Option Bool} {ls : List Literal}
    (h : (linNePlan terms b ev).conflict? = some ls) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hne : linDotSum terms a ≠ b) : Clause.SatisfiedBy ls a := by
  obtain ⟨_, hdotlo, rfl⟩ := linNePlan_conflict_cases h
  exact linNeConflict_satisfied_of_dotLo hdotlo hint hne

theorem linNePlan_prunes_entailed {terms : List LinTerm} {b : Int}
    {ev : Literal → Option Bool} {l : Literal} {r : Clause}
    (h : (l, r) ∈ (linNePlan terms b ev).prunes) {a : Assignment}
    (hint : ∀ t ∈ terms, ∃ x, slotInt a t.s = some x)
    (hne : linDotSum terms a ≠ b) : Clause.SatisfiedBy r a := by
  obtain ⟨i, t, hnf, hterm, hc, hl, heq, hev, hr⟩ := linNePlan_prunes_cases h
  have hr' : r = linFixedLits (terms.eraseIdx i) ++ [l] := by simpa using hr
  have hl' : l = posNe t.s ((b - linOtherMin terms i) / t.c) := by simpa using hl
  rw [hr', hl']
  exact linNePrune_satisfied hterm hnf heq hint hne

def linNeOutWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds) : PropOut p T :=
  linPlanOut p T
    (linNePlan (linTerms coeffs.toArray is.toArray bds) b
      (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l))
    (fun ls hls a ha hacc => by
      obtain ⟨hint, d, hdot, hdne⟩ :=
        linNe_accepts_facts p coeffs is b view hmem hsize bds hbds hacc
      refine linNePlan_conf_entailed hls hint ?_
      intro hb
      exact hdne (by omega))
    (fun l r hpr a ha hacc => by
      obtain ⟨hint, d, hdot, hdne⟩ :=
        linNe_accepts_facts p coeffs is b view hmem hsize bds hbds hacc
      refine linNePlan_prunes_entailed hpr hint ?_
      intro hb
      exact hdne (by omega))

theorem linNeOutWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {ec : EClause p T}
    (h : linNeOutWith p T coeffs is b view hmem hsize bds hbds = .conflict ec) :
    ∃ ls,
      (linNePlan (linTerms coeffs.toArray is.toArray bds) b
        (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? =
          some ls ∧
      T.decodeClause ec.lits = ls ∧ Entailed p ls := by
  unfold linNeOutWith at h
  exact linPlanOut_run_conflict p T _ _ _ h

theorem linNeOutWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (bds : Array (Int × Int))
    (hbds : linExtractBounds view.doms is.toArray = some bds)
    {ps : Array (PLit × EClause p T)}
    (h : linNeOutWith p T coeffs is b view hmem hsize bds hbds = .prune ps) :
    (linNePlan (linTerms coeffs.toArray is.toArray bds) b
        (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).conflict? = none ∧
      (∀ q ∈ ps.toList, ∃ (l : Literal) (r : Clause),
        (l, r) ∈ (linNePlan (linTerms coeffs.toArray is.toArray bds) b
          (fun l => (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l)).prunes ∧
          q.1.lit = l ∧ T.decodeClause q.2.lits = r ∧ Entailed p r) := by
  unfold linNeOutWith at h
  obtain ⟨hconf, _hne, hq⟩ :=
    linPlanOut_run_prune p T _ _ _ h
  exact ⟨hconf, hq⟩

/-- Membership-explicit bounded linear disequality propagator. -/
def linNePropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints) : PropV2 p T :=
  let dc := DomConstraint.linNe coeffs is b
  let cs := coeffs.toArray
  let slots := is.toArray
  { vars := (dcSlotsFull dc).toArray
    events := slots.flatMap fun s => #[(s, .bounds), (s, .fix)]
    run := fun view =>
      if hsize : cs.size = slots.size then
        match hbds : linExtractBounds view.doms slots with
        | none => .fix
        | some bds =>
            if _hguard : viewIntKindB view slots = true then
              linNeOutWith p T coeffs is b view hmem hsize bds hbds
            else .fix
      else
        .fix }

theorem linNePropWith_run_conflict (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linNePropWith p T coeffs is b hmem).run view = .conflict ec) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      linNonFixedIndices terms = [] ∧ linDotLo terms = b ∧
      T.decodeClause ec.lits = linNeConflictLits terms ∧
      Entailed p (T.decodeClause ec.lits) ∧
      (∀ l ∈ T.decodeClause ec.lits,
        (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false) := by
  unfold linNePropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      by_cases hguard' : viewIntKindB view is.toArray = true
      · rw [dif_pos hguard'] at h
        obtain ⟨ls, hls, hdec, hent⟩ :=
          linNeOutWith_run_conflict p T coeffs is b view hmem hsize' bds hbds h
        obtain ⟨hall, hdotlo, hlsEq⟩ := linNePlan_conflict_cases hls
        have hdec' : T.decodeClause ec.lits =
            linNeConflictLits (linTerms coeffs.toArray is.toArray bds) := hdec.trans hlsEq
        have hent' : Entailed p (T.decodeClause ec.lits) := by
          rw [hdec', ← hlsEq]
          exact hent
        refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl,
          hall, hdotlo, hdec', hent', ?_⟩
        intro l hl
        rw [hdec'] at hl
        obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hl
        have htmem : t.s ∈ is.toArray.toList := by
          have := linTerms_slot_mem_is hsize hbds ht
          simpa using this
        have hkind := viewIntKindB_spec hguard' htmem
        have hwf := hWF.dom_wf htmem
        obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds ht
        have hfix := linNonFixedIndices_nil_spec hall t ht
        simpa [posNe, atomSlot] using DomC.evalLit_posNe_intKind hwf hkind hlo hhi hfix
      · rw [dif_neg hguard'] at h
        cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linNePropWith_run_prune (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linNePropWith p T coeffs is b hmem).run view = .prune ps) :
    ∃ bds terms, linExtractBounds view.doms is.toArray = some bds ∧
      terms = linTerms coeffs.toArray is.toArray bds ∧
      (∀ q ∈ ps.toList, ∃ (i : Nat) (t : LinTerm) (v : Int)
          (l : Literal) (r : Clause),
        linNonFixedIndices terms = [i] ∧ terms[i]? = some t ∧ t.c ≠ 0 ∧
          v = (b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i) / t.c ∧
          t.c * v = b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i ∧
          l = posNe t.s v ∧ q.1.lit = l ∧
          T.decodeClause q.2.lits = r ∧
          r = linFixedLits ((linTerms coeffs.toArray is.toArray bds).eraseIdx i) ++ [l] ∧
          Entailed p r ∧
          (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none ∧
          (∀ q' ∈ r, q' ≠ l →
            (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false)) := by
  unfold linNePropWith at h
  dsimp only at h
  by_cases hsize' : coeffs.toArray.size = is.toArray.size
  · rw [dif_pos hsize'] at h
    split at h
    · cases h
    · rename_i bds hbds
      by_cases hguard' : viewIntKindB view is.toArray = true
      · rw [dif_pos hguard'] at h
        obtain ⟨hconf, hqfacts⟩ :=
          linNeOutWith_run_prune p T coeffs is b view hmem hsize' bds hbds h
        refine ⟨bds, linTerms coeffs.toArray is.toArray bds, hbds, rfl, ?_⟩
        intro q hq
        obtain ⟨l, r, hpr, hlit, hdec, hent⟩ := hqfacts q hq
        obtain ⟨i, t, hnf, hterm, hc, hl, heq, hev, hr⟩ :=
          linNePlan_prunes_cases hpr
        have hlit' : q.1.lit = l := hlit
        have hdec' : T.decodeClause q.2.lits = r := hdec
        have hev' : (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = none := by
          simpa using hev
        have hr' : r = linFixedLits ((linTerms coeffs.toArray is.toArray bds).eraseIdx i) ++ [l] := by simpa using hr
        have hl' : l = posNe t.s ((b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i) / t.c) := by simpa using hl
        refine ⟨i, t, (b - linOtherMin (linTerms coeffs.toArray is.toArray bds) i) / t.c, l, r, hnf, hterm, hc,
          rfl, heq, hl', hlit', hdec', hr', hent, hev', ?_⟩
        intro q' hq' hne
        rw [hr'] at hq'
        have hqOther : q' ∈ linFixedLits ((linTerms coeffs.toArray is.toArray bds).eraseIdx i) := by
          rcases List.mem_append.mp hq' with h | h
          · exact h
          · exact absurd (List.mem_singleton.mp h) hne
        obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hqOther
        have hu' : u ∈ linTerms coeffs.toArray is.toArray bds := List.mem_of_mem_eraseIdx hu
        have humem : u.s ∈ is.toArray.toList := by
          have := linTerms_slot_mem_is hsize hbds hu'
          simpa using this
        have hkind := viewIntKindB_spec hguard' humem
        have hwf := hWF.dom_wf humem
        obtain ⟨hlo, hhi⟩ := linTerms_mem_bounds hsize hbds hu'
        have hfix := linNonFixedIndices_singleton_fixed_erase hnf u hu
        simpa [posNe, atomSlot] using DomC.evalLit_posNe_intKind hwf hkind hlo hhi hfix
      · rw [dif_neg hguard'] at h
        cases h
  · rw [dif_neg hsize'] at h
    cases h

theorem linNePropWith_conflict_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linNePropWith p T coeffs is b hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hall, hdotlo, hdec, hent, hfalse⟩ :=
    linNePropWith_run_conflict p T coeffs is b view hmem hsize hWF hguard h
  exact hent

theorem linNePropWith_conflict_lits_false (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ec : EClause p T}
    (h : (linNePropWith p T coeffs is b hmem).run view = .conflict ec) :
    ∀ l ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot l.atom) DomC.empty).evalLit l = some false := by
  obtain ⟨bds, terms, hbds, hterms, hall, hdotlo, hdec, hent, hfalse⟩ :=
    linNePropWith_run_conflict p T coeffs is b view hmem hsize hWF hguard h
  exact hfalse

theorem linNePropWith_prune_reason_entailed (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linNePropWith p T coeffs is b hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linNePropWith_run_prune p T coeffs is b view hmem hsize hWF hguard h
  obtain ⟨i, t, v, l, r, hnf, hterm, hc, hv, heq, hl, hlit, hdec, hr, hent, hnone, hother⟩ :=
    hqfacts q hq
  rwa [hdec]

theorem linNePropWith_prune_lit_none (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.toArray.size = is.toArray.size)
    (hWF : ViewWF view is.toArray)
    (hguard : viewIntKindB view is.toArray = true)
    {ps : Array (PLit × EClause p T)}
    (h : (linNePropWith p T coeffs is b hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  obtain ⟨bds, terms, hbds, hterms, hqfacts⟩ :=
    linNePropWith_run_prune p T coeffs is b view hmem hsize hWF hguard h
  obtain ⟨i, t, v, l, r, hnf, hterm, hc, hv, heq, hl, hlit, hdec, hr, hent, hnone, hother⟩ :=
    hqfacts q hq
  refine ⟨?_, ?_⟩
  · rwa [hlit]
  · intro q' hq' hne
    rw [hdec] at hq'
    exact hother q' hq' (by rwa [hlit] at hne)

theorem linNePropWith_run_fix_of_size_ne (p : CompiledProblem DomConstraint) (T : LitTable)
    (coeffs : List Int) (is : List Nat) (b : Int) (view : EngineView)
    (_hmem : DomConstraint.linNe coeffs is b ∈ p.constraints)
    (hsize : coeffs.length ≠ is.length) :
    (linNePropWith p T coeffs is b _hmem).run view = .fix := by
  unfold linNePropWith
  dsimp only
  have hne : coeffs.toArray.size ≠ is.toArray.size := by
    simpa using hsize
  rw [dif_neg hne]


end LeanFzn.Engine
