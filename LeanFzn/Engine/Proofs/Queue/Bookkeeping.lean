/-
Purpose: Queue bookkeeping lemmas, separated from executable propagation.
Dependencies: LeanFzn.Engine.Proofs.Queue.Invariants
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Proofs.Queue.Invariants

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

set_option maxHeartbeats 4000000

theorem insertPending_reasons {st : EngineState p T} (item : Pending) :
    (insertPending st item).1.reasons = st.reasons := by
  unfold insertPending
  dsimp only
  repeat' (first | split | simp [canonLit_reasons, canonClause_reasons, trailPush_reasons, emitSlot_reasons])

theorem insertPending_props {st : EngineState p T} (item : Pending) :
    (insertPending st item).1.props = st.props := by
  unfold insertPending
  dsimp only
  repeat' (first | split | simp [canonLit_props, canonClause_props, trailPush_props, emitSlot_props])

theorem insertPending_subs {st : EngineState p T} (item : Pending) :
    (insertPending st item).1.subs = st.subs := by
  unfold insertPending
  dsimp only
  repeat' (first | split | simp [canonLit_subs, canonClause_subs, trailPush_subs, emitSlot_subs])

theorem insertPending_level {st : EngineState p T} (item : Pending) :
    (insertPending st item).1.level = st.level := by
  unfold insertPending
  dsimp only
  repeat' (first | split | simp [canonLit_level, canonClause_level, trailPush_level, emitSlot_level])

theorem insertPending_levelStart {st : EngineState p T} (item : Pending) :
    (insertPending st item).1.levelStart = st.levelStart := by
  unfold insertPending
  dsimp only
  repeat' (first | split | simp [canonLit_levelStart, canonClause_levelStart, trailPush_levelStart, emitSlot_levelStart])

theorem insertPending_db {st : EngineState p T} (item : Pending) :
    (insertPending st item).1.db = st.db := by
  unfold insertPending
  dsimp only
  repeat' (first | split | simp [canonLit_db, canonClause_db, trailPush_db, emitSlot_db])

theorem insertPending_table_append_only {st : EngineState p T} (item : Pending) :
    st.table.lits.toList <+: (insertPending st item).1.table.lits.toList := by
  unfold insertPending
  dsimp only
  split
  · exact canonLit_table_append_only _ _
  · split
    · exact (canonLit_table_append_only _ _).trans (canonClause_table_append_only _ _)
    · exact canonLit_table_append_only _ _
  · split
    · split
      · exact (canonLit_table_append_only _ _).trans (canonClause_table_append_only _ _)
      · exact canonLit_table_append_only _ _
    · rename_i hz
      let st1 : EngineState p T := (canonLit st item.lit).2
      let l : PLit := (canonLit st item.lit).1
      let slot : Slot := l.slot
      let d : DomC := st1.doms.getD slot DomC.empty
      let d' : DomC := d.applyLit l.lit
      let e : Entry := { lit := l, level := st1.level, reason := item.reason, slot := slot, prev := d }
      let st2 : EngineState p T := { st1 with
        doms := st1.doms.set! slot d',
        stats := { st1.stats with
          propagations := st1.stats.propagations + (if item.count then 1 else 0) } }
      let st3 : EngineState p T := trailPush st2 e
      let st4 : EngineState p T := emitSlot st3 slot d d'
      change st.table.lits.toList <+: (canonLit st4 l.negate).2.table.lits.toList
      have h01 : st.table.lits.toList <+: st1.table.lits.toList :=
        canonLit_table_append_only st item.lit
      have h14 : st1.table.lits.toList <+: st4.table.lits.toList := by
        simp [st2, st3, st4, trailPush_table, emitSlot_table]
      exact h01.trans (h14.trans (canonLit_table_append_only st4 l.negate))

theorem insertPending_tableWF {st : EngineState p T} (hT : st.table.TableWF) (item : Pending) :
    (insertPending st item).1.table.TableWF := by
  unfold insertPending
  dsimp only
  split
  · exact canonLit_tableWF st item.lit hT
  · split
    · exact canonClause_tableWF _ _ (canonLit_tableWF st item.lit hT)
    · exact canonLit_tableWF st item.lit hT
  · split
    · split
      · exact canonClause_tableWF _ _ (canonLit_tableWF st item.lit hT)
      · exact canonLit_tableWF st item.lit hT
    · rename_i hz
      let st1 : EngineState p T := (canonLit st item.lit).2
      let l : PLit := (canonLit st item.lit).1
      let slot : Slot := l.slot
      let d : DomC := st1.doms.getD slot DomC.empty
      let d' : DomC := d.applyLit l.lit
      let e : Entry := { lit := l, level := st1.level, reason := item.reason, slot := slot, prev := d }
      let st2 : EngineState p T := { st1 with
        doms := st1.doms.set! slot d',
        stats := { st1.stats with
          propagations := st1.stats.propagations + (if item.count then 1 else 0) } }
      let st3 : EngineState p T := trailPush st2 e
      let st4 : EngineState p T := emitSlot st3 slot d d'
      change (canonLit st4 l.negate).2.table.TableWF
      have h1 : st1.table.TableWF := canonLit_tableWF st item.lit hT
      have h4 : st4.table.TableWF := by
        simpa [st2, st3, st4, trailPush_table, emitSlot_table] using h1
      exact canonLit_tableWF st4 l.negate h4

theorem insertPending_trail_push {st : EngineState p T} (item : Pending)
    (h1 : ((canonLit st item.lit).2.doms.getD (canonLit st item.lit).1.slot DomC.empty).evalLit
      (canonLit st item.lit).1.lit = none)
    (h2 : (((canonLit st item.lit).2.doms.getD (canonLit st item.lit).1.slot DomC.empty).applyLit
      (canonLit st item.lit).1.lit).isEmpty = false) :
    ∃ e : Entry, (insertPending st item).1.trail = st.trail.push e ∧
      e.slot = item.lit.slot ∧
      e.prev = st.doms.getD item.lit.slot DomC.empty ∧
      e.level = st.level ∧
      e.lit = (canonLit st item.lit).1 ∧
      e.reason = item.reason ∧
      (insertPending st item).1.trail.size = st.trail.size + 1 := by
  unfold insertPending
  dsimp only
  rw [h1]
  simp only [h2]
  let st1 : EngineState p T := (canonLit st item.lit).2
  let l : PLit := (canonLit st item.lit).1
  let slot : Slot := l.slot
  let d : DomC := st1.doms.getD slot DomC.empty
  let d' : DomC := d.applyLit l.lit
  let e : Entry := { lit := l, level := st1.level, reason := item.reason, slot := slot, prev := d }
  let st2 : EngineState p T := { st1 with
    doms := st1.doms.set! slot d',
    stats := { st1.stats with
      propagations := st1.stats.propagations + (if item.count then 1 else 0) } }
  let st3 : EngineState p T := trailPush st2 e
  let st4 : EngineState p T := emitSlot st3 slot d d'
  change ∃ e' : Entry, (canonLit st4 l.negate).2.trail = st.trail.push e' ∧
    e'.slot = item.lit.slot ∧
    e'.prev = st.doms.getD item.lit.slot DomC.empty ∧
    e'.level = st.level ∧
    e'.lit = l ∧
    e'.reason = item.reason ∧
    (canonLit st4 l.negate).2.trail.size = st.trail.size + 1
  refine ⟨e, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [st4, st3, st2, st1, e, trailPush, emitSlot_trail, canonLit_trail]
  · simp [e, slot, l, PLit.slot, canonLit_lit]
  · simp [e, d, st1, l, slot, PLit.slot, canonLit_doms, canonLit_lit]
  · simp [e, st1, canonLit_level]
  · simp [e]
  · simp [e]
  · simp [st4, st3, st2, st1, e, trailPush, emitSlot_trail, canonLit_trail]

theorem insertPending_trail_doms {st : EngineState p T} (item : Pending)
    (h1 : ((canonLit st item.lit).2.doms.getD (canonLit st item.lit).1.slot DomC.empty).evalLit
      (canonLit st item.lit).1.lit = none)
    (h2 : (((canonLit st item.lit).2.doms.getD (canonLit st item.lit).1.slot DomC.empty).applyLit
      (canonLit st item.lit).1.lit).isEmpty = false) :
    (insertPending st item).1.doms =
      st.doms.set! item.lit.slot
        ((st.doms.getD item.lit.slot DomC.empty).applyLit item.lit.lit) := by
  unfold insertPending
  dsimp only
  rw [h1]
  simp only [h2]
  let st1 : EngineState p T := (canonLit st item.lit).2
  let l : PLit := (canonLit st item.lit).1
  let slot : Slot := l.slot
  let d : DomC := st1.doms.getD slot DomC.empty
  let d' : DomC := d.applyLit l.lit
  let e : Entry := { lit := l, level := st1.level, reason := item.reason, slot := slot, prev := d }
  let st2 : EngineState p T := { st1 with
    doms := st1.doms.set! slot d',
    stats := { st1.stats with
      propagations := st1.stats.propagations + (if item.count then 1 else 0) } }
  let st3 : EngineState p T := trailPush st2 e
  let st4 : EngineState p T := emitSlot st3 slot d d'
  change (canonLit st4 l.negate).2.doms =
    st.doms.set! item.lit.slot ((st.doms.getD item.lit.slot DomC.empty).applyLit item.lit.lit)
  simp [st4, st3, st2, st1, d, d', l, slot, e, PLit.slot, canonLit_doms, canonLit_lit, trailPush_doms, emitSlot_doms]

theorem insertPending_failed {st : EngineState p T} (item : Pending)
    {st' : EngineState p T} {conf : Option (EClause p T)} {neg : Option PLit} {failed : Bool}
    (h : insertPending st item = (st', conf, neg, failed)) (hf : failed = true) :
    conf = none ∧ reasonClause? (canonLit st item.lit).2 item.reason = none := by
  unfold insertPending at h
  dsimp only at h
  repeat' (first | split at h)
  all_goals simp_all

theorem insertPending_conflict {st : EngineState p T} (item : Pending)
    {st' : EngineState p T} {neg : Option PLit} {failed : Bool} {c : EClause p T}
    (h : insertPending st item = (st', some c, neg, failed)) :
    ∃ ec, reasonClause? (canonLit st item.lit).2 item.reason = some ec ∧
      c.lits.size = ec.lits.size ∧
      (∀ (i : Nat) (q : PLit), c.lits[i]? = some q →
        ∃ q0, ec.lits[i]? = some q0 ∧ q.lit = q0.lit) := by
  unfold insertPending at h
  dsimp only at h
  repeat' (first | split at h)
  all_goals simp at h
  all_goals try (obtain ⟨-, hc, -⟩ := h; subst c)
  all_goals exact ⟨_, by assumption, canonClause_lits _ _⟩

theorem insertPending_true_state {st : EngineState p T} (item : Pending)
    (h1 : ((canonLit st item.lit).2.doms.getD (canonLit st item.lit).1.slot DomC.empty).evalLit
      (canonLit st item.lit).1.lit = some true) :
    (insertPending st item).1.doms = st.doms ∧
      (insertPending st item).1.trail = st.trail := by
  unfold insertPending
  dsimp only
  rw [h1]
  exact ⟨canonLit_doms st item.lit, canonLit_trail st item.lit⟩

theorem insertPending_conflict_state {st : EngineState p T} (item : Pending)
    {st' : EngineState p T} {neg : Option PLit} {failed : Bool} {c : EClause p T}
    (h : insertPending st item = (st', some c, neg, failed)) :
    st'.doms = st.doms ∧ st'.trail = st.trail := by
  unfold insertPending at h
  dsimp only at h
  repeat' (first | split at h)
  all_goals simp at h
  all_goals rcases h with ⟨hst, -⟩
  all_goals rw [← hst]
  all_goals first
    | simp [canonLit_doms, canonLit_trail]
    | simp [canonClause_doms, canonClause_trail, canonLit_doms, canonLit_trail]

theorem insertPending_failed_state {st : EngineState p T} (item : Pending)
    {st' : EngineState p T} {conf : Option (EClause p T)} {neg : Option PLit}
    (h : insertPending st item = (st', conf, neg, true)) :
    st'.doms = st.doms ∧ st'.trail = st.trail := by
  unfold insertPending at h
  dsimp only at h
  repeat' (first | split at h)
  all_goals simp at h
  all_goals rcases h with ⟨hst, -⟩
  all_goals rw [← hst]
  all_goals simp [canonLit_doms, canonLit_trail]

theorem pushPropPrunes_eq (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) :
    pushPropPrunes st pending ps = ps.foldl pushPropStep (st, pending, false) := rfl

theorem PropStepOK.trans {a b c : EngineState p T × Array Pending × Bool}
    (h1 : PropStepOK a b) (h2 : PropStepOK b c) : PropStepOK a c where
  failed := h2.failed
  reasons_pre := h1.reasons_pre.trans h2.reasons_pre
  pending_pre := h1.pending_pre.trans h2.pending_pre
  new_pending := by
    intro item hmem hnotin
    by_cases hin : item ∈ b.2.1.toList
    · obtain ⟨rid, c, hr, hc, hget⟩ := h1.new_pending item hin hnotin
      exact ⟨rid, c, hr, hc, h2.old_reasons _ _ hget⟩
    · exact h2.new_pending item hmem hin
  old_reasons := fun i x h => h2.old_reasons i x (h1.old_reasons i x h)

theorem list_foldl_propOK {α : Type}
    (f : EngineState p T × Array Pending × Bool → α → EngineState p T × Array Pending × Bool)
    (hf : ∀ acc a, acc.2.2 = false → PropStepOK acc (f acc a))
    (st : EngineState p T) (pending : Array Pending) (failed : Bool) (hstart : failed = false)
    (l : List α) :
    PropStepOK (st, pending, failed) (l.foldl f (st, pending, failed)) := by
  induction l generalizing st pending failed with
  | nil =>
      refine ⟨hstart, List.prefix_refl _, List.prefix_refl _, ?_, ?_⟩
      · intro item h hnot; exact absurd (by simpa using h) hnot
      · intro i x h; exact h
  | cons a rest ih =>
      rw [List.foldl_cons]
      have h1 := hf (st, pending, failed) a hstart
      exact h1.trans (ih _ _ _ h1.failed)

theorem Array.getElem?_push_of_getElem? {α : Type} {a : Array α} {i : Nat} {x y : α}
    (h : a[i]? = some x) : (a.push y)[i]? = some x := by
  have hi : i < a.size := by
    by_cases hlt : i < a.size
    · exact hlt
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at h
      simp at h
  rw [Array.getElem?_push_lt hi]
  simp only [Array.getElem?_eq_getElem hi] at h
  exact h

theorem pushPropStep_ok (st : EngineState p T) (pending : Array Pending) (failed : Bool)
    (pe : PLit × EClause p T) (hf : failed = false) :
    PropStepOK (st, pending, failed) (pushPropStep (st, pending, failed) pe) := by
  unfold pushPropStep
  dsimp only
  simp only [hf, Bool.false_eq_true, if_false]
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [canonClause_reasons, canonLit_reasons, Array.toList_push]
    exact List.prefix_append _ _
  · rw [Array.toList_push]
    exact List.prefix_append _ _
  · intro item hmem hnotin
    rw [Array.toList_push, List.mem_append] at hmem
    rcases hmem with hmem | hmem
    · exact absurd hmem hnotin
    · simp only [List.mem_singleton] at hmem
      subst hmem
      exact ⟨_, _, rfl, rfl, Array.getElem?_push_size⟩
  · intro i x h
    simpa [canonClause_reasons, canonLit_reasons] using Array.getElem?_push_of_getElem? h

theorem pushPropPrunesOK (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) :
    PropStepOK (st, pending, false) (pushPropPrunes st pending ps) := by
  rw [pushPropPrunes_eq, ← Array.foldl_toList]
  exact list_foldl_propOK pushPropStep (fun acc pe hf => by
    obtain ⟨s, p, f⟩ := acc
    exact pushPropStep_ok s p f pe hf) st pending false rfl ps.toList

theorem pushPropPrunes_reasons_prefix (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) :
    st.reasons.toList <+: (pushPropPrunes st pending ps).1.reasons.toList :=
  (pushPropPrunesOK st pending ps).reasons_pre

theorem pushPropPrunes_pending_prefix (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) :
    pending.toList <+: (pushPropPrunes st pending ps).2.1.toList :=
  (pushPropPrunesOK st pending ps).pending_pre

theorem pushPropPrunes_pending_spec (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) {item : Pending}
    (h : item ∈ (pushPropPrunes st pending ps).2.1.toList) :
    item ∈ pending.toList ∨
      ∃ rid c, item.reason = .reason rid ∧ item.count = true ∧
        (pushPropPrunes st pending ps).1.reasons[rid]? = some c := by
  by_cases hmem : item ∈ pending.toList
  · exact Or.inl hmem
  · exact Or.inr ((pushPropPrunesOK st pending ps).new_pending item h hmem)

theorem pushPropPrunes_pending_reason_resolves (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) {item : Pending}
    (h : item ∈ (pushPropPrunes st pending ps).2.1.toList)
    (hnew : item ∉ pending.toList) :
    ∃ c, reasonClause? (pushPropPrunes st pending ps).1 item.reason = some c := by
  rcases pushPropPrunes_pending_spec st pending ps h with hmem | ⟨rid, c, hr, hc, hget⟩
  · exact absurd hmem hnew
  · exact ⟨c, by rw [hr, reasonClause?_reason]; exact hget⟩

theorem pushClausePrunes_eq (pending : Array Pending) (ps : Array (PLit × Nat)) :
    pushClausePrunes pending ps = ps.foldl
      (fun acc pe => acc.push ({ lit := pe.1, reason := .learned pe.2, count := true } : Pending))
      pending := rfl

theorem list_foldl_push_prefix {α : Type} (f : Array Pending → α → Array Pending)
    (hf : ∀ p a, p.toList <+: (f p a).toList)
    (p : Array Pending) (l : List α) : p.toList <+: (l.foldl f p).toList := by
  induction l generalizing p with
  | nil => exact List.prefix_refl _
  | cons a rest ih => rw [List.foldl_cons]; exact (hf p a).trans (ih _)

theorem pushClausePrunes_prefix (pending : Array Pending) (ps : Array (PLit × Nat)) :
    pending.toList <+: (pushClausePrunes pending ps).toList := by
  rw [pushClausePrunes_eq, ← Array.foldl_toList]
  exact list_foldl_push_prefix _ (fun p pe => by
    rw [Array.toList_push]; exact List.prefix_append _ _) pending ps.toList

theorem pushClausePrunes_mem (pending : Array Pending) (ps : Array (PLit × Nat))
    {item : Pending} (h : item ∈ (pushClausePrunes pending ps).toList) :
    item ∈ pending.toList ∨
      ∃ l id, (l, id) ∈ ps.toList ∧ item = { lit := l, reason := .learned id, count := true } := by
  rw [pushClausePrunes_eq, ← Array.foldl_toList] at h
  revert h
  induction ps.toList generalizing pending with
  | nil => intro h; exact Or.inl (by simpa using h)
  | cons pe rest ih =>
      intro h
      rw [List.foldl_cons] at h
      rcases ih (pending.push ({ lit := pe.1, reason := .learned pe.2, count := true } : Pending)) h with
        hmem | ⟨l, id, hmem, heq⟩
      · rw [Array.toList_push, List.mem_append] at hmem
        rcases hmem with hmem | hmem
        · exact Or.inl hmem
        · right
          simp only [List.mem_singleton] at hmem
          subst hmem
          exact ⟨pe.1, pe.2, List.mem_cons_self, rfl⟩
      · exact Or.inr ⟨l, id, List.mem_cons_of_mem _ hmem, heq⟩

theorem drain_fuel_zero (st : EngineState p T) (pending : Array Pending) :
    (drain p T st pending 0).fuel = 0 ∧
      (drain p T st pending 0).conflict = none ∧
      (drain p T st pending 0).failed = false ∧
      (drain p T st pending 0).st = st := by
  simp [drain]

theorem propagate_fuel_zero (st : EngineState p T) :
    (propagate p T st 0).fuel = 0 ∧
      (propagate p T st 0).conflict = none ∧
      (propagate p T st 0).failed = false ∧
      (propagate p T st 0).st = st :=
  drain_fuel_zero st #[]

theorem drain_fixpoint (st : EngineState p T) (pending : Array Pending) (f : Nat)
    (hconf : (drain p T st pending f).conflict = none)
    (hfail : (drain p T st pending f).failed = false)
    (hfuel : 0 < (drain p T st pending f).fuel) :
    (drain p T st pending f).st.queueHigh.size = 0 ∧
      (drain p T st pending f).st.queueLow.size = 0 := by
  induction st, pending, f using drain.induct with
  | case1 st pending =>
      simp [drain] at hfuel
  | case2 st pending f item hback st1 neg failed ec hins =>
      simp [drain, hback, hins] at hconf
  | case3 st pending f item hback st1 neg hins =>
      simp [drain, hback, hins] at hfail
  | case4 st pending f item hback pending1 st1 failed hf hins ih =>
      have hconf' : (drain p T st1 pending1 f).conflict = none := by
        simpa [drain, hback, hins, hf, pending1] using hconf
      have hfail' : (drain p T st1 pending1 f).failed = false := by
        simpa [drain, hback, hins, hf, pending1] using hfail
      have hfuel' : 0 < (drain p T st1 pending1 f).fuel := by
        simpa [drain, hback, hins, hf, pending1] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hins, hf, pending1] using And.intro h1 h2
  | case5 st pending f item hback pending1 st1 failed hf nl db st2 hins hprop ih =>
      have hconf' : (drain p T { st1 with db := db } pending1 f).conflict = none := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using hconf
      have hfail' : (drain p T { st1 with db := db } pending1 f).failed = false := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using hfail
      have hfuel' : 0 < (drain p T { st1 with db := db } pending1 f).fuel := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using And.intro h1 h2
  | case6 st pending f item hback st1 failed hf nl db st2 ec id ec1 st3 hcanon hins hprop =>
      simp [drain, hback, hins, hprop, hcanon, hf, st2] at hconf
  | case7 st pending f item hback pending1 st1 failed hf nl db st2 ps hins hprop ih =>
      have hconf' : (drain p T { st1 with db := db } (pushClausePrunes pending1 ps) f).conflict = none := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using hconf
      have hfail' : (drain p T { st1 with db := db } (pushClausePrunes pending1 ps) f).failed = false := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using hfail
      have hfuel' : 0 < (drain p T { st1 with db := db } (pushClausePrunes pending1 ps) f).fuel := by
        simpa [drain, hback, hins, hprop, hf, pending1, st2] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using And.intro h1 h2
  | case8 st pending f hback hq id st1 hprops ih =>
      have hconf' : (drain p T st1 pending f).conflict = none := by
        simpa [drain, hback, hq, hprops, st1, id] using hconf
      have hfail' : (drain p T st1 pending f).failed = false := by
        simpa [drain, hback, hq, hprops, st1, id] using hfail
      have hfuel' : 0 < (drain p T st1 pending f).fuel := by
        simpa [drain, hback, hq, hprops, st1, id] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hq, hprops, st1, id] using And.intro h1 h2
  | case9 st pending f hback hq id st1 pr hprops hrun ih =>
      have hconf' : (drain p T st1 pending f).conflict = none := by
        simpa [drain, hback, hq, hprops, hrun, st1, id] using hconf
      have hfail' : (drain p T st1 pending f).failed = false := by
        simpa [drain, hback, hq, hprops, hrun, st1, id] using hfail
      have hfuel' : 0 < (drain p T st1 pending f).fuel := by
        simpa [drain, hback, hq, hprops, hrun, st1, id] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hq, hprops, hrun, st1, id] using And.intro h1 h2
  | case10 st pending f hback hq id st1 pr hprops ec hrun ec1 st2 hcanon =>
      simp [drain, hback, hq, hprops, hrun, hcanon, st1, id] at hconf
  | case11 st pending f hback hq id st1 pr hprops ps hrun st2 pend hpush =>
      simp [drain, hback, hq, hprops, hrun, hpush, st1, id] at hfail
  | case12 st pending f hback hq id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      have hconf' : (drain p T st2 pend f).conflict = none := by
        simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using hconf
      have hfail' : (drain p T st2 pend f).failed = false := by
        simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using hfail
      have hfuel' : 0 < (drain p T st2 pend f).fuel := by
        simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using And.intro h1 h2
  | case13 st pending f hback hq hql id st1 hprops ih =>
      have hconf' : (drain p T st1 pending f).conflict = none := by
        simpa [drain, hback, hq, hql, hprops, st1, id] using hconf
      have hfail' : (drain p T st1 pending f).failed = false := by
        simpa [drain, hback, hq, hql, hprops, st1, id] using hfail
      have hfuel' : 0 < (drain p T st1 pending f).fuel := by
        simpa [drain, hback, hq, hql, hprops, st1, id] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hq, hql, hprops, st1, id] using And.intro h1 h2
  | case14 st pending f hback hq hql id st1 pr hprops hrun ih =>
      have hconf' : (drain p T st1 pending f).conflict = none := by
        simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using hconf
      have hfail' : (drain p T st1 pending f).failed = false := by
        simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using hfail
      have hfuel' : 0 < (drain p T st1 pending f).fuel := by
        simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using And.intro h1 h2
  | case15 st pending f hback hq hql id st1 pr hprops ec hrun ec1 st2 hcanon =>
      simp [drain, hback, hq, hql, hprops, hrun, hcanon, st1, id] at hconf
  | case16 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend hpush =>
      simp [drain, hback, hq, hql, hprops, hrun, hpush, st1, id] at hfail
  | case17 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      have hconf' : (drain p T st2 pend f).conflict = none := by
        simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using hconf
      have hfail' : (drain p T st2 pend f).failed = false := by
        simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using hfail
      have hfuel' : 0 < (drain p T st2 pend f).fuel := by
        simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using hfuel
      obtain ⟨h1, h2⟩ := ih hconf' hfail' hfuel'
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using And.intro h1 h2
  | case18 st pending f hback hq hql =>
      have h1 : st.queueHigh = #[] := Array.eq_empty_of_size_eq_zero (by omega)
      have h2 : st.queueLow = #[] := Array.eq_empty_of_size_eq_zero (by omega)
      simp [drain, hback, h1, h2]

theorem propagate_fixpoint (st : EngineState p T) (f : Nat)
    (hconf : (propagate p T st f).conflict = none)
    (hfail : (propagate p T st f).failed = false)
    (hfuel : 0 < (propagate p T st f).fuel) :
    (propagate p T st f).st.queueHigh.size = 0 ∧
      (propagate p T st f).st.queueLow.size = 0 :=
  drain_fixpoint st #[] f hconf hfail hfuel

theorem Frame.refl (st : EngineState p T) : Frame st st :=
  ⟨rfl, rfl, rfl, rfl, List.prefix_refl _, fun h => h, List.prefix_refl _,
    List.prefix_refl _, fun _ => rfl, rfl, fun h => h⟩

theorem Frame.trans {a b c : EngineState p T} (h1 : Frame a b) (h2 : Frame b c) :
    Frame a c :=
  ⟨h1.props.trans h2.props, h1.subs.trans h2.subs, h1.level.trans h2.level,
    h1.levelStart.trans h2.levelStart, h1.table_pre.trans h2.table_pre,
    fun h => h2.tableWF (h1.tableWF h), h1.reasons_pre.trans h2.reasons_pre,
    h1.trail_pre.trans h2.trail_pre, fun id => (h1.db_e id).trans (h2.db_e id),
    h1.db_size.trans h2.db_size, fun h => h2.db_inv (h1.db_inv h)⟩

theorem Frame.congr {st0 st st' : EngineState p T} (h : Frame st0 st)
    (hp : st'.props = st.props) (hs : st'.subs = st.subs) (hl : st'.level = st.level)
    (hls : st'.levelStart = st.levelStart) (ht : st'.table = st.table)
    (hr : st'.reasons = st.reasons) (htr : st'.trail = st.trail) (hdb : st'.db = st.db) :
    Frame st0 st' :=
  ⟨h.props.trans hp.symm, h.subs.trans hs.symm, h.level.trans hl.symm,
    h.levelStart.trans hls.symm,
    by rw [ht]; exact h.table_pre, by rw [ht]; exact h.tableWF,
    by rw [hr]; exact h.reasons_pre, by rw [htr]; exact h.trail_pre,
    fun id => by rw [hdb]; exact h.db_e id, by rw [hdb]; exact h.db_size,
    fun hinv => by rw [hdb]; exact h.db_inv hinv⟩

theorem frame_canonLit (st : EngineState p T) (l : PLit) :
    Frame st (canonLit st l).2 :=
  ⟨(canonLit_props st l).symm, (canonLit_subs st l).symm, (canonLit_level st l).symm, (canonLit_levelStart st l).symm,
    canonLit_table_append_only st l,
    canonLit_tableWF st l, by rw [canonLit_reasons]; exact List.prefix_refl _,
    by rw [canonLit_trail]; exact List.prefix_refl _, fun _ => by rw [canonLit_db],
    by rw [canonLit_db], fun h => by simpa [canonLit_db] using h⟩

theorem frame_canonClause (st : EngineState p T) (c : EClause p T) :
    Frame st (canonClause st c).2 :=
  ⟨(canonClause_props st c).symm, (canonClause_subs st c).symm, (canonClause_level st c).symm,
    (canonClause_levelStart st c).symm,
    canonClause_table_append_only st c,
    canonClause_tableWF st c, by rw [canonClause_reasons]; exact List.prefix_refl _,
    by rw [canonClause_trail]; exact List.prefix_refl _, fun _ => by rw [canonClause_db],
    by rw [canonClause_db], fun h => by simpa [canonClause_db] using h⟩

theorem frame_trailPush (st : EngineState p T) (e : Entry) :
    Frame st (trailPush st e) :=
  ⟨(trailPush_props st e).symm, (trailPush_subs st e).symm, (trailPush_level st e).symm, (trailPush_levelStart st e).symm,
    by rw [trailPush_table]; exact List.prefix_refl _,
    by rw [trailPush_table]; exact fun h => h,
    by rw [trailPush_reasons]; exact List.prefix_refl _,
    by rw [trailPush_trail, Array.toList_push]; exact List.prefix_append _ _,
    fun _ => by rw [trailPush_db], by rw [trailPush_db],
    fun h => by simpa [trailPush_db] using h⟩

theorem frame_emitSlot (st : EngineState p T) (s : Slot) (old new : DomC) :
    Frame st (emitSlot st s old new) :=
  ⟨(emitSlot_props st s old new).symm, (emitSlot_subs st s old new).symm, (emitSlot_level st s old new).symm,
    (emitSlot_levelStart st s old new).symm,
    by rw [emitSlot_table]; exact List.prefix_refl _,
    by rw [emitSlot_table]; exact fun h => h,
    by rw [emitSlot_reasons]; exact List.prefix_refl _,
    by rw [emitSlot_trail]; exact List.prefix_refl _,
    fun _ => by rw [emitSlot_db], by rw [emitSlot_db],
    fun h => by simpa [emitSlot_db] using h⟩

theorem frame_setInQueue (st : EngineState p T) (id : Nat) (v : UInt8) :
    Frame st (setInQueue st id v) :=
  ⟨(setInQueue_props st id v).symm, (setInQueue_subs st id v).symm, (setInQueue_level st id v).symm,
    (setInQueue_levelStart st id v).symm,
    by rw [setInQueue_table]; exact List.prefix_refl _,
    by rw [setInQueue_table]; exact fun h => h,
    by rw [setInQueue_reasons]; exact List.prefix_refl _,
    by rw [setInQueue_trail]; exact List.prefix_refl _,
    fun _ => by rw [setInQueue_db], by rw [setInQueue_db],
    fun h => by simpa [setInQueue_db] using h⟩

theorem frame_domsStats (st : EngineState p T) (doms : Array DomC) (stats : EngineStats) :
    Frame st { st with doms := doms, stats := stats } :=
  ⟨rfl, rfl, rfl, rfl, List.prefix_refl _, fun h => h, List.prefix_refl _,
    List.prefix_refl _, fun _ => rfl, rfl, fun h => h⟩

theorem frame_reasonsPush (st : EngineState p T) (ec : EClause p T) :
    Frame st { st with reasons := st.reasons.push ec } :=
  ⟨rfl, rfl, rfl, rfl, List.prefix_refl _, fun h => h,
    by rw [Array.toList_push]; exact List.prefix_append _ _, List.prefix_refl _,
    fun _ => rfl, rfl, fun h => h⟩

theorem frame_queueHighPop (st : EngineState p T) :
    Frame st { st with queueHigh := st.queueHigh.pop } :=
  ⟨rfl, rfl, rfl, rfl, List.prefix_refl _, fun h => h, List.prefix_refl _,
    List.prefix_refl _, fun _ => rfl, rfl, fun h => h⟩

theorem frame_queueLowPop (st : EngineState p T) :
    Frame st { st with queueLow := st.queueLow.pop } :=
  ⟨rfl, rfl, rfl, rfl, List.prefix_refl _, fun h => h, List.prefix_refl _,
    List.prefix_refl _, fun _ => rfl, rfl, fun h => h⟩

theorem frame_propagateLiteral (st : EngineState p T) (nl : PLit) :
    Frame st { st with db := (st.db.propagateLiteral p T st.doms nl).1 } :=
  ⟨rfl, rfl, rfl, rfl, List.prefix_refl _, fun h => h, List.prefix_refl _,
    List.prefix_refl _, fun id => (ClauseDB.propagateLiteral_clauses_e st.db st.doms nl id).symm,
    (ClauseDB.propagateLiteral_clauses_size st.db st.doms nl).symm,
    fun h => ClauseDB.propagateLiteral_inv st.db st.doms nl h⟩

theorem frame_insertPending (st : EngineState p T) (item : Pending) :
    Frame st (insertPending st item).1 := by
  unfold insertPending
  dsimp only
  split
  · exact frame_canonLit st item.lit
  · split
    · exact (frame_canonLit st item.lit).trans (frame_canonClause _ _)
    · exact frame_canonLit st item.lit
  · split
    · split
      · exact (frame_canonLit st item.lit).trans (frame_canonClause _ _)
      · exact frame_canonLit st item.lit
    · rename_i hz
      let st1 : EngineState p T := (canonLit st item.lit).2
      let l : PLit := (canonLit st item.lit).1
      let slot : Slot := l.slot
      let d : DomC := st1.doms.getD slot DomC.empty
      let d' : DomC := d.applyLit l.lit
      let e : Entry := { lit := l, level := st1.level, reason := item.reason, slot := slot, prev := d }
      let st2 : EngineState p T := { st1 with
        doms := st1.doms.set! slot d',
        stats := { st1.stats with
          propagations := st1.stats.propagations + (if item.count then 1 else 0) } }
      let st3 : EngineState p T := trailPush st2 e
      let st4 : EngineState p T := emitSlot st3 slot d d'
      change Frame st (canonLit st4 l.negate).2
      exact (frame_canonLit st item.lit).trans
        ((frame_domsStats st1 _ _).trans
          ((frame_trailPush st2 e).trans
            ((frame_emitSlot st3 slot d d').trans (frame_canonLit st4 l.negate))))

theorem pushPropStep_frame (st : EngineState p T) (pending : Array Pending) (failed : Bool)
    (pe : PLit × EClause p T) (hf : failed = false) :
    Frame st (pushPropStep (st, pending, failed) pe).1 := by
  unfold pushPropStep
  dsimp only
  simp only [hf, Bool.false_eq_true, if_false]
  exact (frame_canonLit st pe.1).trans
    ((frame_canonClause _ pe.2).trans (frame_reasonsPush _ _))

theorem pushPropStep_failed (st : EngineState p T) (pending : Array Pending) (failed : Bool)
    (pe : PLit × EClause p T) (hf : failed = false) :
    (pushPropStep (st, pending, failed) pe).2.2 = false := by
  unfold pushPropStep
  dsimp only
  simp only [hf, Bool.false_eq_true, if_false]

theorem list_foldl_frame {α : Type}
    (f : EngineState p T × Array Pending × Bool → α → EngineState p T × Array Pending × Bool)
    (hf : ∀ acc a, acc.2.2 = false → Frame acc.1 (f acc a).1)
    (hff : ∀ acc a, acc.2.2 = false → (f acc a).2.2 = false)
    (st : EngineState p T) (pending : Array Pending) (failed : Bool) (hstart : failed = false)
    (l : List α) :
    Frame st (l.foldl f (st, pending, failed)).1 := by
  induction l generalizing st pending failed with
  | nil => exact Frame.refl st
  | cons a rest ih =>
      rw [List.foldl_cons]
      have h1 := hf (st, pending, failed) a hstart
      exact h1.trans (ih _ _ _ (hff (st, pending, failed) a hstart))

theorem frame_pushPropPrunes (st : EngineState p T) (pending : Array Pending)
    (ps : Array (PLit × EClause p T)) :
    Frame st (pushPropPrunes st pending ps).1 := by
  rw [pushPropPrunes_eq, ← Array.foldl_toList]
  exact list_foldl_frame pushPropStep (fun acc pe hf => by
    obtain ⟨s, p, f⟩ := acc
    exact pushPropStep_frame s p f pe hf) (fun acc pe hf => by
    obtain ⟨s, p, f⟩ := acc
    exact pushPropStep_failed s p f pe hf) st pending false rfl ps.toList

theorem drain_frame {st0 : EngineState p T} (st : EngineState p T)
    (pending : Array Pending) (f : Nat) (h : Frame st0 st) :
    Frame st0 (drain p T st pending f).st := by
  revert h
  induction st, pending, f using drain.induct with
  | case1 st pending =>
      intro h
      simpa [drain] using h
  | case2 st pending f item hback st1 neg failed ec hins =>
      intro h
      have h1 : Frame st0 st1 := by simpa [hins] using h.trans (frame_insertPending st item)
      simpa [drain, hback, hins] using h1
  | case3 st pending f item hback st1 neg hins =>
      intro h
      have h1 : Frame st0 st1 := by simpa [hins] using h.trans (frame_insertPending st item)
      simpa [drain, hback, hins] using h1
  | case4 st pending f item hback pending1 st1 failed hf hins ih =>
      intro h
      have h1 : Frame st0 st1 := by simpa [hins] using h.trans (frame_insertPending st item)
      simpa [drain, hback, hins, hf, pending1] using ih h1
  | case5 st pending f item hback pending1 st1 failed hf nl db st2 hins hprop ih =>
      intro h
      have h1 : Frame st0 st1 := by simpa [hins] using h.trans (frame_insertPending st item)
      have h2 : Frame st0 { st1 with db := db } := by
        simpa [hprop] using h1.trans (frame_propagateLiteral st1 nl)
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2
  | case6 st pending f item hback st1 failed hf nl db st2 ec id ec1 st3 hcanon hins hprop =>
      intro h
      have h1 : Frame st0 st1 := by simpa [hins] using h.trans (frame_insertPending st item)
      have h2 : Frame st0 { st1 with db := db } := by
        simpa [hprop] using h1.trans (frame_propagateLiteral st1 nl)
      have h3 : Frame st0 st3 := by
        simpa [hcanon, st2] using h2.trans (frame_canonClause _ ec)
      simpa [drain, hback, hins, hprop, hcanon, hf, st2] using h3
  | case7 st pending f item hback pending1 st1 failed hf nl db st2 ps hins hprop ih =>
      intro h
      have h1 : Frame st0 st1 := by simpa [hins] using h.trans (frame_insertPending st item)
      have h2 : Frame st0 { st1 with db := db } := by
        simpa [hprop] using h1.trans (frame_propagateLiteral st1 nl)
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2
  | case8 st pending f hback hq id st1 hprops ih =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueHighPop st)).trans (frame_setInQueue _ id 0)
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hprops, st1, id] using ih h1
  | case9 st pending f hback hq id st1 pr hprops hrun ih =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueHighPop st)).trans (frame_setInQueue _ id 0)
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hprops, hrun, st1, id] using ih h1
  | case10 st pending f hback hq id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueHighPop st)).trans (frame_setInQueue _ id 0)
      have h2 : Frame st0 st2 := by
        simpa [hcanon, st1, id] using h1.trans (frame_canonClause _ ec)
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hprops, hrun, hcanon, st1, id] using h2
  | case11 st pending f hback hq id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueHighPop st)).trans (frame_setInQueue _ id 0)
      have h2 : Frame st0 st2 := by
        simpa [hpush] using h1.trans (frame_pushPropPrunes st1 pending ps)
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, st1, id] using h2
  | case12 st pending f hback hq id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueHighPop st)).trans (frame_setInQueue _ id 0)
      have h2 : Frame st0 st2 := by
        simpa [hpush] using h1.trans (frame_pushPropPrunes st1 pending ps)
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using ih h2
  | case13 st pending f hback hq hql id st1 hprops ih =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueLowPop st)).trans (frame_setInQueue _ id 0)
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hql, hprops, st1, id] using ih h1
  | case14 st pending f hback hq hql id st1 pr hprops hrun ih =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueLowPop st)).trans (frame_setInQueue _ id 0)
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using ih h1
  | case15 st pending f hback hq hql id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueLowPop st)).trans (frame_setInQueue _ id 0)
      have h2 : Frame st0 st2 := by
        simpa [hcanon, st1, id] using h1.trans (frame_canonClause _ ec)
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hcanon, st1, id] using h2
  | case16 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueLowPop st)).trans (frame_setInQueue _ id 0)
      have h2 : Frame st0 st2 := by
        simpa [hpush] using h1.trans (frame_pushPropPrunes st1 pending ps)
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, st1, id] using h2
  | case17 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : Frame st0 st1 := by
        dsimp only [st1]
        exact (h.trans (frame_queueLowPop st)).trans (frame_setInQueue _ id 0)
      have h2 : Frame st0 st2 := by
        simpa [hpush] using h1.trans (frame_pushPropPrunes st1 pending ps)
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using ih h2
  | case18 st pending f hback hq hql =>
      intro h
      simpa [drain, hback, hq, hql] using h

theorem drain_props {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) : (drain p T st pending f).st.props = st0.props :=
  (drain_frame st pending f h).props.symm

theorem drain_subs {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) : (drain p T st pending f).st.subs = st0.subs :=
  (drain_frame st pending f h).subs.symm

theorem drain_level {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) : (drain p T st pending f).st.level = st0.level :=
  (drain_frame st pending f h).level.symm

theorem drain_levelStart {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) : (drain p T st pending f).st.levelStart = st0.levelStart :=
  (drain_frame st pending f h).levelStart.symm

theorem drain_table_prefix {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) :
    st0.table.lits.toList <+: (drain p T st pending f).st.table.lits.toList :=
  (drain_frame st pending f h).table_pre

theorem drain_tableWF {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) (h0 : st0.table.TableWF) :
    (drain p T st pending f).st.table.TableWF :=
  (drain_frame st pending f h).tableWF h0

theorem drain_reasons_prefix {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) :
    st0.reasons.toList <+: (drain p T st pending f).st.reasons.toList :=
  (drain_frame st pending f h).reasons_pre

theorem drain_trail_prefix {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) :
    st0.trail.toList <+: (drain p T st pending f).st.trail.toList :=
  (drain_frame st pending f h).trail_pre

theorem drain_db_e {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) (id : Nat) :
    (st0.db.clauses[id]?).map (fun sc : StoredClause p T => sc.e) =
      ((drain p T st pending f).st.db.clauses[id]?).map (fun sc : StoredClause p T => sc.e) :=
  (drain_frame st pending f h).db_e id

theorem drain_db_size {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) :
    st0.db.clauses.size = (drain p T st pending f).st.db.clauses.size :=
  (drain_frame st pending f h).db_size

theorem drain_db_inv {st0 st : EngineState p T} (pending : Array Pending) (f : Nat)
    (h : Frame st0 st) (hinv : st0.db.Inv) : (drain p T st pending f).st.db.Inv :=
  (drain_frame st pending f h).db_inv hinv

theorem propagate_props_subs {st : EngineState p T} (f : Nat) :
    (propagate p T st f).st.props = st.props ∧
      (propagate p T st f).st.subs = st.subs ∧
      (propagate p T st f).st.level = st.level ∧
      (propagate p T st f).st.levelStart = st.levelStart := by
  have h := drain_frame st #[] f (Frame.refl st)
  exact ⟨h.props.symm, h.subs.symm, h.level.symm, h.levelStart.symm⟩

theorem propagate_table {st : EngineState p T} (f : Nat) :
    st.table.lits.toList <+: (propagate p T st f).st.table.lits.toList :=
  (drain_frame st #[] f (Frame.refl st)).table_pre

theorem propagate_tableWF {st : EngineState p T} (f : Nat)
    (hT : st.table.TableWF) : (propagate p T st f).st.table.TableWF :=
  (drain_frame st #[] f (Frame.refl st)).tableWF hT

theorem propagate_reasons {st : EngineState p T} (f : Nat) :
    st.reasons.toList <+: (propagate p T st f).st.reasons.toList :=
  (drain_frame st #[] f (Frame.refl st)).reasons_pre

end LeanFzn.Engine
