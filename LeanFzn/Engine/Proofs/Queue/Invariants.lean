/-
Purpose: Queue invariants lemmas, separated from executable propagation.
Dependencies: LeanFzn.Engine.Proofs.Queue.History
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Proofs.Queue.History

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

set_option maxHeartbeats 4000000

theorem DomC.empty_WF : DomC.empty.WF := by simp [DomC.WF, DomC.empty]

theorem Array.set!_eq_self_of_ge {α : Type} (a : Array α) {i : Nat} (v : α)
    (h : a.size ≤ i) : a.set! i v = a := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hji : i = j
  · subst hji
    rw [if_pos rfl, if_neg (by omega), Array.getElem?_eq_none (by omega)]
  · rw [if_neg hji]

theorem DomsWF.congr {st st' : EngineState p T} (h : DomsWF st) (hd : st'.doms = st.doms) :
    DomsWF st' := by
  intro s hs
  rw [hd] at hs ⊢
  exact h s hs

theorem DomsWF.setGrow {st : EngineState p T} (h : DomsWF st) {i : Nat} {v : DomC}
    (hv : v.WF) : DomsWF { st with doms := st.doms.setGrow i v DomC.empty } := by
  intro s hs
  simp only
  by_cases hsi : s = i
  · subst hsi
    rw [Array.getD_setGrow_self]
    exact hv
  · rw [Array.getD_setGrow_other (d := DomC.empty) st.doms i s v hsi]
    by_cases hso : s < st.doms.size
    · exact h s hso
    · have hempty : st.doms.getD s DomC.empty = DomC.empty := by
        rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_none (Nat.le_of_not_lt hso)]
        rfl
      rw [hempty]
      exact DomC.empty_WF

theorem DomsWF.set!_of_lt {st : EngineState p T} (h : DomsWF st) {i : Nat} {v : DomC}
    (hi : i < st.doms.size) (hv : v.WF) :
    DomsWF { st with doms := st.doms.set! i v } := by
  have hset : st.doms.set! i v = st.doms.setGrow i v DomC.empty :=
    Array.set!_eq_setGrow_of_lt (a := st.doms) (i := i) (v := v) (d := DomC.empty) hi
  have hst : ({ st with doms := st.doms.set! i v } : EngineState p T) =
      { st with doms := st.doms.setGrow i v DomC.empty } := by rw [hset]
  rw [hst]
  exact h.setGrow hv

theorem DomsWF.set! {st : EngineState p T} (h : DomsWF st) {i : Nat} {v : DomC}
    (hv : v.WF) : DomsWF { st with doms := st.doms.set! i v } := by
  by_cases hi : i < st.doms.size
  · exact h.set!_of_lt hi hv
  · have hset : st.doms.set! i v = st.doms :=
      Array.set!_eq_self_of_ge _ _ (Nat.le_of_not_lt hi)
    have hst : ({ st with doms := st.doms.set! i v } : EngineState p T) = st := by
      rw [hset]
    rw [hst]
    exact h

theorem insertPending_domsWF {st : EngineState p T} (h : DomsWF st) (item : Pending) :
    DomsWF (insertPending st item).1 := by
  unfold insertPending
  dsimp only
  split
  · exact DomsWF.congr h (canonLit_doms st item.lit)
  · split
    · exact DomsWF.congr h (canonClause_doms (canonLit st item.lit).2 _)
    · exact DomsWF.congr h (canonLit_doms st item.lit)
  · split
    · split
      · exact DomsWF.congr h (canonClause_doms (canonLit st item.lit).2 _)
      · exact DomsWF.congr h (canonLit_doms st item.lit)
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
      change DomsWF (canonNegLit st4 l).2
      have h1 : DomsWF st1 := DomsWF.congr h (canonLit_doms st item.lit)
      have hdWF : d.WF := by
        by_cases hslot : slot < st1.doms.size
        · exact h1 slot hslot
        · have hempty : d = DomC.empty := by
            simp only [d, Array.getD_eq_getElem?_getD]
            rw [Array.getElem?_eq_none (Nat.le_of_not_lt hslot)]
            rfl
          rw [hempty]
          exact DomC.empty_WF
      have hd'WF : d'.WF := by
        simp only [d']
        exact DomC.applyLit_WF d l.lit hdWF
      have h2 : DomsWF st2 := by
        simp only [st2]
        exact DomsWF.set! h1 hd'WF
      have h3 : DomsWF st3 :=
        DomsWF.congr h2 (by simp [st3, trailPush])
      have h4 : DomsWF st4 :=
        DomsWF.congr h3 (emitSlot_doms st3 slot d d')
      exact DomsWF.congr h4 (canonNegLit_doms st4 l)

theorem ensureInQueue_levelStart (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).levelStart = st.levelStart := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_level (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).level = st.level := by
  unfold ensureInQueue
  rfl

theorem setInQueue_levelStart (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).levelStart = st.levelStart := by
  unfold setInQueue
  split <;> simp

theorem setInQueue_level (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).level = st.level := by
  unfold setInQueue
  split <;> simp

theorem enqueueProp_levelStart (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).levelStart = st.levelStart := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_levelStart]
    · simp [ensureInQueue_levelStart]
  · rfl

theorem enqueueProp_level (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).level = st.level := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_level]
    · simp [ensureInQueue_level]
  · rfl

theorem list_foldl_levelStart {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).levelStart = st.levelStart) (st : EngineState p T) :
    (l.foldl f st).levelStart = st.levelStart := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_level {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).level = st.level) (st : EngineState p T) :
    (l.foldl f st).level = st.level := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem enqueueSubs_levelStart (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).levelStart = st.levelStart := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_levelStart _ _ (fun st id => enqueueProp_levelStart st id) st
  · rfl

theorem enqueueSubs_level (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).level = st.level := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_level _ _ (fun st id => enqueueProp_level st id) st
  · rfl

theorem emitSlot_levelStart (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).levelStart = st.levelStart := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_levelStart]
    · split <;> simp [enqueueSubs_levelStart]

theorem emitSlot_level (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).level = st.level := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_level]
    · split <;> simp [enqueueSubs_level]

theorem insertPending_trailInv {st : EngineState p T} (h : TrailInv st) (item : Pending) :
    TrailInv (insertPending st item).1 := by
  unfold insertPending
  dsimp only
  split
  · exact TrailInv.congr h (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
  · split
    · exact TrailInv.congr h (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
    · exact TrailInv.congr h (by simp [canonLit]) (by simp [canonLit])
        (by simp [canonLit]) (by simp [canonLit]) (by simp [canonLit])
  · split
    · split
      · exact TrailInv.congr h (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      · exact TrailInv.congr h (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
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
      change TrailInv (canonNegLit st4 l).2
      have h1 : TrailInv st1 :=
        TrailInv.congr h (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      have h2 : TrailInv st2 :=
        TrailInv.congr h1 (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      have h3 : TrailInv st3 :=
        trailPush_trailInv h2 (e := e) (by simp [e, st2])
      have h4 : TrailInv st4 :=
        TrailInv.congr h3 (emitSlot_trail st3 slot d d')
          (emitSlot_levelStart st3 slot d d') (emitSlot_level st3 slot d d')
          (emitSlot_changeIndex st3 slot d d') (emitSlot_reasonCap st3 slot d d')
      exact TrailInv.congr h4 (by rfl) (by rfl) (by rfl) (by rfl) (by simp [canonNegLit])

theorem List.foldl_domStep_WF {tr : Array Entry} (l : List Nat) {d : DomC} (hd : d.WF) :
    (l.foldl (domStep tr) d).WF := by
  induction l generalizing d with
  | nil => exact hd
  | cons x xs ih =>
      rw [List.foldl_cons]
      apply ih
      unfold domStep
      split
      · rename_i e he
        exact DomC.applyLit_WF _ e.lit.lit hd
      · exact hd

theorem domAfter_WF {init : Array DomC} {st : EngineState p T} {s k : Nat}
    (hd : (init.getD s DomC.empty).WF) : (domAfter init st s k).WF := by
  rw [domAfter, ← Array.foldl_toList]
  exact List.foldl_domStep_WF _ hd

theorem initWF_of_InitInv {p : CompiledProblem DomConstraint} {init : Array DomC}
    (hi : InitInv p init) : ∀ s, (init.getD s DomC.empty).WF := by
  intro s
  rw [hi s]
  cases h : DomC.ofDom? (p.domains.getD s Dom.empty) with
  | some d => simpa [h] using DomC.ofDom?_wf _ _ h
  | none => simpa [h] using DomC.empty_WF

theorem slotHistory_domsWF {p : CompiledProblem DomConstraint} {init : Array DomC}
    {st : EngineState p T} (hi : InitInv p init) (h : SlotHistory init st) :
    DomsWF st := by
  intro s hs
  rw [h.doms_eq s]
  exact domAfter_WF (initWF_of_InitInv hi s)

theorem HistInv.congr {init : Array DomC} {st st' : EngineState p T} (h : HistInv init st)
    (hd : st'.doms = st.doms) (htr : st'.trail = st.trail)
    (hcl : ∀ s, st'.changeList s = st.changeList s)
    (hci : st'.changeIndex = st.changeIndex)
    (hls : st'.levelStart = st.levelStart) (hl : st'.level = st.level)
    (hrc : st'.reasonCap = st.reasonCap) :
    HistInv init st' := by
  obtain ⟨hsh, hti⟩ := h
  exact ⟨SlotHistory.congr hsh hd htr hcl,
    TrailInv.congr hti htr hls hl hci hrc⟩

theorem insertPending_histInv {init : Array DomC} {st : EngineState p T} (h : HistInv init st)
    (item : Pending) : HistInv init (insertPending st item).1 := by
  obtain ⟨hsh, hti⟩ := h
  exact ⟨insertPending_slotHistory hsh hti item, insertPending_trailInv hti item⟩

theorem canonLit_histInv {init : Array DomC} {st : EngineState p T} (h : HistInv init st)
    (l : PLit) : HistInv init (canonLit st l).2 := by
  obtain ⟨hsh, hti⟩ := h
  exact ⟨SlotHistory.congr hsh (canonLit_doms st l) (canonLit_trail st l)
      (fun s => canonLit_changeList st l s),
    TrailInv.congr hti (canonLit_trail st l) rfl rfl rfl (by rfl)⟩

theorem canonClause_histInv {init : Array DomC} {st : EngineState p T} (h : HistInv init st)
    (c : EClause p T) : HistInv init (canonClause st c).2 := by
  obtain ⟨hsh, hti⟩ := h
  exact ⟨SlotHistory.congr hsh (canonClause_doms st c) (canonClause_trail st c)
      (fun s => canonClause_changeList st c s),
    TrailInv.congr hti (canonClause_trail st c) rfl rfl rfl (by rfl)⟩

theorem setInQueue_histInv {init : Array DomC} {st : EngineState p T} (h : HistInv init st)
    (id : Nat) (v : UInt8) : HistInv init (setInQueue st id v) := by
  obtain ⟨hsh, hti⟩ := h
  exact ⟨SlotHistory.congr hsh (setInQueue_doms st id v) (setInQueue_trail st id v)
      (by intro s; rw [EngineState.changeList, setInQueue_changeIndex]; rfl),
    TrailInv.congr hti (setInQueue_trail st id v) (setInQueue_levelStart st id v)
      (setInQueue_level st id v) (setInQueue_changeIndex st id v)
      (setInQueue_reasonCap st id v)⟩

theorem pushPropPrunes_histInv {init : Array DomC} {st : EngineState p T} (h : HistInv init st)
    (pending : Array Pending) (ps : Array (PLit × EClause p T)) :
    HistInv init (pushPropPrunes st pending ps).1 := by
  unfold pushPropPrunes
  rw [← Array.foldl_toList]
  let f : (EngineState p T × Array Pending × Bool) → (PLit × EClause p T) →
      (EngineState p T × Array Pending × Bool) :=
    fun (acc : EngineState p T × Array Pending × Bool) pe =>
      let (st, pend, failed) := acc
      if failed then acc
      else
        let (l, st) := canonLit st pe.1
        let (ec, st) := canonClause st pe.2
        let rid := st.reasons.size
        let st := { st with reasons := st.reasons.push ec }
        (st, pend.push { lit := l, reason := .reason rid, count := true }, false)
  change HistInv init (List.foldl f (st, pending, false) ps.toList).1
  have step : ∀ (acc : EngineState p T × Array Pending × Bool) (pe : PLit × EClause p T),
      HistInv init acc.1 → HistInv init (f acc pe).1 := by
    intro acc pe hacc
    obtain ⟨st0, pend0, failed0⟩ := acc
    dsimp only [f]
    split
    · simpa using hacc
    · apply HistInv.congr hacc
      · rfl
      · rfl
      · intro s; rfl
      · rfl
      · rfl
      · rfl
      · rfl
  have gen : ∀ (l : List (PLit × EClause p T)) (st : EngineState p T)
      (pend : Array Pending) (failed : Bool),
      HistInv init st → HistInv init (l.foldl f (st, pend, failed)).1 := by
    intro l
    induction l with
    | nil => intro st pend failed h; simpa using h
    | cons pe rest ih =>
        intro st pend failed h
        rw [List.foldl_cons]
        exact ih _ _ _ (step (st, pend, failed) pe h)
  exact gen ps.toList st pending false h

theorem drain_histInv {init : Array DomC} {st : EngineState p T} (h : HistInv init st)
    (pending : Array Pending) (f : Nat) :
    HistInv init (drain p T st pending f).st := by
  revert h
  induction st, pending, f using drain.induct with
  | case1 st pending =>
      intro h
      simpa [drain] using h
  | case2 st pending f item hback st1 neg failed ec hins =>
      intro h
      have h1 : HistInv init st1 := by simpa [hins] using insertPending_histInv h item
      simpa [drain, hback, hins] using h1
  | case3 st pending f item hback st1 neg hins =>
      intro h
      have h1 : HistInv init st1 := by simpa [hins] using insertPending_histInv h item
      simpa [drain, hback, hins] using h1
  | case4 st pending f item hback pending1 st1 failed hf hins ih =>
      intro h
      have h1 : HistInv init st1 := by simpa [hins] using insertPending_histInv h item
      simpa [drain, hback, hins, hf, pending1] using ih h1
  | case5 st pending f item hback pending1 st1 failed hf nl db st2 hins hprop ih =>
      intro h
      have h1 : HistInv init st1 := by simpa [hins] using insertPending_histInv h item
      have h2 : HistInv init { st1 with db := db } := by
        apply HistInv.congr h1
        · rfl
        · rfl
        · intro s; rfl
        · rfl
        · rfl
        · rfl
        · rfl
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2
  | case6 st pending f item hback st1 failed hf nl db st2 ec id ec1 st3 hcanon hins hprop =>
      intro h
      have h1 : HistInv init st1 := by simpa [hins] using insertPending_histInv h item
      have h2 : HistInv init { st1 with db := db } := by
        apply HistInv.congr h1
        · rfl
        · rfl
        · intro s; rfl
        · rfl
        · rfl
        · rfl
        · rfl
      have h3 : HistInv init st3 := by
        have := canonClause_histInv h2 ec
        simpa [hcanon, st2] using this
      simpa [drain, hback, hins, hprop, hcanon, hf, st2] using h3
  | case7 st pending f item hback pending1 st1 failed hf nl db st2 ps hins hprop ih =>
      intro h
      have h1 : HistInv init st1 := by simpa [hins] using insertPending_histInv h item
      have h2 : HistInv init { st1 with db := db } := by
        apply HistInv.congr h1
        · rfl
        · rfl
        · intro s; rfl
        · rfl
        · rfl
        · rfl
        · rfl
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2
  | case8 st pending f hback hq id st1 hprops ih =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hprops, st1, id] using ih h1
  | case9 st pending f hback hq id st1 pr hprops hrun ih =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hprops, hrun, st1, id] using ih h1
  | case10 st pending f hback hq id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : HistInv init st2 := by
        have hc := canonClause_histInv h1 ec
        simpa [hcanon, st1, id] using hc
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hprops, hrun, hcanon, st1, id] using h2
  | case11 st pending f hback hq id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : HistInv init st2 := by
        have := pushPropPrunes_histInv h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, st1, id] using h2
  | case12 st pending f hback hq id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : HistInv init st2 := by
        have := pushPropPrunes_histInv h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using ih h2
  | case13 st pending f hback hq hql id st1 hprops ih =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hql, hprops, st1, id] using ih h1
  | case14 st pending f hback hq hql id st1 pr hprops hrun ih =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using ih h1
  | case15 st pending f hback hq hql id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : HistInv init st2 := by
        have hc := canonClause_histInv h1 ec
        simpa [hcanon, st1, id] using hc
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hcanon, st1, id] using h2
  | case16 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : HistInv init st2 := by
        have := pushPropPrunes_histInv h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, st1, id] using h2
  | case17 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : HistInv init st1 := by
        dsimp only [st1]
        exact setInQueue_histInv (by
          apply HistInv.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : HistInv init st2 := by
        have := pushPropPrunes_histInv h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using ih h2
  | case18 st pending f hback hq hql =>
      intro h
      simpa [drain, hback, hq, hql] using h

theorem drain_slotHistory {init : Array DomC} {st : EngineState p T}
    (h : SlotHistory init st) (ht : TrailInv st) (pending : Array Pending) (f : Nat) :
    SlotHistory init (drain p T st pending f).st :=
  (drain_histInv ⟨h, ht⟩ pending f).1

theorem drain_trailInv {init : Array DomC} {st : EngineState p T}
    (h : SlotHistory init st) (ht : TrailInv st) (pending : Array Pending) (f : Nat) :
    TrailInv (drain p T st pending f).st :=
  (drain_histInv ⟨h, ht⟩ pending f).2

theorem propagate_slotHistory {init : Array DomC} {st : EngineState p T}
    (h : SlotHistory init st) (ht : TrailInv st) (fuel : Nat) :
    SlotHistory init (propagate p T st fuel).st :=
  drain_slotHistory h ht #[] fuel

theorem propagate_trailInv {init : Array DomC} {st : EngineState p T}
    (h : SlotHistory init st) (ht : TrailInv st) (fuel : Nat) :
    TrailInv (propagate p T st fuel).st :=
  drain_trailInv h ht #[] fuel

theorem trail_entry_prev_WF {init : Array DomC} {st : EngineState p T}
    (hi : InitInv p init) (h : SlotHistory init st) (ht : TrailInv st)
    {i : Nat} {e : Entry} (he : st.trail[i]? = some e) : e.prev.WF := by
  have hmem : i ∈ st.changeList e.slot := by
    apply (ht.changeIndex_mem e.slot i).mpr
    refine ⟨?_, e, he, rfl⟩
    by_cases hit : i < st.trail.size
    · exact hit
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hit)] at he
      simp at he
  obtain ⟨j, hj⟩ := Array.mem_iff_getElem?.mp hmem
  have hjlt : j < (st.changeList e.slot).size := by
    by_cases hlt : j < (st.changeList e.slot).size
    · exact hlt
    · rw [Array.getElem?_eq_none (Nat.le_of_not_lt hlt)] at hj
      simp at hj
  have hd := h.prev_eq e.slot j hjlt
  simp only at hd
  have hpos : (st.changeList e.slot).getD j 0 = i := by
    rw [Array.getD_eq_getElem?_getD, hj]
    rfl
  have hget : st.trail.getD ((st.changeList e.slot).getD j 0) default = e := by
    rw [hpos]
    simp [he]
  rw [hget] at hd
  rw [hd]
  exact domAfter_WF (initWF_of_InitInv hi e.slot)

theorem undoFuel_domsWF_aux {init : Array DomC} {st ref : EngineState p T}
    (hi : InitInv p init) (h : SlotHistory init ref) (ht : TrailInv ref)
    (htr : st.trail = ref.trail) (h0 : DomsWF st) (limit f : Nat) :
    DomsWF (undoFuel st limit f) := by
  revert htr h0
  induction f generalizing st with
  | zero =>
      intro htr h0
      simpa [undoFuel] using h0
  | succ f ih =>
      intro htr h0
      unfold undoFuel
      split
      · exact h0
      · rename_i e he
        have he' : ref.trail[limit + f]? = some e := by
          rw [← htr]
          exact he
        have hprevWF : e.prev.WF :=
          trail_entry_prev_WF hi h ht he'
        exact ih (st := undoStep st e limit) (by simp [undoStep, htr])
          (DomsWF.setGrow h0 hprevWF)

theorem undoFuel_domsWF {init : Array DomC} {st : EngineState p T}
    (hi : InitInv p init) (h : SlotHistory init st) (ht : TrailInv st) (limit f : Nat) :
    DomsWF (undoFuel st limit f) :=
  undoFuel_domsWF_aux hi h ht rfl
    (slotHistory_domsWF hi h) limit f

theorem backjump_domsWF {init : Array DomC} {st : EngineState p T}
    (hi : InitInv p init) (h : SlotHistory init st) (ht : TrailInv st) (k : Nat) :
    DomsWF (backjump st k) := by
  have h0 : DomsWF (undoFuel st (st.backjumpLimit (min k st.level))
      (st.trail.size - st.backjumpLimit (min k st.level))) :=
    undoFuel_domsWF hi h ht _ _
  unfold backjump
  dsimp only
  exact DomsWF.congr h0 rfl

theorem Good.congr {init : Array DomC} {st st' : EngineState p T} (h : Good init st)
    (hd : st'.doms = st.doms) (htr : st'.trail = st.trail)
    (hcl : ∀ s, st'.changeList s = st.changeList s)
    (hci : st'.changeIndex = st.changeIndex)
    (hls : st'.levelStart = st.levelStart) (hl : st'.level = st.level)
    (hrc : st'.reasonCap = st.reasonCap) :
    Good init st' := by
  obtain ⟨hsh, hti, hdw⟩ := h
  exact ⟨SlotHistory.congr hsh hd htr hcl,
    TrailInv.congr hti htr hls hl hci hrc, DomsWF.congr hdw hd⟩

theorem insertPending_good {init : Array DomC} {st : EngineState p T} (h : Good init st)
    (item : Pending) : Good init (insertPending st item).1 := by
  obtain ⟨hsh, hti, hdw⟩ := h
  exact ⟨insertPending_slotHistory hsh hti item, insertPending_trailInv hti item,
    insertPending_domsWF hdw item⟩

theorem pushPropPrunes_good {init : Array DomC} {st : EngineState p T} (h : Good init st)
    (pending : Array Pending) (ps : Array (PLit × EClause p T)) :
    Good init (pushPropPrunes st pending ps).1 := by
  unfold pushPropPrunes
  rw [← Array.foldl_toList]
  let f : (EngineState p T × Array Pending × Bool) → (PLit × EClause p T) →
      (EngineState p T × Array Pending × Bool) :=
    fun (acc : EngineState p T × Array Pending × Bool) pe =>
      let (st, pend, failed) := acc
      if failed then acc
      else
        let (l, st) := canonLit st pe.1
        let (ec, st) := canonClause st pe.2
        let rid := st.reasons.size
        let st := { st with reasons := st.reasons.push ec }
        (st, pend.push { lit := l, reason := .reason rid, count := true }, false)
  change Good init (List.foldl f (st, pending, false) ps.toList).1
  have step : ∀ (acc : EngineState p T × Array Pending × Bool) (pe : PLit × EClause p T),
      Good init acc.1 → Good init (f acc pe).1 := by
    intro acc pe hacc
    obtain ⟨st0, pend0, failed0⟩ := acc
    dsimp only [f]
    split
    · simpa using hacc
    · apply Good.congr hacc
      · rfl
      · rfl
      · intro s; rfl
      · rfl
      · rfl
      · rfl
      · rfl
  have gen : ∀ (l : List (PLit × EClause p T)) (st : EngineState p T)
      (pend : Array Pending) (failed : Bool),
      Good init st → Good init (l.foldl f (st, pend, failed)).1 := by
    intro l
    induction l with
    | nil => intro st pend failed h; simpa using h
    | cons pe rest ih =>
        intro st pend failed h
        rw [List.foldl_cons]
        exact ih _ _ _ (step (st, pend, failed) pe h)
  exact gen ps.toList st pending false h

theorem pushClausePrunes_good {init : Array DomC} {st : EngineState p T} (h : Good init st)
    (pending : Array Pending) (ps : Array (PLit × Nat)) :
    Good init (st) := h

theorem canonLit_good {init : Array DomC} {st : EngineState p T} (h : Good init st) (l : PLit) :
    Good init (canonLit st l).2 := by
  apply Good.congr h
  · exact canonLit_doms st l
  · exact canonLit_trail st l
  · intro s; exact canonLit_changeList st l s
  · rfl
  · rfl
  · rfl
  · rfl

theorem canonClause_good {init : Array DomC} {st : EngineState p T} (h : Good init st)
    (c : EClause p T) : Good init (canonClause st c).2 := by
  apply Good.congr h
  · exact canonClause_doms st c
  · exact canonClause_trail st c
  · intro s; exact canonClause_changeList st c s
  · rfl
  · rfl
  · rfl
  · rfl

theorem setInQueue_good {init : Array DomC} {st : EngineState p T} (h : Good init st)
    (id : Nat) (v : UInt8) : Good init (setInQueue st id v) := by
  apply Good.congr h
  · exact setInQueue_doms st id v
  · exact setInQueue_trail st id v
  · intro s; rw [EngineState.changeList, setInQueue_changeIndex]; rfl
  · exact setInQueue_changeIndex st id v
  · exact setInQueue_levelStart st id v
  · exact setInQueue_level st id v
  · exact setInQueue_reasonCap st id v

theorem drain_good {init : Array DomC} {st : EngineState p T} (h : Good init st)
    (pending : Array Pending) (f : Nat) :
    Good init (drain p T st pending f).st := by
  revert h
  induction st, pending, f using drain.induct with
  | case1 st pending =>
      intro h
      simpa [drain] using h
  | case2 st pending f item hback st1 neg failed ec hins =>
      intro h
      have h1 : Good init st1 := by simpa [hins] using insertPending_good h item
      simpa [drain, hback, hins] using h1
  | case3 st pending f item hback st1 neg hins =>
      intro h
      have h1 : Good init st1 := by simpa [hins] using insertPending_good h item
      simpa [drain, hback, hins] using h1
  | case4 st pending f item hback pending1 st1 failed hf hins ih =>
      intro h
      have h1 : Good init st1 := by simpa [hins] using insertPending_good h item
      simpa [drain, hback, hins, hf, pending1] using ih h1
  | case5 st pending f item hback pending1 st1 failed hf nl db st2 hins hprop ih =>
      intro h
      have h1 : Good init st1 := by simpa [hins] using insertPending_good h item
      have h2 : Good init { st1 with db := db } := by
        apply Good.congr h1
        · rfl
        · rfl
        · intro s; rfl
        · rfl
        · rfl
        · rfl
        · rfl
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2
  | case6 st pending f item hback st1 failed hf nl db st2 ec id ec1 st3 hcanon hins hprop =>
      intro h
      have h1 : Good init st1 := by simpa [hins] using insertPending_good h item
      have h2 : Good init { st1 with db := db } := by
        apply Good.congr h1
        · rfl
        · rfl
        · intro s; rfl
        · rfl
        · rfl
        · rfl
        · rfl
      have h3 : Good init st3 := by
        have := canonClause_good h2 ec
        simpa [hcanon, st2] using this
      simpa [drain, hback, hins, hprop, hcanon, hf, st2] using h3
  | case7 st pending f item hback pending1 st1 failed hf nl db st2 ps hins hprop ih =>
      intro h
      have h1 : Good init st1 := by simpa [hins] using insertPending_good h item
      have h2 : Good init { st1 with db := db } := by
        apply Good.congr h1
        · rfl
        · rfl
        · intro s; rfl
        · rfl
        · rfl
        · rfl
        · rfl
      simpa [drain, hback, hins, hprop, hf, pending1, st2] using ih h2
  | case8 st pending f hback hq id st1 hprops ih =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hprops, st1, id] using ih h1
  | case9 st pending f hback hq id st1 pr hprops hrun ih =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hprops, hrun, st1, id] using ih h1
  | case10 st pending f hback hq id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : Good init st2 := by
        have hc := canonClause_good h1 ec
        simpa [hcanon, st1, id] using hc
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hprops, hrun, hcanon, st1, id] using h2
  | case11 st pending f hback hq id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : Good init st2 := by
        have := pushPropPrunes_good h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, st1, id] using h2
  | case12 st pending f hback hq id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : Good init st2 := by
        have := pushPropPrunes_good h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hprops, hrun, hpush, hf, st1, id] using ih h2
  | case13 st pending f hback hq hql id st1 hprops ih =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops ⊢
      simpa [drain, hback, hq, hql, hprops, st1, id] using ih h1
  | case14 st pending f hback hq hql id st1 pr hprops hrun ih =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      simp only [st1, id] at hprops hrun ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, st1, id] using ih h1
  | case15 st pending f hback hq hql id st1 pr hprops ec hrun ec1 st2 hcanon =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : Good init st2 := by
        have hc := canonClause_good h1 ec
        simpa [hcanon, st1, id] using hc
      simp only [st1, id] at hprops hrun hcanon ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hcanon, st1, id] using h2
  | case16 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend hpush =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : Good init st2 := by
        have := pushPropPrunes_good h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, st1, id] using h2
  | case17 st pending f hback hq hql id st1 pr hprops ps hrun st2 pend failed hpush hf ih =>
      intro h
      have h1 : Good init st1 := by
        dsimp only [st1]
        exact setInQueue_good (by
          apply Good.congr h
          · rfl
          · rfl
          · intro s; rfl
          · rfl
          · rfl
          · rfl
          · rfl) id 0
      have h2 : Good init st2 := by
        have := pushPropPrunes_good h1 pending ps
        simpa [hpush] using this
      simp only [st1, id] at hprops hrun hpush ⊢
      simpa [drain, hback, hq, hql, hprops, hrun, hpush, hf, st1, id] using ih h2
  | case18 st pending f hback hq hql =>
      intro h
      simpa [drain, hback, hq, hql] using h

theorem drain_slotHistory_good {init : Array DomC} {st : EngineState p T}
    (h : Good init st) (pending : Array Pending) (f : Nat) :
    SlotHistory init (drain p T st pending f).st :=
  (drain_good h pending f).1

theorem drain_trailInv_good {init : Array DomC} {st : EngineState p T}
    (h : Good init st) (pending : Array Pending) (f : Nat) :
    TrailInv (drain p T st pending f).st :=
  (drain_good h pending f).2.1

theorem drain_domsWF {init : Array DomC} {st : EngineState p T}
    (h : Good init st) (pending : Array Pending) (f : Nat) :
    DomsWF (drain p T st pending f).st :=
  (drain_good h pending f).2.2

theorem propagate_slotHistory_good {init : Array DomC} {st : EngineState p T}
    (h : Good init st) (fuel : Nat) :
    SlotHistory init (propagate p T st fuel).st :=
  drain_slotHistory_good h #[] fuel

theorem propagate_trailInv_good {init : Array DomC} {st : EngineState p T}
    (h : Good init st) (fuel : Nat) :
    TrailInv (propagate p T st fuel).st :=
  drain_trailInv_good h #[] fuel

theorem propagate_domsWF {init : Array DomC} {st : EngineState p T}
    (h : Good init st) (fuel : Nat) :
    DomsWF (propagate p T st fuel).st :=
  drain_domsWF h #[] fuel

theorem list_foldl_props {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).props = st.props) (st : EngineState p T) :
    (l.foldl f st).props = st.props := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_subs {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).subs = st.subs) (st : EngineState p T) :
    (l.foldl f st).subs = st.subs := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_reasons {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).reasons = st.reasons) (st : EngineState p T) :
    (l.foldl f st).reasons = st.reasons := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_db {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).db = st.db) (st : EngineState p T) :
    (l.foldl f st).db = st.db := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_table {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).table = st.table) (st : EngineState p T) :
    (l.foldl f st).table = st.table := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_queueHigh {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).queueHigh = st.queueHigh) (st : EngineState p T) :
    (l.foldl f st).queueHigh = st.queueHigh := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_queueLow {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).queueLow = st.queueLow) (st : EngineState p T) :
    (l.foldl f st).queueLow = st.queueLow := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_inQueue {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).inQueue = st.inQueue) (st : EngineState p T) :
    (l.foldl f st).inQueue = st.inQueue := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_activity {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).activity = st.activity) (st : EngineState p T) :
    (l.foldl f st).activity = st.activity := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_activityHeap {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).activityHeap = st.activityHeap) (st : EngineState p T) :
    (l.foldl f st).activityHeap = st.activityHeap := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_phases {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).phases = st.phases) (st : EngineState p T) :
    (l.foldl f st).phases = st.phases := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_restarts {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).restarts = st.restarts) (st : EngineState p T) :
    (l.foldl f st).restarts = st.restarts := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_stats {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).stats = st.stats) (st : EngineState p T) :
    (l.foldl f st).stats = st.stats := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem canonLit_props (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.props = st.props := by
  unfold canonLit
  rfl

theorem canonLit_subs (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.subs = st.subs := by
  unfold canonLit
  rfl

theorem canonLit_reasons (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.reasons = st.reasons := by
  unfold canonLit
  rfl

theorem canonLit_db (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.db = st.db := by
  unfold canonLit
  rfl

theorem canonLit_level (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.level = st.level := by
  unfold canonLit
  rfl

theorem canonLit_levelStart (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.levelStart = st.levelStart := by
  unfold canonLit
  rfl

theorem canonLit_queueHigh (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.queueHigh = st.queueHigh := by
  unfold canonLit
  rfl

theorem canonLit_queueLow (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.queueLow = st.queueLow := by
  unfold canonLit
  rfl

theorem canonLit_inQueue (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.inQueue = st.inQueue := by
  unfold canonLit
  rfl

theorem canonLit_activity (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.activity = st.activity := by
  unfold canonLit
  rfl

theorem canonLit_activityHeap (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.activityHeap = st.activityHeap := by
  unfold canonLit
  rfl

theorem canonLit_phases (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.phases = st.phases := by
  unfold canonLit
  rfl

theorem canonLit_restarts (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.restarts = st.restarts := by
  unfold canonLit
  rfl

theorem canonLit_stats (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.stats = st.stats := by
  unfold canonLit
  rfl

theorem canonLit_changeIndex (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.changeIndex = st.changeIndex := by
  unfold canonLit
  rfl

theorem canonNegLit_props (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.props = st.props := by
  unfold canonNegLit
  rfl

theorem canonNegLit_subs (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.subs = st.subs := by
  unfold canonNegLit
  rfl

theorem canonNegLit_reasons (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.reasons = st.reasons := by
  unfold canonNegLit
  rfl

theorem canonNegLit_db (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.db = st.db := by
  unfold canonNegLit
  rfl

theorem canonNegLit_level (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.level = st.level := by
  unfold canonNegLit
  rfl

theorem canonNegLit_levelStart (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.levelStart = st.levelStart := by
  unfold canonNegLit
  rfl

theorem canonClause_props (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.props = st.props := by
  unfold canonClause
  rfl

theorem canonClause_subs (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.subs = st.subs := by
  unfold canonClause
  rfl

theorem canonClause_reasons (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.reasons = st.reasons := by
  unfold canonClause
  rfl

theorem canonClause_db (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.db = st.db := by
  unfold canonClause
  rfl

theorem canonClause_level (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.level = st.level := by
  unfold canonClause
  rfl

theorem canonClause_levelStart (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.levelStart = st.levelStart := by
  unfold canonClause
  rfl

theorem canonClause_queueHigh (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.queueHigh = st.queueHigh := by
  unfold canonClause
  rfl

theorem canonClause_queueLow (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.queueLow = st.queueLow := by
  unfold canonClause
  rfl

theorem canonClause_inQueue (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.inQueue = st.inQueue := by
  unfold canonClause
  rfl

theorem canonClause_activity (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.activity = st.activity := by
  unfold canonClause
  rfl

theorem canonClause_activityHeap (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.activityHeap = st.activityHeap := by
  unfold canonClause
  rfl

theorem canonClause_phases (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.phases = st.phases := by
  unfold canonClause
  rfl

theorem canonClause_restarts (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.restarts = st.restarts := by
  unfold canonClause
  rfl

theorem canonClause_stats (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.stats = st.stats := by
  unfold canonClause
  rfl

theorem canonClause_changeIndex (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.changeIndex = st.changeIndex := by
  unfold canonClause
  rfl

theorem ensureSubs_props (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).props = st.props := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_reasons (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).reasons = st.reasons := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_db (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).db = st.db := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_table (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).table = st.table := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_level (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).level = st.level := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_levelStart (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).levelStart = st.levelStart := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_queueHigh (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).queueHigh = st.queueHigh := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_queueLow (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).queueLow = st.queueLow := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_inQueue (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).inQueue = st.inQueue := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_activity (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).activity = st.activity := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_activityHeap (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).activityHeap = st.activityHeap := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_phases (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).phases = st.phases := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_restarts (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).restarts = st.restarts := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_stats (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).stats = st.stats := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_doms (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).doms = st.doms := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_trail (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).trail = st.trail := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_changeIndex (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).changeIndex = st.changeIndex := by
  unfold ensureSubs
  split <;> rfl

theorem ensureSubs_reasonCap (st : EngineState p T) (n : Nat) :
    (ensureSubs st n).reasonCap = st.reasonCap := by
  unfold ensureSubs
  split <;> rfl

/-- A step that only rewrites `subs` preserves the history. -/
theorem ensureSubs_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) (n : Nat) : HistInv init (ensureSubs st n) := by
  apply HistInv.congr h
  · exact ensureSubs_doms st n
  · exact ensureSubs_trail st n
  · intro s
    simp only [EngineState.changeList, ensureSubs_changeIndex st n]
  · exact ensureSubs_changeIndex st n
  · exact ensureSubs_levelStart st n
  · exact ensureSubs_level st n
  · exact ensureSubs_reasonCap st n

theorem list_foldl_histInv {α : Type} {init : Array DomC}
    (l : List α) (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, HistInv init st → HistInv init (f st a)) :
    ∀ st, HistInv init st → HistInv init (l.foldl f st) := by
  intro st h
  induction l generalizing st with
  | nil => exact h
  | cons a rest ih => exact ih (f st a) (hf st a h)

theorem array_foldl_histInv {α : Type} {init : Array DomC}
    (l : Array α) (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, HistInv init st → HistInv init (f st a)) :
    ∀ st, HistInv init st → HistInv init (l.foldl f st) := by
  intro st h
  rw [← Array.foldl_toList]
  exact list_foldl_histInv l.toList f hf st h

/-- Propagator registration only grows `subs`, so it preserves the history. -/
theorem registerProps_go_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) (n id : Nat) :
    HistInv init (registerProps.go n id st) := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → HistInv init st → HistInv init (registerProps.go n id st)
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk hh
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simpa only [hpr] using hh
        | some pr =>
          simp only [hpr]
          apply ih (n - (id + 1)) (by omega) (id + 1) _ rfl
          apply array_foldl_histInv
          · intro st' x hx
            rcases x with ⟨sv, k'⟩
            dsimp only
            apply HistInv.congr hx
            · simp only [ensureSubs_doms]
            · simp only [ensureSubs_trail]
            · intro s
              simp only [EngineState.changeList, ensureSubs_changeIndex]
            · simp only [ensureSubs_changeIndex]
            · simp only [ensureSubs_levelStart]
            · simp only [ensureSubs_level]
            · simp only [ensureSubs_reasonCap]
          · exact hh
      · simp only [dif_neg hid]
        exact hh
  exact aux (n - id) id st rfl h

theorem registerProps_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) : HistInv init (registerProps st) :=
  registerProps_go_histInv h st.props.size 0

theorem array_foldl_doms {α : Type} (l : Array α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).doms = st.doms) :
    ∀ st, (l.foldl f st).doms = st.doms := by
  intro st
  rw [← Array.foldl_toList]
  exact list_foldl_doms l.toList f hf st

theorem registerProps_go_doms (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).doms = st.doms := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).doms = st.doms
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          apply array_foldl_doms
          intro st' x
          rcases x with ⟨sv, k'⟩
          dsimp only
          simp only [ensureSubs_doms]
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_go_props (n id : Nat) (st : EngineState p T) :
    (registerProps.go n id st).props = st.props := by
  let P : Nat → Prop := fun k => ∀ (id : Nat) (st : EngineState p T),
    n - id = k → (registerProps.go n id st).props = st.props
  have aux : ∀ k, P k := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro id st hk
      rw [registerProps.go.eq_def]
      by_cases hid : id < n
      · simp only [dif_pos hid]
        cases hpr : st.props[id]? with
        | none => simp only [hpr]
        | some pr =>
          simp only [hpr]
          rw [ih (n - (id + 1)) (by omega) (id + 1) _ rfl]
          rw [← Array.foldl_toList]
          exact list_foldl_props _ _ (fun st' x => by
            rcases x with ⟨sv, k'⟩
            dsimp only
            simp only [ensureSubs_props]) _
      · simp only [dif_neg hid]
  exact aux (n - id) id st rfl

theorem registerProps_props (st : EngineState p T) :
    (registerProps st).props = st.props :=
  registerProps_go_props st.props.size 0 st

theorem registerProps_doms (st : EngineState p T) :
    (registerProps st).doms = st.doms :=
  registerProps_go_doms st.props.size 0 st

theorem enqueueProp_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) (id : Nat) : HistInv init (enqueueProp st id) := by
  apply HistInv.congr h
  · exact enqueueProp_doms st id
  · exact enqueueProp_trail st id
  · intro s
    simp only [EngineState.changeList, enqueueProp_changeIndex st id]
  · exact enqueueProp_changeIndex st id
  · exact enqueueProp_levelStart st id
  · exact enqueueProp_level st id
  · exact enqueueProp_reasonCap st id

theorem range_enqueueProp_histInv {init : Array DomC} {st : EngineState p T}
    (h : HistInv init st) (n : Nat) :
    HistInv init ((List.range n).foldl (fun st i => enqueueProp st i) st) :=
  list_foldl_histInv _ _ (fun st i hh => enqueueProp_histInv hh i) st h

theorem ensureInQueue_props (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).props = st.props := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_subs (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).subs = st.subs := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_reasons (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).reasons = st.reasons := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_db (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).db = st.db := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_table (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).table = st.table := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_queueHigh (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).queueHigh = st.queueHigh := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_queueLow (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).queueLow = st.queueLow := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_activity (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).activity = st.activity := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_activityHeap (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).activityHeap = st.activityHeap := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_phases (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).phases = st.phases := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_restarts (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).restarts = st.restarts := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_stats (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).stats = st.stats := by
  unfold ensureInQueue
  rfl

theorem setInQueue_props (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).props = st.props := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_subs (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).subs = st.subs := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_reasons (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).reasons = st.reasons := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_db (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).db = st.db := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_table (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).table = st.table := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_queueHigh (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).queueHigh = st.queueHigh := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_queueLow (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).queueLow = st.queueLow := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_activity (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).activity = st.activity := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_activityHeap (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).activityHeap = st.activityHeap := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_phases (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).phases = st.phases := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_restarts (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).restarts = st.restarts := by
  unfold setInQueue
  split <;> rfl

theorem setInQueue_stats (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).stats = st.stats := by
  unfold setInQueue
  split <;> rfl

theorem enqueueProp_props (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).props = st.props := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_props]
    · simp [ensureInQueue_props]
  · rfl

theorem enqueueProp_subs (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).subs = st.subs := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_subs]
    · simp [ensureInQueue_subs]
  · rfl

theorem enqueueProp_reasons (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).reasons = st.reasons := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_reasons]
    · simp [ensureInQueue_reasons]
  · rfl

theorem enqueueProp_db (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).db = st.db := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_db]
    · simp [ensureInQueue_db]
  · rfl

theorem enqueueProp_table (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).table = st.table := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_table]
    · simp [ensureInQueue_table]
  · rfl

theorem enqueueProp_activity (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).activity = st.activity := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_activity]
    · simp [ensureInQueue_activity]
  · rfl

theorem enqueueProp_activityHeap (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).activityHeap = st.activityHeap := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_activityHeap]
    · simp [ensureInQueue_activityHeap]
  · rfl

theorem enqueueProp_phases (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).phases = st.phases := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_phases]
    · simp [ensureInQueue_phases]
  · rfl

theorem enqueueProp_restarts (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).restarts = st.restarts := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_restarts]
    · simp [ensureInQueue_restarts]
  · rfl

theorem enqueueProp_stats (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).stats = st.stats := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_stats]
    · simp [ensureInQueue_stats]
  · rfl

theorem enqueueSubs_props (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).props = st.props := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_props _ _ (fun st id => enqueueProp_props st id) st
  · rfl

theorem enqueueSubs_subs (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).subs = st.subs := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_subs _ _ (fun st id => enqueueProp_subs st id) st
  · rfl

theorem enqueueSubs_reasons (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).reasons = st.reasons := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_reasons _ _ (fun st id => enqueueProp_reasons st id) st
  · rfl

theorem enqueueSubs_db (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).db = st.db := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_db _ _ (fun st id => enqueueProp_db st id) st
  · rfl

theorem enqueueSubs_table (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).table = st.table := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_table _ _ (fun st id => enqueueProp_table st id) st
  · rfl

theorem enqueueSubs_activity (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).activity = st.activity := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_activity _ _ (fun st id => enqueueProp_activity st id) st
  · rfl

theorem enqueueSubs_activityHeap (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).activityHeap = st.activityHeap := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_activityHeap _ _ (fun st id => enqueueProp_activityHeap st id) st
  · rfl

theorem enqueueSubs_phases (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).phases = st.phases := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_phases _ _ (fun st id => enqueueProp_phases st id) st
  · rfl

theorem enqueueSubs_restarts (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).restarts = st.restarts := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_restarts _ _ (fun st id => enqueueProp_restarts st id) st
  · rfl

theorem enqueueSubs_stats (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).stats = st.stats := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_stats _ _ (fun st id => enqueueProp_stats st id) st
  · rfl

theorem emitSlot_props (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).props = st.props := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_props]
    · split <;> simp [enqueueSubs_props]

theorem emitSlot_subs (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).subs = st.subs := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_subs]
    · split <;> simp [enqueueSubs_subs]

theorem emitSlot_reasons (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).reasons = st.reasons := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_reasons]
    · split <;> simp [enqueueSubs_reasons]

theorem emitSlot_db (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).db = st.db := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_db]
    · split <;> simp [enqueueSubs_db]

theorem emitSlot_table (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).table = st.table := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_table]
    · split <;> simp [enqueueSubs_table]

theorem emitSlot_activity (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).activity = st.activity := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_activity]
    · split <;> simp [enqueueSubs_activity]

theorem emitSlot_activityHeap (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).activityHeap = st.activityHeap := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_activityHeap]
    · split <;> simp [enqueueSubs_activityHeap]

theorem emitSlot_phases (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).phases = st.phases := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_phases]
    · split <;> simp [enqueueSubs_phases]

theorem emitSlot_restarts (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).restarts = st.restarts := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_restarts]
    · split <;> simp [enqueueSubs_restarts]

theorem emitSlot_stats (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).stats = st.stats := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_stats]
    · split <;> simp [enqueueSubs_stats]

theorem trailPush_props (st : EngineState p T) (e : Entry) :
    (trailPush st e).props = st.props := by
  unfold trailPush
  rfl

theorem trailPush_subs (st : EngineState p T) (e : Entry) :
    (trailPush st e).subs = st.subs := by
  unfold trailPush
  rfl

theorem trailPush_db (st : EngineState p T) (e : Entry) :
    (trailPush st e).db = st.db := by
  unfold trailPush
  rfl

theorem trailPush_table (st : EngineState p T) (e : Entry) :
    (trailPush st e).table = st.table := by
  unfold trailPush
  rfl

theorem trailPush_queueHigh (st : EngineState p T) (e : Entry) :
    (trailPush st e).queueHigh = st.queueHigh := by
  unfold trailPush
  rfl

theorem trailPush_queueLow (st : EngineState p T) (e : Entry) :
    (trailPush st e).queueLow = st.queueLow := by
  unfold trailPush
  rfl

theorem trailPush_inQueue (st : EngineState p T) (e : Entry) :
    (trailPush st e).inQueue = st.inQueue := by
  unfold trailPush
  rfl

theorem trailPush_activity (st : EngineState p T) (e : Entry) :
    (trailPush st e).activity = st.activity := by
  unfold trailPush
  rfl

theorem trailPush_activityHeap (st : EngineState p T) (e : Entry) :
    (trailPush st e).activityHeap = st.activityHeap := by
  unfold trailPush
  rfl

theorem trailPush_phases (st : EngineState p T) (e : Entry) :
    (trailPush st e).phases = st.phases := by
  unfold trailPush
  rfl

theorem trailPush_restarts (st : EngineState p T) (e : Entry) :
    (trailPush st e).restarts = st.restarts := by
  unfold trailPush
  rfl

theorem trailPush_stats (st : EngineState p T) (e : Entry) :
    (trailPush st e).stats = st.stats := by
  unfold trailPush
  rfl

end LeanFzn.Engine
