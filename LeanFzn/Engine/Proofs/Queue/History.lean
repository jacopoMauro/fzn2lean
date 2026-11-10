/-
Purpose: Queue history lemmas, separated from executable propagation.
Dependencies: LeanFzn.Engine.Queue.Run
DAG: Definitions/specifications -> queue proofs -> compatibility Engine.Queue.
-/
import LeanFzn.Engine.Queue.Run

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

set_option maxHeartbeats 4000000

theorem domAfter_zero (init : Array DomC) (st : EngineState p T) (s : Nat) :
    domAfter init st s 0 = init.getD s DomC.empty := by
  simp [domAfter]

theorem domAfter_succ (init : Array DomC) (st : EngineState p T) (s k : Nat)
    (hk : k < (st.changeList s).size) :
    domAfter init st s (k + 1) =
      domStep st.trail (domAfter init st s k) ((st.changeList s).getD k 0) := by
  have hpush : (st.changeList s).extract 0 (k + 1) =
      ((st.changeList s).extract 0 k).push ((st.changeList s)[k]) :=
    Array.extract_succ_right (i := 0) (j := k) (w := by omega) (h := hk)
  have hget : (st.changeList s)[k] = (st.changeList s).getD k 0 := by
    rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hk]
    rfl
  rw [domAfter, hpush, Array.foldl_push, hget]
  rfl

/-- `domStep` depends on the trail only through the entry at `pos`. -/
theorem domStep_congr {tr tr' : Array Entry} {d : DomC} {pos : Nat}
    (h : tr[pos]? = tr'[pos]?) : domStep tr d pos = domStep tr' d pos := by
  simp [domStep, h]

/-- `domAfter` is invariant when only the state's frames other than `doms`
are changed; the change list and trail must agree up to `k`. -/
theorem domAfter_congr (init : Array DomC) (st : EngineState p T) (s k : Nat)
    {tr : Array Entry}
    (hk : k ≤ (st.changeList s).size)
    (htr : ∀ j, j < k →
      tr[(st.changeList s).getD j 0]? = st.trail[(st.changeList s).getD j 0]?) :
    domAfter init { st with trail := tr } s k = domAfter init st s k := by
  induction k with
  | zero => rw [domAfter_zero, domAfter_zero]
  | succ k ih =>
      have hk' : k < (st.changeList s).size := by omega
      have hcl : ({ st with trail := tr } : EngineState p T).changeList s =
          st.changeList s := rfl
      rw [domAfter_succ (init := init) (st := { st with trail := tr }) (s := s) (k := k)
          (hk := by simpa [hcl] using hk'),
        domAfter_succ (init := init) (st := st) (s := s) (k := k) (hk := hk')]
      have hinner := ih (by omega) (fun j hj => htr j (by omega))
      rw [hinner]
      have hstep : domStep ({ st with trail := tr } : EngineState p T).trail
          (domAfter init st s k) ((st.changeList s).getD k 0) =
          domStep st.trail (domAfter init st s k) ((st.changeList s).getD k 0) :=
        domStep_congr (htr k (Nat.lt_succ_self k))
      exact hstep

/-- Fold congruence for lists. -/
theorem list_foldl_congr {α β : Type} {f g : β → α → β} {l₁ l₂ : List α}
    {b₁ b₂ : β} (hl : l₁ = l₂) (hb : b₁ = b₂)
    (hf : ∀ a ∈ l₂, ∀ b, f b a = g b a) :
    l₁.foldl f b₁ = l₂.foldl g b₂ := by
  cases hl
  cases hb
  induction l₁ generalizing b₁ with
  | nil => rfl
  | cons x xs ih =>
      rw [List.foldl_cons, List.foldl_cons, hf x (by simp) b₁]
      exact ih (fun a ha b => hf a (by simp [ha]) b)

/-- Membership in `extract 0 k` as an index below `k`. -/
theorem mem_extract_zero_getD {a : Array Nat} {k q : Nat}
    (hq : q ∈ a.extract 0 k) : ∃ j, j < k ∧ a.getD j 0 = q := by
  rw [Array.mem_extract_iff_getElem] at hq
  obtain ⟨j, hj, hqj⟩ := hq
  refine ⟨j, by omega, ?_⟩
  rw [Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem (by omega)]
  simpa using hqj

/-- `domAfter` is determined by the extracted change-list prefix and the
trail entries at the listed positions. -/
theorem domAfter_congr_extract (init : Array DomC) {st st' : EngineState p T}
    {s k k' : Nat}
    (hext : (st'.changeList s).extract 0 k' = (st.changeList s).extract 0 k)
    (htr : ∀ j, j < k →
      st'.trail[(st.changeList s).getD j 0]? = st.trail[(st.changeList s).getD j 0]?) :
    domAfter init st' s k' = domAfter init st s k := by
  rw [domAfter, domAfter, ← Array.foldl_toList, ← Array.foldl_toList]
  have hl : ((st'.changeList s).extract 0 k').toList =
      ((st.changeList s).extract 0 k).toList := by rw [hext]
  apply list_foldl_congr hl rfl
  intro q hq b
  have hq' : q ∈ (st.changeList s).extract 0 k := Array.mem_toList_iff.mp hq
  obtain ⟨j, hj, hqj⟩ := mem_extract_zero_getD hq'
  exact domStep_congr (by simpa [hqj] using htr j hj)

/-- Change lists whose entries agree below `k` give the same `domAfter`. -/
theorem domAfter_congr_state (init : Array DomC) {st st' : EngineState p T}
    {s k : Nat} (hcl : st'.changeList s = st.changeList s)
    (htr : ∀ j, j < k →
      st'.trail[(st.changeList s).getD j 0]? = st.trail[(st.changeList s).getD j 0]?) :
    domAfter init st' s k = domAfter init st s k := by
  apply domAfter_congr_extract (init := init) (k := k) (k' := k) (st := st) (st' := st')
  · rw [hcl]
  · exact htr

/-- The position of every listed change is a real trail position. -/
theorem TrailInv.getD_changeList_lt {st : EngineState p T} (h : TrailInv st)
    {s j : Nat} (hj : j < (st.changeList s).size) :
    (st.changeList s).getD j 0 < st.trail.size := by
  have hmem : (st.changeList s).getD j 0 ∈ st.changeList s := Array.getD_mem hj
  exact ((h.changeIndex_mem s _).1 hmem).1

/-- `trailPush` does not change the replay of a proper prefix of the pushed
slot's change list. -/
theorem domAfter_trailPush_self_lt (init : Array DomC) (st : EngineState p T)
    (h : TrailInv st) (e : Entry) (k : Nat)
    (hk : k ≤ (st.changeList e.slot).size) :
    domAfter init (trailPush st e) e.slot k = domAfter init st e.slot k := by
  induction k with
  | zero => rw [domAfter_zero, domAfter_zero]
  | succ k ih =>
      have hk' : k < (st.changeList e.slot).size := by omega
      have hcl : (trailPush st e).changeList e.slot =
          (st.changeList e.slot).push st.trail.size := trailPush_changeList_self st e
      have hsz : k < ((trailPush st e).changeList e.slot).size := by
        rw [hcl, Array.size_push]; omega
      rw [domAfter_succ (init := init) (st := trailPush st e) (s := e.slot) (k := k) hsz,
        domAfter_succ (init := init) (st := st) (s := e.slot) (k := k) hk']
      rw [ih (by omega)]
      have hg : ((trailPush st e).changeList e.slot).getD k 0 =
          (st.changeList e.slot).getD k 0 := by
        rw [hcl]
        exact Array.getD_push_lt _ _ _ hk'
      rw [hg]
      exact domStep_congr (trailPush_trail_old st e (h.getD_changeList_lt hk'))

/-- `trailPush` on another slot does not change the replay. -/
theorem domAfter_trailPush_ne (init : Array DomC) (st : EngineState p T)
    (h : TrailInv st) (e : Entry) {s : Slot} (hs : s ≠ e.slot) (k : Nat)
    (hk : k ≤ (st.changeList s).size) :
    domAfter init (trailPush st e) s k = domAfter init st s k := by
  have hcl : (trailPush st e).changeList s = st.changeList s :=
    trailPush_changeList_ne st e hs
  apply domAfter_congr_state (init := init) (st := st) (st' := trailPush st e) hcl
  intro j hj
  exact trailPush_trail_old st e (h.getD_changeList_lt (by omega))

/-- `getD` congruence from an option-index equality. -/
theorem getD_congr_getElem? {a b : Array Entry} {i : Nat} {d : Entry}
    (h : a[i]? = b[i]?) : a.getD i d = b.getD i d := by
  rw [Array.getD_eq_getElem?_getD, Array.getD_eq_getElem?_getD, h]

/-- `SlotHistory` is insensitive to state fields other than the domains,
the trail and the change index. -/
theorem SlotHistory.congr {init : Array DomC} {st st' : EngineState p T}
    (h : SlotHistory init st) (hd : st'.doms = st.doms) (htr : st'.trail = st.trail)
    (hcl : ∀ s, st'.changeList s = st.changeList s) : SlotHistory init st' := by
  constructor
  · intro s
    rw [hd, show (st'.changeList s).size = (st.changeList s).size by rw [hcl s]]
    rw [domAfter_congr_state (init := init) (st := st) (st' := st') (s := s)
      (k := (st.changeList s).size) (hcl s) (fun j _ => by rw [htr])]
    exact h.doms_eq s
  · intro s k hk
    have hk' : k < (st.changeList s).size := by rwa [hcl s] at hk
    show (st'.trail.getD ((st'.changeList s).getD k 0) default).prev =
      domAfter init st' s k
    rw [show (st'.changeList s).getD k 0 = (st.changeList s).getD k 0 by rw [hcl s], htr]
    rw [domAfter_congr_state (init := init) (st := st) (st' := st') (s := s)
      (k := k) (hcl s) (fun j _ => by rw [htr])]
    exact h.prev_eq s k hk'

/-- `canonLit` changes only the intern table. -/
theorem canonLit_doms (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.doms = st.doms := by
  unfold canonLit
  rfl

theorem canonLit_trail (st : EngineState p T) (l : PLit) :
    (canonLit st l).2.trail = st.trail := by
  unfold canonLit
  rfl

theorem canonLit_changeList (st : EngineState p T) (l : PLit) (s : Slot) :
    (canonLit st l).2.changeList s = st.changeList s := by
  unfold canonLit EngineState.changeList
  rfl

/-- `canonNegLit` changes only the intern table. -/
theorem canonNegLit_doms (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.doms = st.doms := by
  unfold canonNegLit
  rfl

theorem canonNegLit_trail (st : EngineState p T) (l : PLit) :
    (canonNegLit st l).2.trail = st.trail := by
  unfold canonNegLit
  rfl

theorem canonNegLit_changeList (st : EngineState p T) (l : PLit) (s : Slot) :
    (canonNegLit st l).2.changeList s = st.changeList s := by
  unfold canonNegLit EngineState.changeList
  rfl

/-- `canonClause` changes only the intern table. -/
theorem canonClause_doms (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.doms = st.doms := by
  unfold canonClause
  rfl

theorem canonClause_trail (st : EngineState p T) (c : EClause p T) :
    (canonClause st c).2.trail = st.trail := by
  unfold canonClause
  rfl

theorem canonClause_changeList (st : EngineState p T) (c : EClause p T) (s : Slot) :
    (canonClause st c).2.changeList s = st.changeList s := by
  unfold canonClause EngineState.changeList
  rfl

/-- Projection through a Boolean conditional. -/
@[simp] theorem ite_doms (b : Bool) (x y : EngineState p T) :
    (if b then x else y).doms = (if b then x.doms else y.doms) := by
  cases b <;> rfl

@[simp] theorem ite_trail (b : Bool) (x y : EngineState p T) :
    (if b then x else y).trail = (if b then x.trail else y.trail) := by
  cases b <;> rfl

@[simp] theorem ite_changeIndex (b : Bool) (x y : EngineState p T) :
    (if b then x else y).changeIndex =
      (if b then x.changeIndex else y.changeIndex) := by
  cases b <;> rfl

/-- `ensureInQueue` changes only `inQueue`. -/
theorem ensureInQueue_doms (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).doms = st.doms := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_trail (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).trail = st.trail := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_changeIndex (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).changeIndex = st.changeIndex := by
  unfold ensureInQueue
  rfl

theorem ensureInQueue_reasonCap (st : EngineState p T) (n : Nat) :
    (ensureInQueue st n).reasonCap = st.reasonCap := by
  unfold ensureInQueue
  rfl

/-- `setInQueue` changes only `inQueue`. -/
theorem setInQueue_doms (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).doms = st.doms := by
  unfold setInQueue
  split <;> simp

theorem setInQueue_trail (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).trail = st.trail := by
  unfold setInQueue
  split <;> simp

theorem setInQueue_changeIndex (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).changeIndex = st.changeIndex := by
  unfold setInQueue
  split <;> simp

theorem setInQueue_reasonCap (st : EngineState p T) (id : Nat) (v : UInt8) :
    (setInQueue st id v).reasonCap = st.reasonCap := by
  unfold setInQueue
  split <;> simp

/-- `enqueueProp` changes only the worklists and `inQueue`. -/
theorem enqueueProp_doms (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).doms = st.doms := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_doms]
    · simp [ensureInQueue_doms]
  · rfl

theorem enqueueProp_trail (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).trail = st.trail := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_trail]
    · simp [ensureInQueue_trail]
  · rfl

theorem enqueueProp_changeIndex (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).changeIndex = st.changeIndex := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_changeIndex]
    · simp [ensureInQueue_changeIndex]
  · rfl

theorem enqueueProp_reasonCap (st : EngineState p T) (id : Nat) :
    (enqueueProp st id).reasonCap = st.reasonCap := by
  unfold enqueueProp
  split
  · dsimp only
    split
    · split <;> simp [ensureInQueue_reasonCap]
    · simp [ensureInQueue_reasonCap]
  · rfl

/-- Folding a state-preserving function preserves a projection. -/
theorem list_foldl_doms {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).doms = st.doms) (st : EngineState p T) :
    (l.foldl f st).doms = st.doms := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_trail {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).trail = st.trail) (st : EngineState p T) :
    (l.foldl f st).trail = st.trail := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_changeIndex {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).changeIndex = st.changeIndex) (st : EngineState p T) :
    (l.foldl f st).changeIndex = st.changeIndex := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

theorem list_foldl_reasonCap {α : Type} (l : List α)
    (f : EngineState p T → α → EngineState p T)
    (hf : ∀ st a, (f st a).reasonCap = st.reasonCap) (st : EngineState p T) :
    (l.foldl f st).reasonCap = st.reasonCap := by
  induction l generalizing st with
  | nil => rfl
  | cons x xs ih => rw [List.foldl_cons, ih, hf]

/-- `enqueueSubs` changes only the worklists and `inQueue`. -/
theorem enqueueSubs_doms (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).doms = st.doms := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_doms _ _ (fun st id => enqueueProp_doms st id) st
  · rfl

theorem enqueueSubs_trail (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).trail = st.trail := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_trail _ _ (fun st id => enqueueProp_trail st id) st
  · rfl

theorem enqueueSubs_changeIndex (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).changeIndex = st.changeIndex := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_changeIndex _ _ (fun st id => enqueueProp_changeIndex st id) st
  · rfl

theorem enqueueSubs_reasonCap (st : EngineState p T) (s : Slot) (k : EventKind) :
    (enqueueSubs st s k).reasonCap = st.reasonCap := by
  unfold enqueueSubs
  dsimp only
  split
  · rw [← Array.foldl_toList]
    exact list_foldl_reasonCap _ _ (fun st id => enqueueProp_reasonCap st id) st
  · rfl

/-- `emitSlot` changes neither the domains, the trail, nor the change index. -/
theorem emitSlot_doms (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).doms = st.doms := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_doms]
    · split <;> simp [enqueueSubs_doms]

theorem emitSlot_trail (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).trail = st.trail := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_trail]
    · split <;> simp [enqueueSubs_trail]

theorem emitSlot_changeIndex (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).changeIndex = st.changeIndex := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_changeIndex]
    · split <;> simp [enqueueSubs_changeIndex]

theorem emitSlot_reasonCap (st : EngineState p T) (s : Slot) (old new : DomC) :
    (emitSlot st s old new).reasonCap = st.reasonCap := by
  unfold emitSlot
  split
  · rfl
  · dsimp only
    split
    · split <;> simp [enqueueSubs_reasonCap]
    · split <;> simp [enqueueSubs_reasonCap]

theorem emitSlot_changeList (st : EngineState p T) (s : Slot) (old new : DomC) (t : Slot) :
    (emitSlot st s old new).changeList t = st.changeList t := by
  simp [EngineState.changeList, emitSlot_changeIndex]

/-- The canonical initial state satisfies the history invariant. -/
theorem slotHistory_init (init : Array DomC) (st : EngineState p T)
    (hd : st.doms = init) (ht : st.trail = #[]) (hci : ∀ s, st.changeList s = #[]) :
    SlotHistory init st := by
  constructor
  · intro s
    rw [hd, hci s]
    simp [domAfter]
  · intro s k hk
    rw [hci s] at hk
    simp at hk

/-- The core push lemma: appending an entry whose `prev` is the current
domain and installing the new domain preserves the history invariant. -/
theorem slotHistory_trailPush {init : Array DomC} {st : EngineState p T}
    (h : SlotHistory init st) (ht : TrailInv st) {e : Entry}
    (hprev : e.prev = st.doms.getD e.slot DomC.empty) {d' : DomC}
    (hd' : d' = (st.doms.getD e.slot DomC.empty).applyLit e.lit.lit) :
    SlotHistory init
      { (trailPush st e) with doms := st.doms.setGrow e.slot d' DomC.empty } := by
  let st' : EngineState p T :=
    { (trailPush st e) with doms := st.doms.setGrow e.slot d' DomC.empty }
  change SlotHistory init st'
  have hcl_self : st'.changeList e.slot = (st.changeList e.slot).push st.trail.size := by
    simp [st', EngineState.changeList, trailPush]
  have hcl_ne : ∀ s, s ≠ e.slot → st'.changeList s = st.changeList s := by
    intro s hs
    simp [st', EngineState.changeList, trailPush, hs]
  have htr_self : ∀ j, j < (st.changeList e.slot).size →
      st'.trail[(st.changeList e.slot).getD j 0]? =
        st.trail[(st.changeList e.slot).getD j 0]? := by
    intro j hj
    exact trailPush_trail_old st e (ht.getD_changeList_lt hj)
  have htr_ne : ∀ (s : Slot), s ≠ e.slot → ∀ j, j < (st.changeList s).size →
      st'.trail[(st.changeList s).getD j 0]? =
        st.trail[(st.changeList s).getD j 0]? := by
    intro s _ j hj
    exact trailPush_trail_old st e (ht.getD_changeList_lt hj)
  constructor
  · intro s
    by_cases hs : s = e.slot
    · subst hs
      have hsize : (st'.changeList e.slot).size = (st.changeList e.slot).size + 1 := by
        rw [hcl_self, Array.size_push]
      have hlive : st'.doms.getD e.slot DomC.empty = d' := by
        simp [st']
      have hinner : domAfter init st' e.slot (st.changeList e.slot).size =
          domAfter init st e.slot (st.changeList e.slot).size := by
        apply domAfter_congr_extract (init := init) (k := (st.changeList e.slot).size)
          (k' := (st.changeList e.slot).size) (st := st) (st' := st')
        · rw [hcl_self]
          exact Array.extract_push_of_le (by simp)
        · exact htr_self
      rw [hlive, hd', hsize,
        domAfter_succ (init := init) (st := st') (s := e.slot)
          (k := (st.changeList e.slot).size) (by omega)]
      have hget : (st'.changeList e.slot).getD (st.changeList e.slot).size 0 =
          st.trail.size := by
        rw [hcl_self]
        exact Array.getD_push_eq _ _ _
      rw [hget]
      have hstep : domStep st'.trail
          (domAfter init st' e.slot (st.changeList e.slot).size) st.trail.size =
          (domAfter init st' e.slot (st.changeList e.slot).size).applyLit e.lit.lit := by
        simp [domStep, st', trailPush]
      rw [hstep, hinner, h.doms_eq e.slot]
    · have hsize : (st'.changeList s).size = (st.changeList s).size := by rw [hcl_ne s hs]
      have hlive : st'.doms.getD s DomC.empty = st.doms.getD s DomC.empty := by
        simp only [st']
        exact Array.getD_setGrow_other st.doms e.slot s d' DomC.empty hs
      rw [hlive, hsize,
        domAfter_congr_extract (init := init) (st := st) (st' := st') (s := s)
          (k := (st.changeList s).size) (k' := (st.changeList s).size)
          (by rw [hcl_ne s hs]) (htr_ne s hs)]
      exact h.doms_eq s
  · intro s k hk
    by_cases hs : s = e.slot
    · subst hs
      by_cases hkold : k < (st.changeList e.slot).size
      · show (st'.trail.getD ((st'.changeList e.slot).getD k 0) default).prev =
          domAfter init st' e.slot k
        have hpos : (st'.changeList e.slot).getD k 0 = (st.changeList e.slot).getD k 0 := by
          rw [hcl_self]
          exact Array.getD_push_lt _ _ _ hkold
        rw [hpos]
        have hgetD : st'.trail.getD ((st.changeList e.slot).getD k 0) default =
            st.trail.getD ((st.changeList e.slot).getD k 0) default :=
          getD_congr_getElem? (htr_self k hkold)
        rw [hgetD,
          domAfter_congr_extract (init := init) (st := st) (st' := st') (s := e.slot)
            (k := k) (k' := k) (by rw [hcl_self]; exact Array.extract_push_of_le (by omega))
            (fun j hj => htr_self j (by omega))]
        exact h.prev_eq e.slot k hkold
      · have hk_eq : k = (st.changeList e.slot).size := by
          have := hk
          rw [hcl_self, Array.size_push] at this
          omega
        subst hk_eq
        show (st'.trail.getD
          ((st'.changeList e.slot).getD (st.changeList e.slot).size 0) default).prev =
          domAfter init st' e.slot (st.changeList e.slot).size
        have hpos : (st'.changeList e.slot).getD (st.changeList e.slot).size 0 =
            st.trail.size := by
          rw [hcl_self]
          exact Array.getD_push_eq _ _ _
        have hentry : st'.trail[st.trail.size]? = some e := by
          simp [st', trailPush]
        have hgetD : st'.trail.getD st.trail.size default = e := by
          rw [Array.getD_eq_getElem?_getD, hentry]
          rfl
        have hinner : domAfter init st' e.slot (st.changeList e.slot).size =
            domAfter init st e.slot (st.changeList e.slot).size := by
          apply domAfter_congr_extract (init := init) (k := (st.changeList e.slot).size)
            (k' := (st.changeList e.slot).size) (st := st) (st' := st')
          · rw [hcl_self]
            exact Array.extract_push_of_le (by simp)
          · exact htr_self
        rw [hpos, hgetD, hprev, hinner, h.doms_eq e.slot]
    · have hk' : k < (st.changeList s).size := by
        rwa [hcl_ne s hs] at hk
      show (st'.trail.getD ((st'.changeList s).getD k 0) default).prev =
        domAfter init st' s k
      have hpos : (st'.changeList s).getD k 0 = (st.changeList s).getD k 0 := by
        rw [hcl_ne s hs]
      rw [hpos]
      have hgetD : st'.trail.getD ((st.changeList s).getD k 0) default =
          st.trail.getD ((st.changeList s).getD k 0) default :=
        getD_congr_getElem? (htr_ne s hs k hk')
      rw [hgetD,
        domAfter_congr_extract (init := init) (st := st) (st' := st') (s := s)
          (k := k) (k' := k) (by rw [hcl_ne s hs]) (fun j hj => htr_ne s hs j (by omega))]
      exact h.prev_eq s k hk'

theorem test_set! {α : Type} (a : Array α) {i : Nat} (v d : α)
    (h : i < a.size) : a.set! i v = a.setGrow i v d := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_setGrow]
  by_cases hij : i = j
  · subst hij; simp [h]
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    by_cases hj : j < a.size
    · rw [if_pos hj]
    · have hn : a[j]? = none := Array.getElem?_eq_none (by omega)
      rw [if_neg hj, hn]
      have hji2 : ¬ j < i := by omega
      rw [if_neg hji2]

theorem Array.set!_eq_setGrow_of_lt {α : Type} (a : Array α) {i : Nat} (v d : α)
    (h : i < a.size) : a.set! i v = a.setGrow i v d := by
  apply Array.ext_getElem?
  intro j
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_setGrow]
  by_cases hij : i = j
  · subst hij; simp [h]
  · rw [if_neg hij, if_neg (Ne.symm hij)]
    by_cases hj : j < a.size
    · rw [if_pos hj]
    · have hn : a[j]? = none := Array.getElem?_eq_none (by omega)
      rw [if_neg hj, hn]
      have hji2 : ¬ j < i := by omega
      rw [if_neg hji2]

theorem DomC.empty_applyLit_isEmpty (l : Literal) :
    (DomC.empty.applyLit l).isEmpty = true := by
  rcases l with ⟨atom, pos⟩
  cases atom with
  | boolEq s b =>
      cases pos <;> simp [DomC.applyLit, DomC.empty, DomC.fix, DomC.mem, DomC.isEmpty]
  | intLe s k =>
      cases pos
      · simp only [DomC.applyLit, DomC.empty, DomC.setGe, DomC.isEmpty]
        split <;> simp_all <;> omega
      · simp only [DomC.applyLit, DomC.empty, DomC.setLe, DomC.isEmpty]
        split <;> simp_all <;> omega
  | intNe s v =>
      cases pos
      · have hmem : DomC.mem (DomC.bounds 1 0) (.int v) = false := by
          simp only [DomC.mem]
          by_cases h1 : (1 : Int) ≤ v
          · have h2 : ¬ v ≤ (0 : Int) := by omega
            simp [h1, h2]
          · simp [h1]
        simp [DomC.applyLit, DomC.empty, DomC.fixIntView, DomC.fix, hmem, DomC.isEmpty]
      · have hcond : (v < (1 : Int) || (0 : Int) < v) = true := by
          by_cases h : v < (1 : Int)
          · simp [h]
          · have h2 : (0 : Int) < v := by omega
            simp [h, h2]
        simp [DomC.applyLit, DomC.empty, DomC.removeIntView, DomC.remove, hcond,
          DomC.isEmpty]

theorem TrailInv.congr {st st' : EngineState p T} (h : TrailInv st)
    (htr : st'.trail = st.trail) (hls : st'.levelStart = st.levelStart)
    (hl : st'.level = st.level) (hci : st'.changeIndex = st.changeIndex)
    (hrc : st'.reasonCap = st.reasonCap) : TrailInv st' := by
  constructor
  · rw [hls]; exact h.levelStart_zero
  · rw [hls, hl]; exact h.levelStart_size
  · rw [hls]; exact h.levelStart_sorted
  · intro i hi; rw [hls] at hi; rw [hls, htr]; exact h.levelStart_le_trail i hi
  · intro i e he; rw [htr] at he; rw [hls]; exact h.entry_level i e he
  · intro i e he; rw [htr] at he; rw [hls]; exact h.entry_levelStart_le i e he
  · intro s; simp only [EngineState.changeList, hci]; exact h.changeIndex_sorted s
  · intro s p; simp only [EngineState.changeList, hci, htr]; exact h.changeIndex_mem s p
  · rw [hrc, hl]; exact h.reasonCap_size
  · intro k hk
    rw [hrc, htr, hls]
    exact h.reasonCap_exact k (by simpa [hrc] using hk)

theorem insertPending_slotHistory {init : Array DomC} {st : EngineState p T}
    (h : SlotHistory init st) (ht : TrailInv st) (item : Pending) :
    SlotHistory init (insertPending st item).1 := by
  unfold insertPending
  dsimp only
  split
  · exact SlotHistory.congr h (canonLit_doms st item.lit) (canonLit_trail st item.lit)
      (fun s => canonLit_changeList st item.lit s)
  · split
    · exact SlotHistory.congr h (canonClause_doms (canonLit st item.lit).2 _)
        (canonClause_trail (canonLit st item.lit).2 _)
        (fun s => canonClause_changeList (canonLit st item.lit).2 _ s)
    · exact SlotHistory.congr h (canonLit_doms st item.lit) (canonLit_trail st item.lit)
        (fun s => canonLit_changeList st item.lit s)
  · split
    · split
      · exact SlotHistory.congr h (canonClause_doms (canonLit st item.lit).2 _)
          (canonClause_trail (canonLit st item.lit).2 _)
          (fun s => canonClause_changeList (canonLit st item.lit).2 _ s)
      · exact SlotHistory.congr h (canonLit_doms st item.lit) (canonLit_trail st item.lit)
          (fun s => canonLit_changeList st item.lit s)
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
      change SlotHistory init (canonNegLit st4 l).2
      have h1 : SlotHistory init st1 :=
        SlotHistory.congr h (canonLit_doms st item.lit) (canonLit_trail st item.lit)
          (fun s => canonLit_changeList st item.lit s)
      have ht1 : TrailInv st1 :=
        TrailInv.congr ht (by simp [st1, canonLit]) (by simp [st1, canonLit])
          (by simp [st1, canonLit]) (by simp [st1, canonLit]) (by simp [st1, canonLit])
      have hd'f : d'.isEmpty = false := by
        have hfalse : ¬ (d'.isEmpty = true) := hz
        cases hb : d'.isEmpty with
        | false => rfl
        | true => exact absurd hb hfalse
      have hd'_ne : d' ≠ DomC.empty := by
        intro hEq
        have hle : d'.isEmpty = true := by rw [hEq]; rfl
        rw [hd'f] at hle
        exact Bool.noConfusion hle
      have hd_ne : d ≠ DomC.empty := by
        intro hEq
        have hle : d'.isEmpty = true := by
          show (d.applyLit l.lit).isEmpty = true
          rw [hEq]
          exact DomC.empty_applyLit_isEmpty l.lit
        rw [hd'f] at hle
        exact Bool.noConfusion hle
      have hslot : slot < st1.doms.size := by
        by_cases hlt : slot < st1.doms.size
        · exact hlt
        · have hge : st1.doms.size ≤ slot := Nat.le_of_not_lt hlt
          have hdempty : d = DomC.empty := by
            simp only [d, Array.getD_eq_getElem?_getD]
            rw [Array.getElem?_eq_none hge]
            rfl
          exact False.elim (hd_ne hdempty)
      have hset : st2.doms = st1.doms.setGrow slot d' DomC.empty := by
        simp only [st2]
        exact Array.set!_eq_setGrow_of_lt (a := st1.doms) (i := slot) (v := d')
          (d := DomC.empty) hslot
      have h3 : SlotHistory init st3 := by
        have hpt := slotHistory_trailPush (init := init) (st := st1) h1 ht1
          (e := e) (hprev := rfl) (hd' := rfl)
        apply SlotHistory.congr hpt
        · simp only [st3, st2, e, trailPush, hset]
          rfl
        · simp [st3, st2, e, trailPush]
        · intro s
          simp [st3, st2, e, trailPush, EngineState.changeList]
      have h4 : SlotHistory init st4 :=
        SlotHistory.congr h3 (emitSlot_doms st3 slot d d')
          (emitSlot_trail st3 slot d d') (fun s => emitSlot_changeList st3 slot d d' s)
      exact SlotHistory.congr h4 (canonNegLit_doms st4 l)
        (canonNegLit_trail st4 l) (fun s => canonNegLit_changeList st4 l s)

theorem Array.size_filter_le {α : Type} (a : Array α) (p : α → Bool) :
    (a.filter p).size ≤ a.size := by
  rw [← Array.length_toList (xs := a.filter p), Array.toList_filter,
    ← Array.length_toList (xs := a)]
  exact List.length_filter_le p a.toList

theorem List.filter_lt_spec {l : List Nat} (hs : l.Pairwise (· < ·)) (L : Nat) :
    l.filter (fun q => q < L) = l.take (l.filter (fun q => q < L)).length ∧
    (∀ j q, j < (l.filter (fun q => q < L)).length → l[j]? = some q → q < L) ∧
    (∀ j q, (l.filter (fun q => q < L)).length ≤ j → l[j]? = some q → L ≤ q) := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      rw [List.pairwise_cons] at hs
      obtain ⟨hxall, hs'⟩ := hs
      obtain ⟨ihA, ihB, ihC⟩ := ih hs'
      let p : Nat → Bool := fun q => q < L
      by_cases hx : x < L
      · have hpx : p x = true := by simpa [p] using hx
        have hfx : (x :: xs).filter p = x :: xs.filter p := List.filter_cons_of_pos hpx
        have hm : ((x :: xs).filter p).length = (xs.filter p).length + 1 := by
          rw [hfx]; simp
        refine ⟨?_, ?_, ?_⟩
        · rw [hfx]
          simp only [List.length_cons]
          rw [List.take_succ_cons, ← ihA]
        · intro j q hj hq
          rw [hm] at hj
          cases j with
          | zero =>
              rw [List.getElem?_cons_zero] at hq
              injection hq with hq
              subst hq; exact hx
          | succ k =>
              rw [List.getElem?_cons_succ] at hq
              have hk : k < (List.filter (fun q => q < L) xs).length := by
                simp only [p] at hj
                omega
              exact ihB k q hk hq
        · intro j q hj hq
          rw [hm] at hj
          cases j with
          | zero => omega
          | succ k =>
              rw [List.getElem?_cons_succ] at hq
              have hk : (List.filter (fun q => q < L) xs).length ≤ k := by
                simp only [p] at hj
                omega
              exact ihC k q hk hq
      · have hpx : ¬ p x = true := by simpa [p] using hx
        have hxs : xs.filter p = [] := by
          apply List.filter_eq_nil_iff.mpr
          intro a ha
          have hxa := hxall a ha
          have hLx : L ≤ x := by omega
          show ¬ p a = true
          simp [p]
          omega
        have hfx : (x :: xs).filter p = [] := by
          rw [List.filter_cons_of_neg hpx, hxs]
        have hm : ((x :: xs).filter p).length = 0 := by rw [hfx]; rfl
        refine ⟨?_, ?_, ?_⟩
        · rw [hfx]; rfl
        · intro j q hj hq; rw [hm] at hj; omega
        · intro j q hj hq
          rw [hm] at hj
          cases j with
          | zero =>
              rw [List.getElem?_cons_zero] at hq
              injection hq with hq
              subst hq
              omega
          | succ k =>
              rw [List.getElem?_cons_succ] at hq
              have hxq : x < q := hxall q (List.mem_of_getElem? hq)
              omega

theorem SortedList.filter_eq_extract {a : Array Nat} (h : SortedList a) (L : Nat) :
    a.filter (fun q => q < L) = a.extract 0 (a.filter (fun q => q < L)).size := by
  apply Array.ext'
  rw [Array.toList_filter, Array.toList_extract]
  have hlen : (a.filter (fun q => q < L)).size =
      (a.toList.filter (fun q => q < L)).length := by
    rw [← Array.length_toList (xs := a.filter (fun q => q < L)), Array.toList_filter]
  rw [hlen]
  rw [(List.filter_lt_spec (l := a.toList) h L).1, List.extract_eq_take_drop]
  simp

theorem SortedList.filter_getD_lt {a : Array Nat} (h : SortedList a) {L j : Nat}
    (hj : j < (a.filter (fun q => q < L)).size) : a.getD j 0 < L := by
  have hspec := (List.filter_lt_spec (l := a.toList) h L).2.1
  have hjs : j < (a.toList.filter (fun q => q < L)).length := by
    rw [← Array.toList_filter (p := fun q => q < L) (xs := a), Array.length_toList]
    exact hj
  have hjlt : j < a.size := Nat.lt_of_lt_of_le hj (Array.size_filter_le a _)
  refine hspec j (a.getD j 0) hjs ?_
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem hjlt,
    Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hjlt]
  rfl

theorem SortedList.filter_getD_ge {a : Array Nat} (h : SortedList a) {L j : Nat}
    (hj : (a.filter (fun q => q < L)).size ≤ j) (hjlt : j < a.size) :
    L ≤ a.getD j 0 := by
  have hspec := (List.filter_lt_spec (l := a.toList) h L).2.2
  have hjs : (a.toList.filter (fun q => q < L)).length ≤ j := by
    rw [← Array.toList_filter (p := fun q => q < L) (xs := a), Array.length_toList]
    exact hj
  refine hspec j (a.getD j 0) hjs ?_
  rw [Array.getElem?_toList, Array.getElem?_eq_getElem hjlt,
    Array.getD_eq_getElem?_getD, Array.getElem?_eq_getElem hjlt]
  rfl

theorem undoFuel_doms_empty_of_none {st : EngineState p T} {limit f s : Nat}
    (hnone : ∀ q e', limit ≤ q → q < limit + f → st.trail[q]? = some e' → e'.slot ≠ s) :
    (undoFuel st limit f).doms.getD s DomC.empty = st.doms.getD s DomC.empty := by
  induction f generalizing st limit with
  | zero => simp [undoFuel]
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · rename_i e0 he0
        have hnone' : ∀ q e', limit ≤ q → q < limit + f →
            (undoStep st e0 limit).trail[q]? = some e' → e'.slot ≠ s := by
          intro q e' hq hqf hqe
          exact hnone q e' hq (by omega) (by simpa [undoStep] using hqe)
        rw [ih (st := undoStep st e0 limit) (limit := limit) hnone']
        unfold undoStep
        have hne : s ≠ e0.slot := by
          intro h
          exact hnone (limit + f) e0 (by omega) (by omega) he0 h.symm
        exact Array.getD_setGrow_other _ _ _ _ _ hne

theorem backjump_doms_of_none_empty {st : EngineState p T} (h : TrailInv st) {k s : Nat}
    (hk : k < st.level)
    (hnone : ∀ q e', st.levelStart.getD (k + 1) 0 ≤ q → q < st.trail.size →
      st.trail[q]? = some e' → e'.slot ≠ s) :
    (backjump st k).doms.getD s DomC.empty = st.doms.getD s DomC.empty := by
  have hlim : st.backjumpLimit (min k st.level) = st.levelStart.getD (k + 1) 0 := by
    rw [show min k st.level = k by omega]
    exact backjumpLimit_of_lt h hk
  have hLle : st.levelStart.getD (k + 1) 0 ≤ st.trail.size := by
    have := h.levelStart_le_trail (k + 1) (by have := h.levelStart_size; omega)
    exact this
  have hdoms : (backjump st k).doms =
      (undoFuel st (st.levelStart.getD (k + 1) 0)
        (st.trail.size - st.levelStart.getD (k + 1) 0)).doms := by
    simp [backjump, hlim]
  rw [hdoms]
  exact undoFuel_doms_empty_of_none (limit := st.levelStart.getD (k + 1) 0)
    (f := st.trail.size - st.levelStart.getD (k + 1) 0)
    (fun q e' hq hqf hqe => hnone q e' hq (by omega) hqe)

theorem backjump_changeList_eq_extract {st : EngineState p T} (h : TrailInv st) {k : Nat}
    {s : Slot} (hk : k < st.level) :
    (backjump st k).changeList s =
      (st.changeList s).extract 0
        ((st.changeList s).filter (fun q => q < st.levelStart.getD (k + 1) 0)).size := by
  rw [backjump_changeList_eq h hk]
  exact SortedList.filter_eq_extract (h.changeIndex_sorted s) _

theorem domAfter_backjump_eq_of_lt {init : Array DomC} {st : EngineState p T}
    (ht : TrailInv st) {k m : Nat} {s : Slot} (hk : k < st.level)
    (hm : m ≤ (st.changeList s).size)
    (hprefix : ∀ j, j < m → (st.changeList s).getD j 0 < st.levelStart.getD (k + 1) 0) :
    domAfter init (backjump st k) s m = domAfter init st s m := by
  let L := st.levelStart.getD (k + 1) 0
  let a := st.changeList s
  have hsort : SortedList a := ht.changeIndex_sorted s
  have hmM : m ≤ (a.filter (fun q => q < L)).size := by
    by_cases hle : m ≤ (a.filter (fun q => q < L)).size
    · exact hle
    · have hMlt : (a.filter (fun q => q < L)).size < m := by omega
      have hMltA : (a.filter (fun q => q < L)).size < a.size :=
        Nat.lt_of_lt_of_le hMlt hm
      have hge := SortedList.filter_getD_ge hsort (L := L)
        (j := (a.filter (fun q => q < L)).size) (Nat.le_refl _) hMltA
      have hlt : a.getD (a.filter (fun q => q < L)).size 0 < L := by
        simpa [a, L] using hprefix _ hMlt
      omega
  have hcl : (backjump st k).changeList s = a.filter (fun q => q < L) := by
    simpa [a, L] using backjump_changeList_eq ht hk (s := s)
  have hext : ((backjump st k).changeList s).extract 0 m = a.extract 0 m := by
    rw [hcl, SortedList.filter_eq_extract hsort L, Array.extract_extract]
    have hmin : min m (a.filter (fun q => q < L)).size = m := Nat.min_eq_left hmM
    simp only [Nat.zero_add]
    rw [hmin]
  apply domAfter_congr_extract (init := init) (st := st) (st' := backjump st k)
    (k := m) (k' := m) hext
  intro j hj
  have hposlt : a.getD j 0 < L := hprefix j hj
  have hposL : a.getD j 0 < st.levelStart.getD (k + 1) 0 := by simpa [L, a] using hposlt
  have hpost : a.getD j 0 < st.trail.size := ht.getD_changeList_lt (by omega)
  rw [backjump_trail_eq_of_lt ht hk, Array.getElem?_extract]
  have hcond : a.getD j 0 < min (st.levelStart.getD (k + 1) 0) st.trail.size - 0 := by
    rw [Nat.sub_zero]
    exact Nat.lt_min.mpr ⟨hposL, hpost⟩
  rw [if_pos hcond, Nat.zero_add]

theorem backjump_slotHistory {init : Array DomC} {st : EngineState p T}
    (h : SlotHistory init st) (ht : TrailInv st) {k : Nat} (hk : k < st.level) :
    SlotHistory init (backjump st k) := by
  let L := st.levelStart.getD (k + 1) 0
  let M : Slot → Nat := fun s => ((st.changeList s).filter (fun q => q < L)).size
  have hcl : ∀ s, (backjump st k).changeList s = (st.changeList s).extract 0 (M s) := by
    intro s
    simpa [L, M] using backjump_changeList_eq_extract ht hk (s := s)
  have hMle : ∀ s, M s ≤ (st.changeList s).size := by
    intro s
    exact Array.size_filter_le (st.changeList s) _
  have hsz : ∀ s, ((backjump st k).changeList s).size = M s := by
    intro s
    rw [hcl s, Array.size_extract]
    exact Nat.min_eq_left (hMle s)
  have hprefix : ∀ (s : Slot) (j : Nat), j < M s →
      (st.changeList s).getD j 0 < L := by
    intro s j hj
    exact SortedList.filter_getD_lt (ht.changeIndex_sorted s) (L := L) (by simpa [M] using hj)
  constructor
  · intro s
    let a := st.changeList s
    let m := M s
    have hsort : SortedList a := ht.changeIndex_sorted s
    have hmle : m ≤ a.size := by simpa [a, m] using hMle s
    have hcl_s : (backjump st k).changeList s = a.extract 0 m := by simpa [a, m] using hcl s
    by_cases hm : m < a.size
    · let pos := a.getD m 0
      have hmM : (a.filter (fun q => q < L)).size = m := rfl
      have hLle : L ≤ pos := by
        have := SortedList.filter_getD_ge hsort (L := L) (j := m)
          (by rw [← hmM]; exact Nat.le_refl _) (by simpa [a] using hm)
        simpa [pos, a] using this
      have hpost : pos < st.trail.size := by
        have := ht.getD_changeList_lt (s := s) (j := m) (by simpa [a] using hm)
        simpa [pos, a] using this
      have hmem : pos ∈ a := by
        simpa [pos, a] using Array.getD_mem (a := a) hm
      obtain ⟨-, e, he, hslot⟩ := (ht.changeIndex_mem s pos).1 (by simpa [a] using hmem)
      have hprev : e.prev = domAfter init st s m := by
        have hpe := h.prev_eq s m (by simpa [a] using hm)
        have hgd : st.trail.getD pos default = e := by
          rw [Array.getD_eq_getElem?_getD, he]
          rfl
        have hpe' : (st.trail.getD pos default).prev = domAfter init st s m := by
          simpa only [a, pos] using hpe
        rw [hgd] at hpe'
        exact hpe'
      have hmin : ∀ q e', L ≤ q → q < pos → st.trail[q]? = some e' → e'.slot ≠ s := by
        intro q e' hqL hqp hqe hslotq
        have hqmem : q ∈ a := by
          apply (ht.changeIndex_mem s q).2
          exact ⟨by omega, ⟨e', hqe, hslotq⟩⟩
        obtain ⟨j, hjq⟩ := Array.mem_iff_getElem?.1 hqmem
        have hjlt : j < a.size := by
          by_cases hlt : j < a.size
          · exact hlt
          · rw [Array.getElem?_eq_none (by omega)] at hjq
            cases hjq
        have hgdj : a.getD j 0 = q := by
          rw [Array.getD_eq_getElem?_getD, hjq]
          rfl
        by_cases hjm : j < m
        · have hltL : a.getD j 0 < L := by
            exact SortedList.filter_getD_lt hsort (L := L) (by simpa [m, M] using hjm)
          omega
        · have hle : m ≤ j := Nat.le_of_not_lt hjm
          have hmono : pos ≤ a.getD j 0 := by
            have := hsort.getD_le (i := m) (j := j) hle hjlt
            simpa [pos] using this
          omega
      have hdom := backjump_doms_of_least ht hk (s := s) (d := DomC.empty)
        (pos := pos) (e := e)
        (by simpa [L, pos, a] using hLle) hpost he hslot hmin
      rw [hdom, hprev, hsz s]
      have hmle' : m ≤ (st.changeList s).size := hmle
      have hpref' : ∀ j, j < m →
          (st.changeList s).getD j 0 < st.levelStart.getD (k + 1) 0 :=
        fun j hj => hprefix s j hj
      have hcongr : domAfter init (backjump st k) s m = domAfter init st s m :=
        domAfter_backjump_eq_of_lt (init := init) (st := st) ht hk (s := s)
          (m := m) hmle' hpref'
      exact hcongr.symm
    · have hmsize : m = a.size := by omega
      have hnone : ∀ q e', L ≤ q → q < st.trail.size →
          st.trail[q]? = some e' → e'.slot ≠ s := by
        intro q e' hqL hqt hqe hslotq
        have hqmem : q ∈ a := by
          apply (ht.changeIndex_mem s q).2
          exact ⟨hqt, ⟨e', hqe, hslotq⟩⟩
        obtain ⟨j, hjq⟩ := Array.mem_iff_getElem?.1 hqmem
        have hjlt : j < a.size := by
          by_cases hlt : j < a.size
          · exact hlt
          · rw [Array.getElem?_eq_none (by omega)] at hjq
            cases hjq
        have hgdj : a.getD j 0 = q := by
          rw [Array.getD_eq_getElem?_getD, hjq]
          rfl
        have hjm : j < m := by omega
        have hltL : a.getD j 0 < L := by
          exact SortedList.filter_getD_lt (ht.changeIndex_sorted s) (L := L) (by simpa [m, M] using hjm)
        omega
      have hdom := backjump_doms_of_none_empty ht hk hnone
      rw [hdom, h.doms_eq s, hsz s]
      have hsize' : (st.changeList s).size = m := hmsize.symm
      rw [hsize']
      have hmle' : m ≤ (st.changeList s).size := hmle
      have hpref' : ∀ j, j < m →
          (st.changeList s).getD j 0 < st.levelStart.getD (k + 1) 0 :=
        fun j hj => hprefix s j hj
      have hcongr : domAfter init (backjump st k) s m = domAfter init st s m :=
        domAfter_backjump_eq_of_lt (init := init) (st := st) ht hk (s := s)
          (m := m) hmle' hpref'
      exact hcongr.symm
  · intro s j hj
    let a := st.changeList s
    let m := M s
    have hsort : SortedList a := ht.changeIndex_sorted s
    have hmle : m ≤ a.size := by simpa [a, m] using hMle s
    have hj_m : j < m := by
      have h := hj
      rw [hsz s] at h
      exact h
    have hpos : ((backjump st k).changeList s).getD j 0 = a.getD j 0 := by
      rw [show (backjump st k).changeList s = a.extract 0 m by simpa [a, m] using hcl s]
      rw [Array.getD_extract a 0 m j 0 (by
        rw [Nat.sub_zero]
        exact Nat.lt_min.mpr ⟨hj_m, Nat.lt_of_lt_of_le hj_m hmle⟩)]
      simp
    have hposlt : a.getD j 0 < L := by
      exact SortedList.filter_getD_lt hsort (L := L) (by simpa [m, M] using hj_m)
    have hpost : a.getD j 0 < st.trail.size := by
      have hja : j < a.size := Nat.lt_of_lt_of_le hj_m hmle
      exact ht.getD_changeList_lt (s := s) (j := j) (by simpa [a] using hja)
    have htr : (backjump st k).trail.getD (a.getD j 0) default =
        st.trail.getD (a.getD j 0) default := by
      rw [backjump_trail_eq_of_lt ht hk]
      rw [Array.getD_extract st.trail 0 L (a.getD j 0) default (by
        rw [Nat.sub_zero]
        exact Nat.lt_min.mpr ⟨hposlt, hpost⟩)]
      simp
    show ((backjump st k).trail.getD
      (((backjump st k).changeList s).getD j 0) default).prev =
      domAfter init (backjump st k) s j
    rw [hpos, htr]
    have hpe := h.prev_eq s j (by simpa [a] using (by omega : j < a.size))
    have hpe' : (st.trail.getD (a.getD j 0) default).prev = domAfter init st s j := by
      simpa [a] using hpe
    rw [hpe']
    have hjle : j ≤ (st.changeList s).size := by
      have hja : j ≤ a.size := Nat.le_trans (Nat.le_of_lt hj_m) hmle
      simpa [a] using hja
    have hprefj : ∀ i, i < j →
        (st.changeList s).getD i 0 < st.levelStart.getD (k + 1) 0 :=
      fun i hi => hprefix s i (by omega)
    exact (domAfter_backjump_eq_of_lt (init := init) (st := st) ht hk (s := s)
      (m := j) hjle hprefj).symm

end LeanFzn.Engine
