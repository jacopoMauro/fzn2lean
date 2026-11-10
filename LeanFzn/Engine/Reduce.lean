/-
File: LeanFzn/Engine/Reduce.lean

N13: certified learned-clause database reduction.

Every `StoredClause` still carries the kernel-checked entailment proof of its
`EClause`; `reasonClause?` returns the stored clause for a `.learned id`
regardless of the `deleted` flag.  This module deletes learned clauses by
marking slots deleted and rebuilding the watch lists, but it never pushes
those slots on `free` and never changes a slot's contents.  Consequently a
live trail entry that refers to slot `id` keeps pointing at the same clause
with the same proof: deletion can only lose propagation strength, never a
proof or a reason.  (The `Inv` preservation lemmas below make the structural
part of this argument explicit.)

Policy: keep every clause with `lbd ≤ 2` and every clause with at most two
literals; among the remaining live clauses, delete the top LBD buckets until
at least half of them are covered.  At most `nextReduce`-scheduled runs do
any work, and the schedule doubles, so total reduction work is geometric in
the number of conflicts.

DAG:
  LeanFzn.Engine.Clauses -> LeanFzn.Engine.Reduce -> LeanFzn.Engine.Search
  LeanFzn.Engine.Analyze -> LeanFzn.Engine.Search (supplies the LBD field)

No proof holes, no custom axioms.
-/
import LeanFzn.Engine.Clauses

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Small array and counting helpers -/

/-- `getElem?` after `set!`, including the out-of-bounds no-op case. -/
private theorem array_getElem?_set! {α : Type} (xs : Array α) (i j : Nat) (v : α) :
    (xs.set! i v)[j]? =
      if i = j then (if i < xs.size then some v else xs[j]?) else xs[j]? := by
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds]
  by_cases hij : i = j
  · subst j
    by_cases h : i < xs.size
    · simp [h]
    · have hnone : xs[i]? = none := Array.getElem?_eq_none (Nat.le_of_not_lt h)
      simp [h, hnone]
  · simp [hij]

/-- Complement counting: the number of entries failing `p` is the size minus
the number passing `p`. -/
private theorem array_countP_not {α : Type} (xs : Array α) (p : α → Bool) :
    xs.countP (fun a => !p a) = xs.size - xs.countP p := by
  rw [← Array.countP_toList, ← Array.countP_toList]
  have hsum : ∀ l : List α,
      List.countP p l + List.countP (fun a => !p a) l = l.length := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
        rw [List.countP_cons, List.countP_cons, List.length_cons]
        cases hp : p a <;> simp [hp] at ih ⊢ <;> omega
  have h := hsum xs.toList
  have hlen : xs.toList.length = xs.size := Array.length_toList
  omega

/-- A `mapIdx` count is bounded by the count of the source under any pointwise
implication.  The index offset makes the induction go through. -/
private theorem list_countP_mapIdx_le {α β : Type} (f : Nat → α → β)
    (p : β → Bool) (q : α → Bool)
    (h : ∀ i a, p (f i a) = true → q a = true) :
    ∀ (l : List α) (n : Nat),
      (l.mapIdx (fun i a => f (n + i) a)).countP p ≤ l.countP q := by
  intro l
  induction l with
  | nil => intro n; simp
  | cons a t ih =>
      intro n
      rw [List.mapIdx_cons, List.countP_cons, List.countP_cons]
      have hshift : t.mapIdx (fun i a => f (n + (i + 1)) a) =
          t.mapIdx (fun i a => f ((n + 1) + i) a) := by
        congr 1
        funext i a
        congr 1
        omega
      rw [hshift]
      have ht := ih (n + 1)
      have h0 : p (f n a) = true → q a = true := h n a
      simp only [Nat.add_zero]
      by_cases hp : p (f n a)
      · have hq : q a = true := h0 hp
        simp [hp, hq] at ht ⊢
        omega
      · by_cases hq : q a
        · simp [hp, hq] at ht ⊢
          omega
        · simp [hp, hq] at ht ⊢
          omega

/-- Array version of `list_countP_mapIdx_le`. -/
private theorem array_countP_mapIdx_le {α β : Type} (f : Nat → α → β)
    (p : β → Bool) (q : α → Bool)
    (h : ∀ i a, p (f i a) = true → q a = true) (xs : Array α) :
    (xs.mapIdx f).countP p ≤ xs.countP q := by
  rw [← Array.countP_toList, ← Array.countP_toList, Array.toList_mapIdx]
  have := list_countP_mapIdx_le f p q h xs.toList 0
  simpa using this

/-! ## Updating the LBD field -/

/-- Overwrite the LBD of one slot.  Out-of-range ids and all other slots are
left untouched; deleted slots are updated too (the field is pure policy data).
The record update preserves every field read by `ClauseDB.Inv`. -/
def ClauseDB.setLbd (db : ClauseDB p T) (id n : Nat) : ClauseDB p T :=
  match db.clauses[id]? with
  | some sc => { db with clauses := db.clauses.set! id { sc with lbd := n } }
  | none => db

/-- The clause array after `setLbd`, pointwise. -/
theorem ClauseDB.setLbd_getElem? (db : ClauseDB p T) (id n j : Nat) :
    (db.setLbd id n).clauses[j]? =
      if j = id then (db.clauses[j]?).map (fun sc => { sc with lbd := n })
      else db.clauses[j]? := by
  unfold ClauseDB.setLbd
  split
  · rename_i sc hget
    have hsize : id < db.clauses.size := (Array.getElem?_eq_some_iff.mp hget).1
    rw [array_getElem?_set!]
    by_cases hji : j = id
    · subst j
      rw [if_pos rfl]
      rw [if_pos rfl]
      rw [if_pos hsize]
      rw [hget]
      rfl
    · have hidj : ¬ id = j := fun h => hji h.symm
      simp only [if_neg hidj, if_neg hji]
  · rename_i hnone
    have hge : db.clauses.size ≤ id := Array.getElem?_eq_none_iff.mp hnone
    by_cases hji : j = id
    · subst j
      rw [if_pos rfl]
      simp [hnone]
    · have hidj : ¬ id = j := fun h => hji h.symm
      simp only [if_neg hidj, if_neg hji]

@[simp] theorem ClauseDB.setLbd_clauses_size (db : ClauseDB p T) (id n : Nat) :
    (db.setLbd id n).clauses.size = db.clauses.size := by
  unfold ClauseDB.setLbd
  split <;> simp [Array.size_set!]

/-- `setLbd` preserves the structural database invariant: `Inv` never reads
the `lbd` field. -/
theorem ClauseDB.setLbd_inv (db : ClauseDB p T) (id n : Nat) (h : db.Inv) :
    (db.setLbd id n).Inv := by
  unfold ClauseDB.setLbd
  split
  · rename_i sc hget
    have hsize : id < db.clauses.size := (Array.getElem?_eq_some_iff.mp hget).1
    have hnewlive : ({ sc with lbd := n } : StoredClause p T).deleted = sc.deleted := rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i ids hi x hx
      have hx' := h.watch_lt i ids hi x hx
      simpa [Array.size_set!] using hx'
    · intro j scj hj hdel hsz
      rw [array_getElem?_set!] at hj
      by_cases hji : j = id
      · subst j
        simp only [if_pos rfl, hsize, ↓reduceIte] at hj
        obtain rfl : scj = { sc with lbd := n } := (Option.some.inj hj).symm
        have hdel' : sc.deleted = false := by simpa using hdel
        have hsz' : 2 ≤ sc.e.lits.size := by simpa using hsz
        simpa using h.pos_lt id sc hget hdel' hsz'
      · have hidj : ¬ id = j := fun h => hji h.symm
        simp only [if_neg hidj] at hj
        exact h.pos_lt j scj hj hdel hsz
    · intro j scj hj hdel hsz
      rw [array_getElem?_set!] at hj
      by_cases hji : j = id
      · subst j
        simp only [if_pos rfl, hsize, ↓reduceIte] at hj
        obtain rfl : scj = { sc with lbd := n } := (Option.some.inj hj).symm
        have hdel' : sc.deleted = false := by simpa using hdel
        have hsz' : 2 ≤ sc.e.lits.size := by simpa using hsz
        change db.WatchedBy id sc
        exact h.watches id sc hget hdel' hsz'
      · have hidj : ¬ id = j := fun h => hji h.symm
        simp only [if_neg hidj] at hj
        exact h.watches j scj hj hdel hsz
    · have hcnt : ({ db with clauses := db.clauses.set! id { sc with lbd := n } }
          : ClauseDB p T).liveCount = db.liveCount := by
        unfold ClauseDB.liveCount
        rw [ClauseDB.deletedCount_set_same db id sc { sc with lbd := n } hget hsize hnewlive,
          Array.size_set!]
      rw [h.live_eq]
      exact hcnt.symm
    · intro j hj
      obtain ⟨scj, hgetj, hdelj⟩ := h.free_deleted j hj
      by_cases hji : j = id
      · subst j
        rw [hget] at hgetj
        have hscj : scj = sc := (Option.some.inj hgetj).symm
        subst scj
        refine ⟨{ sc with lbd := n }, ?_, by simp [hdelj]⟩
        rw [array_getElem?_set!]
        simp [hsize]
      · refine ⟨scj, ?_, hdelj⟩
        have hidj : ¬ id = j := fun h => hji h.symm
        rw [array_getElem?_set!]
        simpa only [if_neg hidj] using hgetj
    · exact h.free_nodup
  · exact h

/-- A successful `setLbd` reads back with the new LBD. -/
theorem ClauseDB.setLbd_getElem?_self (db : ClauseDB p T) (id n : Nat)
    (sc : StoredClause p T) (h : db.clauses[id]? = some sc) :
    (db.setLbd id n).clauses[id]? = some { sc with lbd := n } := by
  rw [ClauseDB.setLbd_getElem?]
  simp [h]

/-- `setLbd` leaves the live-clause count unchanged. -/
@[simp] theorem ClauseDB.setLbd_live (db : ClauseDB p T) (id n : Nat) :
    (db.setLbd id n).live = db.live := by
  unfold ClauseDB.setLbd
  split <;> rfl

/-! ## Compacting the watch lists -/

/-- True when slot `id` holds a live clause. -/
def ClauseDB.liveB (db : ClauseDB p T) (id : Nat) : Bool :=
  match db.clauses[id]? with
  | some sc => !sc.deleted
  | none => false

/-- Drop every watch entry whose slot is deleted or out of range.  Live
clauses keep all their entries (stale entries of live clauses are harmless). -/
def ClauseDB.compactWatches (db : ClauseDB p T) : ClauseDB p T :=
  { db with watch := db.watch.map fun ids => ids.filter db.liveB }

@[simp] theorem ClauseDB.compactWatches_clauses (db : ClauseDB p T) :
    (db.compactWatches).clauses = db.clauses := rfl

@[simp] theorem ClauseDB.compactWatches_free (db : ClauseDB p T) :
    (db.compactWatches).free = db.free := rfl

@[simp] theorem ClauseDB.compactWatches_live (db : ClauseDB p T) :
    (db.compactWatches).live = db.live := rfl

@[simp] theorem ClauseDB.compactWatches_liveB (db : ClauseDB p T) (id : Nat) :
    (db.compactWatches).liveB id = db.liveB id := rfl

/-- The watch row of a compacted database is the filtered old row. -/
theorem ClauseDB.compactWatches_watchList (db : ClauseDB p T) (i : Nat) :
    (db.compactWatches).watchList i = (db.watchList i).filter db.liveB := by
  unfold ClauseDB.compactWatches ClauseDB.watchList
  dsimp only
  rw [Array.getD_eq_getD_getElem?, Array.getD_eq_getD_getElem?, Array.getElem?_map]
  cases h : db.watch[i]? with
  | none => rfl
  | some ids => rfl

/-- Compaction keeps every live clause's watch membership. -/
theorem ClauseDB.watchesAt_compactWatches (db : ClauseDB p T) (i id : Nat)
    (hmem : db.WatchesAt i id) (hlive : db.liveB id = true) :
    (db.compactWatches).WatchesAt i id := by
  unfold ClauseDB.WatchesAt at hmem ⊢
  rw [ClauseDB.compactWatches_watchList, Array.mem_filter]
  exact ⟨hmem, hlive⟩

/-- Watch compaction preserves the structural database invariant. -/
theorem ClauseDB.compactWatches_inv (db : ClauseDB p T) (h : db.Inv) :
    (db.compactWatches).Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hi x hx
    have hi' : (db.watch.map (fun ids => ids.filter db.liveB))[i]? = some ids := hi
    rw [Array.getElem?_map] at hi'
    cases hrow : db.watch[i]? with
    | none => rw [hrow] at hi'; simp at hi'
    | some old =>
        rw [hrow] at hi'
        simp only [Option.map_some, Option.some.injEq] at hi'
        subst ids
        exact h.watch_lt i old hrow x (Array.mem_filter.mp hx).1
  · intro id sc hget hdel hsz
    exact h.pos_lt id sc hget hdel hsz
  · intro id sc hget hdel hsz
    have hget' : db.clauses[id]? = some sc := by
      simpa [ClauseDB.compactWatches] using hget
    have hlive : db.liveB id = true := by
      unfold ClauseDB.liveB
      rw [hget']
      simp [hdel]
    have hw := h.watches id sc hget' hdel hsz
    constructor
    · intro q hq
      exact ClauseDB.watchesAt_compactWatches db q.idx id (hw.1 q hq) hlive
    · intro q hq
      exact ClauseDB.watchesAt_compactWatches db q.idx id (hw.2 q hq) hlive
  · change db.live = (db.compactWatches).liveCount
    rw [h.live_eq]
    have hcnt : (db.compactWatches).liveCount = db.liveCount := by
      unfold ClauseDB.liveCount ClauseDB.deletedCount
      rfl
    exact hcnt.symm
  · intro id hid
    exact h.free_deleted id hid
  · exact h.free_nodup

/-! ## Retiring clauses without reusing their slots -/

/-- Mark one slot deleted when the policy selects it.  Already deleted slots
are left alone; live slots are never rewritten except for the `deleted` flag. -/
def retireStep (doomed : Nat → StoredClause p T → Bool) (id : Nat)
    (sc : StoredClause p T) : StoredClause p T :=
  if sc.deleted then sc
  else if doomed id sc then { sc with deleted := true } else sc

@[simp] theorem retireStep_e_lits (doomed : Nat → StoredClause p T → Bool)
    (id : Nat) (sc : StoredClause p T) :
    (retireStep doomed id sc).e.lits = sc.e.lits := by
  by_cases hd : sc.deleted <;> by_cases hdoom : doomed id sc <;>
    simp [retireStep, hd, hdoom]

@[simp] theorem retireStep_w1 (doomed : Nat → StoredClause p T → Bool)
    (id : Nat) (sc : StoredClause p T) :
    (retireStep doomed id sc).w1 = sc.w1 := by
  by_cases hd : sc.deleted <;> by_cases hdoom : doomed id sc <;>
    simp [retireStep, hd, hdoom]

@[simp] theorem retireStep_w2 (doomed : Nat → StoredClause p T → Bool)
    (id : Nat) (sc : StoredClause p T) :
    (retireStep doomed id sc).w2 = sc.w2 := by
  by_cases hd : sc.deleted <;> by_cases hdoom : doomed id sc <;>
    simp [retireStep, hd, hdoom]

/-- A marked-live step is the identity step (and the source was live). -/
theorem retireStep_live_eq (doomed : Nat → StoredClause p T → Bool)
    (id : Nat) (sc : StoredClause p T)
    (h : (retireStep doomed id sc).deleted = false) :
    sc.deleted = false ∧ retireStep doomed id sc = sc := by
  by_cases hd : sc.deleted
  · simp [retireStep, hd] at h
  · by_cases hdoom : doomed id sc
    · simp [retireStep, hd, hdoom] at h
    · have hstep : retireStep doomed id sc = sc := by simp [retireStep, hd, hdoom]
      exact ⟨by simpa using hd, hstep⟩

/-- Mark selected live slots deleted and recompute `live`.  The free list and
the clause-array size are untouched: a retired slot is never reused, so every
trail reason keeps pointing at its original clause and proof. -/
def ClauseDB.retireMark (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) : ClauseDB p T :=
  let clauses := db.clauses.mapIdx (retireStep doomed)
  { db with clauses := clauses, live := clauses.countP (fun sc => !sc.deleted) }

@[simp] theorem ClauseDB.retireMark_watch (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireMark doomed).watch = db.watch := rfl

@[simp] theorem ClauseDB.retireMark_free (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireMark doomed).free = db.free := rfl

@[simp] theorem ClauseDB.retireMark_clauses (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireMark doomed).clauses = db.clauses.mapIdx (retireStep doomed) := rfl

@[simp] theorem ClauseDB.retireMark_live (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireMark doomed).live =
      (db.clauses.mapIdx (retireStep doomed)).countP (fun sc => !sc.deleted) := rfl

/-- The marked clause array reads back pointwise. -/
theorem ClauseDB.retireMark_getElem? (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) (id : Nat) :
    (db.retireMark doomed).clauses[id]? =
      (db.clauses[id]?).map (retireStep doomed id) := by
  simp [ClauseDB.retireMark, Array.getElem?_mapIdx]

theorem ClauseDB.retireMark_clauses_size (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireMark doomed).clauses.size = db.clauses.size := by
  simp [ClauseDB.retireMark, Array.size_mapIdx]

/-- Marking preserves the structural database invariant. -/
theorem ClauseDB.retireMark_inv (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) (h : db.Inv) :
    (db.retireMark doomed).Inv := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hi x hx
    have hx' := h.watch_lt i ids hi x hx
    simpa [ClauseDB.retireMark, Array.size_mapIdx] using hx'
  · intro id sc hget hdel hsz
    rw [ClauseDB.retireMark_getElem?] at hget
    cases hold : db.clauses[id]? with
    | none => rw [hold] at hget; simp at hget
    | some old =>
        rw [hold] at hget
        simp only [Option.map_some, Option.some.injEq] at hget
        subst sc
        obtain ⟨holdlive, hstep⟩ := retireStep_live_eq doomed id old hdel
        have hsz' : 2 ≤ old.e.lits.size := by simpa using hsz
        have hpos := h.pos_lt id old hold holdlive hsz'
        simpa [hstep] using hpos
  · intro id sc hget hdel hsz
    rw [ClauseDB.retireMark_getElem?] at hget
    cases hold : db.clauses[id]? with
    | none => rw [hold] at hget; simp at hget
    | some old =>
        rw [hold] at hget
        simp only [Option.map_some, Option.some.injEq] at hget
        subst sc
        obtain ⟨holdlive, hstep⟩ := retireStep_live_eq doomed id old hdel
        have hsz' : 2 ≤ old.e.lits.size := by simpa using hsz
        have hw := h.watches id old hold holdlive hsz'
        rw [hstep]
        change db.WatchedBy id old
        exact hw
  · show (db.clauses.mapIdx (retireStep doomed)).countP (fun sc => !sc.deleted) =
      (db.retireMark doomed).liveCount
    have hcnt : (db.retireMark doomed).liveCount =
        (db.clauses.mapIdx (retireStep doomed)).size -
          (db.clauses.mapIdx (retireStep doomed)).countP (fun sc => sc.deleted) := by
      unfold ClauseDB.liveCount ClauseDB.deletedCount
      rw [ClauseDB.retireMark_clauses, Array.size_mapIdx]
    rw [hcnt, array_countP_not]
  · intro id hid
    obtain ⟨sc, hget, hdel⟩ := h.free_deleted id hid
    refine ⟨sc, ?_, hdel⟩
    rw [ClauseDB.retireMark_getElem?, hget]
    simp [retireStep, hdel]
  · exact h.free_nodup

/-- Retire the selected live clauses, recompute `live`, and compact the watch
lists.  Slots stay allocated (they are not pushed on `free`). -/
def ClauseDB.retireWhere (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) : ClauseDB p T :=
  (db.retireMark doomed).compactWatches

@[simp] theorem ClauseDB.retireWhere_clauses (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireWhere doomed).clauses = db.clauses.mapIdx (retireStep doomed) := rfl

@[simp] theorem ClauseDB.retireWhere_free (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireWhere doomed).free = db.free := rfl

@[simp] theorem ClauseDB.retireWhere_live (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireWhere doomed).live =
      (db.clauses.mapIdx (retireStep doomed)).countP (fun sc => !sc.deleted) := rfl

theorem ClauseDB.retireWhere_clauses_size (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) :
    (db.retireWhere doomed).clauses.size = db.clauses.size := by
  rw [ClauseDB.retireWhere_clauses, Array.size_mapIdx]

/-- Retiring preserves the structural database invariant. -/
theorem ClauseDB.retireWhere_inv (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) (h : db.Inv) :
    (db.retireWhere doomed).Inv :=
  ClauseDB.compactWatches_inv (db.retireMark doomed) (db.retireMark_inv doomed h)

/-- Retiring never increases the live-clause count. -/
theorem ClauseDB.retireWhere_live_le (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) (h : db.Inv) :
    (db.retireWhere doomed).live ≤ db.live := by
  have hlive : db.live = db.clauses.countP (fun sc => !sc.deleted) := by
    rw [h.live_eq]
    unfold ClauseDB.liveCount ClauseDB.deletedCount
    rw [array_countP_not]
  rw [ClauseDB.retireWhere_live, hlive]
  exact array_countP_mapIdx_le (retireStep doomed)
    (fun sc => !sc.deleted) (fun sc => !sc.deleted)
    (fun i sc hp => by
      by_cases hd : sc.deleted
      · simp [retireStep, hd] at hp
      · by_cases hdoom : doomed i sc
        · simp [retireStep, hd, hdoom] at hp
        · simp [retireStep, hd, hdoom])
    db.clauses

/-! ## The reduction policy -/

/-- Cap LBD values into a small histogram bucket. -/
def reduceBucket (lbd : Nat) : Nat :=
  if lbd > 32 then 32 else lbd

/-- A live clause is a reduction candidate when it is neither short nor
low-LBD. -/
def reduceCandidate {p : CompiledProblem DomConstraint} {T : LitTable}
    (sc : StoredClause p T) : Bool :=
  !sc.deleted && decide (2 < sc.lbd) && decide (2 < sc.e.lits.size)

/-- Clear the per-interval usefulness flags.  Slots, clauses, proofs, watch
positions and deletion flags are unchanged. -/
def ClauseDB.clearUsed (db : ClauseDB p T) : ClauseDB p T :=
  { db with clauses := db.clauses.map (fun sc => { sc with used := false }) }

@[simp] theorem ClauseDB.clearUsed_clauses (db : ClauseDB p T) :
    db.clearUsed.clauses = db.clauses.map (fun sc => { sc with used := false }) := rfl

theorem ClauseDB.clearUsed_clauses_size (db : ClauseDB p T) :
    db.clearUsed.clauses.size = db.clauses.size := by
  rw [ClauseDB.clearUsed_clauses, Array.size_map]

@[simp] theorem ClauseDB.clearUsed_live (db : ClauseDB p T) :
    db.clearUsed.live = db.live := rfl

theorem ClauseDB.clearUsed_inv (db : ClauseDB p T) (h : db.Inv) : db.clearUsed.Inv := by
  have hcnt : db.clearUsed.liveCount = db.liveCount := by
    have hcomp : ((fun sc : StoredClause p T => sc.deleted) ∘
        (fun sc : StoredClause p T => { sc with used := false })) =
        (fun sc : StoredClause p T => sc.deleted) := by
      funext sc
      rfl
    unfold ClauseDB.liveCount ClauseDB.deletedCount ClauseDB.clearUsed
    rw [Array.size_map, Array.countP_map, hcomp]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i ids hi id hid
    rw [ClauseDB.clearUsed_clauses_size]
    exact h.watch_lt i ids hi id hid
  · intro id sc hget hdel hsz
    rw [ClauseDB.clearUsed_clauses] at hget
    rw [Array.getElem?_map] at hget
    cases hold : db.clauses[id]? with
    | none => rw [hold] at hget; simp at hget
    | some old =>
        rw [hold] at hget
        simp only [Option.map_some, Option.some.injEq] at hget
        subst sc
        exact h.pos_lt id old hold (by simpa using hdel) (by simpa using hsz)
  · intro id sc hget hdel hsz
    rw [ClauseDB.clearUsed_clauses] at hget
    rw [Array.getElem?_map] at hget
    cases hold : db.clauses[id]? with
    | none => rw [hold] at hget; simp at hget
    | some old =>
        rw [hold] at hget
        simp only [Option.map_some, Option.some.injEq] at hget
        subst sc
        exact h.watches id old hold (by simpa using hdel) (by simpa using hsz)
  · rw [ClauseDB.clearUsed_live, hcnt, h.live_eq]
  · intro id hid
    obtain ⟨sc, hget, hdel⟩ := h.free_deleted id hid
    refine ⟨{ sc with used := false }, ?_, hdel⟩
    rw [ClauseDB.clearUsed_clauses, Array.getElem?_map, hget]
    rfl
  · exact h.free_nodup

/-- LBD histogram of the candidate set, built in one pass over the slots
(bucket `32` collects all LBDs above 32). -/
def ClauseDB.reduceHistogram (db : ClauseDB p T) : Array Nat :=
  db.clauses.foldl (fun hist sc =>
    if reduceCandidate sc then hist.modify (reduceBucket sc.lbd) (· + 1)
    else hist) (Array.replicate 33 0)

/-- The number of reduction candidates. -/
def reduceCandidateCount (hist : Array Nat) : Nat :=
  hist.foldl (· + ·) 0

/-- Walk down the histogram from the highest bucket and return the first
bucket that covers at least half of `total`. -/
def reduceThresholdOf (total : Nat) (hist : Array Nat) : Nat :=
  let rec go (b acc : Nat) : Nat :=
    if b = 0 then 0
    else
      let acc' := acc + hist.getD b 0
      if 2 * acc' ≥ total then b else go (b - 1) acc'
  termination_by b
  decreasing_by omega
  go 32 0

/-- The LBD cutoff selected by the candidate histogram. -/
def ClauseDB.reduceThreshold (db : ClauseDB p T) : Nat :=
  let hist := db.reduceHistogram
  reduceThresholdOf (reduceCandidateCount hist) hist

/-- Policy predicate at a precomputed cutoff: a candidate whose bucket is at
or above `thr`.  `reduce` hoists the cutoff once, so the predicate is O(1)
per slot during retirement. -/
def ClauseDB.reduceDoomed (thr : Nat) (sc : StoredClause p T) : Bool :=
  reduceCandidate sc && decide (thr ≤ reduceBucket sc.lbd)

/-- Certified reduction: keep short and low-LBD clauses; among the remaining
live clauses, retire the top LBD buckets until at least half are covered.
With fewer than 100 candidates the database is returned unchanged. -/
def ClauseDB.reduce (db : ClauseDB p T) : ClauseDB p T :=
  let hist := db.reduceHistogram
  let total := reduceCandidateCount hist
  if total < 100 then db.clearUsed.compactWatches
  else
    let thr := reduceThresholdOf total hist
    ((db.retireWhere (fun _ sc => ClauseDB.reduceDoomed thr sc)).clearUsed).compactWatches

theorem ClauseDB.reduce_clauses_size (db : ClauseDB p T) :
    db.reduce.clauses.size = db.clauses.size := by
  unfold ClauseDB.reduce
  dsimp only
  split
  · rw [ClauseDB.compactWatches_clauses]
    exact ClauseDB.clearUsed_clauses_size db
  · rw [ClauseDB.compactWatches_clauses, ClauseDB.clearUsed_clauses_size]
    exact ClauseDB.retireWhere_clauses_size db _

/-- Reduction preserves the structural database invariant. -/
theorem ClauseDB.reduce_inv (db : ClauseDB p T) (h : db.Inv) : db.reduce.Inv := by
  unfold ClauseDB.reduce
  dsimp only
  split
  · exact ClauseDB.compactWatches_inv (db.clearUsed) (ClauseDB.clearUsed_inv db h)
  · have hdb : (db.retireWhere (fun _ sc =>
        ClauseDB.reduceDoomed
          (reduceThresholdOf (reduceCandidateCount db.reduceHistogram)
            db.reduceHistogram) sc)).Inv :=
      ClauseDB.retireWhere_inv db _ h
    exact ClauseDB.compactWatches_inv _ (ClauseDB.clearUsed_inv _ hdb)

/-- Reduction never increases the live-clause count. -/
theorem ClauseDB.reduce_live_le (db : ClauseDB p T) (h : db.Inv) :
    db.reduce.live ≤ db.live := by
  unfold ClauseDB.reduce
  dsimp only
  split
  · exact Nat.le_refl _
  · exact ClauseDB.retireWhere_live_le db _ h

/-! ## The reduction schedule -/

/-- Run reduction when `stats.learned` reaches `nextReduce`, then advance the
threshold to at least twice its old value and strictly past the current
learned count.  The strict-growth clause matters once the count is large: a
plain capped doubling would freeze the threshold at the cap and then reduce
at every decision boundary.  The threshold is advanced even when the policy
deleted nothing, so the work is geometric in the conflict count. -/
def maybeReduce (st : EngineState p T) : EngineState p T :=
  if st.stats.learned >= st.nextReduce then
    let db := st.db.reduce
    { st with
      db := db
      nextReduce := max 2000 (max (st.stats.learned + 1) (st.nextReduce * 2))
      stats := { st.stats with
        reductions := st.stats.reductions + 1
        reducedClauses := st.stats.reducedClauses + (st.db.live - db.live) } }
  else st

@[simp] theorem maybeReduce_doms (st : EngineState p T) :
    (maybeReduce st).doms = st.doms := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_trail (st : EngineState p T) :
    (maybeReduce st).trail = st.trail := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_level (st : EngineState p T) :
    (maybeReduce st).level = st.level := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_stats (st : EngineState p T) :
    (maybeReduce st).stats =
      if st.stats.learned >= st.nextReduce then
        { st.stats with
          reductions := st.stats.reductions + 1
          reducedClauses := st.stats.reducedClauses +
            (st.db.live - st.db.reduce.live) }
      else st.stats := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_table (st : EngineState p T) :
    (maybeReduce st).table = st.table := by
  unfold maybeReduce
  split <;> rfl

@[simp] theorem maybeReduce_nextReduce (st : EngineState p T) :
    (maybeReduce st).nextReduce =
      if st.stats.learned >= st.nextReduce then
        max 2000 (max (st.stats.learned + 1) (st.nextReduce * 2))
      else st.nextReduce := by
  unfold maybeReduce
  split <;> rfl

/-- The schedule is the only state change: the database and the threshold. -/
theorem maybeReduce_db (st : EngineState p T) :
    (maybeReduce st).db =
      if st.stats.learned >= st.nextReduce then st.db.reduce else st.db := by
  unfold maybeReduce
  split <;> rfl

/-- When a reduction may run, the database still satisfies `Inv`. -/
theorem maybeReduce_inv (st : EngineState p T) (h : st.db.Inv) :
    (maybeReduce st).db.Inv := by
  rw [maybeReduce_db]
  split
  · exact ClauseDB.reduce_inv st.db h
  · exact h

/-! ## Reduction preserves stored-literal well-formedness -/

/-- `setLbd` only changes the LBD policy field of one slot. -/
theorem ClauseDB.setLbd_clauses_e (db : ClauseDB p T) (id n j : Nat) :
    ((db.setLbd id n).clauses[j]?).map (fun sc : StoredClause p T => sc.e) =
      (db.clauses[j]?).map (fun sc : StoredClause p T => sc.e) := by
  rw [ClauseDB.setLbd_getElem?]
  by_cases hji : j = id
  · rw [if_pos hji]
    cases hget : db.clauses[j]? with
    | none => rfl
    | some sc => simp
  · rw [if_neg hji]

theorem ClauseDB.LitsWF.setLbd {S : LitTable} {db : ClauseDB p T}
    (h : db.LitsWF S) (id n : Nat) : (db.setLbd id n).LitsWF S :=
  ClauseDB.LitsWF.of_map_e h (ClauseDB.setLbd_clauses_e db id n)

/-- `retireStep` never changes the carried clause. -/
@[simp] theorem retireStep_e (doomed : Nat → StoredClause p T → Bool)
    (id : Nat) (sc : StoredClause p T) :
    (retireStep doomed id sc).e = sc.e := by
  by_cases hd : sc.deleted <;> by_cases hdoom : doomed id sc <;>
    simp [retireStep, hd, hdoom]

theorem ClauseDB.retireMark_clauses_e (db : ClauseDB p T)
    (doomed : Nat → StoredClause p T → Bool) (j : Nat) :
    ((db.retireMark doomed).clauses[j]?).map
        (fun sc : StoredClause p T => sc.e) =
      (db.clauses[j]?).map (fun sc : StoredClause p T => sc.e) := by
  rw [ClauseDB.retireMark_getElem?, Option.map_map]
  congr 1
  funext sc
  exact retireStep_e doomed j sc

theorem ClauseDB.LitsWF.retireMark {S : LitTable} {db : ClauseDB p T}
    (h : db.LitsWF S) (doomed : Nat → StoredClause p T → Bool) :
    (db.retireMark doomed).LitsWF S :=
  ClauseDB.LitsWF.of_map_e h (ClauseDB.retireMark_clauses_e db doomed)

theorem ClauseDB.LitsWF.retireWhere {S : LitTable} {db : ClauseDB p T}
    (h : db.LitsWF S) (doomed : Nat → StoredClause p T → Bool) :
    (db.retireWhere doomed).LitsWF S := by
  unfold ClauseDB.retireWhere
  exact ClauseDB.LitsWF.of_map_e (ClauseDB.LitsWF.retireMark h doomed)
    (fun j => by rw [ClauseDB.compactWatches_clauses])

theorem ClauseDB.clearUsed_clauses_e (db : ClauseDB p T) (j : Nat) :
    ((db.clearUsed).clauses[j]?).map (fun sc : StoredClause p T => sc.e) =
      (db.clauses[j]?).map (fun sc : StoredClause p T => sc.e) := by
  rw [ClauseDB.clearUsed_clauses, Array.getElem?_map]
  cases hget : db.clauses[j]? with
  | none => rfl
  | some sc => simp

theorem ClauseDB.LitsWF.clearUsed {S : LitTable} {db : ClauseDB p T}
    (h : db.LitsWF S) : (db.clearUsed).LitsWF S :=
  ClauseDB.LitsWF.of_map_e h (ClauseDB.clearUsed_clauses_e db)

theorem ClauseDB.LitsWF.compactWatches {S : LitTable} {db : ClauseDB p T}
    (h : db.LitsWF S) : (db.compactWatches).LitsWF S :=
  ClauseDB.LitsWF.of_map_e h (fun j => by rw [ClauseDB.compactWatches_clauses])

theorem ClauseDB.LitsWF.reduce {S : LitTable} {db : ClauseDB p T}
    (h : db.LitsWF S) : db.reduce.LitsWF S := by
  unfold ClauseDB.reduce
  dsimp only
  split
  · exact ClauseDB.LitsWF.compactWatches (ClauseDB.LitsWF.clearUsed h)
  · exact ClauseDB.LitsWF.compactWatches
      (ClauseDB.LitsWF.clearUsed (ClauseDB.LitsWF.retireWhere h _))

theorem maybeReduce_litsWF {S : LitTable} {st : EngineState p T}
    (h : st.db.LitsWF S) : (maybeReduce st).db.LitsWF S := by
  rw [maybeReduce_db]
  split
  · exact ClauseDB.LitsWF.reduce h
  · exact h

end LeanFzn.Engine
