/-
File: LeanFzn/Engine/Trail.lean

N4: array trail, levels, undo and the per-slot change index.

The trail records, for every domain change, the literal that was set, the
decision level, the reason that justified it, the slot and the previous
domain (the undo image).  The undo path replays those images in reverse;
`changeIndex[s]` lists, oldest first, the trail positions at which slot `s`
changed.

The linearity rule is respected: every operation threads the state and
returns it; no copy of `doms`/`trail` is retained.  The transient reason
store `st.reasons` is append-only for the lifetime of one solve and is
**not** truncated by `backjump` (R6(a) in `docs/N0-core-design.md` §15):
reason ids are allocated in propagator-batch order, not trail order, so a
surviving entry can reference a larger id than a popped one.

`earliestImplying` is the indexed query N8 uses to find the earliest trail
entry after which a literal became false.  It binary searches the slot's
change list under the semantic predicate `FalsifiedAfter`
(`entry.prev.applyLit entry.lit.lit` falsifies the target); the predicate is
monotone along the list whenever the slot's domains shrink, which is the
runtime behaviour of the trail.  The specification is
`Trail.earliestImplying_spec`.
-/
import LeanFzn.Engine.Types
import LeanFzn.Engine.Lit
import LeanFzn.Engine.Dom

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace Array

/-! ## Array growth helper

`Array.set!` (`= Array.setIfInBounds`) silently drops a write whose index is
out of range.  Both the change index and the domain array must instead grow
on demand: a dropped change-index write would hide the entry from
`earliestImplying` and a dropped domain write would lose an undo image. -/

/-- `a.setGrow i v d` sets index `i` of `a` to `v`, extending `a` with `d`
when `i ≥ a.size`. -/
def setGrow {α : Type} (a : Array α) (i : Nat) (v : α) (d : α) : Array α :=
  (a ++ Array.replicate (i + 1 - a.size) d).set! i v

@[simp] theorem size_setGrow {α : Type} (a : Array α) (i : Nat) (v d : α) :
    (a.setGrow i v d).size = max a.size (i + 1) := by
  unfold setGrow
  rw [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds, Array.size_append,
    Array.size_replicate]
  omega

theorem getElem?_setGrow {α : Type} (a : Array α) (i : Nat) (v d : α) (j : Nat) :
    (a.setGrow i v d)[j]? =
      (if j = i then some v
        else if j < a.size then a[j]? else if j < i then some d else none) := by
  unfold setGrow
  rw [Array.set!_eq_setIfInBounds, Array.getElem?_setIfInBounds, Array.getElem?_append,
    Array.getElem?_replicate]
  by_cases hji : j = i
  · subst j
    have hi : i < a.size + (i + 1 - a.size) := by omega
    simp [hi]
  · have hne : i ≠ j := fun h => hji h.symm
    simp only [hji, if_false, hne, if_false]
    by_cases hjs : j < a.size
    · simp [hjs]
    · rw [if_neg hjs, if_neg hjs]
      by_cases hlt : j < i
      · have : j - a.size < i + 1 - a.size := by omega
        simp [hlt, this]
      · have : ¬ j - a.size < i + 1 - a.size := by omega
        simp [hlt, this]

theorem getD_eq_getElem?_getD {α : Type} (a : Array α) (i : Nat) (d : α) :
    a.getD i d = (a[i]?).getD d := by
  unfold Array.getD
  split
  · rename_i h
    rw [Array.getElem?_eq_getElem h]
    simp
  · rename_i h
    rw [Array.getElem?_eq_none_iff.mpr (by omega)]
    simp

theorem getD_setGrow_self {α : Type} (a : Array α) (i : Nat) (v d d' : α) :
    (a.setGrow i v d).getD i d' = v := by
  rw [getD_eq_getElem?_getD, getElem?_setGrow]
  simp

theorem getD_setGrow_other {α : Type} (a : Array α) (i j : Nat) (v d : α)
    (h : j ≠ i) : (a.setGrow i v d).getD j d = a.getD j d := by
  rw [getD_eq_getElem?_getD, getD_eq_getElem?_getD, getElem?_setGrow]
  by_cases hjs : j < a.size
  · simp [h, hjs]
  · by_cases hji : j < i
    · simp [h, hjs, hji]
    · simp [h, hjs, hji]

/-- Reading a different index that is already inside the array is unchanged
even when the two defaults differ (the `setGrow` padding is not consulted). -/
theorem getD_setGrow_other_of_lt {α : Type} (a : Array α) (i j : Nat) (v d d' : α)
    (hj : j < a.size) (h : j ≠ i) : (a.setGrow i v d).getD j d' = a.getD j d' := by
  rw [getD_eq_getElem?_getD, getD_eq_getElem?_getD, getElem?_setGrow]
  simp [h, hj]

@[simp] theorem getElem?_getD_setGrow_self {α : Type} (a : Array α) (i : Nat) (v d : α) :
    (a.setGrow i v d)[i]?.getD d = v := by
  rw [← Array.getD_eq_getElem?_getD]
  exact Array.getD_setGrow_self a i v d d

@[simp] theorem getElem?_getD_setGrow_other {α : Type} (a : Array α) (i j : Nat) (v d : α)
    (h : j ≠ i) : (a.setGrow i v d)[j]?.getD d = a[j]?.getD d := by
  rw [← Array.getD_eq_getElem?_getD, ← Array.getD_eq_getElem?_getD]
  exact Array.getD_setGrow_other a i j v d h

theorem getD_extract {α : Type} (a : Array α) (s t i : Nat) (d : α)
    (h : i < min t a.size - s) :
    (a.extract s t).getD i d = a.getD (s + i) d := by
  rw [getD_eq_getElem?_getD, Array.getElem?_extract, if_pos h]
  exact (getD_eq_getElem?_getD a (s + i) d).symm

end Array

namespace LeanFzn.Engine

/-! ## Sortedness of position lists

The change lists are strictly increasing positions.  Sorting is a
representation invariant used by the binary search; it carries no
soundness obligation (`docs/N0-core-design.md` §7). -/

/-- A strictly increasing array of naturals. -/
def SortedList (a : Array Nat) : Prop := a.toList.Pairwise (· < ·)

theorem SortedList.getD_lt {a : Array Nat} (h : SortedList a) {i j : Nat}
    (hij : i < j) (hj : j < a.size) : a.getD i 0 < a.getD j 0 := by
  have hi : i < a.size := Nat.lt_trans hij hj
  have hi' : i < a.toList.length := by simpa [Array.length_toList] using hi
  have hj' : j < a.toList.length := by simpa [Array.length_toList] using hj
  have hp := (List.pairwise_iff_getElem.mp h) i j hi' hj' hij
  have hgi : a.getD i 0 = a[i] := by simp [Array.getD, hi]
  have hgj : a.getD j 0 = a[j] := by simp [Array.getD, hj]
  rw [hgi, hgj]
  rw [Array.getElem_toList hi', Array.getElem_toList hj'] at hp
  exact hp

theorem SortedList.getD_le {a : Array Nat} (h : SortedList a) {i j : Nat}
    (hij : i ≤ j) (hj : j < a.size) : a.getD i 0 ≤ a.getD j 0 := by
  rcases Nat.lt_or_eq_of_le hij with hlt | heq
  · exact Nat.le_of_lt (h.getD_lt hlt hj)
  · subst heq
    exact Nat.le_refl _

theorem SortedList.extract {a : Array Nat} (h : SortedList a) (s t : Nat) :
    SortedList (a.extract s t) := by
  have h' : a.toList.Pairwise (· < ·) := h
  rw [SortedList, Array.toList_extract, List.extract_eq_take_drop]
  exact (h'.drop (i := s)).take (i := t - s)

theorem SortedList.filter {a : Array Nat} (h : SortedList a) (p : Nat → Bool) :
    SortedList (a.filter p) := by
  have h' : a.toList.Pairwise (· < ·) := h
  rw [SortedList, Array.toList_filter]
  exact h'.filter p

theorem SortedList.push {a : Array Nat} {v : Nat} (h : SortedList a)
    (hv : ∀ x, x ∈ a → x < v) : SortedList (a.push v) := by
  have h' : a.toList.Pairwise (· < ·) := h
  rw [SortedList, Array.toList_push, List.pairwise_append]
  refine ⟨h', by simp, ?_⟩
  intro x hx y hy
  simp only [List.mem_singleton] at hy
  subst hy
  exact hv x (by simpa using hx)

theorem Array.getD_mem {a : Array Nat} {i : Nat} (h : i < a.size) :
    a.getD i 0 ∈ a := by
  have hgi : a.getD i 0 = a[i] := by simp [Array.getD, h]
  rw [hgi]
  exact Array.getElem_mem h

/-! ## Trail operations -/

namespace EngineState

/-- The change list of `slot`: the trail positions at which the slot changed,
oldest first.  Missing slots read as the empty list. -/
def changeList (st : EngineState p T) (s : Slot) : Array Nat :=
  st.changeIndex.getD s #[]

/-- `backjumpLimit st k` is the number of trail entries kept by
`backjump st k` when `k` is the target level: the start of level `k+1`,
clamped to the trail size.  (Clamping matters only for a malformed
`levelStart`; the search always jumps to `k < level`.) -/
def backjumpLimit (st : EngineState p T) (k : Nat) : Nat :=
  min (st.levelStart.getD (k + 1) st.trail.size) st.trail.size

end EngineState

/-- Append one trail entry, updating the per-slot change index with the new
trail position (oldest first).  The change index grows on demand. -/
def trailPush (st : EngineState p T) (e : Entry) : EngineState p T :=
  let pos := st.trail.size
  { st with
    trail := st.trail.push e
    changeIndex := st.changeIndex.setGrow e.slot
      ((st.changeIndex.getD e.slot #[]).push pos) #[] }

/-- Enter a new decision level. -/
def newLevel (st : EngineState p T) : EngineState p T :=
  { st with
    level := st.level + 1
    levelStart := st.levelStart.push st.trail.size }

/-- Replace the change list of `slot` by its positions below `limit`,
growing the index array on demand. -/
def dropChangeFrom (ci : Array (Array Nat)) (slot limit : Nat) : Array (Array Nat) :=
  ci.setGrow slot ((ci.getD slot #[]).filter (fun p => p < limit)) #[]

/-- One undo step: restore `e.prev` for the entry's slot and drop that slot's
change-index positions at or above `limit`. -/
def undoStep (st : EngineState p T) (e : Entry) (limit : Nat) : EngineState p T :=
  { st with
    doms := st.doms.setGrow e.slot e.prev DomC.empty
    changeIndex := dropChangeFrom st.changeIndex e.slot limit }

/-- Undo the trail positions `[limit, limit + f)` in reverse, restoring each
slot's previous domain and dropping change-index positions at or above
`limit`.  The trail, levels and the transient reason store are untouched. -/
def undoFuel (st : EngineState p T) (limit : Nat) : Nat → EngineState p T
  | 0 => st
  | f + 1 =>
      match st.trail[limit + f]? with
      | none => st
      | some e => undoFuel (undoStep st e limit) limit f

/-- Undo every entry above level `k`, restoring the previous domain and
truncating the trail, `levelStart` and the change index.

`k` is clamped to the current level, so an out-of-range target cannot make
`levelStart` malformed.  The transient reason store is **not** truncated
(R6(a)): reason ids are not trail-ordered, so a surviving entry can carry a
larger reason id than a popped one. -/
def backjump (st : EngineState p T) (k : Nat) : EngineState p T :=
  let k := min k st.level
  let limit := st.backjumpLimit k
  let s := undoFuel st limit (st.trail.size - limit)
  { s with
    trail := s.trail.extract 0 limit
    levelStart := s.levelStart.extract 0 (k + 1)
    level := k }

/-! ## In-place runtime twins

`trailPush` reads the slot's change list while the index still holds it, so
`push` copies the row on every assignment; `backjump`'s `extract` rebuilds
the kept trail.  The twins below swap the row out with `Array.modify` and
pop the trail with `shrink`; `@[csimp]` makes the compiled code use them
while every proof keeps the reference definitions. -/

theorem setGrow_push_eq {α : Type} (a : Array (Array α)) (i : Nat) (x : α) :
    a.setGrow i ((a.getD i #[]).push x) #[] =
      if i < a.size then a.modify i (·.push x) else a.setGrow i #[x] #[] := by
  split
  · rename_i h
    have h0 : i + 1 - a.size = 0 := by omega
    simp only [Array.setGrow, h0, Array.replicate_zero, Array.append_empty,
      Array.set!_eq_setIfInBounds]
    apply Array.ext
    · simp
    · intro j hj1 hj2
      rw [Array.getElem_setIfInBounds, Array.getElem_modify]
      · split <;> simp_all
      · simpa using hj1
  · simp_all

/-- Runtime twin of `trailPush`. -/
def trailPushFast (st : EngineState p T) (e : Entry) : EngineState p T :=
  let pos := st.trail.size
  { st with
    trail := st.trail.push e
    changeIndex :=
      if e.slot < st.changeIndex.size then st.changeIndex.modify e.slot (·.push pos)
      else st.changeIndex.setGrow e.slot #[pos] #[] }

@[csimp] theorem trailPush_eq_fast : @trailPush = @trailPushFast := by
  funext p T st e
  simp only [trailPush, trailPushFast, setGrow_push_eq]

/-- Runtime twin of `backjump`. -/
def backjumpFast (st : EngineState p T) (k : Nat) : EngineState p T :=
  let k := min k st.level
  let limit := st.backjumpLimit k
  let s := undoFuel st limit (st.trail.size - limit)
  { s with
    trail := s.trail.shrink limit
    levelStart := s.levelStart.shrink (k + 1)
    level := k }

@[csimp] theorem backjump_eq_fast : @backjump = @backjumpFast := by
  funext p T st k
  simp only [backjump, backjumpFast, Array.shrink_eq_take, Array.take_eq_extract]

/-- Scan `trail[0..i)` from the end for the entry carrying exactly `l`
(whole-`PLit` identity: index and denotation). -/
def latestEntryFrom (trail : Array Entry) (l : PLit) : Nat → Option Nat
  | 0 => none
  | i + 1 =>
      match trail[i]? with
      | some e => if e.lit == l then some i else latestEntryFrom trail l i
      | none => none

/-- The latest trail entry carrying exactly `l` (whole-`PLit` identity). -/
def latestEntryOf (st : EngineState p T) (l : PLit) : Option Nat :=
  latestEntryFrom st.trail l st.trail.size

/-! ## Earliest explaining trail position

N8 (`Analyze.explainLit`) asks: at which trail position did `l` first become
false in slot `s`?  The semantic test below replays the entry's own
assignment on its previous domain, exactly as `explainLit` does, and asks
whether `l` is false afterwards.  The test is deliberately not the syntactic
`Lit.litImpliesNot` scan of the spike: the semantic test is what the
explanation path consumes, and it remains correct when the slot's domain was
tightened by several independent propagations. -/

/-- The semantic predicate of `earliestImplying`: after the trail entry at
`pos` sets its literal, the target literal `l` is false in that entry's
previous domain.  Missing positions are not falsifying. -/
def falsifiedAfter (st : EngineState p T) (pos : Nat) (l : Literal) : Bool :=
  match st.trail[pos]? with
  | some e => (e.prev.applyLit e.lit.lit).evalLit l == some false
  | none => false

/-- Numeric monotonicity of `falsifiedAfter` along the slot's change list.
This is the runtime assumption behind the binary search: once a literal has
become false, later entries of the same slot keep it false because domains
only shrink.  N3's `DomC` nesting lemmas are not available here, so the
monotonicity is an explicit hypothesis of `earliestImplying_spec`. -/
def FalsifiedMonotone (st : EngineState p T) (s : Slot) (l : Literal) : Prop :=
  ∀ i j, i < j → j < (st.changeList s).size →
    falsifiedAfter st ((st.changeList s).getD i 0) l = true →
    falsifiedAfter st ((st.changeList s).getD j 0) l = true

/-- Binary search for the first index in `[lo, hi)` satisfying `P`, assuming
`P` is monotone on that range.  `best` is a previously established
qualifying index at or above `hi`; the result is an index (not an element),
so callers map it through `getD`.  Fuel `hi - lo` suffices. -/
def bsearchFrom (a : Array Nat) (P : Nat → Bool) (lo hi : Nat)
    (best : Option Nat) : Nat → Option Nat
  | 0 => best
  | fuel + 1 =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if P (a.getD mid 0) then
          bsearchFrom a P lo mid (some mid) fuel
        else
          bsearchFrom a P (mid + 1) hi best fuel
      else best

/-- The earliest trail position in `changeIndex[s]` at which `l` became
false; `none` when no change in the slot ever falsified `l`.  This is the
indexed replacement for N8's linear `findSome?` scan over the same list.
The specification is `earliestImplying_spec`. -/
def earliestImplying (st : EngineState p T) (s : Slot) (l : Literal) : Option Nat :=
  let a := st.changeList s
  (bsearchFrom a (fun pos => falsifiedAfter st pos l) 0 a.size none a.size).map
    (fun i => a.getD i 0)

/-! ## Basic API lemmas -/

@[simp] theorem trailPush_trail (st : EngineState p T) (e : Entry) :
    (trailPush st e).trail = st.trail.push e := rfl

@[simp] theorem trailPush_trail_size (st : EngineState p T) (e : Entry) :
    (trailPush st e).trail.size = st.trail.size + 1 := by
  simp [trailPush]

@[simp] theorem trailPush_level (st : EngineState p T) (e : Entry) :
    (trailPush st e).level = st.level := rfl

@[simp] theorem trailPush_levelStart (st : EngineState p T) (e : Entry) :
    (trailPush st e).levelStart = st.levelStart := rfl

@[simp] theorem trailPush_doms (st : EngineState p T) (e : Entry) :
    (trailPush st e).doms = st.doms := rfl

@[simp] theorem trailPush_reasons (st : EngineState p T) (e : Entry) :
    (trailPush st e).reasons = st.reasons := rfl

@[simp] theorem trailPush_changeList_self (st : EngineState p T) (e : Entry) :
    (trailPush st e).changeList e.slot = (st.changeList e.slot).push st.trail.size := by
  simp [EngineState.changeList, trailPush]

theorem trailPush_changeList_ne (st : EngineState p T) (e : Entry) {s : Slot}
    (h : s ≠ e.slot) :
    (trailPush st e).changeList s = st.changeList s := by
  simp [EngineState.changeList, trailPush, h]

theorem trailPush_trail_old (st : EngineState p T) (e : Entry) {i : Nat}
    (h : i < st.trail.size) :
    (trailPush st e).trail[i]? = st.trail[i]? := by
  simp [trailPush, Array.getElem?_push, Nat.ne_of_lt h]

@[simp] theorem trailPush_trail_new (st : EngineState p T) (e : Entry) :
    (trailPush st e).trail[st.trail.size]? = some e := by
  simp [trailPush]

@[simp] theorem newLevel_level (st : EngineState p T) :
    (newLevel st).level = st.level + 1 := rfl

@[simp] theorem newLevel_levelStart (st : EngineState p T) :
    (newLevel st).levelStart = st.levelStart.push st.trail.size := rfl

@[simp] theorem newLevel_trail (st : EngineState p T) :
    (newLevel st).trail = st.trail := rfl

@[simp] theorem newLevel_doms (st : EngineState p T) :
    (newLevel st).doms = st.doms := rfl

@[simp] theorem newLevel_reasons (st : EngineState p T) :
    (newLevel st).reasons = st.reasons := rfl

@[simp] theorem newLevel_changeIndex (st : EngineState p T) :
    (newLevel st).changeIndex = st.changeIndex := rfl

@[simp] theorem newLevel_levelStart_size (st : EngineState p T) :
    (newLevel st).levelStart.size = st.levelStart.size + 1 := by
  simp [newLevel]

@[simp] theorem backjump_level (st : EngineState p T) (k : Nat) :
    (backjump st k).level = min k st.level := rfl

@[simp] theorem undoFuel_trail (st : EngineState p T) (limit f : Nat) :
    (undoFuel st limit f).trail = st.trail := by
  induction f generalizing st with
  | zero => rfl
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · exact ih _

@[simp] theorem undoFuel_level (st : EngineState p T) (limit f : Nat) :
    (undoFuel st limit f).level = st.level := by
  induction f generalizing st with
  | zero => rfl
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · exact ih _

@[simp] theorem undoFuel_levelStart (st : EngineState p T) (limit f : Nat) :
    (undoFuel st limit f).levelStart = st.levelStart := by
  induction f generalizing st with
  | zero => rfl
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · exact ih _

@[simp] theorem undoFuel_reasons (st : EngineState p T) (limit f : Nat) :
    (undoFuel st limit f).reasons = st.reasons := by
  induction f generalizing st with
  | zero => rfl
  | succ f ih =>
      unfold undoFuel
      split
      · rfl
      · exact ih _

@[simp] theorem backjump_trail (st : EngineState p T) (k : Nat) :
    (backjump st k).trail = st.trail.extract 0 (st.backjumpLimit (min k st.level)) := by
  simp [backjump, EngineState.backjumpLimit]

@[simp] theorem backjump_levelStart (st : EngineState p T) (k : Nat) :
    (backjump st k).levelStart = st.levelStart.extract 0 (min k st.level + 1) := by
  simp [backjump]

@[simp] theorem backjump_reasons (st : EngineState p T) (k : Nat) :
    (backjump st k).reasons = st.reasons := by
  simp [backjump]

@[simp] theorem backjump_limit_le_trail (st : EngineState p T) (k : Nat) :
    st.backjumpLimit k ≤ st.trail.size := by
  simp only [EngineState.backjumpLimit]
  omega

theorem backjump_trail_size (st : EngineState p T) (k : Nat) :
    (backjump st k).trail.size = st.backjumpLimit (min k st.level) := by
  rw [backjump_trail, Array.size_extract]
  have := backjump_limit_le_trail st (min k st.level)
  omega

theorem _root_.Array.getD_push_lt {α : Type} (a : Array α) {i : Nat} (v d : α)
    (h : i < a.size) : (a.push v).getD i d = a.getD i d := by
  rw [Array.getD_eq_getElem?_getD, Array.getD_eq_getElem?_getD, Array.getElem?_push,
    if_neg (Nat.ne_of_lt h)]

theorem _root_.Array.getD_push_eq {α : Type} (a : Array α) (v d : α) :
    (a.push v).getD a.size d = v := by
  rw [Array.getD_eq_getElem?_getD, Array.getElem?_push, if_pos rfl, Option.getD_some]

/-! ## Shape invariant

`TrailInv` collects the trail/level/change-index shape facts later modules
consume.  It is a representation invariant only: a violation can cost speed
or force `gaveUp`, never a wrong claim (`docs/N0-core-design.md` §4).

* `levelStart[0] = 0` and `levelStart.size = level + 1`;
* `levelStart` is strictly increasing and bounded by the trail size;
* every trail entry sits at a position inside its own level's
  `levelStart` range;
* every per-slot change list is strictly increasing and lists exactly the
  positions of that slot's entries. -/
structure TrailInv (st : EngineState p T) : Prop where
  /-- The first level starts at trail position zero. -/
  levelStart_zero : st.levelStart[0]? = some 0
  /-- There is one start per level, plus the initial level. -/
  levelStart_size : st.levelStart.size = st.level + 1
  /-- Level starts are strictly increasing. -/
  levelStart_strict : SortedList st.levelStart
  /-- No level starts beyond the current trail. -/
  levelStart_le_trail : ∀ i, i < st.levelStart.size → st.levelStart.getD i 0 ≤ st.trail.size
  /-- Every entry's level is a live level. -/
  entry_level : ∀ (i : Nat) (e : Entry), st.trail[i]? = some e → e.level < st.levelStart.size
  /-- Every entry lies at or after the start of its level. -/
  entry_levelStart_le : ∀ (i : Nat) (e : Entry), st.trail[i]? = some e → st.levelStart.getD e.level 0 ≤ i
  /-- Change lists are strictly increasing. -/
  changeIndex_sorted : ∀ s, SortedList (st.changeList s)
  /-- Change lists are exactly the entry positions of the slot. -/
  changeIndex_mem : ∀ s p, p ∈ st.changeList s ↔
    p < st.trail.size ∧ ∃ e, st.trail[p]? = some e ∧ e.slot = s

/-- Every entry's level is at most the current level. -/
theorem TrailInv.entry_level_le {st : EngineState p T} (h : TrailInv st) {i : Nat} {e : Entry}
    (he : st.trail[i]? = some e) : e.level ≤ st.level := by
  have h1 := h.entry_level i e he
  have h2 := h.levelStart_size
  omega

/-- The shape invariant of the canonical initial state built by `Search.initState`
(`levelStart = #[0]`, `level = 0`, empty trail, empty change lists). -/
theorem trailInv_init {st : EngineState p T} (hls : st.levelStart = #[0])
    (hl : st.level = 0) (ht : st.trail = #[])
    (hci : ∀ s, st.changeList s = #[]) : TrailInv st := by
  constructor
  · simp [hls]
  · simp [hls, hl]
  · rw [hls]
    simp [SortedList]
  · intro i hi
    rw [hls] at hi
    simp at hi
    have hi0 : i = 0 := by omega
    subst hi0
    simp [hls, ht]
  · intro i e he
    simp [ht] at he
  · intro i e he
    simp [ht] at he
  · intro s
    rw [hci s]
    simp [SortedList]
  · intro s p
    rw [hci s]
    simp [ht]

/-! ## `trailPush` preserves the shape -/

theorem trailPush_trailInv {st : EngineState p T} (h : TrailInv st) {e : Entry}
    (he : e.level ≤ st.level) : TrailInv (trailPush st e) := by
  have hsz : (trailPush st e).trail.size = st.trail.size + 1 := trailPush_trail_size st e
  constructor
  · simpa using h.levelStart_zero
  · simpa using h.levelStart_size
  · simpa using h.levelStart_strict
  · intro i hi
    have hi' : i < st.levelStart.size := by simpa using hi
    have hle := h.levelStart_le_trail i hi'
    simp only [trailPush, Array.size_push]
    omega
  · intro i e' hge
    simp only [trailPush] at hge
    rw [Array.getElem?_push] at hge
    split at hge
    · rename_i hsize
      injection hge with heq
      subst heq
      have h1 := h.levelStart_size
      simp only [trailPush]
      omega
    · rename_i hne
      have := h.entry_level i e' hge
      simpa using this
  · intro i e' hge
    simp only [trailPush] at hge
    rw [Array.getElem?_push] at hge
    split at hge
    · rename_i hsize
      injection hge with heq
      subst heq
      have hlt : e.level < st.levelStart.size := by
        have := h.levelStart_size
        omega
      have hle := h.levelStart_le_trail e.level hlt
      simp only [trailPush]
      omega
    · rename_i hne
      have := h.entry_levelStart_le i e' hge
      simpa using this
  · intro s
    by_cases hs : s = e.slot
    · subst hs
      rw [trailPush_changeList_self]
      refine SortedList.push (h.changeIndex_sorted e.slot) ?_
      intro x hx
      exact ((h.changeIndex_mem e.slot x).1 hx).1
    · rw [trailPush_changeList_ne st e hs]
      exact h.changeIndex_sorted s
  · intro s p
    by_cases hs : s = e.slot
    · subst hs
      rw [trailPush_changeList_self, Array.mem_push]
      constructor
      · intro hp
        rcases hp with hp | hp
        · have hold := (h.changeIndex_mem e.slot p).1 hp
          obtain ⟨hplt, e', he', hslot⟩ := hold
          refine ⟨by omega, e', ?_, hslot⟩
          simp only [trailPush]
          rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hplt)]
          exact he'
        · subst hp
          refine ⟨?_, e, ?_, rfl⟩
          · simp [trailPush]
          · simp [trailPush]
      · intro hp
        obtain ⟨hplt, e', he', hslot⟩ := hp
        simp only [trailPush] at he'
        rw [Array.getElem?_push] at he'
        split at he'
        · rename_i hsize
          injection he' with heq
          subst heq
          exact Or.inr hsize
        · rename_i hne
          refine Or.inl ((h.changeIndex_mem e.slot p).2 ⟨?_, e', he', hslot⟩)
          omega
    · rw [trailPush_changeList_ne st e hs]
      rw [h.changeIndex_mem s p]
      constructor
      · intro hp
        obtain ⟨hplt, e', he', hslot⟩ := hp
        refine ⟨by omega, e', ?_, hslot⟩
        simp only [trailPush]
        rw [Array.getElem?_push, if_neg (Nat.ne_of_lt hplt)]
        exact he'
      · intro hp
        obtain ⟨hplt, e', he', hslot⟩ := hp
        by_cases hpe : p = st.trail.size
        · exfalso
          simp only [trailPush] at he'
          rw [Array.getElem?_push, if_pos hpe] at he'
          injection he' with heq
          subst heq
          exact hs hslot.symm
        · refine ⟨?_, e', ?_, hslot⟩
          · simp only [trailPush] at hplt
            rw [Array.size_push] at hplt
            omega
          · simp only [trailPush] at he'
            rwa [Array.getElem?_push, if_neg (Nat.ne_of_lt (by
              simp only [trailPush] at hplt
              rw [Array.size_push] at hplt
              omega))] at he'

/-- After a push the current level has a non-empty trail prefix, the
precondition `newLevel` needs for strict `levelStart`. -/
theorem trailPush_levelStart_lt_trail {st : EngineState p T} (h : TrailInv st) (e : Entry) :
    (trailPush st e).levelStart.getD (trailPush st e).level 0 < (trailPush st e).trail.size := by
  have hlt : st.level < st.levelStart.size := by
    have := h.levelStart_size
    omega
  have hle := h.levelStart_le_trail st.level hlt
  simp only [trailPush, Array.size_push]
  omega

/-! ## `newLevel` preserves the shape -/

/-- `newLevel` preserves the shape invariant provided the current level is
non-empty (`levelStart[level] < trail.size`).  The engine calls `newLevel`
immediately before pushing a decision, so the hypothesis holds at every
call site; `trailPush_levelStart_lt_trail` re-establishes it after a push. -/
theorem newLevel_trailInv {st : EngineState p T} (h : TrailInv st)
    (hlast : st.levelStart.getD st.level 0 < st.trail.size) : TrailInv (newLevel st) := by
  constructor
  · have hs : st.levelStart.size ≠ 0 := by
      intro h0
      have hz := h.levelStart_zero
      have hnone : st.levelStart[0]? = none := by
        rw [Array.getElem?_eq_none_iff]
        omega
      rw [hnone] at hz
      simp at hz
    simp only [newLevel, Array.getElem?_push]
    rw [if_neg]
    · exact h.levelStart_zero
    · exact fun h0 => hs h0.symm
  · simp [newLevel, h.levelStart_size]
  · have h' : st.levelStart.toList.Pairwise (· < ·) := h.levelStart_strict
    have hstrict : SortedList (st.levelStart.push st.trail.size) := by
      rw [SortedList, Array.toList_push, List.pairwise_append]
      refine ⟨h', by simp, ?_⟩
      intro x hx y hy
      simp only [List.mem_singleton] at hy
      subst hy
      have hx' : x ∈ st.levelStart := by simpa using hx
      obtain ⟨i, hi⟩ := Array.mem_iff_getElem?.mp hx'
      obtain ⟨hlt, hei⟩ := Array.getElem?_eq_some_iff.mp hi
      have hix : st.levelStart.getD i 0 = x := by
        simp [Array.getD, hlt, hei]
      have hile : i ≤ st.level := by
        have := h.levelStart_size
        omega
      have hlev : st.level < st.levelStart.size := by
        have := h.levelStart_size
        omega
      have hle := h.levelStart_strict.getD_le hile hlev
      rw [hix] at hle
      omega
    simpa [newLevel] using hstrict
  · intro i hi
    rw [newLevel] at hi
    simp only [Array.size_push] at hi
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | heq
    · rw [newLevel]
      simp only
      rw [Array.getD_push_lt (a := st.levelStart) (i := i) (v := st.trail.size) (d := 0) hlt]
      exact h.levelStart_le_trail i hlt
    · subst heq
      rw [newLevel]
      simp only
      rw [Array.getD_push_eq]
      simp
  · intro i e' he'
    have := h.entry_level i e' he'
    rw [newLevel]
    simp only [Array.size_push]
    omega
  · intro i e' he'
    have hlt := h.entry_level i e' he'
    have hle := h.entry_levelStart_le i e' he'
    rw [newLevel]
    simp only
    rw [Array.getD_push_lt (a := st.levelStart) (i := e'.level) (v := st.trail.size) (d := 0) hlt]
    exact hle
  · intro s
    simpa [newLevel, EngineState.changeList] using h.changeIndex_sorted s
  · intro s p
    simpa [newLevel, EngineState.changeList] using h.changeIndex_mem s p

/-! ## Undo: restored domains

`undoFuel` walks the undone range from its top down, restoring `e.prev` for
the slot of each entry.  The last write to a slot is the one made by its
*lowest* undone entry, which is exactly the domain the slot had before the
target level began.  The next two lemmas state this precisely: if no undone
entry touches `s` the domain is unchanged, and if `pos` is the least undone
position touching `s` the domain becomes `trail[pos].prev`. -/

@[simp] theorem undoStep_trail (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).trail = st.trail := rfl

@[simp] theorem undoStep_level (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).level = st.level := rfl

@[simp] theorem undoStep_levelStart (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).levelStart = st.levelStart := rfl

@[simp] theorem undoStep_reasons (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).reasons = st.reasons := rfl

theorem undoStep_doms_size (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).doms.size = max st.doms.size (e.slot + 1) := by
  show (st.doms.setGrow e.slot e.prev DomC.empty).size = _
  rw [Array.size_setGrow]

theorem undoStep_changeList_self (st : EngineState p T) (e : Entry) (limit : Nat) :
    (undoStep st e limit).changeList e.slot =
      (st.changeList e.slot).filter (fun q => q < limit) := by
  simp [EngineState.changeList, undoStep, dropChangeFrom]

theorem undoStep_changeList_ne (st : EngineState p T) (e : Entry) (limit : Nat)
    {s : Slot} (h : s ≠ e.slot) :
    (undoStep st e limit).changeList s = st.changeList s := by
  simp [EngineState.changeList, undoStep, dropChangeFrom, h]

theorem undoFuel_doms_of_none {st : EngineState p T} {limit f s : Nat} {d : DomC}
    (hsize : limit + f ≤ st.trail.size) (hs : s < st.doms.size)
    (hnone : ∀ q e', limit ≤ q → q < limit + f → st.trail[q]? = some e' → e'.slot ≠ s) :
    (undoFuel st limit f).doms.getD s d = st.doms.getD s d := by
  induction f generalizing st limit with
  | zero => simp [undoFuel]
  | succ f ih =>
      unfold undoFuel
      split
      · rename_i hmiss
        have := Array.getElem?_eq_none_iff.mp hmiss
        omega
      · rename_i e0 he0
        have hsize' : limit + f ≤ (undoStep st e0 limit).trail.size := by
          rw [undoStep_trail]
          omega
        have hs' : s < (undoStep st e0 limit).doms.size := by
          rw [undoStep_doms_size]
          exact Nat.lt_of_lt_of_le hs (Nat.le_max_left _ _)
        have hnone' : ∀ q e', limit ≤ q → q < limit + f →
            (undoStep st e0 limit).trail[q]? = some e' → e'.slot ≠ s := by
          intro q e' hq hqf hqe
          exact hnone q e' hq (by omega) (by simpa [undoStep] using hqe)
        rw [ih (st := undoStep st e0 limit) (limit := limit) hsize' hs' hnone']
        have hne : s ≠ e0.slot := fun h => hnone (limit + f) e0 (by omega) (by omega) he0 h.symm
        simp only [undoStep]
        exact Array.getD_setGrow_other_of_lt _ _ _ _ _ _ hs hne

theorem undoFuel_doms_of_least {st : EngineState p T} {limit f s : Nat} {d : DomC}
    {pos : Nat} {e : Entry} (hsize : limit + f ≤ st.trail.size)
    (hp : limit ≤ pos) (hpf : pos < limit + f)
    (he : st.trail[pos]? = some e) (hslot : e.slot = s)
    (hmin : ∀ q e', limit ≤ q → q < pos → st.trail[q]? = some e' → e'.slot ≠ s) :
    (undoFuel st limit f).doms.getD s d = e.prev := by
  induction f generalizing st limit with
  | zero => exfalso; omega
  | succ f ih =>
      unfold undoFuel
      split
      · rename_i hmiss
        have := Array.getElem?_eq_none_iff.mp hmiss
        omega
      · rename_i e0 he0
        have hsize' : limit + f ≤ (undoStep st e0 limit).trail.size := by
          rw [undoStep_trail]
          omega
        by_cases hpx : pos < limit + f
        · have hmin' : ∀ q e', limit ≤ q → q < pos →
              (undoStep st e0 limit).trail[q]? = some e' → e'.slot ≠ s := by
            intro q e' hq hqp hqe
            exact hmin q e' hq hqp (by simpa [undoStep] using hqe)
          rw [ih (st := undoStep st e0 limit) (limit := limit) hsize' hp hpx
            (by simpa [undoStep] using he) hmin']
        · have hpe : pos = limit + f := by omega
          subst hpe
          have hee : e = e0 := by
            rw [he] at he0
            exact Option.some.inj he0
          subst e0
          have hse : s = e.slot := hslot.symm
          have hs' : s < (undoStep st e limit).doms.size := by
            rw [undoStep_doms_size]
            exact Nat.lt_of_lt_of_le (by rw [hse]; exact Nat.lt_succ_self _) (Nat.le_max_right _ _)
          have hnone' : ∀ q e', limit ≤ q → q < limit + f →
              (undoStep st e limit).trail[q]? = some e' → e'.slot ≠ s := by
            intro q e' hq hqf hqe
            exact hmin q e' hq hqf (by simpa [undoStep] using hqe)
          rw [undoFuel_doms_of_none hsize' hs' hnone']
          simp only [undoStep]
          rw [hse]
          exact Array.getD_setGrow_self _ _ _ _ _

section
open Classical

/-- Undoing a range `[limit, limit + f)` filters a slot's change list to
positions below `limit` exactly when the range contains an entry of that
slot; otherwise the list is untouched.  Positions above the range are not
examined. -/
theorem undoFuel_changeList_aux {st : EngineState p T} (s : Slot) {limit f : Nat}
    (hsize : limit + f ≤ st.trail.size) :
    (undoFuel st limit f).changeList s =
      if _h : ∃ q e, limit ≤ q ∧ q < limit + f ∧ st.trail[q]? = some e ∧ e.slot = s
      then (st.changeList s).filter (fun q => q < limit)
      else st.changeList s := by
  induction f generalizing st limit with
  | zero =>
      have hempty : ¬ ∃ q e, limit ≤ q ∧ q < limit + 0 ∧ st.trail[q]? = some e ∧ e.slot = s := by
        rintro ⟨q, e, hq, hqf, _⟩
        omega
      rw [show (undoFuel st limit 0).changeList s = st.changeList s from rfl]
      rw [dif_neg hempty]
  | succ f ih =>
      unfold undoFuel
      split
      · rename_i hmiss
        have := Array.getElem?_eq_none_iff.mp hmiss
        omega
      · rename_i e0 he0
        have hsize' : limit + f ≤ (undoStep st e0 limit).trail.size := by
          rw [undoStep_trail]
          omega
        rw [ih hsize']
        have hex_iff : (∃ q e, limit ≤ q ∧ q < limit + f ∧
            (undoStep st e0 limit).trail[q]? = some e ∧ e.slot = s) ↔
            (∃ q e, limit ≤ q ∧ q < limit + f ∧ st.trail[q]? = some e ∧ e.slot = s) := by
          simp [undoStep]
        by_cases ht : ∃ q e, limit ≤ q ∧ q < limit + f ∧ st.trail[q]? = some e ∧ e.slot = s
        · have ht' : ∃ q e, limit ≤ q ∧ q < limit + f ∧
              (undoStep st e0 limit).trail[q]? = some e ∧ e.slot = s := hex_iff.mpr ht
          have hbig : ∃ q e, limit ≤ q ∧ q < limit + (f + 1) ∧
              st.trail[q]? = some e ∧ e.slot = s := by
            obtain ⟨q, e, hq, hqf, hqe, hsl⟩ := ht
            exact ⟨q, e, hq, by omega, hqe, hsl⟩
          rw [dif_pos ht', dif_pos hbig]
          by_cases hs : s = e0.slot
          · rw [hs]
            rw [undoStep_changeList_self]
            rw [Array.filter_filter]
            simp [Bool.and_self]
          · rw [undoStep_changeList_ne st e0 limit hs]
        · have ht'_neg : ¬ ∃ q e, limit ≤ q ∧ q < limit + f ∧
              (undoStep st e0 limit).trail[q]? = some e ∧ e.slot = s :=
            fun h => ht (hex_iff.mp h)
          rw [dif_neg ht'_neg]
          by_cases hs : s = e0.slot
          · have hbig : ∃ q e, limit ≤ q ∧ q < limit + (f + 1) ∧
                st.trail[q]? = some e ∧ e.slot = s := by
              exact ⟨limit + f, e0, by omega, by omega, he0, hs.symm⟩
            rw [dif_pos hbig]
            rw [hs]
            rw [undoStep_changeList_self]
          · have hbig_neg : ¬ ∃ q e, limit ≤ q ∧ q < limit + (f + 1) ∧
                st.trail[q]? = some e ∧ e.slot = s := by
              rintro ⟨q, e, hq, hqf, hqe, hsl⟩
              by_cases hqtop : q = limit + f
              · subst hqtop
                rw [he0] at hqe
                injection hqe with heq
                subst heq
                exact hs hsl.symm
              · exact ht ⟨q, e, hq, by omega, hqe, hsl⟩
            rw [dif_neg hbig_neg]
            rw [undoStep_changeList_ne st e0 limit hs]

/-- After undoing the whole trail suffix `[limit, trail.size)` the change list
of every slot is exactly its old list filtered to positions below `limit`.
`hexact` says listed positions are real entries of the slot; it is the
`changeIndex_mem` half of `TrailInv`. -/
theorem undoFuel_changeList {st : EngineState p T} (s : Slot) {limit f : Nat}
    (hsize : limit + f = st.trail.size)
    (hexact : ∀ q, q ∈ st.changeList s → ∃ e, st.trail[q]? = some e ∧ e.slot = s) :
    (undoFuel st limit f).changeList s =
      (st.changeList s).filter (fun q => q < limit) := by
  rw [undoFuel_changeList_aux s (by omega)]
  by_cases ht : ∃ q e, limit ≤ q ∧ q < limit + f ∧ st.trail[q]? = some e ∧ e.slot = s
  · rw [dif_pos ht]
  · rw [dif_neg ht]
    symm
    rw [Array.filter_eq_self]
    intro q hq
    obtain ⟨e, hqe, hsl⟩ := hexact q hq
    obtain ⟨hqsz, _⟩ := Array.getElem?_eq_some_iff.mp hqe
    cases h : decide (q < limit) with
    | true => rfl
    | false =>
        exfalso
        have hqge : ¬ q < limit := by simpa using h
        exact ht ⟨q, e, by omega, by omega, hqe, hsl⟩

/-! ## `backjump` specification -/

theorem backjumpLimit_of_lt {st : EngineState p T} (h : TrailInv st) {k : Nat}
    (hk : k < st.level) :
    st.backjumpLimit k = st.levelStart.getD (k + 1) 0 := by
  have hsize := h.levelStart_size
  have hk1 : k + 1 < st.levelStart.size := by omega
  have hle := h.levelStart_le_trail (k + 1) hk1
  have hgd : st.levelStart.getD (k + 1) st.trail.size = st.levelStart.getD (k + 1) 0 := by
    simp [Array.getD, hk1]
  simp only [EngineState.backjumpLimit, hgd]
  omega

theorem backjumpLimit_of_le {st : EngineState p T} (h : TrailInv st) {k : Nat}
    (hk : st.level ≤ k) : st.backjumpLimit k = st.trail.size := by
  have hsize := h.levelStart_size
  have hnone : st.levelStart[k + 1]? = none := by
    rw [Array.getElem?_eq_none_iff]
    omega
  unfold EngineState.backjumpLimit
  rw [Array.getD_eq_getElem?_getD, hnone]
  simp

/-- Jumping to the current level or above is the identity. -/
theorem backjump_noop {st : EngineState p T} (h : TrailInv st) {k : Nat}
    (hk : st.level ≤ k) : backjump st k = st := by
  have hmin : min k st.level = st.level := by omega
  have hlim : st.backjumpLimit st.level = st.trail.size :=
    backjumpLimit_of_le h (Nat.le_refl _)
  have hun : undoFuel st st.trail.size 0 = st := rfl
  have ht : st.trail.extract 0 st.trail.size = st.trail := Array.extract_size
  have hls : st.levelStart.extract 0 (st.level + 1) = st.levelStart := by
    rw [← h.levelStart_size]
    exact Array.extract_size
  simp [backjump, hmin, hlim, hun, ht, hls]

theorem backjump_level_eq_of_lt {st : EngineState p T} {k : Nat}
    (hk : k < st.level) : (backjump st k).level = k := by
  rw [backjump_level]
  omega

theorem backjump_trail_eq_of_lt {st : EngineState p T} (h : TrailInv st) {k : Nat}
    (hk : k < st.level) :
    (backjump st k).trail = st.trail.extract 0 (st.levelStart.getD (k + 1) 0) := by
  rw [backjump_trail, show min k st.level = k by omega, backjumpLimit_of_lt h hk]

theorem backjump_trail_size_of_lt {st : EngineState p T} (h : TrailInv st) {k : Nat}
    (hk : k < st.level) :
    (backjump st k).trail.size = st.levelStart.getD (k + 1) 0 := by
  rw [backjump_trail_eq_of_lt h hk, Array.size_extract]
  have hsize := h.levelStart_size
  have hle := h.levelStart_le_trail (k + 1) (by omega)
  omega

theorem backjump_levelStart_eq_of_lt {st : EngineState p T} {k : Nat}
    (hk : k < st.level) :
    (backjump st k).levelStart = st.levelStart.extract 0 (k + 1) := by
  rw [backjump_levelStart, show min k st.level = k by omega]

/-- The domain of a slot not touched above the target level is unchanged by
`backjump`. -/
theorem backjump_doms_of_none {st : EngineState p T} (h : TrailInv st) {k s : Nat}
    {d : DomC} (hk : k < st.level) (hs : s < st.doms.size)
    (hnone : ∀ q e', st.levelStart.getD (k + 1) 0 ≤ q → q < st.trail.size →
      st.trail[q]? = some e' → e'.slot ≠ s) :
    (backjump st k).doms.getD s d = st.doms.getD s d := by
  have hlim : st.backjumpLimit (min k st.level) = st.levelStart.getD (k + 1) 0 := by
    rw [show min k st.level = k by omega]
    exact backjumpLimit_of_lt h hk
  have hsz := h.levelStart_size
  have hle := h.levelStart_le_trail (k + 1) (by omega)
  have hsize : st.levelStart.getD (k + 1) 0 +
      (st.trail.size - st.levelStart.getD (k + 1) 0) = st.trail.size := by omega
  have hdoms : (backjump st k).doms =
      (undoFuel st (st.levelStart.getD (k + 1) 0)
        (st.trail.size - st.levelStart.getD (k + 1) 0)).doms := by
    simp [backjump, hlim]
  rw [hdoms]
  exact undoFuel_doms_of_none (Nat.le_of_eq hsize) hs (fun q e' hq hqf hqe =>
    hnone q e' hq (by omega) hqe)

/-- The domain of the least slot-`s` entry above the target level is restored
to that entry's `prev`. -/
theorem backjump_doms_of_least {st : EngineState p T} (h : TrailInv st)
    {k s : Nat} {d : DomC} {pos : Nat} {e : Entry} (hk : k < st.level)
    (hp : st.levelStart.getD (k + 1) 0 ≤ pos) (hpos : pos < st.trail.size)
    (he : st.trail[pos]? = some e) (hslot : e.slot = s)
    (hmin : ∀ q e', st.levelStart.getD (k + 1) 0 ≤ q → q < pos →
      st.trail[q]? = some e' → e'.slot ≠ s) :
    (backjump st k).doms.getD s d = e.prev := by
  have hlim : st.backjumpLimit (min k st.level) = st.levelStart.getD (k + 1) 0 := by
    rw [show min k st.level = k by omega]
    exact backjumpLimit_of_lt h hk
  have hsz := h.levelStart_size
  have hle := h.levelStart_le_trail (k + 1) (by omega)
  have hsize : st.levelStart.getD (k + 1) 0 +
      (st.trail.size - st.levelStart.getD (k + 1) 0) = st.trail.size := by omega
  have hdoms : (backjump st k).doms =
      (undoFuel st (st.levelStart.getD (k + 1) 0)
        (st.trail.size - st.levelStart.getD (k + 1) 0)).doms := by
    simp [backjump, hlim]
  rw [hdoms]
  exact undoFuel_doms_of_least (Nat.le_of_eq hsize) hp (by omega) he hslot hmin

/-- Every per-slot change list is filtered to the positions below the target
level's start. -/
theorem backjump_changeList_eq {st : EngineState p T} (h : TrailInv st) {k : Nat}
    {s : Slot} (hk : k < st.level) :
    (backjump st k).changeList s =
      (st.changeList s).filter (fun q => q < st.levelStart.getD (k + 1) 0) := by
  have hlim : st.backjumpLimit (min k st.level) = st.levelStart.getD (k + 1) 0 := by
    rw [show min k st.level = k by omega]
    exact backjumpLimit_of_lt h hk
  have hsz := h.levelStart_size
  have hle := h.levelStart_le_trail (k + 1) (by omega)
  have hsize : st.levelStart.getD (k + 1) 0 +
      (st.trail.size - st.levelStart.getD (k + 1) 0) = st.trail.size := by omega
  have hci : (backjump st k).changeIndex =
      (undoFuel st (st.levelStart.getD (k + 1) 0)
        (st.trail.size - st.levelStart.getD (k + 1) 0)).changeIndex := by
    simp [backjump, hlim]
  rw [show (backjump st k).changeList s =
      (undoFuel st (st.levelStart.getD (k + 1) 0)
        (st.trail.size - st.levelStart.getD (k + 1) 0)).changeList s by
    simp only [EngineState.changeList, hci]]
  exact undoFuel_changeList s hsize (fun q hq => (h.changeIndex_mem s q).1 hq |>.2)

/-- Exact membership of the post-jump change lists. -/
theorem backjump_changeList_mem {st : EngineState p T} (h : TrailInv st) {k : Nat}
    {s : Slot} {p : Nat} (hk : k < st.level) :
    p ∈ (backjump st k).changeList s ↔
      p < (backjump st k).trail.size ∧
        ∃ e, (backjump st k).trail[p]? = some e ∧ e.slot = s := by
  rw [backjump_changeList_eq h hk, Array.mem_filter]
  constructor
  · rintro ⟨hp, hplt⟩
    obtain ⟨_, e, he, hsl⟩ := (h.changeIndex_mem s p).1 hp
    have hplt' : p < st.levelStart.getD (k + 1) 0 := of_decide_eq_true hplt
    refine ⟨?_, e, ?_, hsl⟩
    · rw [backjump_trail_size_of_lt h hk]
      exact hplt'
    · rw [backjump_trail_eq_of_lt h hk, Array.getElem?_extract]
      have hlt : p < min (st.levelStart.getD (k + 1) 0) st.trail.size - 0 := by
        have hsz := h.levelStart_size
        have := h.levelStart_le_trail (k + 1) (by omega)
        omega
      rw [if_pos hlt]
      simpa using he
  · rintro ⟨hpsz, e, he, hsl⟩
    refine ⟨?_, ?_⟩
    · apply (h.changeIndex_mem s p).2
      refine ⟨?_, e, ?_, hsl⟩
      · rw [backjump_trail_size_of_lt h hk] at hpsz
        have hsz := h.levelStart_size
        exact Nat.lt_of_lt_of_le hpsz (h.levelStart_le_trail (k + 1) (by omega))
      · rw [backjump_trail_eq_of_lt h hk, Array.getElem?_extract] at he
        have hlt : p < min (st.levelStart.getD (k + 1) 0) st.trail.size - 0 := by
          have hsz := h.levelStart_size
          have hle := h.levelStart_le_trail (k + 1) (by omega)
          rw [backjump_trail_size_of_lt h hk] at hpsz
          omega
        rw [if_pos hlt] at he
        simpa using he
    · rw [backjump_trail_size_of_lt h hk] at hpsz
      exact decide_eq_true_eq.mpr hpsz

/-- The shape invariant is preserved by `backjump`. -/
theorem backjump_trailInv {st : EngineState p T} (h : TrailInv st) (k : Nat) :
    TrailInv (backjump st k) := by
  by_cases hk : k < st.level
  · have hsize := h.levelStart_size
    have hk1size : k + 1 < st.levelStart.size := by omega
    have hLle : st.levelStart.getD (k + 1) 0 ≤ st.trail.size :=
      h.levelStart_le_trail (k + 1) (by omega)
    -- Reading the truncated trail.
    have htrail : ∀ {i e}, (st.trail.extract 0 (st.levelStart.getD (k + 1) 0))[i]? = some e →
        i < st.levelStart.getD (k + 1) 0 ∧ st.trail[i]? = some e := by
      intro i e he
      by_cases hlt : i < min (st.levelStart.getD (k + 1) 0) st.trail.size - 0
      · rw [Array.getElem?_extract, if_pos hlt] at he
        exact ⟨by omega, by simpa using he⟩
      · rw [Array.getElem?_extract, if_neg hlt] at he
        exact absurd he (by simp)
    -- Reading the truncated level starts.
    have hlevelStart : ∀ i, i < k + 1 →
        (st.levelStart.extract 0 (k + 1)).getD i 0 = st.levelStart.getD i 0 := by
      intro i hi
      rw [Array.getD_extract]
      · simp
      · omega
    -- No kept entry lies above the target level.
    have hlevel_lt : ∀ i e, st.trail[i]? = some e →
        i < st.levelStart.getD (k + 1) 0 → e.level < k + 1 := by
      intro i e he hiL
      by_cases hlt : e.level < k + 1
      · exact hlt
      · exfalso
        have hge : k + 1 ≤ e.level := by omega
        have hlevsize := h.entry_level i e he
        have hmono := h.levelStart_strict.getD_le hge hlevsize
        have hstart := h.entry_levelStart_le i e he
        omega
    constructor
    · -- `levelStart[0] = 0`
      rw [backjump_levelStart_eq_of_lt hk]
      rw [Array.getElem?_extract]
      have h0 : 0 < min (k + 1) st.levelStart.size - 0 := by omega
      rw [if_pos h0]
      simpa using h.levelStart_zero
    · -- one start per level
      rw [backjump_levelStart_eq_of_lt hk, Array.size_extract, hsize,
        backjump_level_eq_of_lt hk]
      omega
    · -- strictly increasing
      rw [backjump_levelStart_eq_of_lt hk]
      exact SortedList.extract h.levelStart_strict 0 (k + 1)
    · -- starts bounded by the trail
      intro i hi
      rw [backjump_levelStart_eq_of_lt hk] at hi
      rw [Array.size_extract] at hi
      have hi' : i < k + 1 := by omega
      rw [backjump_trail_size_of_lt h hk, backjump_levelStart_eq_of_lt hk,
        hlevelStart i hi']
      exact h.levelStart_strict.getD_le (by omega) hk1size
    · -- entries live on a live level
      intro i e he
      rw [backjump_trail_eq_of_lt h hk] at he
      obtain ⟨hiL, he'⟩ := htrail he
      have hlev := hlevel_lt i e he' hiL
      rw [backjump_levelStart_eq_of_lt hk, Array.size_extract]
      omega
    · -- entries lie at or after their level start
      intro i e he
      rw [backjump_trail_eq_of_lt h hk] at he
      obtain ⟨hiL, he'⟩ := htrail he
      have hlev := hlevel_lt i e he' hiL
      rw [backjump_levelStart_eq_of_lt hk, hlevelStart e.level hlev]
      exact h.entry_levelStart_le i e he'
    · -- sorted change lists
      intro s
      rw [backjump_changeList_eq h hk]
      exact SortedList.filter (h.changeIndex_sorted s)
        (fun q => q < st.levelStart.getD (k + 1) 0)
    · -- exact change-list membership
      intro s p
      exact backjump_changeList_mem h hk
  · have hkge : st.level ≤ k := by omega
    rw [backjump_noop h hkge]
    exact h

/-- Bundled postcondition of `backjump st k` for a live target level: the
trail is the prefix below `levelStart[k+1]`, the level is `k`, `levelStart`
is truncated to `k+1`, the reason store is untouched (R6(a)), every restored
slot gets its pre-level domain by replaying `prev` in reverse, and each
change list contains exactly the positions below the new trail size. -/
theorem backjump_spec {st : EngineState p T} (h : TrailInv st) {k : Nat}
    (hk : k < st.level) :
    (backjump st k).level = k ∧
    (backjump st k).trail = st.trail.extract 0 (st.levelStart.getD (k + 1) 0) ∧
    (backjump st k).levelStart = st.levelStart.extract 0 (k + 1) ∧
    (backjump st k).trail.size = st.levelStart.getD (k + 1) 0 ∧
    (backjump st k).reasons = st.reasons ∧
    (∀ s p, p ∈ (backjump st k).changeList s ↔
      p < (backjump st k).trail.size ∧
        ∃ e, (backjump st k).trail[p]? = some e ∧ e.slot = s) ∧
    (∀ s, (backjump st k).changeList s =
      (st.changeList s).filter (fun q => q < st.levelStart.getD (k + 1) 0)) ∧
    (∀ s (d : DomC), s < st.doms.size →
      (∀ q e, st.levelStart.getD (k + 1) 0 ≤ q → q < st.trail.size →
        st.trail[q]? = some e → e.slot ≠ s) →
      (backjump st k).doms.getD s d = st.doms.getD s d) ∧
    (∀ s pos e (d : DomC), st.levelStart.getD (k + 1) 0 ≤ pos →
      pos < st.trail.size → st.trail[pos]? = some e → e.slot = s →
      (∀ q e', st.levelStart.getD (k + 1) 0 ≤ q → q < pos →
        st.trail[q]? = some e' → e'.slot ≠ s) →
      (backjump st k).doms.getD s d = e.prev) ∧
    TrailInv (backjump st k) := by
  refine ⟨backjump_level_eq_of_lt hk, backjump_trail_eq_of_lt h hk,
    backjump_levelStart_eq_of_lt hk, backjump_trail_size_of_lt h hk,
    backjump_reasons st k, ?_, ?_, ?_, ?_, backjump_trailInv h k⟩
  · intro s p
    exact backjump_changeList_mem h hk
  · intro s
    exact backjump_changeList_eq h hk
  · intro s d hs hnone
    exact backjump_doms_of_none h hk hs hnone
  · intro s pos e d hp hpos he hslot hmin
    exact backjump_doms_of_least h hk hp hpos he hslot hmin

/-! ## `latestEntryOf` specification -/

/-- `PLit`'s derived `BEq` is whole-packed-literal equality. -/
theorem PLit.beq_eq_true_iff (a b : PLit) : (a == b) = true ↔ a = b := by
  cases a with
  | mk ai al =>
  cases b with
  | mk bi bl =>
  have hbeq : (({ idx := ai, lit := al } : PLit) == { idx := bi, lit := bl }) =
      (ai == bi && al == bl) := rfl
  rw [hbeq, Bool.and_eq_true, beq_iff_eq, beq_iff_eq]
  simp [PLit.mk.injEq]

/-- `latestEntryFrom trail l i` finds the greatest position below `i` whose
entry carries exactly `l`.  The equivalence also records maximality: there
is no matching entry between the result and `i`. -/
theorem latestEntryFrom_spec (trail : Array Entry) (l : PLit) :
    ∀ i, i ≤ trail.size →
      ((∀ r, latestEntryFrom trail l i = some r ↔
          r < i ∧ (∃ e, trail[r]? = some e ∧ e.lit = l) ∧
            (∀ j, r < j → j < i → ∀ e, trail[j]? = some e → e.lit ≠ l)) ∧
       (latestEntryFrom trail l i = none ↔
          ∀ r, r < i → ∀ e, trail[r]? = some e → e.lit ≠ l)) := by
  intro i
  induction i with
  | zero =>
      intro hi
      constructor
      · intro r
        constructor
        · intro h
          simp [latestEntryFrom] at h
        · rintro ⟨hr, _⟩
          omega
      · simp [latestEntryFrom]
  | succ i ih =>
      intro hi
      have hi' : i < trail.size := by omega
      cases htr : trail[i]? with
      | none =>
          have hle : trail.size ≤ i := Array.getElem?_eq_none_iff.mp htr
          omega
      | some e =>
          have ih' := ih (by omega)
          by_cases hlit : e.lit == l
          · have heq : e.lit = l := (PLit.beq_eq_true_iff e.lit l).1 hlit
            constructor
            · intro r
              constructor
              · intro h
                simp only [latestEntryFrom, htr] at h
                rw [if_pos hlit] at h
                have hri : i = r := Option.some.inj h
                subst r
                refine ⟨by omega, ⟨e, htr, heq⟩, ?_⟩
                intro j hj1 hj2 e' he'
                omega
              · rintro ⟨hri, hmatch, hlast⟩
                have hri' : r = i := by
                  by_cases hlt : r < i
                  · exfalso
                    exact hlast i hlt (by omega) e htr heq
                  · omega
                subst r
                simp only [latestEntryFrom, htr, if_pos hlit]
            · constructor
              · intro h
                simp only [latestEntryFrom, htr] at h
                rw [if_pos hlit] at h
                exact absurd h (by simp)
              · intro h
                exact absurd heq (h i (by omega) e htr)
          · have hne : e.lit ≠ l := by
              intro heq
              exact hlit ((PLit.beq_eq_true_iff e.lit l).2 heq)
            have hnotmatch : ¬ ∃ e', trail[i]? = some e' ∧ e'.lit = l := by
              rintro ⟨e', he', hlit'⟩
              rw [htr] at he'
              have hsame : e' = e := (Option.some.inj he').symm
              rw [hsame] at hlit'
              exact hne hlit'
            have hL : latestEntryFrom trail l (i + 1) = latestEntryFrom trail l i := by
              simp [latestEntryFrom, htr, hlit]
            constructor
            · intro r
              constructor
              · intro h
                have hsome : latestEntryFrom trail l i = some r := by
                  rw [hL] at h
                  exact h
                obtain ⟨hri, hmatch, hlast⟩ := (ih'.1 r).1 hsome
                refine ⟨by omega, hmatch, ?_⟩
                intro j hrj hji e' he'
                by_cases hje : j = i
                · subst j
                  intro hlit'
                  exact hnotmatch ⟨e', he', hlit'⟩
                · intro hlit'
                  exact hlast j hrj (by omega) e' he' hlit'
              · rintro ⟨hri, hmatch, hlast⟩
                have hlt : r < i := by
                  by_cases hri' : r < i
                  · exact hri'
                  · exfalso
                    have hreq : r = i := by omega
                    subst r
                    exact hnotmatch hmatch
                have hsome : latestEntryFrom trail l i = some r :=
                  (ih'.1 r).2 ⟨hlt, hmatch, fun j hj1 hj2 e' he' =>
                    hlast j hj1 (by omega) e' he'⟩
                rw [hL]
                exact hsome
            · constructor
              · intro h
                have hnone : latestEntryFrom trail l i = none := by
                  rw [hL] at h
                  exact h
                have hnoi := (ih'.2).1 hnone
                intro r hri e' he'
                by_cases hre : r = i
                · subst r
                  intro hlit'
                  exact hnotmatch ⟨e', he', hlit'⟩
                · exact hnoi r (by omega) e' he'
              · intro h
                rw [hL]
                exact (ih'.2).2 (fun r hri e' he' => h r (by omega) e' he')

/-- `latestEntryOf` finds the greatest trail position carrying exactly the
whole packed literal `l` (index and denotation), or `none`. -/
theorem latestEntryOf_spec (st : EngineState p T) (l : PLit) :
    ((∀ r, latestEntryOf st l = some r ↔
        r < st.trail.size ∧ (∃ e, st.trail[r]? = some e ∧ e.lit = l) ∧
          (∀ j, r < j → j < st.trail.size →
            ∀ e, st.trail[j]? = some e → e.lit ≠ l)) ∧
     (latestEntryOf st l = none ↔
        ∀ r, r < st.trail.size → ∀ e, st.trail[r]? = some e → e.lit ≠ l)) := by
  unfold latestEntryOf
  exact latestEntryFrom_spec st.trail l st.trail.size (Nat.le_refl _)

/-! ## Binary-search specification -/

/-- Fuel-free correctness of `bsearchFrom`: either every index in `[lo,hi)`
fails (and the search returns the incoming `best`), or the search returns
some index `m` in `[lo,hi)` where `P` first holds. -/
theorem bsearchFrom_spec {a : Array Nat} {P : Nat → Bool} {lo hi : Nat}
    {best : Option Nat} {fuel : Nat}
    (hmono : ∀ i j, i < j → j < a.size → P (a.getD i 0) = true →
      P (a.getD j 0) = true)
    (hlohi : lo ≤ hi) (hhi : hi ≤ a.size) (hfuel : hi - lo ≤ fuel)
    (hbest : ∀ b, best = some b → hi ≤ b ∧ b < a.size ∧ P (a.getD b 0) = true ∧
        ∀ j, hi ≤ j → j < b → P (a.getD j 0) = false) :
    ((∀ j, lo ≤ j → j < hi → P (a.getD j 0) = false) ∧
      bsearchFrom a P lo hi best fuel = best)
    ∨ (∃ m, lo ≤ m ∧ m < hi ∧ P (a.getD m 0) = true ∧
        (∀ j, lo ≤ j → j < m → P (a.getD j 0) = false) ∧
        bsearchFrom a P lo hi best fuel = some m) := by
  induction fuel generalizing lo hi best with
  | zero =>
      left
      constructor
      · intro j hjlo hjhi
        omega
      · rfl
  | succ fuel ih =>
      simp only [bsearchFrom]
      by_cases hlt : lo < hi
      · rw [if_pos hlt]
        have hmid_lo : lo ≤ (lo + hi) / 2 := by omega
        have hmid_hi : (lo + hi) / 2 < hi := by omega
        have hmid_size : (lo + hi) / 2 < a.size := by omega
        by_cases hp : P (a.getD ((lo + hi) / 2) 0) = true
        · rw [if_pos hp]
          have ih' := ih (lo := lo) (hi := (lo + hi) / 2)
            (best := some ((lo + hi) / 2))
            (by omega) (by omega) (by omega) (by
              intro b hb
              rw [Option.some.injEq] at hb
              subst b
              exact ⟨Nat.le_refl _, hmid_size, hp, by omega⟩)
          rcases ih' with ⟨hall, hres⟩ | ⟨m, hm_lo, hm_hi, hm_p, hm_least, hres⟩
          · right
            exact ⟨(lo + hi) / 2, hmid_lo, hmid_hi, hp, hall, hres⟩
          · right
            exact ⟨m, hm_lo, by omega, hm_p, hm_least, hres⟩
        · rw [if_neg hp]
          have ih' := ih (lo := (lo + hi) / 2 + 1) (hi := hi) (best := best)
            (by omega) hhi (by omega) hbest
          rcases ih' with ⟨hall, hres⟩ | ⟨m, hm_lo, hm_hi, hm_p, hm_least, hres⟩
          · left
            refine ⟨?_, hres⟩
            intro j hjlo hjhi
            by_cases hjm : j ≤ (lo + hi) / 2
            · by_cases hje : j = (lo + hi) / 2
              · rw [hje]
                cases h : P (a.getD ((lo + hi) / 2) 0) with
                | false => rfl
                | true => exact absurd h hp
              · have hjlt : j < (lo + hi) / 2 := by omega
                cases h : P (a.getD j 0) with
                | false => rfl
                | true => exact absurd (hmono j ((lo + hi) / 2) hjlt hmid_size h) hp
            · exact hall j (by omega) hjhi
          · right
            refine ⟨m, by omega, hm_hi, hm_p, ?_, hres⟩
            intro j hjlo hjm
            by_cases hjm' : j ≤ (lo + hi) / 2
            · by_cases hje : j = (lo + hi) / 2
              · rw [hje]
                cases h : P (a.getD ((lo + hi) / 2) 0) with
                | false => rfl
                | true => exact absurd h hp
              · have hjlt : j < (lo + hi) / 2 := by omega
                cases h : P (a.getD j 0) with
                | false => rfl
                | true => exact absurd (hmono j ((lo + hi) / 2) hjlt hmid_size h) hp
            · exact hm_least j (by omega) hjm
      · rw [if_neg hlt]
        left
        constructor
        · intro j hjlo hjhi
          omega
        · rfl

/-! ## `earliestImplying` specification -/

/-- `earliestImplying` returns the minimum qualifying member of the slot's
change index, and returns `none` exactly when no member qualifies.  Under
`FalsifiedMonotone` this is the indexed form of N8's linear `explainLit`
scan. -/
theorem earliestImplying_spec {st : EngineState p T} (h : TrailInv st)
    {s : Slot} {l : Literal} (hmono : FalsifiedMonotone st s l) :
    (∀ r, earliestImplying st s l = some r →
      r ∈ st.changeList s ∧ falsifiedAfter st r l = true ∧
        ∀ q, q ∈ st.changeList s → q < r → falsifiedAfter st q l = false)
    ∧ (earliestImplying st s l = none ↔
      ∀ q, q ∈ st.changeList s → falsifiedAfter st q l = false) := by
  have hspec := bsearchFrom_spec
    (a := st.changeList s) (P := fun pos => falsifiedAfter st pos l)
    (lo := 0) (hi := (st.changeList s).size) (best := none)
    (fuel := (st.changeList s).size)
    hmono (Nat.zero_le _) (Nat.le_refl _) (by omega)
    (by intro b hb; cases hb)
  have hmem_getD : ∀ {q : Nat}, q ∈ st.changeList s →
      ∃ j, j < (st.changeList s).size ∧ (st.changeList s).getD j 0 = q := by
    intro q hq
    obtain ⟨j, hj, heq⟩ := Array.mem_iff_getElem.mp hq
    refine ⟨j, hj, ?_⟩
    rw [show (st.changeList s).getD j 0 = (st.changeList s)[j] by
      simp [Array.getD, hj], heq]
  have hleast : ∀ {m q : Nat}, m < (st.changeList s).size →
      (∀ j, j < m → falsifiedAfter st ((st.changeList s).getD j 0) l = false) →
      q ∈ st.changeList s → q < (st.changeList s).getD m 0 →
      falsifiedAfter st q l = false := by
    intro m q hm hleastq hq hqlt
    obtain ⟨j, hj, hqj⟩ := hmem_getD hq
    have hjlt : j < m := by
      by_cases hjm : j < m
      · exact hjm
      · exfalso
        have hmj : m ≤ j := by omega
        have hle := (h.changeIndex_sorted s).getD_le hmj hj
        rw [hqj] at hle
        omega
    have hf := hleastq j hjlt
    rwa [hqj] at hf
  constructor
  · intro r hr
    rcases hspec with ⟨hall, hres⟩ | ⟨m, hm_lo, hm_hi, hm_p, hm_least, hres⟩
    · simp [earliestImplying, hres] at hr
    · have hmap : earliestImplying st s l = some ((st.changeList s).getD m 0) := by
        simp [earliestImplying, hres]
      have hrm : r = (st.changeList s).getD m 0 := by
        rw [hmap] at hr
        exact (Option.some.inj hr).symm
      subst r
      refine ⟨Array.getD_mem hm_hi, hm_p, ?_⟩
      intro q hq hqlt
      exact hleast hm_hi (fun j hj => hm_least j (Nat.zero_le j) hj) hq hqlt
  · constructor
    · intro hn
      rcases hspec with ⟨hall, hres⟩ | ⟨m, hm_lo, hm_hi, hm_p, hm_least, hres⟩
      · intro q hq
        obtain ⟨j, hj, hqj⟩ := hmem_getD hq
        have hf := hall j (Nat.zero_le j) hj
        rwa [hqj] at hf
      · exfalso
        have hmap : earliestImplying st s l = some ((st.changeList s).getD m 0) := by
          simp [earliestImplying, hres]
        rw [hmap] at hn
        exact absurd hn (Option.some_ne_none _)
    · intro hnone
      rcases hspec with ⟨hall, hres⟩ | ⟨m, hm_lo, hm_hi, hm_p, hm_least, hres⟩
      · simp [earliestImplying, hres]
      · exfalso
        have hf := hnone ((st.changeList s).getD m 0) (Array.getD_mem hm_hi)
        rw [hm_p] at hf
        exact Bool.noConfusion hf

end
end LeanFzn.Engine
