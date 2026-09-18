import LeanFzn
import solver.Fixpoint

/-!
# Reversible executable state (PLAN.md 6.4)

This module implements the first milestone of PLAN 6.4: an
*efficient* solver state that **refines** the functional
list-of-lists domain representation consumed by the propagator
stack (`solver/Propagators.lean`, `solver/Fixpoint.lean`), together
with the representation invariants and refinement theorems the
plan demands.  The scope of this round is deliberately reduced
relative to the full 6.4 vision (the propagation queue and watched
constraints are later work): what is delivered is **sparse-set
domains with a trail** — Sabori's reversible-state core — as a
verified refinement.

## The representation

A `SparseDom` is Sabori's sparse set: an array `vals` of values
whose first `size` entries are *in* the domain (the window) and
whose remaining entries have been swapped out.  The representation
invariant (`SparseDom.Valid`) is `size ≤ vals.size`; the *logical
view* (`sparseToList`) is `vals.toList.take size` — exactly a
`List Value` domain, the shape `getSlot` reads.  Removal is the
classic constant-time swap-and-shrink (`sparseRemove`): the value
at window position `i` is swapped with the last in-window entry
and the window shrinks by one, permuting only the first `size`
entries.  Backtracking is the constant-time `sparseRestore`: reset
the window size on the *same* array (clamped to the array size, so
the function is total).  Narrowing (`sparseNarrow`) is a single
in-place compaction pass (`narrowPass`) that rewrites every window
value passing `keep` to the front in order, in one sweep,
allocation-free.

## What is proved

Every operation carries a theorem connecting it to the logical
view, in the membership form the propagator stack consumes:

* `sparseMem_iff` — **the refinement bridge**: Boolean membership
  in the sparse window agrees with membership in the logical view.
* `sparseRemove_spec` — removal drops exactly the value at the
  removed position and keeps every other window value (under the
  duplicate-freedom of the window); `sparseRemove_prefix` — a
  removal permutes only the first `size` entries.
* `sparseRestore_recovers` / `sparseRestore_recovers_seq` —
  **the trail guarantee**: after any single removal, and after
  any sequence of removals from a common ancestor
  (`SparseRemovalsFrom`), restoring the ancestor's size recovers
  the ancestor's membership set.  (Membership-level, as
  specified: the array stays a permutation of the ancestor's
  window; no array-extensional equality is claimed.)
* `sparseNarrow_spec` — narrowing computes the *filter*: the
  narrowed logical view is exactly `(sparseToList d).filter keep`
  (a list equality — stronger than the membership level asked
  for), the window only shrinks, and the array size is preserved.
  `sparseNarrow_prefix` is the prefix invariance the trail proof
  needs: the compaction pass permutes only the window.
* `revNarrow_mem` / `revNarrow_subset` / `revNarrow_keeps` — the
  state-level narrowing facts, at the `revGet` logical view.
* `revBacktrack_recovers` — **the state-level trail guarantee**:
  if the trail records the narrowings that turned `s0` into `sk`
  (`RevNarrowingsFrom`), then backtracking `sk` along the trail
  restores every slot's logical view to `s0`'s.  The trail is a
  stack (most recent first) folded head-first, so the *oldest*
  entry for each slot is applied last and wins — and that entry
  records the slot's size before its first narrowing, i.e. the
  ancestor's window.
* `revPropPass_refines` — **the propagation-pass refinement**: one
  round-robin pass on the reversible state (materialize the
  logical views, run the verified list-level `propPass`, apply the
  narrowed domains back through `revNarrowFrom`) computes the same
  logical domains as running the pass on lists directly, for every
  propagator list meeting the subset half of the propagation
  contract (`AllNarrowOnly`, implied by `AllPreserve` — the
  `Preserves.subset` field).  The single-step refinement
  (`revNarrowFrom_refines`) is stated separately below it.

## Design notes

* All operations are pure functions; the "mutability" is the O(1)
  swap-and-shrink and the O(1) size-restore, which is where the
  sparse-set representation wins (the narrow itself is a linear
  compaction pass either way).
* Every array-level argument is transported to lists through
  `Array.toList` (via `Array.toList_setIfInBounds` and the
  `getD`-level bridges), so the proofs reason about `List.set`,
  `List.take` and `List.drop` — the same membership-level style as
  the rest of the solver stack.
* The value equality throughout is the checker's structural
  `Value.eqB` (`value_eqB_iff`), the development's established
  pattern; no new `BEq` instances are introduced.

The propagation-queue and watched-constraint halves of 6.4, and the
integration of this state into a full search loop, are later
rounds; `revPropPass` is the (real, proved) connection point to
the existing propagator stack.
-/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution

/-! ## Private list and array bridges

The proofs below work at the `List Value` level throughout; these
helpers transport the array operations (`Array.getD`,
`Array.setIfInBounds`) to `List.getD`/`List.set` and provide the
take/drop/set membership lemmas the refinement theorems use. -/

/-- One more prefix entry of a cons. -/
private theorem take_cons_succ {a : Value} {as : List Value} {j : Nat} :
    (a :: as).take (j + 1) = a :: as.take j := by
  have := List.take_cons (i := j + 1) (a := a) (l := as) (by omega)
  rwa [Nat.add_sub_cancel] at this

/-- An in-bounds `getD` is the indexed element. -/
private theorem list_getD_eq_of_lt {L : List Value} {j : Nat} (h : j < L.length) :
    L.getD j default = L[j] := by
  show (L[j]?.getD default) = L[j]
  rw [List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩, Option.getD_some]

/-- An in-bounds position carries its `getD` value. -/
private theorem getElem?_getD {L : List Value} {j : Nat} (h : j < L.length) :
    L[j]? = some (L.getD j default) := by
  rw [list_getD_eq_of_lt h]
  exact List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩

/-- **Membership in a prefix, by index** (the master membership
characterization; no side conditions — positions past the prefix
length never arise because `getElem?` yields `none` there). -/
private theorem mem_take_iff {L : List Value} :
    ∀ (k : Nat) (v : Value), v ∈ L.take k ↔ ∃ j, j < k ∧ L[j]? = some v := by
  induction L with
  | nil => intro k v; simp
  | cons a as ih =>
      intro k v
      cases k with
      | zero => simp
      | succ k' =>
          simp only [take_cons_succ, List.mem_cons]
          constructor
          · rintro (rfl | h)
            · exact ⟨0, by omega, rfl⟩
            · obtain ⟨j, hj, hget⟩ := (ih k' v).mp h
              exact ⟨j + 1, by omega, hget⟩
          · rintro ⟨j, hj, hget⟩
            cases j with
            | zero =>
                left
                have h0 : (a :: as)[0]? = some a := rfl
                rw [h0] at hget
                exact (Option.some.inj hget).symm
            | succ j' => right; exact (ih k' v).mpr ⟨j', by omega, hget⟩

/-- `getElem?` of `List.set`: setting position `i` replaces
exactly the `i = j` entry when `i` is in bounds. -/
private theorem getElem?_set_iff {L : List Value} {i j : Nat} {a : Value} :
    (L.set i a)[j]? = if i = j then (if i < L.length then some a else none) else L[j]? := by
  have hlen : (L.set i a).length = L.length := List.length_set
  by_cases hij : i = j
  · subst hij
    by_cases hil : i < L.length
    · have h1 : (L.set i a)[i]? = some a := by
        refine List.getElem?_eq_some_iff.mpr ⟨by rw [hlen]; exact hil, ?_⟩
        rw [List.getElem_set (by rw [hlen]; exact hil)]
        exact if_pos rfl
      rw [h1, if_pos rfl, if_pos hil]
    · have h1 : (L.set i a)[i]? = none :=
        List.getElem?_eq_none_iff.mpr (by rw [hlen]; omega)
      rw [h1, if_pos rfl, if_neg (by omega)]
  · by_cases hj : j < (L.set i a).length
    · have h1 : (L.set i a)[j] = L[j] := by
        rw [List.getElem_set hj, if_neg hij]
      have h2 : (L.set i a)[j]? = some L[j] := List.getElem?_eq_some_iff.mpr ⟨hj, h1⟩
      have h3 : L[j]? = some L[j] :=
        List.getElem?_eq_some_iff.mpr ⟨by rw [← hlen]; omega, rfl⟩
      rw [h2, if_neg hij, h3]
    · have h1 : (L.set i a)[j]? = none := List.getElem?_eq_none_iff.mpr (by omega)
      have h2 : L[j]? = none := List.getElem?_eq_none_iff.mpr (by rw [← hlen]; omega)
      rw [h1, if_neg hij, h2]

/-- The window swap at `getElem?` level: swapping the values at two
in-bounds positions `w` and `p` (both read from the original
list). -/
private theorem getElem?_swap {L : List Value} {w p j : Nat} (hw : w < L.length)
    (hp : p < L.length) :
    ((L.set w (L.getD p default)).set p (L.getD w default))[j]? =
      if p = j then some (L.getD w default)
        else if w = j then some (L.getD p default) else L[j]? := by
  have hlen1 : (L.set w (L.getD p default)).length = L.length := List.length_set
  rw [getElem?_set_iff (L := L.set w (L.getD p default)) (i := p) (j := j)
    (a := L.getD w default)]
  by_cases hpj : p = j
  · subst hpj
    rw [if_pos rfl, if_pos (by rw [hlen1]; exact hp), if_pos rfl]
  · rw [if_neg hpj,
      getElem?_set_iff (L := L) (i := w) (j := j) (a := L.getD p default), if_neg hpj]
    by_cases hwj : w = j
    · subst hwj
      rw [if_pos rfl, if_pos hw, if_pos rfl]
    · rw [if_neg hwj, if_neg hwj]

/-- **The window-swap membership lemma**: swapping two in-bounds
positions `w < p` (both reading from the original list) of a
prefix containing both positions preserves the prefix's membership
— the swap permutes the window. -/
private theorem mem_take_swap {L : List Value} {w p k : Nat}
    (hw : w < L.length) (hp : p < L.length) (hwp : w < p) (hwk : w < k) (hpk : p < k)
    (v : Value) :
    v ∈ ((L.set w (L.getD p default)).set p (L.getD w default)).take k ↔
      v ∈ L.take k := by
  rw [mem_take_iff, mem_take_iff]
  have hswap : ∀ j, ((L.set w (L.getD p default)).set p (L.getD w default))[j]? =
      if p = j then some (L.getD w default)
        else if w = j then some (L.getD p default) else L[j]? :=
    fun j => getElem?_swap hw hp
  constructor
  · rintro ⟨j, hj, hget⟩
    rw [hswap j] at hget
    by_cases hpj : p = j
    · subst hpj
      rw [if_pos rfl] at hget
      have hv : L.getD w default = v := Option.some.inj hget
      exact ⟨w, by omega, (getElem?_getD hw).trans (congrArg some hv)⟩
    · rw [if_neg hpj] at hget
      by_cases hwj : w = j
      · subst hwj
        rw [if_pos rfl] at hget
        have hv : L.getD p default = v := Option.some.inj hget
        exact ⟨p, by omega, (getElem?_getD hp).trans (congrArg some hv)⟩
      · rw [if_neg hwj] at hget
        exact ⟨j, by omega, hget⟩
  · rintro ⟨j, hj, hget⟩
    by_cases hpj : p = j
    · subst hpj
      have hvp : L.getD p default = v := by
        obtain ⟨_, hpv⟩ := List.getElem?_eq_some_iff.mp hget
        exact (list_getD_eq_of_lt hp).trans hpv
      refine ⟨w, by omega, ?_⟩
      rw [hswap w, if_neg (by omega : ¬ p = w), if_pos rfl]
      exact congrArg some hvp
    · by_cases hwj : w = j
      · subst hwj
        have hvw : L.getD w default = v := by
          obtain ⟨_, hwv⟩ := List.getElem?_eq_some_iff.mp hget
          exact (list_getD_eq_of_lt hw).trans hwv
        refine ⟨p, by omega, ?_⟩
        rw [hswap p, if_pos rfl]
        exact congrArg some hvw
      · refine ⟨j, by omega, ?_⟩
        rw [hswap j, if_neg (fun hc => hpj hc), if_neg (fun hc => hwj hc)]
        exact hget

/-- Duplicate-freedom of a prefix is index-injectivity of its
positions (the prefix must fit the list). -/
private theorem nodup_take_inj {L : List Value} {k : Nat} (hk : k ≤ L.length)
    (hnd : (L.take k).Nodup) {a b : Nat} (ha : a < k) (hb : b < k)
    (h : L.getD a default = L.getD b default) : a = b := by
  by_cases hab : a = b
  · exact hab
  · exfalso
    have hla : a < (L.take k).length := by rw [List.length_take]; omega
    have hlb : b < (L.take k).length := by rw [List.length_take]; omega
    have hpa : (L.take k)[a]? = some (L.getD a default) := by
      rw [List.getElem?_take, if_pos ha]
      exact List.getElem?_eq_some_iff.mpr ⟨by omega, by
        rw [list_getD_eq_of_lt (by omega)]⟩
    have hpb : (L.take k)[b]? = some (L.getD b default) := by
      rw [List.getElem?_take, if_pos hb]
      exact List.getElem?_eq_some_iff.mpr ⟨by omega, by
        rw [list_getD_eq_of_lt (by omega)]⟩
    exact hab (List.getElem?_inj hla hnd |>.mp (by rw [hpa, hpb, h]))

/-- The tail of a list, by position: dropping to an in-bounds
position exposes that position's value as the head. -/
private theorem drop_eq_getD_cons {L : List Value} :
    ∀ (p : Nat) (h : p < L.length), L.drop p = (L.getD p default) :: L.drop (p + 1) := by
  induction L with
  | nil => intro p h; exact absurd h (by simp)
  | cons a as ih =>
      intro p h
      cases p with
      | zero => simp
      | succ p' =>
          show (a :: as).drop (p' + 1) = _
          rw [List.drop_succ_cons, ih p' (by simp only [List.length_cons] at h; omega)]
          simp

/-- One more prefix entry is the value at the prefix boundary. -/
private theorem take_succ_getD {L : List Value} :
    ∀ (k : Nat) (h : k < L.length), L.take (k + 1) = L.take k ++ [L.getD k default] := by
  induction L with
  | nil => intro k h; exact absurd h (by simp)
  | cons a as ih =>
      intro k h
      cases k with
      | zero => simp
      | succ k' =>
          show (a :: as).take (k' + 1 + 1) = (a :: as).take (k' + 1) ++ [(a :: as).getD (k' + 1) default]
          rw [take_cons_succ, take_cons_succ, ih k' (by simp only [List.length_cons] at h; omega)]
          simp

/-- Setting a position at or beyond a prefix leaves the prefix
alone. -/
private theorem take_set_ge {L : List Value} :
    ∀ (m p : Nat) (y : Value) (h : m ≤ p), (L.set p y).take m = L.take m := by
  intro m p
  induction L generalizing m p with
  | nil => intro y h; cases m <;> rfl
  | cons x xs ih =>
      intro y h
      cases m with
      | zero => rfl
      | succ m' =>
          cases p with
          | zero => exact absurd h (by omega)
          | succ p' =>
              show (x :: xs.set p' y).take (m' + 1) = (x :: xs).take (m' + 1)
              rw [take_cons_succ, take_cons_succ]
              exact congrArg (fun t => x :: t) (ih m' p' y (by omega))

/-- Setting a position below the boundary extends the prefix with
the new value. -/
private theorem take_set_succ {L : List Value} :
    ∀ (w : Nat) (x : Value) (hw : w < L.length), (L.set w x).take (w + 1) = L.take w ++ [x] := by
  induction L with
  | nil => intro w x hw; exact absurd hw (by simp)
  | cons a as ih =>
      intro w x hw
      cases w with
      | zero => rfl
      | succ w' =>
          show (a :: as.set w' x).take (w' + 1 + 1) = (a :: as).take (w' + 1) ++ [x]
          rw [take_cons_succ, take_cons_succ, ih w' x (by simp only [List.length_cons] at hw; omega)]
          simp

/-- Setting a position below the drop point leaves the tail alone. -/
private theorem drop_set_of_lt {L : List Value} :
    ∀ (k i : Nat) (a : Value) (h : i < k), (L.set i a).drop k = L.drop k := by
  intro k i
  induction L generalizing k i with
  | nil => intro a h; cases k <;> rfl
  | cons x xs ih =>
      intro a h
      cases k with
      | zero => exact absurd h (by omega)
      | succ k' =>
          cases i with
          | zero => rfl
          | succ i' =>
              show (x :: xs.set i' a).drop (k' + 1) = (x :: xs).drop (k' + 1)
              rw [List.drop_succ_cons, List.drop_succ_cons]
              exact ih k' i' a (by omega)
/-- Array `getD` agrees with list `getD` on the transported list. -/
private theorem arrayToList_getD {α : Type} [Inhabited α] (A : Array α) (j : Nat) :
    A.toList.getD j default = A.getD j default := by
  show (A.toList[j]?.getD default) = (if h : j < A.size then A[j] else default)
  rw [Array.getElem?_toList]
  by_cases h : j < A.size
  · rw [dif_pos h, Array.getElem?_eq_some_iff.mpr ⟨h, rfl⟩, Option.getD_some]
  · rw [dif_neg h, Array.getElem?_eq_none_iff.mpr (by omega), Option.getD_none]

/-- Array `getD` past the end is the default. -/
private theorem array_getD_of_ge {α : Type} [Inhabited α] (A : Array α) {j : Nat}
    (h : A.size ≤ j) :
    A.getD j default = default := by
  show (if h : j < A.size then A[j] else default) = default
  rw [dif_neg (by omega)]

/-- `Array.setIfInBounds` at `getD` level. -/
private theorem getD_setIfInBounds {α : Type} [Inhabited α] (A : Array α) (i j : Nat)
    (x : α) :
    (A.setIfInBounds i x).getD j default =
      if i = j ∧ i < A.size then x else A.getD j default := by
  by_cases hij : i = j
  · subst hij
    by_cases hlt : i < A.size
    · have h1 : (A.setIfInBounds i x).getD i default = x := by
        show (if h : i < (A.setIfInBounds i x).size then (A.setIfInBounds i x)[i] else default) = x
        rw [dif_pos (by rw [Array.size_setIfInBounds]; exact hlt),
          Array.getElem_setIfInBounds (xs := A) (i := i) (a := x) (hj := hlt),
          if_pos rfl]
      rw [h1, if_pos ⟨rfl, hlt⟩]
    · have h1 : (A.setIfInBounds i x).getD i default = A.getD i default := by
        show (if h : i < (A.setIfInBounds i x).size then (A.setIfInBounds i x)[i] else default) = _
        rw [dif_neg (by rw [Array.size_setIfInBounds]; omega)]
        show default = (A.getD i default)
        have h2 : A.getD i default = default := by
          show (if h : i < A.size then A[i] else default) = default
          rw [dif_neg (by omega)]
        rw [h2]
      rw [h1, if_neg (fun hc => hlt hc.2)]
  · by_cases hjlt : j < A.size
    · have h1 : (A.setIfInBounds i x).getD j default = A.getD j default := by
        show (if h : j < (A.setIfInBounds i x).size then (A.setIfInBounds i x)[j] else default) = _
        rw [dif_pos (by rw [Array.size_setIfInBounds]; exact hjlt),
          Array.getElem_setIfInBounds (xs := A) (i := i) (a := x) (hj := hjlt),
          if_neg hij]
        show A[j] = (A.getD j default)
        have h2 : A.getD j default = A[j] := by
          show (if h : j < A.size then A[j] else default) = A[j]
          rw [dif_pos hjlt]
        rw [h2]
      rw [h1, if_neg (fun hc => hij hc.1)]
    · have h1 : (A.setIfInBounds i x).getD j default = A.getD j default := by
        show (if h : j < (A.setIfInBounds i x).size then (A.setIfInBounds i x)[j] else default) = _
        rw [dif_neg (by rw [Array.size_setIfInBounds]; omega)]
        show default = (A.getD j default)
        have h2 : A.getD j default = default := by
          show (if h : j < A.size then A[j] else default) = default
          rw [dif_neg (by omega)]
        rw [h2]
      rw [h1, if_neg (fun hc => hij hc.1)]

/-! ## Sparse-set domains -/

/-- A sparse-set domain: the first `size` entries of `vals` are the
values *in* the domain; the entries past `size` have been swapped
out.  Sabori's reversible-domain representation. -/
structure SparseDom where
  /-- The value store; its first `size` entries are the domain. -/
  vals : Array Value
  /-- The number of leading `vals` entries that are in the domain. -/
  size : Nat
  deriving Repr, Inhabited

/-- The representation invariant: the window fits the array. -/
def SparseDom.Valid (d : SparseDom) : Prop := d.size ≤ d.vals.size

/-- The logical view of a sparse domain: the list of values in the
window — exactly the `List Value` domain the propagator stack
consumes. -/
def sparseToList (d : SparseDom) : List Value := d.vals.toList.take d.size

/-- The window length is the window size (under the invariant). -/
theorem sparseToList_length {d : SparseDom} (hd : d.Valid) :
    (sparseToList d).length = d.size := by
  rw [sparseToList, List.length_take]
  have hL : d.vals.toList.length = d.vals.size := by simp
  have hle : d.size ≤ d.vals.toList.length := by rw [hL]; exact hd
  omega

/-- Build a sparse domain from a list (the window is the whole
array, in order). -/
def sparseOfList (l : List Value) : SparseDom := ⟨l.toArray, l.length⟩

/-- The logical view of a list-built domain is the list. -/
theorem sparseToList_sparseOfList (l : List Value) :
    sparseToList (sparseOfList l) = l := by
  show (l.toArray.toList.take l.length) = l
  rw [List.take_of_length_le (by simp : l.length ≤ l.toArray.toList.length)]

/-- List-built domains satisfy the representation invariant. -/
theorem sparseOfList_valid (l : List Value) : (sparseOfList l).Valid := by
  show l.length ≤ l.toArray.size
  simp

/-- The membership scan of the sparse window: examines the first
`size` entries of the array, back to front (no allocation). -/
private def sparseMemGo (A : Array Value) : Nat → Value → Bool
  | 0, _ => false
  | n + 1, v => (A.getD n default).eqB v || sparseMemGo A n v

/-- Membership in the sparse window. -/
def sparseMem (d : SparseDom) (v : Value) : Bool := sparseMemGo d.vals d.size v

/-- The scan decides membership by index. -/
private theorem sparseMemGo_iff (A : Array Value) :
    ∀ (n : Nat) (v : Value),
      sparseMemGo A n v = true ↔ ∃ i, i < n ∧ (A.getD i default).eqB v = true := by
  intro n
  induction n with
  | zero => intro v; simp [sparseMemGo]
  | succ n ih =>
      intro v
      simp only [sparseMemGo, Bool.or_eq_true]
      constructor
      · rintro (h | h)
        · exact ⟨n, by omega, h⟩
        · obtain ⟨i, hi, hget⟩ := ih v |>.mp h
          exact ⟨i, by omega, hget⟩
      · rintro ⟨i, hi, hget⟩
        by_cases hin : i = n
        · subst hin; exact Or.inl hget
        · exact Or.inr ((ih v).mpr ⟨i, by omega, hget⟩)

/-- **The refinement bridge**: Boolean membership in the sparse
window agrees with membership in the logical view (the
representation invariant makes the scan reach only real window
entries). -/
theorem sparseMem_iff {d : SparseDom} (hd : d.Valid) {v : Value} :
    sparseMem d v = true ↔ v ∈ sparseToList d := by
  have hL : d.vals.toList.length = d.vals.size := by simp
  have hd' : d.size ≤ d.vals.size := hd
  rw [sparseToList, mem_take_iff, sparseMem, sparseMemGo_iff]
  constructor
  · rintro ⟨j, hj, hget⟩
    refine ⟨j, hj, ?_⟩
    have hjl : j < d.vals.toList.length := by omega
    have harr : d.vals.getD j default = d.vals.toList.getD j default :=
      (arrayToList_getD d.vals j).symm
    show d.vals.toList[j]? = some v
    have hval : d.vals.toList.getD j default = v := by
      rw [← harr]
      exact value_eqB_iff.mp hget
    have hidx : d.vals.toList[j] = d.vals.toList.getD j default :=
      (list_getD_eq_of_lt hjl).symm
    have hsome : d.vals.toList[j]? = some d.vals.toList[j] :=
      List.getElem?_eq_some_iff.mpr ⟨hjl, rfl⟩
    rw [hsome, hidx, hval]
  · rintro ⟨j, hj, hget⟩
    refine ⟨j, hj, ?_⟩
    have hjl : j < d.vals.toList.length := by omega
    have harr : d.vals.getD j default = d.vals.toList.getD j default :=
      (arrayToList_getD d.vals j).symm
    show (d.vals.getD j default).eqB v = true
    have hval : d.vals.toList.getD j default = v := by
      obtain ⟨hlen, hjj⟩ := List.getElem?_eq_some_iff.mp hget
      rw [list_getD_eq_of_lt hlen, hjj]
    rw [harr, hval]
    exact value_eqB_iff.mpr rfl

/-! ## Removal: constant-time swap-and-shrink -/

/-- Remove the window value at position `i`: swap it with the last
in-window entry and shrink the window by one.  O(1); positions at
or past the window are no-ops. -/
def sparseRemove (d : SparseDom) (i : Nat) : SparseDom :=
  if i < d.size then
    ⟨(d.vals.setIfInBounds i (d.vals.getD (d.size - 1) default)).setIfInBounds (d.size - 1)
      (d.vals.getD i default), d.size - 1⟩
  else d

/-- Removal preserves the array and shrinks the window by one. -/
theorem sparseRemove_size {d : SparseDom} {i : Nat} (hi : i < d.size) :
    (sparseRemove d i).size + 1 = d.size ∧ (sparseRemove d i).vals.size = d.vals.size := by
  rw [sparseRemove, if_pos hi]
  simp only [SparseDom.size, SparseDom.vals]
  rw [Array.size_setIfInBounds, Array.size_setIfInBounds]
  omega

/-- Removal preserves the representation invariant. -/
theorem sparseRemove_valid {d : SparseDom} (hd : d.Valid) (i : Nat) :
    (sparseRemove d i).Valid := by
  have hd' : d.size ≤ d.vals.size := hd
  by_cases hi : i < d.size
  · rw [sparseRemove, if_pos hi]
    show d.size - 1 ≤ _
    rw [Array.size_setIfInBounds, Array.size_setIfInBounds]
    omega
  · rw [sparseRemove, if_neg hi]; exact hd

/-- **Prefix invariance of removal**: a removal permutes only the
first `size` entries, so membership in every prefix of at least
that length is preserved — the fact that makes size-restoring
backtrack recover the ancestor's window. -/
theorem sparseRemove_prefix {d : SparseDom} (hd : d.Valid) (i : Nat) {k : Nat}
    (hk : d.size ≤ k) (v : Value) :
    v ∈ (sparseRemove d i).vals.toList.take k ↔ v ∈ d.vals.toList.take k := by
  have hd' : d.size ≤ d.vals.size := hd
  by_cases hi : i < d.size
  · have hLL : d.vals.toList.length = d.vals.size := by simp
    have h1 : (sparseRemove d i).vals.toList =
        (d.vals.toList.set i (d.vals.toList.getD (d.size - 1) default)).set
          (d.size - 1) (d.vals.toList.getD i default) := by
      rw [sparseRemove, if_pos hi]
      simp only [SparseDom.vals, Array.toList_setIfInBounds, Array.toList_setIfInBounds,
        ← arrayToList_getD, ← arrayToList_getD]
    by_cases hieq : i = d.size - 1
    · -- degenerate swap: both writes hit the same position, final value
      -- is the original one, so the array is unchanged
      rw [h1, hieq]
      -- both writes hit the same position with the position's own value,
      -- so the resulting array is the original
      have hlen : d.size - 1 < d.vals.toList.length := by omega
      have harrunchanged : (d.vals.toList.set (d.size - 1)
            (d.vals.toList.getD (d.size - 1) default)).set (d.size - 1)
          (d.vals.toList.getD (d.size - 1) default) = d.vals.toList := by
        apply List.ext_getElem
        · rw [List.length_set, List.length_set]
        · intro j h1' h2'
          rw [List.getElem_set, List.getElem_set]
          by_cases hjj : d.size - 1 = j
          · subst hjj
            rw [if_pos rfl]
            exact list_getD_eq_of_lt hlen
          · rw [if_neg (by omega), if_neg (by omega)]
      rw [harrunchanged]
    · -- general swap: i < d.size - 1, so the lemma's w < p holds
      have hilt : i < d.size - 1 := by omega
      rw [h1]
      exact mem_take_swap (by omega) (by omega) hilt (by omega) (by omega) v
  · rw [sparseRemove, if_neg hi]

/-- **The removal spec**: under the representation invariant and
duplicate-freedom of the window, removing position `i` drops
exactly the value at that position and keeps every other window
value. -/
theorem sparseRemove_spec {d : SparseDom} (hd : d.Valid) (hnd : (sparseToList d).Nodup)
    {i : Nat} (hi : i < d.size) :
    (sparseRemove d i).Valid ∧ (sparseRemove d i).size + 1 = d.size ∧
    ∀ v, sparseMem (sparseRemove d i) v = true ↔
      sparseMem d v = true ∧ v ≠ d.vals.getD i default := by
  obtain ⟨hsz, hvsz⟩ := sparseRemove_size hi
  have hd' : d.size ≤ d.vals.size := hd
  refine ⟨sparseRemove_valid hd i, hsz, ?_⟩
  have hLL : d.vals.toList.length = d.vals.size := by simp
  have hlend : d.size ≤ d.vals.toList.length := by rw [hLL]; exact hd
  have hli : d.size - 1 < d.vals.toList.length := by omega
  have hwi : i < d.vals.toList.length := by omega
  have hinj : ∀ a b, a < d.size → b < d.size →
      d.vals.toList.getD a default = d.vals.toList.getD b default → a = b :=
    fun a b ha hb h => nodup_take_inj hlend hnd ha hb h
  -- the swap, read at positions below size - 1
  have hsw : ∀ j, j < d.size - 1 →
      ((d.vals.toList.set i (d.vals.toList.getD (d.size - 1) default)).set
        (d.size - 1) (d.vals.toList.getD i default))[j]? =
        if i = j then some (d.vals.toList.getD (d.size - 1) default)
          else d.vals.toList[j]? := by
    intro j hj
    rw [getElem?_swap (L := d.vals.toList) (w := i) (p := d.size - 1) hwi hli,
      if_neg (by omega)]
  -- membership, by index, in old and new windows
  have hold : ∀ (v : Value), sparseMem d v = true ↔
      ∃ j, j < d.size ∧ d.vals.toList[j]? = some v := by
    intro v
    rw [sparseMem_iff hd, sparseToList, mem_take_iff]
  -- membership in the new window, by index on the swapped list
  have hnewmem : ∀ (v : Value),
      sparseMem (sparseRemove d i) v = true ↔
        ∃ j, j < d.size - 1 ∧
          ((d.vals.toList.set i (d.vals.toList.getD (d.size - 1) default)).set
            (d.size - 1) (d.vals.toList.getD i default))[j]? = some v := by
    intro v
    rw [sparseMem_iff (sparseRemove_valid hd i), sparseToList, sparseRemove, if_pos hi]
    show v ∈ ((d.vals.setIfInBounds i (d.vals.getD (d.size - 1) default)).setIfInBounds
        (d.size - 1) (d.vals.getD i default)).toList.take (d.size - 1) ↔ _
    rw [Array.toList_setIfInBounds, Array.toList_setIfInBounds, ← arrayToList_getD,
      ← arrayToList_getD, mem_take_iff]
  -- the removed value, by index
  have hremoved : d.vals.getD i default = d.vals.toList.getD i default :=
    (arrayToList_getD d.vals i).symm
  intro v
  rw [hnewmem v, hold v]
  constructor
  · rintro ⟨j, hj, hget⟩
    rw [hsw j hj] at hget
    by_cases hij : i = j
    · -- the value sits at the removed position in the swapped window: it is
      -- the old LAST value, an old-window member distinct from the removed
      rw [hij, if_pos rfl] at hget
      have hv : d.vals.toList.getD (d.size - 1) default = v := Option.some.inj hget
      refine ⟨⟨d.size - 1, by omega, ?_⟩, ?_⟩
      · rw [getElem?_getD hli]
        exact congrArg some hv
      · intro hcon
        have hvali : d.vals.toList.getD i default = v := (hremoved ▸ hcon).symm
        have : i = d.size - 1 := hinj i (d.size - 1) hi (by omega)
          (hvali.trans hv.symm)
        omega
    · -- a surviving position: in the old window, distinct from the removed
      rw [if_neg hij] at hget
      refine ⟨⟨j, by omega, hget⟩, ?_⟩
      intro hcon
      -- v is at old position j and (via hcon) at position i: nodup forces
      -- j = i, contradicting the case hypothesis
      have hvalj : d.vals.toList.getD j default = v :=
        (list_getD_eq_of_lt (by omega)).trans (List.getElem?_eq_some_iff.mp hget).2
      have hvali : d.vals.toList.getD i default = v := (hremoved ▸ hcon).symm
      exact hij (hinj j i (by omega) hi (hvalj.trans hvali.symm)).symm
  · -- an old-window value distinct from the removed one survives
    rintro ⟨⟨j, hj, hget⟩, hne⟩
    by_cases hjlast : j = d.size - 1
    · -- the value was the LAST in-window value: the swap moved it to the
      -- removed position
      subst hjlast
      by_cases hiseq : i = d.size - 1
      · -- self-swap: the value was at the removed position itself —
        -- excluded by hne
        exfalso
        apply hne
        have hv : d.vals.toList.getD i default = v := by
          rw [hiseq]
          rw [list_getD_eq_of_lt hli]
          exact (List.getElem?_eq_some_iff.mp hget).2
        rw [hremoved]
        exact hv.symm
      · -- the swap moved the old LAST value (v) into position i
        have hilt : i < d.size - 1 := by omega
        refine ⟨i, by omega, ?_⟩
        rw [hsw i hilt, if_pos rfl]
        have hv : d.vals.toList.getD (d.size - 1) default = v :=
          (list_getD_eq_of_lt hli).trans (List.getElem?_eq_some_iff.mp hget).2
        exact congrArg some hv
    · -- the value stays at its own position (the removed position is
      -- excluded by hne)
      refine ⟨j, by omega, ?_⟩
      rw [hsw j (by omega)]
      have hne' : i ≠ j := by
        intro hij
        apply hne
        have hvalj : d.vals.toList.getD j default = v :=
          (list_getD_eq_of_lt (by omega)).trans (List.getElem?_eq_some_iff.mp hget).2
        exact (hremoved.trans (hij ▸ hvalj)).symm
      rw [if_neg hne']
      exact hget

/-! ## Restore: constant-time window reset -/

/-- Restore a previously saved window size on the same array — the
trail mechanism's primitive.  Restoring can grow the window (that
is the point: backtracking reveals swapped-out values); a size
past the array end is clamped to the array size, so the function
is total. -/
def sparseRestore (d : SparseDom) (sz : Nat) : SparseDom :=
  ⟨d.vals, min sz d.vals.size⟩

/-- Restoring always yields a valid domain. -/
theorem sparseRestore_valid (d : SparseDom) (sz : Nat) :
    (sparseRestore d sz).Valid :=
  Nat.min_le_right _ _

/-- Restoring never touches the array. -/
theorem sparseRestore_vals (d : SparseDom) (sz : Nat) :
    (sparseRestore d sz).vals = d.vals := rfl

/-- Restoring twice is the last restore (the size is overwritten,
not composed). -/
theorem sparseRestore_comp (d : SparseDom) (p q : Nat) :
    sparseRestore (sparseRestore d p) q = sparseRestore d q := rfl

/-- **The trail guarantee, single removal**: restoring the
ancestor's size after any single removal recovers the ancestor's
membership set. -/
theorem sparseRestore_recovers {d : SparseDom} (hd : d.Valid) (i : Nat) (v : Value) :
    sparseMem (sparseRestore (sparseRemove d i) d.size) v = sparseMem d v := by
  have hd' : (sparseRestore (sparseRemove d i) d.size).Valid :=
    sparseRestore_valid _ _
  have hL : sparseMem (sparseRestore (sparseRemove d i) d.size) v = true ↔
      v ∈ (sparseRestore (sparseRemove d i) d.size).vals.toList.take
        (sparseRestore (sparseRemove d i) d.size).size := sparseMem_iff hd'
  have hR : sparseMem d v = true ↔ v ∈ sparseToList d := sparseMem_iff hd
  have hmem : v ∈ (sparseRestore (sparseRemove d i) d.size).vals.toList.take
      (sparseRestore (sparseRemove d i) d.size).size ↔ v ∈ sparseToList d := by
    rw [show (sparseRestore (sparseRemove d i) d.size).size =
        min d.size (sparseRemove d i).vals.size from rfl,
      show min d.size (sparseRemove d i).vals.size = d.size from
        Nat.min_eq_left (by
          have hvsz : (sparseRemove d i).vals.size = d.vals.size := by
            by_cases hilt : i < d.size
            · exact (sparseRemove_size hilt).2
            · rw [sparseRemove, if_neg hilt]
          rw [hvsz]
          exact hd)]
    exact sparseRemove_prefix hd i (Nat.le_refl d.size) v
  cases hl : sparseMem (sparseRestore (sparseRemove d i) d.size) v with
  | true =>
      have hmem' : v ∈ (sparseRestore (sparseRemove d i) d.size).vals.toList.take
          (sparseRestore (sparseRemove d i) d.size).size := hL.mp hl
      rw [show sparseMem d v = true from hR.mpr (hmem.mp hmem')]
  | false =>
      cases hr : sparseMem d v with
      | true =>
          exfalso
          exact absurd (hL.mpr (hmem.mpr (hR.mp hr))) (by rw [hl]; simp)
      | false => rfl

/-- Removal chains: `d2` is reachable from `d1` by a sequence of
window removals. -/
inductive SparseRemovalsFrom : SparseDom → SparseDom → Prop
  /-- The empty sequence. -/
  | refl (d : SparseDom) : SparseRemovalsFrom d d
  /-- One more removal. -/
  | step {d1 d2 d3 : SparseDom} {i : Nat}
      (h : SparseRemovalsFrom d1 d2) (hi : i < d2.size)
      (heq : d3 = sparseRemove d2 i) : SparseRemovalsFrom d1 d3

/-- Removals only shrink windows. -/
theorem SparseRemovalsFrom.size_le {d1 d2 : SparseDom} (h : SparseRemovalsFrom d1 d2) :
    d2.size ≤ d1.size := by
  induction h with
  | refl => exact Nat.le_refl _
  | @step d2' d3' i' h' hsize heq' ih =>
      subst heq'
      by_cases hlt : i' < d2'.size
      · have := (sparseRemove_size hlt).1; omega
      · exact absurd hsize hlt

/-- Removals preserve the representation invariant. -/
theorem SparseRemovalsFrom.valid {d1 d2 : SparseDom} (h : SparseRemovalsFrom d1 d2)
    (hd1 : d1.Valid) : d2.Valid := by
  induction h with
  | refl => exact hd1
  | @step d2' d3' i' h' hsize heq' ih => subst heq'; exact sparseRemove_valid ih i' 

/-- Removals preserve the array size. -/
theorem SparseRemovalsFrom.vals_size {d1 d2 : SparseDom} (h : SparseRemovalsFrom d1 d2) :
    d2.vals.size = d1.vals.size := by
  induction h with
  | refl => rfl
  | @step d2' d3' i' h' hsize heq' ih =>
      subst heq'
      by_cases hlt : i' < d2'.size
      · rw [(sparseRemove_size hlt).2]; exact ih
      · simp only [sparseRemove, if_neg hlt]; exact ih

/-- **Prefix invariance of removal chains**: a sequence of removals
from a common ancestor permutes only within the shrinking windows,
so membership in every prefix at least the ancestor's window is
preserved throughout. -/
theorem SparseRemovalsFrom.prefix {d0 dk : SparseDom} (h : SparseRemovalsFrom d0 dk)
    (hd0 : d0.Valid) {k : Nat} (hk : d0.size ≤ k) (v : Value) :
    v ∈ dk.vals.toList.take k ↔ v ∈ d0.vals.toList.take k := by
  induction h with
  | refl => rfl
  | @step d2' d3' i' h' hsize heq' ih =>
      subst heq'
      rw [sparseRemove_prefix (SparseRemovalsFrom.valid h' hd0) i'
        (Nat.le_trans (SparseRemovalsFrom.size_le h') hk) v]
      exact ih

/-- **The trail guarantee, removal sequences**: after any sequence
of removals from a common ancestor, restoring the ancestor's size
recovers the ancestor's membership set.  This is the membership
specification of backtracking by size restoration; the array
itself stays a permutation of the ancestor's window, so no
array-extensional equality holds (nor is it needed). -/
theorem sparseRestore_recovers_seq {d0 dk : SparseDom} (h : SparseRemovalsFrom d0 dk)
    (hd0 : d0.Valid) (v : Value) :
    sparseMem (sparseRestore dk d0.size) v = sparseMem d0 v := by
  have hfit : d0.size ≤ dk.vals.size := by
    rw [h.vals_size]; exact hd0
  have hd' : (sparseRestore dk d0.size).Valid := sparseRestore_valid _ _
  have hL : sparseMem (sparseRestore dk d0.size) v = true ↔
      v ∈ (sparseRestore dk d0.size).vals.toList.take
        (sparseRestore dk d0.size).size := sparseMem_iff hd'
  have hR : sparseMem d0 v = true ↔ v ∈ sparseToList d0 := sparseMem_iff hd0
  have hmem : v ∈ (sparseRestore dk d0.size).vals.toList.take
      (sparseRestore dk d0.size).size ↔ v ∈ sparseToList d0 := by
    rw [show (sparseRestore dk d0.size).size =
        min d0.size dk.vals.size from rfl,
      show min d0.size dk.vals.size = d0.size from Nat.min_eq_left hfit]
    exact SparseRemovalsFrom.prefix h hd0 (Nat.le_refl d0.size) v
  cases hl : sparseMem (sparseRestore dk d0.size) v with
  | true =>
      have hmem' : v ∈ (sparseRestore dk d0.size).vals.toList.take
          (sparseRestore dk d0.size).size := hL.mp hl
      rw [show sparseMem d0 v = true from hR.mpr (hmem.mp hmem')]
  | false =>
      cases hr : sparseMem d0 v with
      | true =>
          exfalso
          exact absurd (hL.mpr (hmem.mpr (hR.mp hr))) (by rw [hl]; simp)
      | false => rfl

/-! ## Narrowing: the in-place compaction pass -/

/-- The compaction pass: scan the window positions `p ..< n` of
`A`, writing every value that passes `keep` to the positions from
`w` onwards (in order, by swapping; when `w = p` the kept value
is already in place).  The result's window is the kept values in
order; the pass permutes only the first `n` entries. -/
private def narrowPass (keep : Value → Bool) (A : Array Value) (p w n : Nat) : SparseDom :=
  if p < n then
    if keep (A.getD p default) then
      if w < p then
        narrowPass keep
          ((A.setIfInBounds w (A.getD p default)).setIfInBounds p (A.getD w default))
          (p + 1) (w + 1) n
      else
        narrowPass keep A (p + 1) (w + 1) n
    else
      narrowPass keep A (p + 1) w n
  else ⟨A, w⟩
termination_by n - p
decreasing_by all_goals omega

/-- **The full specification of the compaction pass**: reading
window positions `p ..< n` and writing kept values from `w`
onwards, the pass produces the kept suffix-filter — the window is
exactly `take w ++ filter keep (drop p (take (n - p)))`, the new
size is its length, and the array size is preserved.
(Instantiated at `p = w = 0` this is `sparseNarrow_spec`.) -/
private theorem narrowPass_spec (keep : Value → Bool) (n : Nat) :
    ∀ (A : Array Value) (p w : Nat),
      w ≤ p → p ≤ n → n ≤ A.size →
      (narrowPass keep A p w n).vals.size = A.size ∧
      (narrowPass keep A p w n).size =
        w + ((A.toList.drop p).take (n - p) |>.filter keep).length ∧
      (narrowPass keep A p w n).vals.toList.take
          (w + ((A.toList.drop p).take (n - p) |>.filter keep).length) =
        (A.toList.take w) ++ ((A.toList.drop p).take (n - p) |>.filter keep) := by
  intro A p w
  induction A, p, w using narrowPass.induct (keep := keep) (n := n) with
  | case1 A p w hpn hkeep hwp ih =>
      intro hwle hple hnle
      rw [narrowPass.eq_def, if_pos hpn, if_pos hkeep, if_pos hwp]
      have hA'sz : ((A.setIfInBounds w (A.getD p default)).setIfInBounds p
          (A.getD w default)).size = A.size := by
        rw [Array.size_setIfInBounds, Array.size_setIfInBounds]
      obtain ⟨ih1, ih2, ih3⟩ := ih (by omega) (by omega) (by rw [hA'sz]; exact hnle)
      -- transport the recursion's list to the swapped list
      have hL' : ((A.setIfInBounds w (A.getD p default)).setIfInBounds p
          (A.getD w default)).toList =
          (A.toList.set w (A.getD p default)).set p (A.getD w default) := by
        rw [Array.toList_setIfInBounds, Array.toList_setIfInBounds]
      rw [hL'] at ih2 ih3
      have hLA : A.toList.length = A.size := by simp
      have hwL : w < A.toList.length := by rw [hLA]; omega
      have hpL : p < A.toList.length := by rw [hLA]; omega
      -- the swap only permutes below p+1 and w+1
      have hdrop : ((A.toList.set w (A.getD p default)).set p (A.getD w default)).drop (p + 1) =
          A.toList.drop (p + 1) := by
        rw [drop_set_of_lt (L := A.toList.set w (A.getD p default)) (p + 1) p
          (A.getD w default) (by omega)]
        exact drop_set_of_lt (L := A.toList) (p + 1) w (A.getD p default) (by omega)
      have htake : ((A.toList.set w (A.getD p default)).set p (A.getD w default)).take (w + 1) =
          A.toList.take w ++ [A.getD p default] := by
        rw [take_set_ge (L := A.toList.set w (A.getD p default)) (w + 1) p
          (A.getD w default) (by omega),
          take_set_succ (L := A.toList) w (A.getD p default) hwL]
      -- the scan suffix, unrolled one step
      have hdropp : A.toList.drop p = (A.getD p default) :: A.toList.drop (p + 1) := by
        rw [← arrayToList_getD A p]
        exact drop_eq_getD_cons p hpL
      have hstep : ((A.toList.drop p).take (n - p)).filter keep =
          (A.getD p default) ::
            (((A.toList.drop (p + 1)).take (n - p - 1)).filter keep) := by
        rw [hdropp, List.take_cons (by omega), List.filter_cons, if_pos hkeep]
      have hnp1 : n - (p + 1) = n - p - 1 := by omega
      rw [hnp1, hdrop] at ih2 ih3
      have hswsz : ((A.setIfInBounds w (A.getD p default)).setIfInBounds p
          (A.getD w default)).size = A.size := by
        rw [Array.size_setIfInBounds, Array.size_setIfInBounds]
      rw [hswsz] at ih1
      refine ⟨ih1, ?_, ?_⟩
      · rw [ih2, hstep]
        simp only [List.length_cons]
        omega
      · have hlen : w + (((A.toList.drop p).take (n - p)).filter keep).length =
            (w + 1) + (((A.toList.drop (p + 1)).take (n - p - 1)).filter keep).length := by
          rw [hstep]
          simp only [List.length_cons]
          omega
        rw [hlen, ih3, htake, hstep]
        simp
  | case2 A p w hpn hkeep hwp ih =>
      intro hwle hple hnle
      rw [narrowPass.eq_def, if_pos hpn, if_pos hkeep, if_neg hwp]
      obtain ⟨ih1, ih2, ih3⟩ := ih (by omega) (by omega) hnle
      have hLA : A.toList.length = A.size := by simp
      have hpL : p < A.toList.length := by rw [hLA]; omega
      have hwp' : w = p := by omega
      have hdropp : A.toList.drop p = (A.getD p default) :: A.toList.drop (p + 1) := by
        rw [← arrayToList_getD A p]
        exact drop_eq_getD_cons p hpL
      have hstep : ((A.toList.drop p).take (n - p)).filter keep =
          (A.getD p default) ::
            (((A.toList.drop (p + 1)).take (n - p - 1)).filter keep) := by
        rw [hdropp, List.take_cons (by omega), List.filter_cons, if_pos hkeep]
      have hnp1 : n - (p + 1) = n - p - 1 := by omega
      rw [hnp1] at ih2 ih3
      have htake : A.toList.take (w + 1) =
          A.toList.take w ++ [A.getD p default] := by
        rw [hwp']
        exact (take_succ_getD p hpL).trans (by rw [arrayToList_getD A p])
      refine ⟨ih1, ?_, ?_⟩
      · rw [ih2, hstep]
        simp only [List.length_cons]
        omega
      · have hlen : w + (((A.toList.drop p).take (n - p)).filter keep).length =
            (w + 1) + (((A.toList.drop (p + 1)).take (n - p - 1)).filter keep).length := by
          rw [hstep]
          simp only [List.length_cons]
          omega
        rw [hlen, ih3, htake, hstep]
        simp
  | case3 A p w hpn hkeep ih =>
      intro hwle hple hnle
      rw [narrowPass.eq_def, if_pos hpn, if_neg hkeep]
      obtain ⟨ih1, ih2, ih3⟩ := ih (by omega) (by omega) hnle
      have hLA : A.toList.length = A.size := by simp
      have hpL : p < A.toList.length := by rw [hLA]; omega
      have hdropp : A.toList.drop p = (A.getD p default) :: A.toList.drop (p + 1) := by
        rw [← arrayToList_getD A p]
        exact drop_eq_getD_cons p hpL
      have hstep : ((A.toList.drop p).take (n - p)).filter keep =
          (((A.toList.drop (p + 1)).take (n - p - 1)).filter keep) := by
        rw [hdropp, List.take_cons (by omega), List.filter_cons, if_neg hkeep]
      have hnp1 : n - (p + 1) = n - p - 1 := by omega
      rw [hnp1] at ih2 ih3
      refine ⟨ih1, ?_, ?_⟩
      · rw [ih2, ← hstep]
      · have hlen : w + (((A.toList.drop p).take (n - p)).filter keep).length =
            w + (((A.toList.drop (p + 1)).take (n - p - 1)).filter keep).length := by
          rw [hstep]
        rw [hlen, ih3, hstep]
  | case4 A p w hpn =>
      intro hwle hple _
      rw [narrowPass.eq_def, if_neg hpn]
      have hp : p = n := by omega
      refine ⟨rfl, ?_, ?_⟩
      · rw [hp]
        simp
      · rw [hp]
        simp

/-- **Prefix invariance of the compaction pass**: the pass
permutes only the first `n` entries (the window), so membership in
every prefix of at least the window length is preserved — the fact
the state-level trail proof needs. -/
private theorem narrowPass_prefix (keep : Value → Bool) (n k : Nat) (hkn : n ≤ k)
    (v : Value) :
    ∀ (A : Array Value) (p w : Nat) (hnle : n ≤ A.size),
      v ∈ (narrowPass keep A p w n).vals.toList.take k ↔ v ∈ A.toList.take k := by
  intro A p w
  induction A, p, w using narrowPass.induct (keep := keep) (n := n) with
  | case1 A p w hpn hkeep hwp ih =>
      intro hnle
      rw [narrowPass.eq_def, if_pos hpn, if_pos hkeep, if_pos hwp]
      have hA'sz : ((A.setIfInBounds w (A.getD p default)).setIfInBounds p
          (A.getD w default)).size = A.size := by
        rw [Array.size_setIfInBounds, Array.size_setIfInBounds]
      rw [ih (by rw [hA'sz]; exact hnle)]
      have hL' : ((A.setIfInBounds w (A.getD p default)).setIfInBounds p
          (A.getD w default)).toList =
          (A.toList.set w (A.getD p default)).set p (A.getD w default) := by
        rw [Array.toList_setIfInBounds, Array.toList_setIfInBounds]
      rw [hL']
      have hLA : A.toList.length = A.size := by simp
      have hwL : w < A.toList.length := by rw [hLA]; omega
      have hpL : p < A.toList.length := by rw [hLA]; omega
      have hwk : w < k := by omega
      have hpk : p < k := by omega
      have hg1 : A.getD p default = A.toList.getD p default := (arrayToList_getD A p).symm
      have hg2 : A.getD w default = A.toList.getD w default := (arrayToList_getD A w).symm
      rw [hg1, hg2]
      exact mem_take_swap (L := A.toList) hwL hpL (by omega) hwk hpk v
  | case2 A p w hpn hkeep hwp ih =>
      intro hnle
      rw [narrowPass.eq_def, if_pos hpn, if_pos hkeep, if_neg hwp]
      exact ih hnle
  | case3 A p w hpn hkeep ih =>
      intro hnle
      rw [narrowPass.eq_def, if_pos hpn, if_neg hkeep]
      exact ih hnle
  | case4 A p w hpn =>
      intro hnle
      rw [narrowPass.eq_def, if_neg hpn]

/-- Narrow a sparse domain to the values passing `keep`: one
compaction pass over the window (kept values in order at the
front).  Linear in the window, allocation-free; the *restore*
after it is the constant-time part. -/
def sparseNarrow (keep : Value → Bool) (d : SparseDom) : SparseDom :=
  narrowPass keep d.vals 0 0 d.size

/-- **The narrow spec**: the narrowed logical view is exactly the
filter of the old logical view (a list equality — the kept values
appear in order), the window only shrinks, and the array size is
preserved. -/
theorem sparseNarrow_spec (keep : Value → Bool) (d : SparseDom) (hd : d.Valid) :
    (sparseNarrow keep d).Valid ∧ (sparseNarrow keep d).size ≤ d.size ∧
    (sparseNarrow keep d).vals.size = d.vals.size ∧
    sparseToList (sparseNarrow keep d) = (sparseToList d).filter keep := by
  -- the spec needs the invariant only for the window/size bookkeeping;
  -- narrowPass_spec's hypotheses hold unconditionally at p = w = 0
  have hspec := narrowPass_spec keep d.size d.vals 0 0 (Nat.zero_le _) (Nat.zero_le _) hd
  obtain ⟨h1, h2, h3⟩ := hspec
  -- the scan window at p = w = 0 is the logical view
  have hsimplify : (d.vals.toList.drop 0).take (d.size - 0) = d.vals.toList.take d.size := by
    simp
  rw [hsimplify, Nat.zero_add] at h2 h3
  refine ⟨?_, ?_, h1, ?_⟩
  · show (sparseNarrow keep d).size ≤ (sparseNarrow keep d).vals.size
    show (narrowPass keep d.vals 0 0 d.size).size ≤
        (narrowPass keep d.vals 0 0 d.size).vals.size
    rw [h2, h1]
    have hle : ((d.vals.toList.take d.size).filter keep).length ≤
        (d.vals.toList.take d.size).length := List.length_filter_le _ _
    have hlentake : (d.vals.toList.take d.size).length ≤ d.size := by
      rw [List.length_take]
      omega
    have hdd : d.size ≤ d.vals.size := hd
    omega
  · show (sparseNarrow keep d).size ≤ d.size
    show (narrowPass keep d.vals 0 0 d.size).size ≤ d.size
    rw [h2]
    have hle : ((d.vals.toList.take d.size).filter keep).length ≤
        (d.vals.toList.take d.size).length := List.length_filter_le _ _
    have hlentake : (d.vals.toList.take d.size).length ≤ d.size := by
      rw [List.length_take]
      omega
    omega
  show sparseToList (sparseNarrow keep d) = (sparseToList d).filter keep
  show (narrowPass keep d.vals 0 0 d.size).vals.toList.take
      (narrowPass keep d.vals 0 0 d.size).size = _
  rw [h2]
  exact h3

/-- Narrowing preserves validity (the window only shrinks and the
array size is preserved). -/
theorem sparseNarrow_valid (keep : Value → Bool) (d : SparseDom) (hd : d.Valid) :
    (sparseNarrow keep d).Valid := (sparseNarrow_spec keep d hd).1

/-- **Prefix invariance of narrowing**: the compaction pass
permutes only the window, so membership in every prefix of at least
the window length is preserved — the fact the state-level trail
proof needs. -/
theorem sparseNarrow_prefix (keep : Value → Bool) (d : SparseDom) (hd : d.Valid) {k : Nat}
    (hk : d.size ≤ k) (v : Value) :
    v ∈ (sparseNarrow keep d).vals.toList.take k ↔ v ∈ d.vals.toList.take k :=
  narrowPass_prefix keep d.size k hk v d.vals 0 0 hd

/-! ## The solver-level state -/

/-- The full reversible search state: one sparse-set domain per
slot.  Slot access is positional (index into `doms`), matching
`getSlot` on the list representation. -/
structure RevState where
  /-- One sparse-set domain per slot. -/
  doms : Array SparseDom
  deriving Repr, Inhabited

/-- The state-level representation invariant: every slot's domain
satisfies the sparse-set invariant (the out-of-range default
`⟨#[], 0⟩` is valid). -/
def RevState.Valid (s : RevState) : Prop := ∀ i, (s.doms.getD i default).Valid

/-- The logical view of slot `i`'s domain. -/
def revGet (s : RevState) (i : Nat) : List Value := sparseToList (s.doms.getD i default)

/-- The logical view of the whole state, as the list of
list-of-values the propagator stack consumes. -/
def revDoms (s : RevState) : List (List Value) := s.doms.toList.map sparseToList

/-- The state's logical view, slot by slot, agrees with `revGet`
(and hence with `getSlot` on the materialized list). -/
theorem getSlot_revDoms (s : RevState) :
    ∀ (i : Nat), getSlot (revDoms s) i = revGet s i := by
  have hmap : ∀ (l : List SparseDom) (i : Nat),
      getSlot (l.map sparseToList) i = sparseToList (l.getD i default) := by
    intro l i
    induction l generalizing i with
    | nil => cases i <;> rfl
    | cons d ds ih =>
        cases i with
        | zero => rfl
        | succ i' => exact ih i'
  intro i
  rw [revDoms, hmap, arrayToList_getD]
  rfl

/-- The slot count of the logical view. -/
theorem revDoms_length (s : RevState) :
    (revDoms s).length = s.doms.toList.length := by
  simp [revDoms]

/-- Narrow slot `i` of the state to the values passing `keep`
(single compaction pass; out-of-range slots are untouched). -/
def revNarrow (s : RevState) (i : Nat) (keep : Value → Bool) : RevState :=
  ⟨s.doms.setIfInBounds i (sparseNarrow keep (s.doms.getD i default))⟩

/-- `revNarrow`'s effect at the slot level: the narrowed slot, or
the untouched original. -/
theorem revNarrow_getD (s : RevState) (i j : Nat) (keep : Value → Bool) :
    (revNarrow s i keep).doms.getD j default =
      if i = j ∧ i < s.doms.size then sparseNarrow keep (s.doms.getD i default)
        else s.doms.getD j default := by
  show (s.doms.setIfInBounds i (sparseNarrow keep (s.doms.getD i default))).getD j default = _
  rw [getD_setIfInBounds]

/-- The out-of-range default slot is valid and empty-viewed. -/
private theorem slot_default_valid : (default : SparseDom).Valid := Nat.le_refl _

/-- Narrowing one slot leaves every other slot untouched. -/
theorem revGet_revNarrow_of_ne (s : RevState) (i j : Nat) (keep : Value → Bool)
    (h : j ≠ i) :
    revGet (revNarrow s i keep) j = revGet s j := by
  show sparseToList ((revNarrow s i keep).doms.getD j default) = _
  rw [revNarrow_getD, if_neg (fun hc => h hc.1.symm)]
  rfl

/-- **The narrowing spec at the state level**: the narrowed slot's
logical view is exactly the filter of the old one. -/
theorem revGet_revNarrow_self (s : RevState) (i : Nat) (keep : Value → Bool)
    (hs : RevState.Valid s) :
    revGet (revNarrow s i keep) i = (revGet s i).filter keep := by
  show sparseToList ((revNarrow s i keep).doms.getD i default) = _
  rw [revNarrow_getD]
  by_cases hlt : i < s.doms.size
  · rw [if_pos ⟨rfl, hlt⟩, (sparseNarrow_spec keep _ (hs i)).2.2.2]
    rfl
  · have hge : s.doms.size ≤ i := by omega
    have hdef : s.doms.getD i default = default := array_getD_of_ge s.doms hge
    rw [if_neg (fun hc => hlt hc.2), hdef]
    have hempty : revGet s i = [] := by
      show sparseToList (s.doms.getD i default) = []
      rw [hdef]
      rfl
    rw [hempty]
    rfl

/-- Narrowing preserves the state invariant. -/
theorem revNarrow_valid (s : RevState) (i : Nat) (keep : Value → Bool) (hs : s.Valid) :
    (revNarrow s i keep).Valid := by
  intro j
  show ((revNarrow s i keep).doms.getD j default).Valid
  rw [revNarrow_getD]
  by_cases h : i = j ∧ i < s.doms.size
  · rw [if_pos h]
    exact sparseNarrow_valid _ _ (hs i)
  · rw [if_neg h]
    have hs' : ∀ k, (s.doms.getD k default).Valid := by
      intro k
      exact hs k
    exact hs' j

/-- **Narrowing only removes values** (the subset half). -/
theorem revNarrow_subset (s : RevState) (i : Nat) (keep : Value → Bool)
    (hs : RevState.Valid s) :
    ∀ j v, v ∈ revGet (revNarrow s i keep) j → v ∈ revGet s j := by
  intro j v hmem
  by_cases hji : j = i
  · subst hji
    rw [revGet_revNarrow_self s j keep hs, List.mem_filter] at hmem
    exact hmem.1
  · rw [revGet_revNarrow_of_ne s i j keep (fun hc => hji hc)] at hmem
    exact hmem

/-- **Narrowing keeps the passing values** (the keeps half). -/
theorem revNarrow_keeps (s : RevState) (i : Nat) (keep : Value → Bool)
    (hs : RevState.Valid s) {v : Value} (hmem : v ∈ revGet s i)
    (hkeep : keep v = true) :
    v ∈ revGet (revNarrow s i keep) i := by
  rw [revGet_revNarrow_self s i keep hs, List.mem_filter]
  exact ⟨hmem, hkeep⟩

/-- **The full narrowing characterization**: a value is in the
narrowed state's slot `j` exactly when it was in the old slot and
either survives (other slot) or passes `keep` (narrowed slot). -/
theorem revNarrow_mem (s : RevState) (i : Nat) (keep : Value → Bool)
    (hs : RevState.Valid s) (j : Nat) (v : Value) :
    v ∈ revGet (revNarrow s i keep) j ↔
      v ∈ revGet s j ∧ (j ≠ i ∨ keep v = true) := by
  by_cases hji : j = i
  · subst hji
    rw [revGet_revNarrow_self s j keep hs, List.mem_filter]
    constructor
    · rintro ⟨hmem, hkeep⟩
      exact ⟨hmem, Or.inr hkeep⟩
    · rintro ⟨hmem, hrest⟩
      rcases hrest with hne | hkeep
      · exact absurd rfl hne
      · exact ⟨hmem, hkeep⟩
  · rw [revGet_revNarrow_of_ne s i j keep (fun hc => hji hc)]
    constructor
    · intro hmem; exact ⟨hmem, Or.inl hji⟩
    · rintro ⟨hmem, _⟩; exact hmem

/-! ## The trail -/

/-- One trail entry: the slot that was narrowed, and the window
size it had *before* the narrowing. -/
structure RevTrailEntry where
  /-- The narrowed slot. -/
  slot : Nat
  /-- The slot's window size before the narrowing. -/
  prevSize : Nat
  deriving Repr

/-- The trail: a stack, most recent entry first. -/
abbrev revTrail := List RevTrailEntry

/-- One narrowing step: the narrowed state paired with the trail
entry to push. -/
def revNarrowStep (s : RevState) (i : Nat) (keep : Value → Bool) :
    RevState × RevTrailEntry :=
  (revNarrow s i keep, ⟨i, (s.doms.getD i default).size⟩)

/-- `sk` is reachable from `s0` by the sequence of narrowings
recorded in `tl` (entries pushed most recent first; each entry
records the pre-narrowing size of the slot it narrowed). -/
inductive RevNarrowingsFrom : RevState → RevState → revTrail → Prop
  /-- The empty sequence. -/
  | refl (s : RevState) : RevNarrowingsFrom s s []
  /-- One more narrowing: `s3` is `s2` with slot `i` narrowed, and
      the pushed entry records `s2`'s slot-`i` size. -/
  | step {s0 s2 s3 : RevState} {tl : revTrail} {i : Nat} {keep : Value → Bool}
      {e : RevTrailEntry}
      (h : RevNarrowingsFrom s0 s2 tl)
      (hstep : s3 = revNarrow s2 i keep)
      (hentry : e.slot = i ∧ e.prevSize = (s2.doms.getD i default).size) :
      RevNarrowingsFrom s0 s3 (e :: tl)

/-- The trail entries' slots and sizes match the narrowings. -/
theorem revNarrowingsFrom_valid {s0 sk : RevState} {tl : revTrail}
    (h : RevNarrowingsFrom s0 sk tl) (hvalid : s0.Valid) :
    sk.Valid := by
  induction h with
  | refl => exact hvalid
  | step h hstep hentry ih =>
      subst hstep
      exact revNarrow_valid _ _ _ ih

/-- Narrowing sequences only shrink each slot's window, and never
change any array's size. -/
private theorem narrowingsFrom_slot_inv {s0 sk : RevState} {tl : revTrail}
    (h : RevNarrowingsFrom s0 sk tl) (hvalid : s0.Valid) :
    ∀ j, (sk.doms.getD j default).size ≤ (s0.doms.getD j default).size ∧
      (sk.doms.getD j default).vals.size = (s0.doms.getD j default).vals.size := by
  induction h with
  | refl =>
      intro j
      exact ⟨Nat.le_refl _, rfl⟩
  | step h hstep hentry ih =>
      subst hstep
      rename_i s2 tl i keep e
      intro j
      obtain ⟨h1, h2⟩ := ih j
      have hs2valid : RevState.Valid s2 := revNarrowingsFrom_valid h hvalid
      have hread : ∀ (k : Nat) (P : SparseDom → Prop),
          (i = k → i < s2.doms.size → P (sparseNarrow keep (s2.doms.getD i default))) →
          (¬(i = k ∧ i < s2.doms.size) → P (s2.doms.getD k default)) →
          P ((revNarrow s2 i keep).doms.getD k default) := by
        intro k P hpos hneg
        rw [revNarrow_getD]
        by_cases hcond : i = k ∧ i < s2.doms.size
        · rw [if_pos hcond]
          exact hpos hcond.1 hcond.2
        · rw [if_neg hcond]
          exact hneg hcond
      by_cases hji : i = j
      · -- the narrowed slot itself
        have hslotvalid : (s2.doms.getD i default).Valid := hs2valid i
        have hnslot := (sparseNarrow_spec keep (s2.doms.getD i default) hslotvalid).2.1
        have hnarr := (sparseNarrow_spec keep (s2.doms.getD i default) hslotvalid).2.2.1
        constructor
        · have key := hread j (fun d => d.size ≤ (s0.doms.getD j default).size)
            (fun hji' _ => by
              have hn := hnslot
              have hj := h1
              show (sparseNarrow keep (s2.doms.getD i default)).size ≤
                (s0.doms.getD j default).size
              have hij : i = j := hji'
              rw [hij] at hn
              subst hij
              omega)
            (fun _ => h1)
          simpa using key
        · have key := hread j (fun d => d.vals.size = (s0.doms.getD j default).vals.size)
            (fun hji' _ => by
              have hn := hnarr
              have ha := h2
              show (sparseNarrow keep (s2.doms.getD i default)).vals.size =
                (s0.doms.getD j default).vals.size
              have hij : i = j := hji'
              rw [hij] at hn
              subst hij
              omega)
            (fun _ => h2)
          simpa using key
      · -- a different slot: untouched
        constructor
        · have key := hread j (fun d => d.size ≤ (s0.doms.getD j default).size)
            (fun hji' _ => absurd hji' hji)
            (fun _ => h1)
          simpa using key
        · have key := hread j (fun d => d.vals.size = (s0.doms.getD j default).vals.size)
            (fun hji' _ => absurd hji' hji)
            (fun _ => h2)
          simpa using key

/-- Restore one slot to a recorded size (one trail entry). -/
def revRestore1 (s : RevState) (e : RevTrailEntry) : RevState :=
  ⟨s.doms.setIfInBounds e.slot (sparseRestore (s.doms.getD e.slot default) e.prevSize)⟩

/-- **Backtracking**: fold the trail (most recent entry first),
restoring each recorded size.  The oldest entry for a slot is
applied last, so it wins — and it records the slot's size before
its first narrowing, i.e. the ancestor's window. -/
def revBacktrack (s : RevState) (tl : revTrail) : RevState :=
  tl.foldl (fun st e => revRestore1 st e) s

/-- The oldest recorded size for slot `j` in the trail (the last
entry in list order), if any. -/
def trailPrevSize (j : Nat) : revTrail → Option Nat
  | [] => none
  | e :: tl =>
      match trailPrevSize j tl with
      | some sz => some sz
      | none => if e.slot = j then some e.prevSize else none

/-- Every slot of a *valid* state is valid: in-range slots by the
state's validity, out-of-range slots by being the (valid) default. -/
private theorem slot_valid_of_state (s : RevState) (hs : RevState.Valid s) (j : Nat) :
    (s.doms.getD j default).size ≤ (s.doms.getD j default).vals.size := by
  by_cases hlt : j < s.doms.size
  · exact hs j
  · have hdef : s.doms.getD j default = default :=
      array_getD_of_ge s.doms (by omega)
    rw [hdef]
    show (default : SparseDom).size ≤ (default : SparseDom).vals.size
    have hsize0 : (default : SparseDom).size = 0 := rfl
    have hdefsz : (default : SparseDom).vals.size = 0 := by
      show (Array.mk ([] : List Value)).size = 0
      rfl
    rw [hsize0, hdefsz]
    omega

/-- Restoring a slot reads back the restored domain. -/
private theorem revRestore1_getD_self (s : RevState) (e : RevTrailEntry) :
    (revRestore1 s e).doms.getD e.slot default =
      sparseRestore (s.doms.getD e.slot default) e.prevSize := by
  show (s.doms.setIfInBounds e.slot (sparseRestore (s.doms.getD e.slot default)
      e.prevSize)).getD e.slot default = _
  rw [getD_setIfInBounds]
  by_cases hlt : e.slot < s.doms.size
  · rw [if_pos ⟨rfl, hlt⟩]
  · rw [if_neg (fun hc => hlt hc.2)]
    show s.doms.getD e.slot default = sparseRestore (s.doms.getD e.slot default) e.prevSize
    rw [array_getD_of_ge s.doms (by omega)]
    show (default : SparseDom) = sparseRestore (default : SparseDom) e.prevSize
    have hdefsz : (default : SparseDom).vals.size = 0 := by
      show (Array.mk ([] : List Value)).size = 0
      rfl
    show (default : SparseDom) = ⟨(default : SparseDom).vals, min e.prevSize
        (default : SparseDom).vals.size⟩
    rw [hdefsz, Nat.min_zero]
    rfl

/-- Restoring one slot leaves every other slot untouched. -/
private theorem revRestore1_getD_of_ne (s : RevState) (e : RevTrailEntry) {j : Nat}
    (h : j ≠ e.slot) :
    (revRestore1 s e).doms.getD j default = s.doms.getD j default := by
  show (s.doms.setIfInBounds e.slot (sparseRestore (s.doms.getD e.slot default)
      e.prevSize)).getD j default = _
  rw [getD_setIfInBounds, if_neg (fun hc : e.slot = j ∧ e.slot < s.doms.size =>
    h hc.1.symm)]

/-- Restoring preserves validity. -/
private theorem revRestore1_valid (s : RevState) (e : RevTrailEntry) (hs : s.Valid) :
    (revRestore1 s e).Valid := by
  intro j
  show ((revRestore1 s e).doms.getD j default).Valid
  by_cases h : e.slot = j
  · subst h
    rw [revRestore1_getD_self]
    exact sparseRestore_valid _ _
  · rw [revRestore1_getD_of_ne s e (fun hc => h hc.symm)]
    exact hs j

/-- **The fold's per-slot characterization**: backtracking `s` along
`tl` leaves every slot's array untouched and sets slot `j`'s
window to the oldest recorded size for `j` (clamped to the
array), or leaves it alone if `j` was never narrowed. -/
private theorem revBacktrack_slot (tl : revTrail) :
    ∀ (s : RevState) (j : Nat) (hs : RevState.Valid s),
      (revBacktrack s tl).doms.getD j default =
        sparseRestore (s.doms.getD j default)
          ((trailPrevSize j tl).getD (s.doms.getD j default).size) := by
  induction tl with
  | nil =>
      intro s j hs
      show s.doms.getD j default = _
      rw [trailPrevSize]
      show s.doms.getD j default = sparseRestore (s.doms.getD j default)
        (s.doms.getD j default).size
      have hslot : (s.doms.getD j default).size ≤ (s.doms.getD j default).vals.size :=
        slot_valid_of_state s hs j
      rw [sparseRestore, Nat.min_eq_left hslot]
  | cons e tl ih =>
      intro s j hs
      simp only [revBacktrack, List.foldl_cons]
      have hih := ih (revRestore1 s e) j (revRestore1_valid s e hs)
      by_cases hej : e.slot = j
      · -- the entry restores slot j itself: restores overwrite, so the
        -- fold's result is the restore of the OLDEST recorded size for j
        have hslot : (revRestore1 s e).doms.getD j default =
            sparseRestore (s.doms.getD j default) e.prevSize := by
          rw [← hej]
          exact revRestore1_getD_self s e
        rw [hslot] at hih
        rw [sparseRestore_comp] at hih
        rw [trailPrevSize]
        cases hol : trailPrevSize j tl with
        | none =>
            show (List.foldl (fun st e => revRestore1 st e) (revRestore1 s e) tl).doms.getD
                j default = _
            rw [show ((if e.slot = j then some e.prevSize else none :
                Option Nat)).getD (s.doms.getD j default).size = e.prevSize from by
              rw [if_pos hej]
              rfl]
            have hih' : (revBacktrack (revRestore1 s e) tl).doms.getD j default =
                sparseRestore (s.doms.getD j default)
                  (min e.prevSize (s.doms.getD j default).vals.size) := by
              have hnone : (trailPrevSize j tl).getD
                  (sparseRestore (s.doms.getD j default) e.prevSize).size =
                  min e.prevSize (s.doms.getD j default).vals.size := by
                rw [hol]
                rfl
              rw [hnone] at hih
              exact hih
            show (revBacktrack (revRestore1 s e) tl).doms.getD j default = _
            rw [hih', sparseRestore, sparseRestore]
            apply congrArg
            rw [Nat.min_assoc]
            have hself : min (s.doms.getD j default).vals.size
                (s.doms.getD j default).vals.size =
                (s.doms.getD j default).vals.size :=
              Nat.min_eq_left (Nat.le_refl _)
            rw [hself]
        | some sz =>
            show (List.foldl (fun st e => revRestore1 st e) (revRestore1 s e) tl).doms.getD
                j default = _
            rw [show ((match some sz with
                | some sz => some sz
                | none => if e.slot = j then some e.prevSize else none :
                Option Nat)).getD (s.doms.getD j default).size = sz from rfl]
            have hih' : (revBacktrack (revRestore1 s e) tl).doms.getD j default =
                sparseRestore (s.doms.getD j default) sz := by
              have hsz : trailPrevSize j tl = some sz := hol
              rw [hsz] at hih
              exact hih
            show (revBacktrack (revRestore1 s e) tl).doms.getD j default = _
            exact hih'
      · have hslot : (revRestore1 s e).doms.getD j default =
            s.doms.getD j default :=
          revRestore1_getD_of_ne s e (fun hc => hej hc.symm)
        rw [hslot] at hih
        rw [trailPrevSize, if_neg (fun hc => hej hc)]
        cases hol : trailPrevSize j tl with
        | none =>
            show (List.foldl (fun st e => revRestore1 st e) (revRestore1 s e) tl).doms.getD
                j default = _
            rw [show ((match none with
                | some sz => some sz
                | none => none : Option Nat)).getD
                (s.doms.getD j default).size =
                (s.doms.getD j default).size from rfl]
            have hih' : (revBacktrack (revRestore1 s e) tl).doms.getD j default =
                sparseRestore (s.doms.getD j default)
                  ((s.doms.getD j default).size) := by
              rw [hol] at hih
              exact hih
            show (revBacktrack (revRestore1 s e) tl).doms.getD j default = _
            rw [hih', sparseRestore, Nat.min_eq_left (slot_valid_of_state s hs j)]
        | some sz =>
            show (List.foldl (fun st e => revRestore1 st e) (revRestore1 s e) tl).doms.getD
                j default = _
            rw [show ((match some sz with
                | some sz => some sz
                | none => none : Option Nat)).getD
                (s.doms.getD j default).size = sz from rfl]
            have hih' : (revBacktrack (revRestore1 s e) tl).doms.getD j default =
                sparseRestore (s.doms.getD j default) sz := by
              have hsz : trailPrevSize j tl = some sz := hol
              rw [hsz] at hih
              exact hih
            show (revBacktrack (revRestore1 s e) tl).doms.getD j default = _
            exact hih'

/-- **The state-level trail guarantee** (PLAN 6.4's "trail
restoration recreates the exact ancestor domains", at the
membership level the logical view provides): if the trail records
the narrowings that turned `s0` into `sk`, then backtracking `sk`
along the trail restores every slot's logical view to `s0`'s. -/
theorem revBacktrack_recovers {s0 sk : RevState} {tl : revTrail}
    (h : RevNarrowingsFrom s0 sk tl) (hvalid : s0.Valid) :
    ∀ j v, v ∈ revGet (revBacktrack sk tl) j ↔ v ∈ revGet s0 j := by
  -- one induction over the narrowing sequence carries everything the
  -- final membership argument needs: validity, monotone windows,
  -- unchanged arrays, membership preservation at the ancestor's window
  -- (the compaction permutes only within it), and that the oldest
  -- recorded size for each slot is the ancestor's (or the slot was
  -- never narrowed and is still the ancestor's)
  have hmain : ∀ (s1 s2 : RevState) (t : revTrail),
      RevNarrowingsFrom s1 s2 t → RevState.Valid s1 →
      RevState.Valid s2 ∧
      (∀ j, (s2.doms.getD j default).size ≤ (s1.doms.getD j default).size) ∧
      (∀ j, (s2.doms.getD j default).vals.size = (s1.doms.getD j default).vals.size) ∧
      (∀ j v, v ∈ (s2.doms.getD j default).vals.toList.take
          ((s1.doms.getD j default).size) ↔
        v ∈ (s1.doms.getD j default).vals.toList.take
          ((s1.doms.getD j default).size)) ∧
      (∀ j, trailPrevSize j t = some (s1.doms.getD j default).size ∨
        (trailPrevSize j t = none ∧
          s2.doms.getD j default = s1.doms.getD j default)) := by
    intro s1 s2 t h
    induction h with
    | refl =>
        intro hv
        exact ⟨hv, fun _ => Nat.le_refl _, fun _ => rfl, fun _ _ => Iff.rfl,
          fun _ => Or.inr ⟨rfl, rfl⟩⟩
    | step h hstep hentry ih =>
        intro hv
        subst hstep
        rename_i s2a tl i keep e
        obtain ⟨hv2, hsz, harr, hperm, holdest⟩ := ih hv
        -- the pre-narrowing state's slot i and the narrowed slot's spec
        have hslotvalid : (s2a.doms.getD i default).Valid := hv2 i
        have hnspec := sparseNarrow_spec keep (s2a.doms.getD i default) hslotvalid
        -- the new state's slot readings, case-analyzed once
        have hread : ∀ (j : Nat) (P : SparseDom → Prop),
            (i = j → i < s2a.doms.size → P (sparseNarrow keep (s2a.doms.getD i default))) →
            (¬(i = j ∧ i < s2a.doms.size) → P (s2a.doms.getD j default)) →
            P ((revNarrow s2a i keep).doms.getD j default) := by
          intro j P hpos hneg
          rw [revNarrow_getD]
          by_cases hcond : i = j ∧ i < s2a.doms.size
          · rw [if_pos hcond]
            exact hpos hcond.1 hcond.2
          · rw [if_neg hcond]
            exact hneg hcond
        refine ⟨revNarrow_valid _ _ _ hv2, ?_, ?_, ?_, ?_⟩
        · -- sizes only shrink
          intro j
          by_cases hji : i = j
          · have key := hread j (fun d => d.size ≤ (s1.doms.getD j default).size)
              (fun hji' _ => by
                have hn := hnspec.2.1
                have hj := hsz j
                show (sparseNarrow keep (s2a.doms.getD i default)).size ≤
                  (s1.doms.getD j default).size
                have hij : i = j := hji'
                rw [hij] at hn ⊢
                omega)
              (fun _ => hsz j)
            simpa using key
          · have key := hread j (fun d => d.size ≤ (s1.doms.getD j default).size)
              (fun hji' _ => absurd hji' hji)
              (fun _ => hsz j)
            simpa using key
        · -- array sizes unchanged
          intro j
          by_cases hji : i = j
          · have key := hread j (fun d => d.vals.size = (s1.doms.getD j default).vals.size)
              (fun hji' _ => by
                have hn := hnspec.2.2.1
                have ha := harr j
                show (sparseNarrow keep (s2a.doms.getD i default)).vals.size =
                  (s1.doms.getD j default).vals.size
                have hij : i = j := hji'
                rw [hij] at hn ⊢
                omega)
              (fun _ => harr j)
            simpa using key
          · have key := hread j (fun d => d.vals.size = (s1.doms.getD j default).vals.size)
              (fun hji' _ => absurd hji' hji)
              (fun _ => harr j)
            simpa using key
        · -- membership at the ancestor's window
          intro j v
          by_cases hji : i = j
          · have key := hread j (fun d =>
              v ∈ d.vals.toList.take ((s1.doms.getD j default).size) ↔
                v ∈ (s1.doms.getD j default).vals.toList.take
                  ((s1.doms.getD j default).size))
              (fun hji' _ => by
                have hp := sparseNarrow_prefix keep (s2a.doms.getD i default) hslotvalid
                  (k := (s1.doms.getD i default).size) (hsz i) v
                have hb := hperm j v
                have hij : i = j := hji'
                rw [hij] at hp ⊢
                exact hp.trans hb)
              (fun _ => hperm j v)
            simpa using key
          · have key := hread j (fun d =>
              v ∈ d.vals.toList.take ((s1.doms.getD j default).size) ↔
                v ∈ (s1.doms.getD j default).vals.toList.take
                  ((s1.doms.getD j default).size))
              (fun hji' _ => absurd hji' hji)
              (fun _ => hperm j v)
            simpa using key
        · -- the oldest recorded size
          intro j
          rw [trailPrevSize]
          by_cases hji : j = i
          · -- this entry narrows slot j
            have hsloti : e.slot = i := hentry.1
            have hprev : e.prevSize = (s2a.doms.getD i default).size := hentry.2
            rw [if_pos (hsloti.trans hji.symm)]
            cases hol : trailPrevSize j tl with
            | none =>
                rcases holdest j with hsome | ⟨hnone, hsame2⟩
                · rw [hsome] at hol
                  exact absurd hol (by simp)
                · -- no older entry: s2a's slot j is s1's, so the entry's
                  -- prevSize is exactly s1's slot-j size
                  have hsamei : s2a.doms.getD j default = s1.doms.getD j default := hsame2
                  have hsizeq : (s2a.doms.getD i default).size =
                      (s1.doms.getD i default).size := by
                    rw [← hji]
                    exact congrArg SparseDom.size hsamei
                  rw [show e.prevSize = (s1.doms.getD j default).size from by
                    rw [hprev, hji]
                    exact hsizeq]
                  exact Or.inl rfl
            | some sz =>
                show some sz = some (s1.doms.getD j default).size ∨
                  (some sz = none ∧
                    (revNarrow s2a i keep).doms.getD j default =
                      s1.doms.getD j default)
                rcases holdest j with hsome | ⟨hnone, _⟩
                · exact Or.inl (hol ▸ hsome)
                · exact absurd hnone (by rw [hol]; simp)
          · -- a different slot: this entry does not record j
            have hslotne : e.slot ≠ j := fun hc => hji (hentry.1 ▸ hc).symm
            rw [if_neg hslotne]
            cases hol : trailPrevSize j tl with
            | none =>
                rcases holdest j with hsome | ⟨hnone, hsame⟩
                · rw [hsome] at hol
                  exact absurd hol (by simp)
                · rw [hnone] at hol
                  exact Or.inr ⟨by rw [hol], hread j (fun d => d = s1.doms.getD j default)
                    (fun hji' _ => absurd hji'.symm hji)
                    (fun _ => hsame)⟩
            | some sz =>
                show some sz = some (s1.doms.getD j default).size ∨
                  (some sz = none ∧
                    (revNarrow s2a i keep).doms.getD j default =
                      s1.doms.getD j default)
                rcases holdest j with hsome | ⟨hnone, _⟩
                · exact Or.inl (hol ▸ hsome)
                · exact absurd hnone (by rw [hol]; simp)
  -- instantiate and conclude
  obtain ⟨hvsk, hsz, harr, hperm, holdest⟩ := hmain s0 sk tl h hvalid
  intro j v
  -- the backtracked slot, by the fold characterization
  show v ∈ sparseToList ((revBacktrack sk tl).doms.getD j default) ↔ _
  rw [revBacktrack_slot tl sk j hvsk]
  rcases holdest j with hsome | ⟨hnone, hsame⟩
  · -- the oldest recorded size is the ancestor's
    rw [hsome]
    show v ∈ sparseToList
      (sparseRestore (sk.doms.getD j default) (s0.doms.getD j default).size) ↔
      v ∈ sparseToList (s0.doms.getD j default)
    rw [sparseRestore, show min (s0.doms.getD j default).size
      (sk.doms.getD j default).vals.size = (s0.doms.getD j default).size from by
        rw [harr j]
        exact Nat.min_eq_left (hvalid j)]
    show v ∈ (sk.doms.getD j default).vals.toList.take
      ((s0.doms.getD j default).size) ↔ _
    rw [hperm j v]
    rfl
  · -- the slot was never narrowed: it IS the ancestor's
    rw [hnone]
    show v ∈ sparseToList
      (sparseRestore (sk.doms.getD j default) (sk.doms.getD j default).size) ↔
      v ∈ sparseToList (s0.doms.getD j default)
    have hself : sparseRestore (sk.doms.getD j default)
        (sk.doms.getD j default).size = sk.doms.getD j default := by
      rw [sparseRestore, Nat.min_eq_left (hvsk j)]
    rw [hself, hsame]

/-! ## A propagation round on the reversible state -/

/-- The propagator-list side condition: every propagator's
`narrowed` output is pointwise-subset its input — the subset half
of the `Preserves` contract, which is all the refinement needs. -/
def AllNarrowOnly : List (List (List Value) → PropResult) → Prop
  | [] => True
  | p :: ps => (∀ doms doms', p doms = .narrowed doms' → DomPointwiseSub doms' doms) ∧
    AllNarrowOnly ps

/-- The `Preserves` contract implies `AllNarrowOnly` (the subset
field, point by point). -/
theorem allPreserve_narrowOnly {cs : List DomConstraint}
    {props : List (List (List Value) → PropResult)} (h : AllPreserve cs props) :
    AllNarrowOnly props := by
  induction h with
  | nil => trivial
  | cons hp hrest ih => exact ⟨fun doms doms' hcall => hp.subset hcall, ih⟩

/-- A pass of `AllNarrowOnly` propagators only shrinks domains. -/
theorem propPass_subset (props : List (List (List Value) → PropResult))
    (hn : AllNarrowOnly props) :
    ∀ doms doms', propPass props doms = .narrowed doms' → DomPointwiseSub doms' doms := by
  induction props with
  | nil =>
      intro doms doms2 h
      have hd : doms = doms2 := PropResult.narrowed.inj h
      subst hd
      exact DomPointwiseSub.refl doms
  | cons p ps ih =>
      intro doms doms' h
      simp only [propPass] at h
      cases hp : p doms with
      | contradiction => rw [hp] at h; exact absurd h (by simp)
      | narrowed doms1 =>
          rw [hp] at h
          exact DomPointwiseSub.trans (ih hn.2 doms1 doms' h) (hn.1 doms doms1 hp)

/-- Apply a list of narrowed domains (as a keep-list per slot)
back onto the state, slot by slot.  Fuel-structured: fuel `n`
narrows slots `n-1, ..., 0`. -/
def revNarrowFrom (s : RevState) (doms' : List (List Value)) : Nat → RevState
  | 0 => s
  | n + 1 => revNarrowFrom (revNarrow s n (fun v => valueMemB v (getSlot doms' n))) doms' n

/-- **The single-step refinement**: applying a pointwise-subset
family of narrowed domains onto the state through `revNarrowFrom`
yields exactly those domains at the logical view (per-slot
membership). -/
theorem revNarrowFrom_refines (doms' : List (List Value)) (n : Nat) :
    ∀ (s : RevState) (hs : RevState.Valid s)
      (hsub : DomPointwiseSub doms' (revDoms s)),
      (∀ i (v : Value) (hi : i < n), v ∈ revGet (revNarrowFrom s doms' n) i ↔
        v ∈ getSlot doms' i) ∧
      (∀ i (v : Value) (hle : n ≤ i), v ∈ revGet (revNarrowFrom s doms' n) i ↔
        v ∈ revGet s i) := by
  induction n with
  | zero =>
      intro s hs hsub
      -- fuel 0: nothing was narrowed
      constructor
      · intro i v hi
        exact absurd hi (Nat.not_lt.mpr (Nat.zero_le i))
      · intro i v hle
        exact Iff.rfl
  | succ n ih =>
      intro s hs hsub
      -- the narrowed slot's view: the filter of the old view over the keep
      have hview : revGet (revNarrow s n (fun v => valueMemB v (getSlot doms' n))) n =
          (revGet s n).filter (fun v => valueMemB v (getSlot doms' n)) :=
        revGet_revNarrow_self s n _ hs
      -- the filter's membership is exactly the target domain's (the filter
      -- keeps the old view's members of the target; the subset direction says
      -- every target value was in the old view)
      have hsetmem : ∀ v, v ∈ (revGet s n).filter
          (fun v => valueMemB v (getSlot doms' n)) ↔ v ∈ getSlot doms' n := by
        intro v
        rw [List.mem_filter, valueMemB_iff]
        constructor
        · rintro ⟨h1, h2⟩
          exact h2
        · intro h2
          have h1 : v ∈ revGet s n := by
            have hx2 := hsub.2 n v h2
            rw [getSlot_revDoms s n] at hx2
            exact hx2
          exact ⟨h1, h2⟩
      -- the length is preserved by the narrowing (the slot count is unchanged)
      have hlenEq : (revDoms (revNarrow s n
          (fun v => valueMemB v (getSlot doms' n)))).length = (revDoms s).length := by
        rw [revDoms_length, revDoms_length]
        show ((s.doms.setIfInBounds n
          (sparseNarrow (fun v => valueMemB v (getSlot doms' n))
            (s.doms.getD n default))).toList).length = s.doms.toList.length
        have hsz : (s.doms.setIfInBounds n
            (sparseNarrow (fun v => valueMemB v (getSlot doms' n))
              (s.doms.getD n default))).size = s.doms.size :=
          Array.size_setIfInBounds
        have hlen1 : ((s.doms.setIfInBounds n
            (sparseNarrow (fun v => valueMemB v (getSlot doms' n))
              (s.doms.getD n default))).toList).length =
            (s.doms.setIfInBounds n
              (sparseNarrow (fun v => valueMemB v (getSlot doms' n))
                (s.doms.getD n default))).size := by simp
        have hlen2 : s.doms.toList.length = s.doms.size := by simp
        omega
      -- the subset survives the step
      have hsub' : DomPointwiseSub doms'
          (revDoms (revNarrow s n (fun v => valueMemB v (getSlot doms' n)))) := by
        refine ⟨hsub.1.trans hlenEq.symm, ?_⟩
        intro k x hx
        rw [getSlot_revDoms]
        by_cases hk : k = n
        · rw [hk, hview]
          rw [hk] at hx
          have hxn : x ∈ revGet s n := by
            rw [← getSlot_revDoms s n]
            exact hsub.2 n x hx
          exact List.mem_filter.mpr ⟨hxn, valueMemB_iff.mpr hx⟩
        · rw [revGet_revNarrow_of_ne s n k _ (fun hc => hk hc)]
          have hx2 := hsub.2 k x hx
          rw [getSlot_revDoms s k] at hx2
          exact hx2
      -- the fuel (n+1) step narrows slot n, then the fuel-n tail runs on the rest
      rw [show revNarrowFrom s doms' (n + 1) =
          revNarrowFrom (revNarrow s n (fun v => valueMemB v (getSlot doms' n)))
            doms' n from rfl]
      obtain ⟨ih1, ih2⟩ := ih (revNarrow s n (fun v => valueMemB v (getSlot doms' n)))
        (revNarrow_valid _ _ _ hs) hsub'
      constructor
      · -- slots below n+1: slot n is finalized by this step
        intro i v hi
        by_cases hcase : i = n
        · rw [hcase, ih2 n v (Nat.le_refl n), hview]
          exact hsetmem v
        · exact ih1 i v (by omega)
      · -- slots at or above n+1: untouched
        intro i v hle
        rw [ih2 i v (by omega)]
        have hne : revGet (revNarrow s n
            (fun v => valueMemB v (getSlot doms' n))) i = revGet s i :=
          revGet_revNarrow_of_ne s n i _ (fun hc => by omega)
        rw [hne]

/-- The result of one propagation round on the reversible state. -/
inductive RevPropResult where
  /-- The pass narrowed; the carried state's logical view agrees
      with the list-level pass's output (membership, per slot). -/
  | narrowed (s' : RevState)
  /-- The pass found a certified contradiction. -/
  | contradiction
  deriving Repr

/-- **One round-robin propagation pass on the reversible state**:
materialize the logical views (`revDoms s`), run the verified
list-level `propPass`, and apply the narrowed domains back onto
the sparse state slot by slot (`revNarrowFrom` with the
narrowed-domains membership as the keep predicate).  On
`contradiction` the pass fails. -/
def revPropPass (s : RevState) (props : List (List (List Value) → PropResult)) :
    RevPropResult :=
  match propPass props (revDoms s) with
  | .contradiction => .contradiction
  | .narrowed doms' => .narrowed (revNarrowFrom s doms' doms'.length)

/-- **The propagation-pass refinement**: if the pass on the
reversible state narrows, then the list-level pass on the
materialized logical view narrows to some `doms'`, and the
reversible state's logical view agrees with `doms'` slot by slot
(membership) — running the propagators on the sparse state
computes the same logical domains as running them on lists. -/
theorem revPropPass_refines {s : RevState} (hsv : RevState.Valid s)
    {props : List (List (List Value) → PropResult)} (hn : AllNarrowOnly props)
    {s' : RevState} (h : revPropPass s props = .narrowed s') :
    ∃ doms', propPass props (revDoms s) = .narrowed doms' ∧
      s' = revNarrowFrom s doms' doms'.length ∧
      (∀ (i : Nat) (v : Value) (hi : i < doms'.length),
          v ∈ revGet s' i ↔ v ∈ getSlot doms' i) := by
  simp only [revPropPass] at h
  cases hp : propPass props (revDoms s) with
  | contradiction =>
      rw [hp] at h
      exact absurd h (by intro hcon; cases hcon)
  | narrowed doms' =>
      -- the pass narrowed; the carried state is the slot-by-slot application
      have hs' : s' = revNarrowFrom s doms' doms'.length := by
        rw [hp] at h
        exact (RevPropResult.narrowed.inj h).symm
      have hsub : DomPointwiseSub doms' (revDoms s) := propPass_subset props hn
        (revDoms s) doms' hp
      have href := revNarrowFrom_refines doms' doms'.length s hsv hsub |>.1
      refine ⟨doms', rfl, hs', fun (i : Nat) (v : Value) (hi : i < doms'.length) =>
        (Iff.trans (show v ∈ revGet s' i ↔ v ∈
            revGet (revNarrowFrom s doms' doms'.length) i from
          hs' ▸ Iff.rfl)
          (href i v hi))⟩

/-- A `contradiction` on the reversible state is a `contradiction`
of the list-level pass on the same logical view. -/
theorem revPropPass_contradicts {s : RevState}
    {props : List (List (List Value) → PropResult)}
    (h : revPropPass s props = .contradiction) :
    propPass props (revDoms s) = .contradiction := by
  simp only [revPropPass] at h
  cases hp : propPass props (revDoms s) with
  | contradiction => rfl
  | narrowed doms' =>
      rw [hp] at h
      exact absurd h (by
        intro hcon
        cases hcon)

end LeanFzn.Solver
