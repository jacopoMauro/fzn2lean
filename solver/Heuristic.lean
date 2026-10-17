import solver.Search

/-!
# Correctness-neutral search heuristics (PLAN.md 6.5)

PLAN 6.5 adds heuristics "only after exhaustive search is proved",
beginning with minimum remaining values (MRV), and requires that they
"choose only the order of an otherwise exhaustive branch partition".
This module implements exactly that: heuristic search is *permutation
composition* with the proved reference search, not a new algorithm.

* `selectSlots order slots` reorders the slot list: position `p` of
  the reordered problem is slot `order[p]` of the original;
* `unpermute order b` maps an assignment of the reordered problem back
  to original slot order: position `i` reads the value `b` gives to the
  position where `order` places slot `i`;
* `heuristicSearch leaf order slots` runs the *unchanged reference
  `search`* on the reordered slots — with the leaf predicate conjugated
  by `unpermute` so that assignments are judged in original slot
  order — and unpermutes the result.

The central result is the branch-coverage lemma of PLAN 6.5 in this
setting, stated as `unpermute_mem_allAssigns_iff`: when `order` is an
admissible permutation of the slot indices (`IsPerm`), an assignment
satisfies the original slots exactly when it is the unpermute of an
assignment of the reordered slots.  The reordered branch partition
covers the same complete assignments as the original one.  With it,
both master theorems of the reference search transfer without any new
induction over the search:

* `heuristicSearch_some`: a returned assignment (already in original
  slot order) is a complete assignment of the slots and passes the
  leaf predicate;
* `heuristicSearch_none`: `none` means every complete assignment of
  the slots fails the leaf predicate;
* `heuristicSearch_none_iff`: the heuristic search returns `none`
  exactly when the reference search does, so it accepts exactly the
  instances the reference search accepts.

On top of the permuted plumbing sit two concrete selectors, which are
correctness-neutral by construction because they only produce the
`order`:

* `lexOrder n` — the identity (reference) order `List.range n`;
* `mrvOrder slots` — minimum-remaining-values: slot indices sorted by
  ascending domain size, ties by ascending index (a stable insertion
  sort on `(size, index)` pairs).  `mrvOrder_isPerm` proves the result
  really is a permutation of the slot indices, so MRV inherits the
  master theorems through `mrvSearch` and its corollaries.

The `unpermute`/`permMap` plumbing is generic over any inhabited value
type (the pointwise slot lookups need a default value; the theorems
never depend on which default is chosen).
-/

namespace LeanFzn.Solver

/-! ## Basic facts about `List.getD`

Index lookups with a default are the workhorse of the pointwise
membership style below: they avoid threading proof terms for index
bounds through every statement. -/

/-- Looking up an in-bounds index never falls back to the default. -/
private theorem getD_of_lt {α : Type} {l : List α} {i : Nat} (d : α)
    (h : i < l.length) : l.getD i d = l[i]'h := by
  have h1 : l[i]? = some (l[i]'h) := List.getElem?_eq_some_iff.mpr ⟨h, rfl⟩
  show (l[i]?.getD d) = l[i]'h
  rw [h1, Option.getD_some]

/-- Looking up an index of a mapped list applies the function to the
    looked-up element (the inner fallback is irrelevant in bounds). -/
private theorem getD_map {α β : Type} (f : α → β) (l : List α) (q : Nat) (d : β) (d' : α)
    (h : q < l.length) : (l.map f).getD q d = f (l.getD q d') := by
  have h1 : q < (l.map f).length := by rw [List.length_map]; exact h
  rw [getD_of_lt d h1, getD_of_lt d' h, List.getElem_map]

/-- Looking up an in-bounds position of the canonical index list. -/
private theorem range_getD {m i : Nat} (d : Nat) (h : i < m) :
    (List.range m).getD i d = i := by
  have h1 : (List.range m)[i]? = some i := List.getElem?_range h
  show ((List.range m)[i]?.getD d) = i
  rw [h1, Option.getD_some]

/-! ## Admissible orders

An `order` guides the heuristic search: position `p` of the reordered
slot list is slot `order[p]` of the original list.  Such an order is
admissible when it names every slot index exactly once — most
conveniently, when it is a permutation of the canonical index list
`List.range n`, from which length, membership and range facts all
follow in one line each. -/

/-- `order` is an admissible branching order for `n` slots: a
    permutation of the canonical index list `List.range n`, i.e. it
    names every slot index exactly once. -/
def IsPerm (order : List Nat) (n : Nat) : Prop :=
  order.Perm (List.range n)

/-- An admissible order has exactly `n` entries. -/
theorem isPerm_length {order : List Nat} {n : Nat} (h : IsPerm order n) :
    order.length = n :=
  (List.Perm.length_eq h).trans List.length_range

/-- An admissible order contains every slot index. -/
theorem isPerm_mem {order : List Nat} {n : Nat} (h : IsPerm order n) {i : Nat}
    (hi : i < n) : i ∈ order :=
  (List.Perm.mem_iff h).mpr (List.mem_range.mpr hi)

/-- An admissible order contains no index outside the slot range. -/
theorem isPerm_lt_length {order : List Nat} {n : Nat} (h : IsPerm order n) {i : Nat}
    (hi : i ∈ order) : i < n :=
  List.mem_range.mp ((List.Perm.mem_iff h).mp hi)

/-- An admissible order contains every slot index exactly once (the
    count view of `IsPerm`, convenient for sanity checks). -/
theorem isPerm_count {order : List Nat} {n : Nat} (h : IsPerm order n) {i : Nat}
    (hi : i < n) : order.count i = 1 := by
  rw [h.count_eq i, List.count_range, if_pos hi]

/-- For an admissible order, every slot index `i < n` occurs at some
    position of `order`. -/
theorem isPerm_idxOf_lt {order : List Nat} {n : Nat} (h : IsPerm order n) {i : Nat}
    (hi : i < n) : order.idxOf i < order.length := by
  have hmem : i ∈ order := isPerm_mem h hi
  have hfind : order.idxOf i = order.findIdx (fun x => x == i) := rfl
  rw [hfind]
  exact List.findIdx_lt_length.mpr ⟨i, hmem, by simp⟩

/-- The position where an admissible order places slot `i` indeed
    holds slot `i` (default-free lookup form). -/
theorem isPerm_order_idxOf {order : List Nat} {n : Nat} (h : IsPerm order n) {i : Nat}
    (hi : i < n) : order.getD (order.idxOf i) 0 = i := by
  have hq : order.idxOf i < order.length := isPerm_idxOf_lt h hi
  have h1 : order[order.idxOf i]? = some i :=
    List.getElem?_eq_some_iff.mpr ⟨hq, List.getElem_idxOf hq⟩
  show (order[order.idxOf i]?.getD 0) = i
  rw [h1, Option.getD_some]

/-! ## Reordering the slots -/

/-- The slot list visited by the heuristic search: position `p` is
    slot `order[p]` of `slots` (the empty list for out-of-range
    indices, which admissible orders never produce). -/
def selectSlots {α : Type} (order : List Nat) (slots : List (List α)) :
    List (List α) :=
  order.map (fun i => slots.getD i [])

/-- Pointwise lookup into a reordered slot list. -/
private theorem selectSlots_getD {α : Type} (order : List Nat) (slots : List (List α))
    {q : Nat} (hq : q < order.length) :
    (selectSlots order slots).getD q [] = slots.getD (order.getD q 0) [] := by
  have hdef : (selectSlots order slots).getD q []
      = ((order.map (fun i => slots.getD i [])).getD q []) := rfl
  rw [hdef, getD_map (fun i => slots.getD i []) order q [] 0 hq]

/-- The forward spread of an assignment through an order: position
    `p` holds the value the assignment gives to slot `order[p]`. -/
def permMap {α : Type} [Inhabited α] (order : List Nat) (a : List α) : List α :=
  order.map (fun i => a.getD i default)

/-- Pointwise lookup into a spread assignment. -/
private theorem permMap_getD {α : Type} [Inhabited α] (order : List Nat) (a : List α)
    {q : Nat} (hq : q < order.length) :
    (permMap order a).getD q default = a.getD (order.getD q 0) default := by
  have hdef : (permMap order a).getD q default
      = ((order.map (fun i => a.getD i default)).getD q default) := rfl
  rw [hdef, getD_map (fun i => a.getD i default) order q default 0 hq]

/-- Map an assignment of the reordered slots back to original slot
    order: position `i` of the result holds the value the assignment
    gives to the position where `order` places slot `i`.  For
    admissible orders this inverts `permMap`.  The compiled code
    runs the inverse-table twin (`unpermuteI`, defined below with
    its equality theorem `unpermuteI_eq`). -/
def unpermute {α : Type} [Inhabited α] (order : List Nat) (b : List α) : List α :=
  (List.range order.length).map (fun i => b.getD (order.idxOf i) default)

/-- Pointwise lookup into an unpermuted assignment. -/
private theorem unpermute_getD {α : Type} [Inhabited α] (order : List Nat) (b : List α)
    {i : Nat} (hi : i < order.length) :
    (unpermute order b).getD i default = b.getD (order.idxOf i) default := by
  have hdef : (unpermute order b).getD i default
      = (((List.range order.length).map
          (fun j => b.getD (order.idxOf j) default)).getD i default) := rfl
  have h1 : i < (List.range order.length).length := by
    rw [List.length_range]; exact hi
  rw [hdef, getD_map (fun j => b.getD (order.idxOf j) default)
    (List.range order.length) i default 0 h1, range_getD 0 hi]

/-! ## The fast unpermute twin (IDEAS 1.3)

`unpermute` looks up `order.idxOf i` for every position `i` — a
linear scan per element, so the leaf conjugation is O(n²) per call.
The fast twin precomputes the inverse permutation *once per search*
and then maps `b.getD` over it:

* `invPosList order` builds the position list — position `i` holds
  the position where `order` places slot `i` (a `setIfInBounds`
  fold over `order.zipIdx`, O(n) array writes) — logically
  characterized by `invPosList_getElem?`;
* `unpermuteFast pos b` maps `b.getD · default` over the
  precomputed positions — O(n) per leaf, no `idxOf` scans;
* `unpermuteFast_eq` connects the two on the *same* arguments: with
  `pos = invPosList order`, the fast twin is the reference
  `unpermute order b`, so the caller may compute `pos` once and
  reuse it for every leaf of a search. -/

/-- The position list of an order: an array fold writing, for every
    position `p` of `order`, the value `p` at index `order[p]` — the
    inverse permutation as a lookup table (out-of-range indices keep
    the sentinel `order.length`, matching `idxOf`'s
    not-found value). -/
def invPosList (order : List Nat) : List Nat :=
  (order.zipIdx.foldl (fun A ip => A.setIfInBounds ip.1 ip.2)
    (Array.replicate order.length order.length)).toList

/-- The writes performed by the inverse-position fold. -/
private def foldSets (l : List (Nat × Nat)) (A : Array Nat) : Array Nat :=
  l.foldl (fun B ip => B.setIfInBounds ip.1 ip.2) A

/-- The fold behind `invPosList` is `foldSets` on the indexed
    order. -/
private theorem invPosList_eq_foldSets (order : List Nat) :
    invPosList order = (foldSets order.zipIdx
      (Array.replicate order.length order.length)).toList := rfl

/-- A fold step that does not write `j` preserves `[j]?`. -/
private theorem foldSets_getElem?_of_not_mem {l : List (Nat × Nat)}
    {A : Array Nat} {j : Nat}
    (h : ∀ p, (j, p) ∉ l) : (foldSets l A)[j]? = A[j]? := by
  induction l generalizing A with
  | nil => rfl
  | cons ip rest ih =>
      have hj : ip.1 ≠ j := fun heq => h ip.2 (by
        have hmem : (ip.1, ip.2) ∈ ip :: rest := List.mem_cons_self
        rw [heq] at hmem
        exact hmem)
      have hrest : ∀ p, (j, p) ∉ rest := fun p hmem =>
        h p (List.mem_cons_of_mem _ hmem)
      show (foldSets rest (A.setIfInBounds ip.1 ip.2))[j]? = A[j]?
      rw [ih hrest, Array.getElem?_setIfInBounds]
      by_cases hcase : ip.1 = j
      · exact absurd hcase hj
      · simp [hcase]

/-- The write fold preserves the array size (every `setIfInBounds`
    does). -/
private theorem foldSets_size (l : List (Nat × Nat)) (A : Array Nat) :
    (foldSets l A).size = A.size := by
  induction l generalizing A with
  | nil => rfl
  | cons ip rest ih =>
      show (foldSets rest (A.setIfInBounds ip.1 ip.2)).size = A.size
      rw [ih, Array.size_setIfInBounds]

/-- The head of a cons writes its first component (membership
    helper). -/
private theorem mem_cons_of_fst_eq {ip : Nat × Nat} {rest : List (Nat × Nat)}
    {j : Nat} (h : ip.1 = j) : (j, ip.2) ∈ ip :: rest := by
  have hip : ip = (j, ip.2) := Prod.ext h rfl
  rw [hip]
  exact List.mem_cons_self

/-- An in-bounds `setIfInBounds` write reads back. -/
private theorem setIfInBounds_getElem?_self {A : Array Nat} {j v : Nat}
    (hlt : j < A.size) : (A.setIfInBounds j v)[j]? = some v := by
  rw [Array.getElem?_setIfInBounds, if_pos rfl, if_pos hlt]

/-- A current `some v` at `j` survives a fold whose writes to `j`
    all write `v`. -/
private theorem foldSets_getElem?_preserve {l : List (Nat × Nat)}
    {A : Array Nat} {j v : Nat}
    (hcur : A[j]? = some v)
    (honly : ∀ p, (j, p) ∈ l → p = v) :
    (foldSets l A)[j]? = some v := by
  induction l generalizing A with
  | nil => exact hcur
  | cons ip rest ih =>
      have honlyrest : ∀ p, (j, p) ∈ rest → p = v :=
        fun p hmemr => honly p (List.mem_cons_of_mem _ hmemr)
      by_cases hcase : ip.1 = j
      · have hv : ip.2 = v := honly ip.2 (mem_cons_of_fst_eq hcase)
        have hlt : j < A.size := by
          by_cases hclt : j < A.size
          · exact hclt
          · rw [Array.getElem?_eq_none_iff.mpr (by omega)] at hcur
            exact absurd hcur (by simp)
        have hstep : (A.setIfInBounds ip.1 ip.2)[j]? = some v := by
          rw [hcase, hv]
          exact setIfInBounds_getElem?_self hlt
        show (foldSets rest (A.setIfInBounds ip.1 ip.2))[j]? = some v
        exact ih hstep honlyrest
      · have hstep : (A.setIfInBounds ip.1 ip.2)[j]? = A[j]? := by
          rw [Array.getElem?_setIfInBounds]
          by_cases hcase2 : ip.1 = j
          · exact absurd hcase2 hcase
          · simp [hcase2]
        show (foldSets rest (A.setIfInBounds ip.1 ip.2))[j]? = some v
        exact ih (hstep.trans hcur) honlyrest

/-- Every position `k` of an indexed order contributes the write
    pair `(order[k], k)`. -/
private theorem mem_zipIdx_of_getElem : ∀ (l : List Nat) (k c : Nat), k < l.length →
    ∃ v, l[k]? = some v ∧ (v, c + k) ∈ l.zipIdx c := by
  intro l
  induction l with
  | nil => intro k c h; exact absurd h (by simp)
  | cons a as ih =>
      intro k c h
      cases k with
      | zero => exact ⟨a, rfl, List.mem_cons_self⟩
      | succ k' =>
          have h' : k' < as.length := by simp at h; omega
          obtain ⟨v, hv, hmem⟩ := ih k' (c + 1) h'
          have harith : c + 1 + k' = c + (k' + 1) := by omega
          rw [harith] at hmem
          exact ⟨v, hv, List.mem_cons_of_mem _ hmem⟩

/-- An in-bounds write wins over the initial table: if some write to
    `j` lands `v` and every write to `j` lands `v`, the fold reads
    `some v` at `j`. -/
private theorem foldSets_getElem?_only {l : List (Nat × Nat)} {A : Array Nat} {j v : Nat}
    (hlt : j < A.size)
    (hmem : (j, v) ∈ l)
    (honly : ∀ p, (j, p) ∈ l → p = v) :
    (foldSets l A)[j]? = some v := by
  induction l generalizing A with
  | nil => exact absurd hmem (by simp)
  | cons ip rest ih =>
      by_cases hcase : ip.1 = j
      · have hv : ip.2 = v := honly ip.2 (mem_cons_of_fst_eq hcase)
        have hstep : (A.setIfInBounds ip.1 ip.2)[j]? = some v := by
          rw [hcase, hv]
          exact setIfInBounds_getElem?_self hlt
        show (foldSets rest (A.setIfInBounds ip.1 ip.2))[j]? = some v
        exact foldSets_getElem?_preserve hstep
          (fun p hmemr => honly p (List.mem_cons_of_mem _ hmemr))
      · have hmem' : (j, v) ∈ rest := by
          rcases List.mem_cons.mp hmem with heq | hin
          · exact absurd (congrArg Prod.fst heq).symm hcase
          · exact hin
        have hlt' : j < (A.setIfInBounds ip.1 ip.2).size := by
          rw [Array.size_setIfInBounds]
          exact hlt
        exact ih hlt' hmem' (fun p hmemr => honly p (List.mem_cons_of_mem _ hmemr))

/-- **The inverse-position table**: for an admissible order,
    position `i < n` of `invPosList order` holds exactly
    `order.idxOf i` — the table agrees with the linear-scan
    definition it replaces. -/
theorem invPosList_getElem? {order : List Nat} {n : Nat}
    (hperm : IsPerm order n) {i : Nat} (hi : i < n) :
    (invPosList order)[i]? = some (order.idxOf i) := by
  have hlen : order.length = n := isPerm_length hperm
  have hmemi : i ∈ order := isPerm_mem hperm hi
  have hi' : i < order.length := by omega
  -- the pair (i, idxOf i) is a write of the fold
  have hwrite : (i, order.idxOf i) ∈ order.zipIdx 0 := by
    have hidx : order.idxOf i < order.length :=
      isPerm_idxOf_lt hperm hi
    obtain ⟨v, hv, hmem⟩ :=
      mem_zipIdx_of_getElem order (order.idxOf i) 0 hidx
    have hvi : v = i := by
      have hget := List.getElem_idxOf (xs := order) (x := i) hidx
      have hsome : order[order.idxOf i]? = some v := hv
      have hopt : order[order.idxOf i]? = some order[order.idxOf i] :=
        List.getElem?_eq_some_iff.mpr ⟨hidx, rfl⟩
      rw [hopt, hget] at hsome
      exact (Option.some.inj hsome).symm
    rw [hvi] at hmem
    have harith : 0 + order.idxOf i = order.idxOf i := Nat.zero_add _
    rwa [harith] at hmem
  -- every other write to i writes the same value (idxOf of a perm element)
  have honly : ∀ p, (i, p) ∈ order.zipIdx 0 → p = order.idxOf i := by
    intro p hmemr
    have hspec := List.mem_zipIdx hmemr
    -- p is a position with order[p] = i
    have hplt : p < order.length := by omega
    have hval : order[p] = i := by
      have hget : i = order[p - 0] := hspec.2.2
      -- `p - 0` is definitionally `p`
      exact hget.symm
    -- an admissible order is nodup, so positions are injective:
    -- idxOf i is a position holding i, and p is one, so they coincide
    have hnodup : order.Nodup := hperm.symm.nodup List.nodup_range
    have hidx : order.idxOf i < order.length :=
      isPerm_idxOf_lt hperm hi
    have hidxval : order[order.idxOf i] = i := List.getElem_idxOf hidx
    exact (List.getElem_inj (xs := order) (h₀ := hplt) (h₁ := hidx) hnodup).mp
      (by rw [hval, hidxval])
  rw [invPosList_eq_foldSets, Array.getElem?_toList]
  have hsize : (Array.replicate order.length order.length).size = order.length :=
    Array.size_replicate
  have hlt : i < (Array.replicate order.length order.length).size := by
    rw [hsize]
    omega
  exact foldSets_getElem?_only (l := order.zipIdx)
    (A := Array.replicate order.length order.length) hlt hwrite honly

/-- The fast unpermute: map the assignment lookup over a
    precomputed position list (the caller computes the positions once
    per search with `invPosList`). -/
def unpermuteFast {α : Type} [Inhabited α] (pos : List Nat) (b : List α) : List α :=
  pos.map (fun j => b.getD j default)

/-- **The fast twin is the reference `unpermute`**: with the
    precomputed position list of an admissible order, mapping
    `b.getD` over the positions is exactly the `idxOf`-scanning
    definition. -/
theorem unpermuteFast_eq {α : Type} [Inhabited α] {order : List Nat} {n : Nat}
    (hperm : IsPerm order n) (b : List α) :
    unpermuteFast (invPosList order) b = unpermute order b := by
  have hlen : order.length = n := isPerm_length hperm
  have hlen' : (List.range order.length).length = order.length := List.length_range
  -- the two lists have the same length (both n)
  have hposlen : (invPosList order).length = order.length := by
    rw [invPosList_eq_foldSets]
    rw [Array.length_toList, foldSets_size, Array.size_replicate]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < n
  · have hi' : i < order.length := by omega
    have h1 : (unpermuteFast (invPosList order) b)[i]? =
        (invPosList order)[i]?.map (fun j => b.getD j default) := by
      rw [show unpermuteFast (invPosList order) b =
        (invPosList order).map (fun j => b.getD j default) from rfl,
        List.getElem?_map]
    rw [h1, invPosList_getElem? hperm hi, Option.map_some]
    have h2 : (unpermute order b)[i]? =
        some (b.getD (order.idxOf i) default) := by
      have hdef : (unpermute order b)[i]?
          = (((List.range order.length).map
              (fun j => b.getD (order.idxOf j) default))[i]?) := rfl
      rw [hdef, List.getElem?_map, List.getElem?_range hi', Option.map_some]
    rw [h2]
  · have h1 : (unpermuteFast (invPosList order) b)[i]? = none := by
      refine List.getElem?_eq_none_iff.mpr ?_
      have hlenfast : (unpermuteFast (invPosList order) b).length
          = (invPosList order).length := by
        simp only [unpermuteFast, List.length_map]
      rw [hlenfast, hposlen]
      omega
    have h2 : (unpermute order b)[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by
        have : (unpermute order b).length = order.length := by
          simp only [unpermute, List.length_map, List.length_range]
        omega)
    rw [h1, h2]

/-- Same-shape fast twin of `unpermute` (the `implemented_by`
    target): builds the inverse-position table and maps over it —
    O(n) per call instead of `unpermute`'s O(n²) `idxOf` scans.  For
    callers that conjugate many leaves with the same order,
    `heuristicSearchFast` hoists the table out of the leaf entirely;
    this twin covers the remaining call sites (e.g. `mrvLeaf`). -/
def unpermuteI {α : Type} [Inhabited α] (order : List Nat) (b : List α) : List α :=
  unpermuteFast (invPosList order) b

/-- The same-shape fast twin is the reference `unpermute` on
    admissible orders (the equality behind the `implemented_by`). -/
theorem unpermuteI_eq {α : Type} [Inhabited α] {order : List Nat} {n : Nat}
    (hperm : IsPerm order n) (b : List α) :
    unpermuteI order b = unpermute order b :=
  unpermuteFast_eq hperm b

-- IDEAS 1.3: the compiled `unpermute` runs the inverse-table twin
-- (equal on admissible orders by `unpermuteI_eq`)
attribute [implemented_by unpermuteI] unpermute

/-! ## A pointwise characterization of `allAssigns`

The single induction of this module: complete assignments are exactly
the length-matching lists picking each value from its own slot.  With
it, the permutation lemmas below are index juggling rather than
structural inductions over `allAssigns`. -/

/-- Membership in `allAssigns`, pointwise: an assignment of the slots
    is a list of the slot count whose position `i` comes from slot
    `i`. -/
private theorem mem_allAssigns_iff {α : Type} [Inhabited α] :
    ∀ (slots : List (List α)) (a : List α),
      a ∈ allAssigns slots ↔
        a.length = slots.length ∧
        ∀ i, i < a.length → a.getD i default ∈ slots.getD i [] := by
  intro slots
  induction slots with
  | nil =>
      intro a
      constructor
      · intro ha
        have ha' : a = [] := List.mem_singleton.mp (by simpa [allAssigns] using ha)
        subst ha'
        exact ⟨rfl, fun _ hi => absurd hi (by simp)⟩
      · intro ⟨hlen, _⟩
        cases a with
        | nil => simp [allAssigns]
        | cons w a' =>
            exact absurd hlen (by simp only [List.length_cons, List.length_nil]; omega)
  | cons d ds ih =>
      intro a
      cases d with
      | nil =>
          have hnone : allAssigns (([] : List α) :: ds) = [] := rfl
          rw [hnone]
          constructor
          · intro hmem
            exact absurd hmem (by simp)
          · intro ⟨hlen, hmem⟩
            have hlen' : a.length = ds.length + 1 := by
              simpa only [List.length_cons] using hlen
            have h0 := hmem 0 (by omega)
            rw [List.getD_cons_zero] at h0
            exact absurd h0 (by simp)
      | cons v vs =>
          constructor
          · intro ha
            rw [mem_allAssigns_singleton] at ha
            obtain ⟨w, hw, a', ha', rfl⟩ := ha
            have ih' := (ih a').mp ha'
            refine ⟨?_, ?_⟩
            · simp only [List.length_cons, ih'.1]
            · intro i hi
              cases i with
              | zero =>
                  rw [List.getD_cons_zero, List.getD_cons_zero]
                  exact hw
              | succ j =>
                  have hj : j < a'.length := by
                    simp only [List.length_cons] at hi; omega
                  rw [List.getD_cons_succ, List.getD_cons_succ]
                  exact ih'.2 j hj
          · rintro ⟨hlen, hmem⟩
            have hlen' : a.length = ds.length + 1 := by
              simpa only [List.length_cons] using hlen
            cases a with
            | nil =>
                simp only [List.length_nil] at hlen'
                exact absurd hlen' (by omega)
            | cons w a' =>
                simp only [List.length_cons] at hlen'
                have hw : w ∈ v :: vs := by
                  have h0 := hmem 0 (by simp only [List.length_cons]; omega)
                  rw [List.getD_cons_zero, List.getD_cons_zero] at h0
                  exact h0
                refine (mem_allAssigns_singleton v vs ds (w :: a')).mpr
                  ⟨w, hw, a', (ih a').mpr ⟨by omega, ?_⟩, rfl⟩
                intro i hi
                have hisucc : i + 1 < (w :: a').length := by
                  simp only [List.length_cons]; omega
                have hv := hmem (i + 1) hisucc
                rw [List.getD_cons_succ, List.getD_cons_succ] at hv
                exact hv

/-! ## The branch-coverage lemma (PLAN 6.5)

Reordering the slots by an admissible order permutes the space of
complete assignments: every assignment of the original slots, spread
through the order, is an assignment of the reordered slots, and every
assignment of the reordered slots unpermutes to an assignment of the
original slots.  Everything is pointwise membership. -/

/-- Every assignment of the original slots, spread through the
    order, is an assignment of the reordered slots. -/
theorem permMap_mem_allAssigns {α : Type} [Inhabited α] (order : List Nat)
    (slots : List (List α)) (hperm : IsPerm order slots.length) {a : List α}
    (ha : a ∈ allAssigns slots) :
    permMap order a ∈ allAssigns (selectSlots order slots) := by
  have hlen : order.length = slots.length := isPerm_length hperm
  obtain ⟨halen, hamem⟩ := (mem_allAssigns_iff slots a).mp ha
  have hpm : (permMap order a).length = order.length := by
    simp only [permMap, List.length_map]
  have hssl : (selectSlots order slots).length = order.length := by
    simp only [selectSlots, List.length_map]
  refine (mem_allAssigns_iff _ _).mpr ⟨?_, ?_⟩
  · rw [hpm, hssl]
  · intro q hq
    have hq' : q < order.length := by rw [hpm] at hq; exact hq
    rw [permMap_getD order a hq', selectSlots_getD order slots hq']
    have hin : order.getD q 0 ∈ order := by
      rw [getD_of_lt 0 hq']
      exact List.getElem_mem hq'
    have hlt : order.getD q 0 < slots.length := isPerm_lt_length hperm hin
    exact hamem (order.getD q 0) (by rw [halen]; exact hlt)

/-- Unpermuting inverts the spread: an assignment of the original
    slots is recovered from its spread through an admissible order. -/
theorem unpermute_permMap {α : Type} [Inhabited α] (order : List Nat)
    (slots : List (List α)) (hperm : IsPerm order slots.length) {a : List α}
    (ha : a ∈ allAssigns slots) : unpermute order (permMap order a) = a := by
  have hlen : order.length = slots.length := isPerm_length hperm
  obtain ⟨halen, _⟩ := (mem_allAssigns_iff slots a).mp ha
  have huplen : (unpermute order (permMap order a)).length = order.length := by
    simp only [unpermute, List.length_map, List.length_range]
  apply List.ext_getElem?
  intro i
  by_cases hi : i < order.length
  · have h1 : (unpermute order (permMap order a))[i]? =
        some ((permMap order a).getD (order.idxOf i) default) := by
      have hdef : (unpermute order (permMap order a))[i]?
          = (((List.range order.length).map
              (fun j => (permMap order a).getD (order.idxOf j) default))[i]?) := rfl
      rw [hdef, List.getElem?_map, List.getElem?_range hi, Option.map_some]
    rw [h1, permMap_getD order a (isPerm_idxOf_lt hperm (by omega)),
      isPerm_order_idxOf hperm (by omega)]
    have hia : i < a.length := by omega
    rw [getD_of_lt default hia]
    exact (List.getElem?_eq_some_iff.mpr ⟨hia, rfl⟩).symm
  · have h1 : (unpermute order (permMap order a))[i]? = none :=
      List.getElem?_eq_none_iff.mpr (by rw [huplen]; omega)
    have h2 : a[i]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [h1, h2]

/-- Every assignment of the reordered slots unpermutes to an
    assignment of the original slots. -/
theorem unpermute_mem_allAssigns {α : Type} [Inhabited α] (order : List Nat)
    (slots : List (List α)) (hperm : IsPerm order slots.length) {b : List α}
    (hb : b ∈ allAssigns (selectSlots order slots)) :
    unpermute order b ∈ allAssigns slots := by
  have hlen : order.length = slots.length := isPerm_length hperm
  have hssl : (selectSlots order slots).length = order.length := by
    simp only [selectSlots, List.length_map]
  obtain ⟨hblen, hmem⟩ := (mem_allAssigns_iff (selectSlots order slots) b).mp hb
  rw [hssl] at hblen
  have huplen : (unpermute order b).length = order.length := by
    simp only [unpermute, List.length_map, List.length_range]
  refine (mem_allAssigns_iff slots _).mpr ⟨?_, ?_⟩
  · rw [huplen, hlen]
  · intro i hi
    have hi' : i < order.length := by rw [huplen] at hi; exact hi
    rw [unpermute_getD order b hi']
    have hq : order.idxOf i < order.length :=
      isPerm_idxOf_lt hperm (by rw [← hlen]; exact hi')
    have hbq := hmem (order.idxOf i) (by rw [hblen]; exact hq)
    rw [selectSlots_getD order slots hq,
      isPerm_order_idxOf hperm (by rw [← hlen]; exact hi')] at hbq
    exact hbq

/-- **The branch-coverage lemma (PLAN 6.5)**: with an admissible
    order, an assignment satisfies the original slots exactly when it
    is the unpermute of an assignment of the reordered slots.  The
    reordered branch partition covers the same complete assignments
    as the original one — a heuristic chooses only their order. -/
theorem unpermute_mem_allAssigns_iff {α : Type} [Inhabited α] (order : List Nat)
    (slots : List (List α)) (hperm : IsPerm order slots.length) (a : List α) :
    a ∈ allAssigns slots ↔
      ∃ b, b ∈ allAssigns (selectSlots order slots) ∧ unpermute order b = a := by
  constructor
  · intro ha
    exact ⟨permMap order a, permMap_mem_allAssigns order slots hperm ha,
      unpermute_permMap order slots hperm ha⟩
  · rintro ⟨b, hb, rfl⟩
    exact unpermute_mem_allAssigns order slots hperm hb

/-! ## The heuristic search -/

/-- Heuristic search by permutation composition: run the reference
    `search` on the slot list reordered by `order`, then map the
    result back to original slot order.  The leaf predicate is
    conjugated by `unpermute` so that the reference search judges
    assignments in *original* slot order — branching order is the
    only difference from `search leaf slots []`.  The compiled code
    runs the precomputed-position twin (`heuristicSearchFast`,
    equal by `heuristicSearchFast_eq` under `IsPerm`). -/
def heuristicSearch {α : Type} [Inhabited α] (leaf : List α → Bool) (order : List Nat)
    (slots : List (List α)) : Option (List α) :=
  (search (fun b => leaf (unpermute order b)) (selectSlots order slots) []).map
    (unpermute order)

/-- The fast twin of `heuristicSearch` (IDEAS 1.3): the inverse
    permutation is precomputed once per search (`invPosList`, an
    O(n) array fold), so every leaf's conjugation and the result
    mapping run in O(n) instead of `unpermute`'s per-element `idxOf`
    scans (O(n²) per leaf call). -/
def heuristicSearchFast {α : Type} [Inhabited α] (leaf : List α → Bool) (order : List Nat)
    (slots : List (List α)) : Option (List α) :=
  let pos := invPosList order
  (search (fun b => leaf (unpermuteFast pos b)) (selectSlots order slots) []).map
    (unpermuteFast pos)

attribute [implemented_by heuristicSearchFast] heuristicSearch

/-- The fast twin is the reference `heuristicSearch` for admissible
    orders: the precomputed positions read back exactly what
    `order.idxOf` computes (IDEAS 1.3's proof obligation). -/
theorem heuristicSearchFast_eq {α : Type} [Inhabited α] (leaf : List α → Bool)
    (order : List Nat) (slots : List (List α)) (hperm : IsPerm order slots.length) :
    heuristicSearchFast leaf order slots = heuristicSearch leaf order slots := by
  have hmap : (unpermuteFast (invPosList order) : List α → List α) = unpermute order := by
    funext b
    rw [unpermuteFast_eq hperm]
  unfold heuristicSearch heuristicSearchFast
  show (search (fun b => leaf (unpermuteFast (invPosList order) b))
      (selectSlots order slots) []).map (unpermuteFast (invPosList order)) =
    (search (fun b => leaf (unpermute order b)) (selectSlots order slots) []).map
      (unpermute order)
  rw [hmap]

/-- **Soundness of a successful heuristic search**: the returned
    assignment (in original slot order) is a complete assignment of
    the slots and passes the leaf predicate. -/
theorem heuristicSearch_some {α : Type} [Inhabited α] (leaf : List α → Bool)
    (order : List Nat) (slots : List (List α)) (hperm : IsPerm order slots.length)
    {r : List α} (hr : heuristicSearch leaf order slots = some r) :
    r ∈ allAssigns slots ∧ leaf r = true := by
  unfold heuristicSearch at hr
  rw [Option.map_eq_some_iff] at hr
  obtain ⟨b, hb, rfl⟩ := hr
  obtain ⟨a, ha, hba, hleaf⟩ :=
    search_some (fun b => leaf (unpermute order b)) (selectSlots order slots) [] b hb
  rw [List.nil_append] at hba hleaf
  have hra : a = b := hba.symm
  subst hra
  exact ⟨unpermute_mem_allAssigns order slots hperm ha, hleaf⟩

/-- **Soundness of an unsuccessful heuristic search**: `none` means
    every complete assignment of the slots fails the leaf predicate. -/
theorem heuristicSearch_none {α : Type} [Inhabited α] (leaf : List α → Bool)
    (order : List Nat) (slots : List (List α)) (hperm : IsPerm order slots.length)
    (hnone : heuristicSearch leaf order slots = none) :
    ∀ a ∈ allAssigns slots, leaf a = false := by
  unfold heuristicSearch at hnone
  rw [Option.map_eq_none_iff] at hnone
  intro a ha
  have hb := permMap_mem_allAssigns order slots hperm ha
  have hinv := unpermute_permMap order slots hperm ha
  have h := search_none (fun b => leaf (unpermute order b)) (selectSlots order slots) []
    hnone (permMap order a) hb
  simpa [List.nil_append, hinv] using h

/-- The heuristic search and the reference search agree on rejection:
    one returns `none` exactly when the other does. -/
theorem heuristicSearch_none_iff {α : Type} [Inhabited α] (leaf : List α → Bool)
    (order : List Nat) (slots : List (List α)) (hperm : IsPerm order slots.length) :
    heuristicSearch leaf order slots = none ↔ search leaf slots [] = none := by
  constructor
  · intro hheur
    unfold heuristicSearch at hheur
    rw [Option.map_eq_none_iff] at hheur
    cases hh : search leaf slots [] with
    | none => rfl
    | some a =>
        obtain ⟨a', ha', _, hleafa⟩ := search_some leaf slots [] a hh
        rw [List.nil_append] at hleafa
        have hb := permMap_mem_allAssigns order slots hperm ha'
        have hinv := unpermute_permMap order slots hperm ha'
        have h := search_none (fun b => leaf (unpermute order b))
          (selectSlots order slots) [] hheur (permMap order a') hb
        have h' : leaf a' = false := by simpa [List.nil_append, hinv] using h
        rw [hleafa] at h'
        exact absurd h' (by simp)
  · intro href
    unfold heuristicSearch
    cases hh : search (fun b => leaf (unpermute order b)) (selectSlots order slots) [] with
    | none => rfl
    | some b =>
        obtain ⟨a, ha, hba, hleaf⟩ := search_some (fun b => leaf (unpermute order b))
          (selectSlots order slots) [] b hh
        rw [List.nil_append] at hba hleaf
        have hab : a = b := hba.symm
        rw [hab] at ha hleaf
        have hleaf' : leaf (unpermute order b) = true := by simpa using hleaf
        have hup := unpermute_mem_allAssigns order slots hperm ha
        have h := search_none leaf slots [] href (unpermute order b) hup
        have h' : leaf (unpermute order b) = false := by simpa [List.nil_append] using h
        rw [hleaf'] at h'
        exact absurd h' (by simp)

/-! ## Concrete selectors

The selectors are correctness-neutral by construction: they only
produce the `order`, and each comes with a proof that its order is
admissible. -/

/-- The identity (reference) order: branch on the slots left to
    right, exactly like the reference search. -/
def lexOrder (n : Nat) : List Nat := List.range n

/-- The identity order is admissible. -/
theorem lexOrder_isPerm (n : Nat) : IsPerm (lexOrder n) n :=
  List.Perm.refl (List.range n)

/-- MRV comparison: slot `i` comes before slot `j` when its domain is
    smaller, ties broken by smaller index (stability). -/
private def mrvLt {α : Type} (slots : List (List α)) (i j : Nat) : Bool :=
  decide ((slots.getD i []).length < (slots.getD j []).length)
  || (decide ((slots.getD i []).length = (slots.getD j []).length) && decide (i < j))

/-- One stable insertion step (insert before the first entry the
    comparison places after `x`). -/
private def insertSlot (lt : Nat → Nat → Bool) (x : Nat) : List Nat → List Nat
  | [] => [x]
  | y :: ys => if lt x y = true then x :: y :: ys else y :: insertSlot lt x ys

/-- Insertion sort over the slot indices. -/
private def sortSlots (lt : Nat → Nat → Bool) : List Nat → List Nat
  | [] => []
  | x :: xs => insertSlot lt x (sortSlots lt xs)

/-- Insertion permutes the input list (regardless of the
    comparison). -/
private theorem perm_insertSlot (lt : Nat → Nat → Bool) (x : Nat) :
    ∀ l : List Nat, (insertSlot lt x l).Perm (x :: l) := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons y ys ih =>
      show (if lt x y = true then x :: y :: ys else y :: insertSlot lt x ys).Perm (x :: y :: ys)
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons y ih).trans (List.Perm.swap x y ys)

/-- Sorting permutes the input list (regardless of the
    comparison). -/
private theorem perm_sortSlots (lt : Nat → Nat → Bool) :
    ∀ l : List Nat, (sortSlots lt l).Perm l := by
  intro l
  induction l with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      show (insertSlot lt x (sortSlots lt xs)).Perm (x :: xs)
      exact (perm_insertSlot lt x (sortSlots lt xs)).trans (List.Perm.cons x ih)

/-- Minimum-remaining-values slot selection: the slot indices sorted
    by ascending domain size, ties by ascending index.  Branching in
    this order changes only which slot the search splits on next. -/
def mrvOrder {α : Type} (slots : List (List α)) : List Nat :=
  sortSlots (mrvLt slots) (List.range slots.length)

/-- The MRV order is admissible: it really is a permutation of the
    slot indices, so MRV inherits the master theorems. -/
theorem mrvOrder_isPerm {α : Type} (slots : List (List α)) :
    IsPerm (mrvOrder slots) slots.length :=
  perm_sortSlots (mrvLt slots) (List.range slots.length)

/-- Heuristic search with MRV slot selection. -/
def mrvSearch {α : Type} [Inhabited α] (leaf : List α → Bool) (slots : List (List α)) :
    Option (List α) :=
  heuristicSearch leaf (mrvOrder slots) slots

/-- **Soundness of a successful MRV search**: the returned assignment
    is a complete assignment of the slots and passes the leaf
    predicate. -/
theorem mrvSearch_some {α : Type} [Inhabited α] (leaf : List α → Bool)
    (slots : List (List α)) {r : List α} (hr : mrvSearch leaf slots = some r) :
    r ∈ allAssigns slots ∧ leaf r = true :=
  heuristicSearch_some leaf (mrvOrder slots) slots (mrvOrder_isPerm slots) hr

/-- **Soundness of an unsuccessful MRV search**: `none` means every
    complete assignment of the slots fails the leaf predicate. -/
theorem mrvSearch_none {α : Type} [Inhabited α] (leaf : List α → Bool)
    (slots : List (List α)) (hnone : mrvSearch leaf slots = none) :
    ∀ a ∈ allAssigns slots, leaf a = false :=
  heuristicSearch_none leaf (mrvOrder slots) slots (mrvOrder_isPerm slots) hnone

/-- The MRV search and the reference search agree on rejection. -/
theorem mrvSearch_none_iff {α : Type} [Inhabited α] (leaf : List α → Bool)
    (slots : List (List α)) :
    mrvSearch leaf slots = none ↔ search leaf slots [] = none :=
  heuristicSearch_none_iff leaf (mrvOrder slots) slots (mrvOrder_isPerm slots)

end LeanFzn.Solver
