import LeanFzn.Semantics.Globals.Common
import LeanFzn.Semantics.Globals.AllDiffCounting
open LeanFzn.Semantics


/-!
# Set-related and mathematical global constraints

Mathematical interpretations (`setMathInterp`) and executable Boolean
twins (`setMathInterpB`) for the set-related and mathematical families
of global constraints of the pinned MiniZinc 2.10.0 FlatZinc tree:

set family — `fzn_disjoint`, `fzn_set_member`, `fzn_partition_set`,
`fzn_at_most1`, `fzn_array_set_union`, `fzn_array_set_intersect`;
math family — `fzn_sum_set`, `fzn_sum_pred`, `fzn_range`, `fzn_roots`,
`fzn_array_int_union`, `fzn_sliding_sum`, `fzn_sliding_among_int`,
`fzn_sliding_among_bool`.

Each predicate name gets a per-name agreement theorem `<name>_iff`
proving that the Boolean twin is `true` exactly when the mathematical
interpretation holds, following the `lexSortInterp` pattern of
`LexSort.lean` and the `allDiffInterp` pattern of `AllDiffCounting.lean`.

Semantics per the MiniZinc 2.10.0 handbook, Sections 4.2.2.7
("Set-related constraints"), 4.2.2.5 ("Counting constraints":
`at_most1`, `sliding_among`) and 4.2.2.8 ("Mathematical constraints"),
and per the pinned `share/minizinc/std/fzn_*.mzn` decompositions:

* `disjoint` — "Requires that sets s and t do not intersect."
* `set_member` — member overload 5: "Requires that y occurs in the
  set x" (arguments in the order (x, y) = (set, element)).
* `partition_set` — "Constrains the sets in array xs to partition the
  univ": pairwise disjoint with union equal to the univ
  (`fzn_partition_set.mzn`: `all_disjoint(xs) /\ univ ==
  array_union (i in index_set(xs)) (xs[i])`).
* `at_most1` — "Requires that each pair of sets in xs overlap in at
  most one element" (`fzn_at_most1.mzn`):
  `forall (i, j in index_set(xs) where i < j)
     (card(xs[i] intersect xs[j]) <= 1)`.
  Note: this is overlap of at most one element per pair, which is
  weaker than pairwise disjointness.
* `sum_set` — "Requires that the sum of the weights weights[i1]..
  weights[iN] equals total, where values[i1]..values[iN] are the
  elements appearing in set selected" (`fzn_sum_set.mzn`):
  `total == sum (j in index_set(values)) ((values[j] in selected) *
  weights[j])`.
* `sum_pred` — "Requires that the sum of coefficients[i1]..
  coefficients[iN] equals total, where i1..iN are the elements of the
  idx-th set in sets" (`fzn_sum_pred.mzn`): `sums[idx] = total` with
  `sums[j] = sum (k in sets[j]) (coefficients[k])`; the elements of
  `sets[j]` are interpreted as 1-based indices into `coefficients`.
* `range` — "Requires that the image of function xs (represented as
  an array) on set of values domain is image" (1-based positions).
* `roots` — "Requires that xs[i] in image for all i in preimage, i.e.
  preimage is the set of indices i for which xs[i] is in image"
  (1-based positions; `fzn_roots.mzn` additionally constrains every
  `i` with `xs[i] in image` to lie in `preimage`, making `preimage`
  exactly that index set).
* `array_int_union` — "Constrain y to be the set of the elements in
  x" (`fzn_array_int_union.mzn`).
* `array_set_union` — "Constrain z to be the union of the elements in
  x" (`fzn_array_set_union.mzn`; empty array: the empty set).
* `array_set_intersect` — "Constrain z to be the intersection of the
  elements in x. False if x is empty"
  (`fzn_array_set_intersect.mzn`).
* `sliding_sum` — "Requires that in each subsequence xs[i], …,
  xs[i + window_size - 1] the sum of the values belongs to the interval
  [low, up]".
* `sliding_among` — "Every subsequence of xs of length window_size has
  at least low and at most up occurrences of the values in values"
  (int) / "of the value value" (bool); per
  `fzn_sliding_among_int.mzn` / `fzn_sliding_among_bool.mzn`, the
  array is mapped to 0/1 indicators before applying `sliding_sum`.

All FlatZinc arrays are 1-based; the interpretations below work on
the decoded 0-based Lean lists with a `+1`/`-1` shift where positions
appear in the semantics.  Decoding a wrong argument shape yields
`False` (interpretation) / `false` (twin).

The interpretive decisions specific to this family (`at_most1` as
overlap ≤ 1 rather than disjointness, the empty-array corner cases of
`array_set_union`/`array_set_intersect`, the index-based reading of
`sum_pred`, the exactness of `range`/`roots`, and vacuous
non-positive window sizes for the sliding predicates) are recorded
in `specification/flatzinc_specification_assumptions.md`, G21–G22.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.SetMath

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Globals.AllDiffCounting LeanFzn.Semantics.Evaluation

/-! ## Typed argument decoders -/

/-- Decode `[.setOfInt s, .setOfInt t]`. -/
private def twoSets (args : List Value) : Option (IntSetValue × IntSetValue) :=
  match args with
  | [.setOfInt s, .setOfInt t] => some (s, t)
  | _ => none

/-- Decode `[.setOfInt s, .int i]` (`fzn_set_member(x, y)`: set first). -/
private def setAndInt (args : List Value) : Option (IntSetValue × Int) :=
  match args with
  | [.setOfInt s, .int i] => some (s, i)
  | _ => none

/-- Decode `[.array xs, .setOfInt u]` (array of var sets, par set). -/
private def setArrAndSet (args : List Value) : Option (List IntSetValue × IntSetValue) :=
  match args with
  | [.array xs, .setOfInt u] =>
      match valueSets xs with
      | some ss => some (ss, u)
      | none => none
  | _ => none

/-- Decode `[.array a, .setOfInt s]` (array of var int, var set). -/
private def intArrAndSet (args : List Value) : Option (List Int × IntSetValue) :=
  match args with
  | [.array a, .setOfInt s] =>
      match valueInts a with
      | some xs => some (xs, s)
      | none => none
  | _ => none

/-- Decode `[.array a, .setOfInt s]` (array of var sets, var set). -/
private def setArrAndOneSet (args : List Value) : Option (List IntSetValue × IntSetValue) :=
  match args with
  | [.array a, .setOfInt s] =>
      match valueSets a with
      | some xs => some (xs, s)
      | none => none
  | _ => none

/-- Decode `[.array a, .array b, .setOfInt s, .int t]`
    (`fzn_sum_set(values, weights, selected, total)`). -/
private def sumSetArgs (args : List Value) :
    Option (List Int × List Int × IntSetValue × Int) :=
  match args with
  | [.array a, .array b, .setOfInt s, .int t] =>
      match valueInts a, valueInts b with
      | some vs, some ws => some (vs, ws, s, t)
      | _, _ => none
  | _ => none

/-- Decode `[.int idx, .array a, .array b, .int t]`
    (`fzn_sum_pred(idx, sets, coefficients, total)`). -/
private def sumPredArgs (args : List Value) :
    Option (Int × List IntSetValue × List Int × Int) :=
  match args with
  | [.int idx, .array a, .array b, .int t] =>
      match valueSets a, valueInts b with
      | some ss, some cs => some (idx, ss, cs, t)
      | _, _ => none
  | _ => none

/-- Decode `[.array a, .setOfInt s1, .setOfInt s2]`
    (`fzn_range(xs, domain, image)`, `fzn_roots(xs, preimage, image)`). -/
private def intArrSetSet (args : List Value) :
    Option (List Int × IntSetValue × IntSetValue) :=
  match args with
  | [.array a, .setOfInt s1, .setOfInt s2] =>
      match valueInts a with
      | some xs => some (xs, s1, s2)
      | none => none
  | _ => none

/-- Decode `[.int l, .int u, .int w, .array a]`
    (`fzn_sliding_sum(low, up, window_size, xs)`). -/
private def slidingSumArgs (args : List Value) :
    Option (Int × Int × Int × List Int) :=
  match args with
  | [.int l, .int u, .int w, .array a] =>
      match valueInts a with
      | some xs => some (l, u, w, xs)
      | none => none
  | _ => none

/-- Decode `[.int l, .int u, .int w, .array a, .setOfInt S]`
    (`fzn_sliding_among_int(low, up, window_size, xs, values)`). -/
private def slidingAmongIntArgs (args : List Value) :
    Option (Int × Int × Int × List Int × IntSetValue) :=
  match args with
  | [.int l, .int u, .int w, .array a, .setOfInt S] =>
      match valueInts a with
      | some xs => some (l, u, w, xs, S)
      | none => none
  | _ => none

/-- Decode `[.int l, .int u, .int w, .array a, .bool b]`
    (`fzn_sliding_among_bool(low, up, window_size, xs, value)`). -/
private def slidingAmongBoolArgs (args : List Value) :
    Option (Int × Int × Int × List Bool × Bool) :=
  match args with
  | [.int l, .int u, .int w, .array a, .bool b] =>
      match valueBools a with
      | some xs => some (l, u, w, xs, b)
      | none => none
  | _ => none

/-! ## Small bridges -/

private theorem optBne_iff {a b : Option Int} : (a != b) = true ↔ a ≠ b := by
  cases a <;> cases b <;> simp_all

/-- 1-based lookup in a list; `none` unless `1 ≤ i ≤ length`. -/
private def at1 {α : Type} (l : List α) (i : Int) : Option α :=
  if 1 ≤ i then l[i.toNat - 1]? else none

/-! ## fzn_disjoint -/

/-- `fzn_disjoint(s, t)`: the sets share no element. -/
def disjointProp (s t : IntSetValue) : Prop :=
  ∀ k, ¬ (s.Contains k ∧ t.Contains k)

/-- Boolean twin of `disjointProp`. -/
def disjointB (s t : IntSetValue) : Bool :=
  setDisjB s t && setDisjB t s

theorem disjointB_iff (s t : IntSetValue) :
    disjointB s t = true ↔ disjointProp s t := by
  unfold disjointB
  rw [Bool.and_eq_true, setDisjB_iff, setDisjB_iff]
  constructor
  · rintro ⟨h1, h2⟩ k ⟨hk1, hk2⟩
    exact h1 k hk1 hk2
  · intro h
    exact ⟨fun k hk hk2 => h k ⟨hk, hk2⟩, fun k hk hk2 => h k ⟨hk2, hk⟩⟩

/-! ## fzn_set_member -/

/-- `fzn_set_member(x, y)`: `y` occurs in the set `x`. -/
def setMemberProp (x : IntSetValue) (y : Int) : Prop :=
  x.Contains y

/-- Boolean twin of `setMemberProp`. -/
def setMemberB (x : IntSetValue) (y : Int) : Bool :=
  setMemB x y

theorem setMemberB_iff (x : IntSetValue) (y : Int) :
    setMemberB x y = true ↔ setMemberProp x y :=
  setMemB_iff

/-! ## fzn_partition_set -/

/-- `fzn_partition_set(xs, univ)`: the sets are pairwise disjoint
    and their union is `univ`: every `xs[i]` is included in
    `univ` and every element of `univ` is in some `xs[i]`. -/
def partitionSetProp (xs : List IntSetValue) (univ : IntSetValue) : Prop :=
  (∀ i j : Nat, i < j → j < xs.length →
    ∀ k, ¬ (xs[i]!.Contains k ∧ xs[j]!.Contains k)) ∧
  (∀ i : Nat, i < xs.length → ∀ k, xs[i]!.Contains k → univ.Contains k) ∧
  (∀ k, univ.Contains k → ∃ i : Nat, i < xs.length ∧ xs[i]!.Contains k)

/-- Boolean twin of `partitionSetProp`. -/
def partitionSetB (xs : List IntSetValue) (univ : IntSetValue) : Bool :=
  allDisjointB xs &&
  ((List.range xs.length).all (fun i =>
    (setElems xs[i]!).all (fun k => setMemB univ k))) &&
  ((setElems univ).all (fun k =>
    (List.range xs.length).any (fun i => setMemB xs[i]! k)))

theorem partitionSetB_iff (xs : List IntSetValue) (univ : IntSetValue) :
    partitionSetB xs univ = true ↔ partitionSetProp xs univ := by
  constructor
  · intro h
    unfold partitionSetB at h
    rw [Bool.and_eq_true, Bool.and_eq_true] at h
    obtain ⟨⟨hdisj, hsub⟩, hcov⟩ := h
    refine ⟨(allDisjointB_iff xs).mp hdisj, ?_, ?_⟩
    · intro i _ k hk
      have himem : k ∈ setElems xs[i]! := setElems_mem_iff.mp hk
      have hall := List.all_eq_true.mp hsub i (List.mem_range.mpr (by omega))
      exact setMemB_iff.mp ((List.all_eq_true.mp hall) k himem)
    · intro k hk
      have himem : k ∈ setElems univ := setElems_mem_iff.mp hk
      obtain ⟨i', hi', hmem⟩ :=
        List.any_eq_true.mp ((List.all_eq_true.mp hcov) k himem)
      simp only [List.mem_range] at hi'
      exact ⟨i', hi', setMemB_iff.mp hmem⟩
  · intro h
    obtain ⟨hdisj, hsub, hcov⟩ := h
    show ((allDisjointB xs && _) && _) = true
    rw [Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨⟨(allDisjointB_iff xs).mpr hdisj, List.all_eq_true.mpr ?_⟩,
      List.all_eq_true.mpr ?_⟩
    · intro i hi
      simp only [List.mem_range] at hi
      refine List.all_eq_true.mpr ?_
      intro k hk
      exact setMemB_iff.mpr (hsub i hi k (setElems_mem_iff.mpr hk))
    · intro k hk
      obtain ⟨i', hi', hmem⟩ := hcov k (setElems_mem_iff.mpr hk)
      exact List.any_eq_true.mpr ⟨i', List.mem_range.mpr hi', setMemB_iff.mpr hmem⟩

/-! ## fzn_at_most1 -/

/-- Shared elements of two sets (each shared element occurs once per
    occurrence in `a`'s element list). -/
private def sharedElems (a b : IntSetValue) : List Int :=
  (setElems a).filter (fun k => setMemB b k)

/-- `fzn_at_most1(xs)`: each pair of sets in `xs` (with distinct
    positions `i < j`) overlaps in at most one element. -/
def atMost1Prop (xs : List IntSetValue) : Prop :=
  ∀ i j : Nat, i < j → j < xs.length → (sharedElems xs[j]! xs[i]!).length ≤ 1

/-- Boolean twin of `atMost1Prop`: for each pair of positions `i2`
    and the smaller `j2 < i2`, the shared-element list of `xs[i2]!`
    and `xs[j2]!` has length ≤ 1. -/
def atMost1B (xs : List IntSetValue) : Bool :=
  (List.range xs.length).all (fun i2 =>
    (List.range i2).all (fun j2 =>
      decide ((sharedElems xs[i2]! xs[j2]!).length ≤ 1)))

theorem atMost1B_iff (xs : List IntSetValue) :
    atMost1B xs = true ↔ atMost1Prop xs := by
  constructor
  · intro h i j hij hjlen
    have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hjlen)
    have h2 : decide ((sharedElems xs[j]! xs[i]!).length ≤ 1) = true :=
      List.all_eq_true.mp h1 i (List.mem_range.mpr hij)
    exact of_decide_eq_true h2
  · intro h
    refine List.all_eq_true.mpr ?_
    intro i2 hi2
    simp only [List.mem_range] at hi2
    refine List.all_eq_true.mpr ?_
    intro j2 hj2
    simp only [List.mem_range] at hj2
    exact decide_eq_true (h j2 i2 hj2 (by omega))

/-! ## fzn_sum_set -/

/-- `fzn_sum_set(values, weights, selected, total)`: `total` is the sum
    of `weights[j]` over all 1-based positions `j` with
    `values[j] ∈ selected`. -/
def sumSetProp (values weights : List Int) (selected : IntSetValue) (total : Int) : Prop :=
  total = (((values.zip weights).filter
    (fun q => setMemB selected q.1)).map (fun q => q.2)).sum

/-- Boolean twin of `sumSetProp`. -/
def sumSetB (values weights : List Int) (selected : IntSetValue) (total : Int) : Bool :=
  decide (total = (((values.zip weights).filter
    (fun q => setMemB selected q.1)).map (fun q => q.2)).sum)

theorem sumSetB_iff (values weights : List Int) (selected : IntSetValue) (total : Int) :
    sumSetB values weights selected total = true ↔
      sumSetProp values weights selected total :=
  decide_eq_true_iff

/-! ## fzn_sum_pred -/

/-- The coefficients at the 1-based indices `ks` (out-of-range
    indices dropped), duplicates included. -/
private def coeffsAt (cs : List Int) (ks : List Int) : List Int :=
  ((ks.filter (fun k => decide (1 ≤ k ∧ k ≤ (cs.length : Int)))).map
    (fun k => cs[k.toNat - 1]!))

/-- `fzn_sum_pred(idx, sets, coefficients, total)`: `total` is the sum
    of `coefficients[k]` over the elements `k` of the `idx`-th set of
    `sets`, the elements being 1-based indices into `coefficients`
    (out-of-range indices contribute nothing); `idx` out of range
    makes the constraint false. -/
def sumPredProp (idx : Int) (sets : List IntSetValue) (coefficients : List Int)
    (total : Int) : Prop :=
  match at1 sets idx with
  | none => False
  | some s => total = (coeffsAt coefficients (setElems s)).sum

/-- Boolean twin of `sumPredProp`. -/
def sumPredB (idx : Int) (sets : List IntSetValue) (coefficients : List Int)
    (total : Int) : Bool :=
  match at1 sets idx with
  | none => false
  | some s => decide (total = (coeffsAt coefficients (setElems s)).sum)

theorem sumPredB_iff (idx : Int) (sets : List IntSetValue) (coefficients : List Int)
    (total : Int) :
    sumPredB idx sets coefficients total = true ↔
      sumPredProp idx sets coefficients total := by
  cases h : at1 sets idx with
  | none => simp [sumPredB, sumPredProp, h]
  | some s =>
    simp only [sumPredB, sumPredProp, h]
    exact decide_eq_true_iff

/-! ## fzn_range -/

/-- `fzn_range(xs, domain, image)`: `image` is the image of `xs` on
    `domain` (1-based positions): for every `k`,
    `image.Contains k ↔ ∃ i : Nat, i < xs.length ∧
    domain.Contains (i + 1) ∧ xs[i]! = k`. -/
def rangeProp (xs : List Int) (domain image : IntSetValue) : Prop :=
  ∀ k, image.Contains k ↔
    ∃ i : Nat, i < xs.length ∧ domain.Contains ((i : Int) + 1) ∧ xs[i]! = k

/-- Boolean twin of `rangeProp`: every element of `image` is hit by
    some position in `domain`, and every position in `domain` maps
    into `image`. -/
def rangeB (xs : List Int) (domain image : IntSetValue) : Bool :=
  (setElems image).all (fun k =>
    (List.range xs.length).any (fun i =>
      decide (domain.Contains ((i : Int) + 1) ∧ xs[i]! = k)))
  &&
  (setElems domain).all (fun i =>
    (!(decide (1 ≤ i ∧ i ≤ xs.length))) ||
      (setElems image).any (fun k => decide (xs[i.toNat - 1]! = k)))

theorem rangeB_iff (xs : List Int) (domain image : IntSetValue) :
    rangeB xs domain image = true ↔ rangeProp xs domain image := by
  constructor
  · intro h
    unfold rangeB at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro k
    constructor
    · intro hk
      obtain ⟨i, himem, hdec⟩ :=
        List.any_eq_true.mp ((List.all_eq_true.mp h1) k (setElems_mem_iff.mp hk))
      simp only [List.mem_range] at himem
      obtain ⟨hdom, rfl⟩ := of_decide_eq_true hdec
      exact ⟨i, himem, hdom, rfl⟩
    · rintro ⟨i, hi, hdom, rfl⟩
      have hposnat : (((i : Int) + 1).toNat - 1) = i := by omega
      have hall := (List.all_eq_true.mp h2) ((i : Int) + 1) (setElems_mem_iff.mp hdom)
      rw [hposnat] at hall
      have hbounds : (1 ≤ (i : Int) + 1 ∧ (i : Int) + 1 ≤ xs.length) := by omega
      cases hor : ((setElems image).any (fun k => xs[i]! = k)) with
      | true =>
          have hall' : ((setElems image).any (fun k => xs[i]! = k)) = true := hor
          obtain ⟨k, hk, hkeq⟩ := List.any_eq_true.mp hall'
          have hkeq' : xs[i]! = k := of_decide_eq_true hkeq
          rw [hkeq']
          exact setElems_mem_iff.mpr hk
      | false =>
          rw [hor, Bool.or_false] at hall
          have hneg : (!(decide (1 ≤ (i : Int) + 1 ∧ (i : Int) + 1 ≤ xs.length))) = true :=
            hall
          rw [Bool.not_eq_true'] at hneg
          have hcon : ¬ (1 ≤ (i : Int) + 1 ∧ (i : Int) + 1 ≤ xs.length) := by
            simpa using hneg
          omega
  · intro h
    unfold rangeB
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr ?_, List.all_eq_true.mpr ?_⟩
    · intro k hk
      obtain ⟨i, hi, hdom, hkeq⟩ := (h k).mp (setElems_mem_iff.mpr hk)
      rw [← hkeq]
      exact List.any_eq_true.mpr
        ⟨i, List.mem_range.mpr hi, decide_eq_true ⟨hdom, rfl⟩⟩
    · intro i hi
      by_cases hbounds : 1 ≤ i ∧ i ≤ xs.length
      · obtain ⟨hlo, hhi⟩ := hbounds
        have hdom : domain.Contains i := setElems_mem_iff.mpr hi
        have hcn : (((i : Int) - 1).toNat : Int) + 1 = i := by omega
        have hidx : ((i : Int) - 1).toNat < xs.length := by omega
        have hdom' : domain.Contains ((((i : Int) - 1).toNat : Int) + 1) := by
          rw [hcn]; exact hdom
        have hmem : image.Contains xs[((i : Int) - 1).toNat]! :=
          (h xs[((i : Int) - 1).toNat]!).mpr
            ⟨((i : Int) - 1).toNat, hidx, hdom', rfl⟩
        have heq : ((i : Int) - 1).toNat = i.toNat - 1 := by omega
        rw [Bool.or_eq_true]
        refine Or.inr ?_
        rw [← heq]
        exact List.any_eq_true.mpr
          ⟨xs[((i : Int) - 1).toNat]!, setElems_mem_iff.mp hmem,
            decide_eq_true rfl⟩
      · have hout : ¬ (1 ≤ i ∧ i ≤ xs.length) := hbounds
        show ((!decide (1 ≤ i ∧ i ≤ xs.length) ||
            (setElems image).any (fun k => decide (xs[i.toNat - 1]! = k))) = true)
        rw [Bool.or_eq_true]
        by_cases hin : (decide (1 ≤ i ∧ i ≤ xs.length)) = false
        · rw [Bool.not_eq_true'] at *
          exact Or.inl hin
        · exfalso
          have hcon : (decide (1 ≤ i ∧ i ≤ xs.length)) = true := by
            cases hdec : (decide (1 ≤ i ∧ i ≤ xs.length)) with
            | true => rfl
            | false => exact absurd hdec hin
          rw [decide_eq_true_iff] at hcon
          exact hout hcon

/-! ## fzn_roots -/

/-- `fzn_roots(xs, preimage, image)`: `preimage` is exactly the set of
    1-based positions `i` with `xs[i] ∈ image`: for every `k`,
    `preimage.Contains k ↔ 1 ≤ k ∧ k ≤ xs.length ∧
    image.Contains xs[k.toNat - 1]!`. -/
def rootsProp (xs : List Int) (preimage image : IntSetValue) : Prop :=
  ∀ k, preimage.Contains k ↔
    (1 ≤ k ∧ k ≤ xs.length ∧ image.Contains xs[k.toNat - 1]!)

/-- Boolean twin of `rootsProp`: every element of `preimage` is a valid
    position mapping into `image`, and every position mapping into
    `image` lies in `preimage`. -/
def rootsB (xs : List Int) (preimage image : IntSetValue) : Bool :=
  (setElems preimage).all (fun k =>
    decide (1 ≤ k ∧ k ≤ xs.length ∧ image.Contains xs[k.toNat - 1]!))
  &&
  (List.range xs.length).all (fun i =>
    (!decide (image.Contains xs[i]!) || setMemB preimage ((i : Int) + 1)))

theorem rootsB_iff (xs : List Int) (preimage image : IntSetValue) :
    rootsB xs preimage image = true ↔ rootsProp xs preimage image := by
  constructor
  · intro h
    unfold rootsB at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro k
    constructor
    · intro hk
      exact of_decide_eq_true ((List.all_eq_true.mp h1) k (setElems_mem_iff.mp hk))
    · intro ⟨hlo, hhi, himg⟩
      have himem : (k.toNat - 1) ∈ List.range xs.length := by
        simp only [List.mem_range]
        omega
      have hall := (List.all_eq_true.mp h2) (k.toNat - 1) himem
      rw [Bool.or_eq_true, Bool.not_eq_true'] at hall
      have hdec : (decide (image.Contains xs[k.toNat - 1]!)) = true :=
        decide_eq_true himg
      rw [hdec] at hall
      rcases hall with hfalse | hmem
      · exfalso
        exact absurd hfalse (by simp)
      · have hres : preimage.Contains (((k.toNat - 1 : Nat) : Int) + 1) :=
          setMemB_iff.mp hmem
        have hkp : (((k.toNat - 1 : Nat) : Int) + 1) = k := by omega
        rw [hkp] at hres
        exact hres
  · intro h
    unfold rootsB
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr ?_, List.all_eq_true.mpr ?_⟩
    · intro k hk
      exact decide_eq_true ((h k).mp (setElems_mem_iff.mpr hk))
    · intro i hi
      simp only [List.mem_range] at hi
      by_cases himg : image.Contains xs[i]!
      · have hmem : preimage.Contains ((i : Int) + 1) :=
          (h ((i : Int) + 1)).mpr ⟨by omega, by omega, himg⟩
        show ((!decide (image.Contains xs[i]!) || setMemB preimage ((i : Int) + 1))) = true
        rw [Bool.or_eq_true, Bool.not_eq_true']
        rw [decide_eq_true himg]
        exact Or.inr (setMemB_iff.mpr hmem)
      · show ((!decide (image.Contains xs[i]!) || setMemB preimage ((i : Int) + 1))) = true
        rw [Bool.or_eq_true, Bool.not_eq_true']
        rw [decide_eq_false_iff_not.mpr himg]
        exact Or.inl rfl

/-! ## fzn_array_int_union -/

/-- `fzn_array_int_union(x, y)`: `y` is the set of the elements in
    `x` (1-based positions): for every `k`,
    `y.Contains k ↔ ∃ i : Nat, i < x.length ∧ x[i]! = k`. -/
def arrayIntUnionProp (x : List Int) (y : IntSetValue) : Prop :=
  ∀ k, y.Contains k ↔ ∃ i : Nat, i < x.length ∧ x[i]! = k

/-- Boolean twin of `arrayIntUnionProp`: every element of `y` occurs
    in `x`, and every element of `x` lies in `y`. -/
def arrayIntUnionB (x : List Int) (y : IntSetValue) : Bool :=
  (setElems y).all (fun k => (List.range x.length).any (fun i => x[i]! == k))
  && (List.range x.length).all (fun i => (setElems y).contains (x[i]!))

theorem arrayIntUnionB_iff (x : List Int) (y : IntSetValue) :
    arrayIntUnionB x y = true ↔ arrayIntUnionProp x y := by
  constructor
  · intro h
    unfold arrayIntUnionB at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro k
    constructor
    · intro hk
      obtain ⟨i, himem, hbeq⟩ :=
        List.any_eq_true.mp ((List.all_eq_true.mp h1) k (setElems_mem_iff.mp hk))
      simp only [List.mem_range] at himem
      simp only [beq_iff_eq] at hbeq
      exact ⟨i, himem, hbeq⟩
    · rintro ⟨i, hi, rfl⟩
      have hmem : (setElems y).contains x[i]! = true :=
        (List.all_eq_true.mp h2) i (List.mem_range.mpr hi)
      rw [List.contains_iff_mem] at hmem
      exact setElems_mem_iff.mpr hmem
  · intro h
    unfold arrayIntUnionB
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr ?_, List.all_eq_true.mpr ?_⟩
    · intro k hk
      obtain ⟨i, hi, hkeq⟩ := (h k).mp (setElems_mem_iff.mpr hk)
      rw [← hkeq]
      exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, by simp⟩
    · intro i hi
      simp only [List.mem_range] at hi
      show ((setElems y).contains x[i]!) = true
      rw [List.contains_iff_mem]
      exact setElems_mem_iff.mp ((h x[i]!).mpr ⟨i, hi, rfl⟩)

/-! ## fzn_array_set_union -/

/-- `fzn_array_set_union(x, z)`: `z` is the union of the sets in `x`
    (empty array: the empty set). -/
def arraySetUnionProp (x : List IntSetValue) (z : IntSetValue) : Prop :=
  ∀ k, z.Contains k ↔ ∃ i : Nat, i < x.length ∧ x[i]!.Contains k

/-- Boolean twin of `arraySetUnionProp`. -/
def arraySetUnionB (x : List IntSetValue) (z : IntSetValue) : Bool :=
  (setElems z).all (fun k =>
    (List.range x.length).any (fun i => setMemB x[i]! k))
  && (List.range x.length).all (fun i =>
    (setElems x[i]!).all (fun k => setMemB z k))

theorem arraySetUnionB_iff (x : List IntSetValue) (z : IntSetValue) :
    arraySetUnionB x z = true ↔ arraySetUnionProp x z := by
  constructor
  · intro h
    unfold arraySetUnionB at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    intro k
    constructor
    · intro hk
      obtain ⟨i, himem, hmem⟩ :=
        List.any_eq_true.mp ((List.all_eq_true.mp h1) k (setElems_mem_iff.mp hk))
      simp only [List.mem_range] at himem
      exact ⟨i, himem, setMemB_iff.mp hmem⟩
    · rintro ⟨i, hi, hk⟩
      have hall := (List.all_eq_true.mp h2) i (List.mem_range.mpr hi)
      exact setMemB_iff.mp ((List.all_eq_true.mp hall) k (setElems_mem_iff.mp hk))
  · intro h
    unfold arraySetUnionB
    rw [Bool.and_eq_true]
    refine ⟨List.all_eq_true.mpr ?_, List.all_eq_true.mpr ?_⟩
    · intro k hk
      obtain ⟨i, hi, hmem⟩ := (h k).mp (setElems_mem_iff.mpr hk)
      exact List.any_eq_true.mpr ⟨i, List.mem_range.mpr hi, setMemB_iff.mpr hmem⟩
    · intro i hi
      simp only [List.mem_range] at hi
      refine List.all_eq_true.mpr ?_
      intro k hk
      exact setMemB_iff.mpr ((h k).mpr ⟨i, hi, setElems_mem_iff.mpr hk⟩)

/-! ## fzn_array_set_intersect -/

/-- The elements of `x` that lie in every set of `xs`: `k ∈
    interAll x xs ↔ x.Contains k ∧ every set of `xs` contains `k`. -/
private def interAll (x : IntSetValue) : List IntSetValue → IntSetValue
  | [] => x
  | s :: rest => interAll (.enumeration ((setElems x).filter (fun k => setMemB s k))) rest

private theorem mem_filter_setMemB {x s : IntSetValue} {k : Int} :
    k ∈ (setElems x).filter (fun j => setMemB s j) ↔ (x.Contains k ∧ s.Contains k) := by
  constructor
  · intro hk
    obtain ⟨hx, hmem2⟩ := List.mem_filter.mp hk
    exact ⟨setElems_mem_iff.mpr hx, setMemB_iff.mp hmem2⟩
  · rintro ⟨hx, hs⟩
    exact List.mem_filter.mpr ⟨setElems_mem_iff.mp hx, setMemB_iff.mpr hs⟩

private theorem interAll_contains : ∀ (xs : List IntSetValue) (x : IntSetValue) (k : Int),
    (interAll x xs).Contains k ↔
      (x.Contains k ∧ ∀ i : Nat, i < xs.length → xs[i]!.Contains k) := by
  intro xs
  induction xs with
  | nil =>
    intro x k
    constructor
    · intro hk
      refine ⟨hk, ?_⟩
      intro i hi
      have hnp : ¬ (i < ([] : List IntSetValue).length) := by simp
      omega
    · intro hk
      exact hk.1
  | cons s rest ih =>
    intro x k
    have hlen : (s :: rest).length = rest.length + 1 := rfl
    have hnil : (interAll x (s :: rest)).Contains k ↔
        (interAll (IntSetValue.enumeration
          ((setElems x).filter (fun j => setMemB s j))) rest).Contains k :=
      Iff.rfl
    have hfil : (IntSetValue.enumeration
        ((setElems x).filter (fun j => setMemB s j))).Contains k ↔
        (x.Contains k ∧ s.Contains k) := mem_filter_setMemB
    rw [hnil, ih (IntSetValue.enumeration
      ((setElems x).filter (fun j => setMemB s j))) k, hfil]
    constructor
    · rintro ⟨⟨hx, hs⟩, hrest⟩
      refine ⟨hx, ?_⟩
      intro i hi
      by_cases hi0 : i = 0
      · rw [hi0]
        exact hs
      · have hip : i - 1 < rest.length := by omega
        have hget : (s :: rest)[i]! = rest[i - 1]! := by
          match i with
          | 0 => omega
          | (n + 1) =>
            show (s :: rest)[n + 1]! = rest[n]!
            rw [List.getElem!_cons_succ]
        have := hrest (i - 1) hip
        rw [hget]
        exact this
    · intro hx
      refine ⟨⟨hx.1, hx.2 0 (by rw [hlen]; omega)⟩, ?_⟩
      intro i hi
      have hgt : i + 1 < (s :: rest).length := by
        have : (s :: rest).length = rest.length + 1 := rfl
        omega
      have := hx.2 (i + 1) hgt
      have hget : (s :: rest)[i + 1]! = rest[i]! := List.getElem!_cons_succ
      exact hget ▸ this

/-- `fzn_array_set_intersect(x, z)`: `z` is the intersection of the
    sets in `x`; an empty array makes the constraint false (per
    `fzn_array_set_intersect.mzn`: "False if x is empty"). -/
def arraySetIntersectProp (x : List IntSetValue) (z : IntSetValue) : Prop :=
  match x with
  | [] => False
  | _ :: _ => ∀ k, z.Contains k ↔ ∀ i : Nat, i < x.length → x[i]!.Contains k

/-- Boolean twin of `arraySetIntersectProp`: `z` extensionally equals
    the intersection of all sets in `x`; `false` on the empty array. -/
def arraySetIntersectB (x : List IntSetValue) (z : IntSetValue) : Bool :=
  match x with
  | [] => false
  | s :: rest => setEqB (interAll s rest) z

theorem arraySetIntersectB_iff (x : List IntSetValue) (z : IntSetValue) :
    arraySetIntersectB x z = true ↔ arraySetIntersectProp x z := by
  cases x with
  | nil => simp [arraySetIntersectB, arraySetIntersectProp]
  | cons s rest =>
    show setEqB (interAll s rest) z = true ↔
      ∀ k, z.Contains k ↔ ∀ i : Nat, i < (s :: rest).length → (s :: rest)[i]!.Contains k
    have hlen : (s :: rest).length = rest.length + 1 := rfl
    constructor
    · intro h k
      rw [setEqB_iff] at h
      rw [← h k, interAll_contains rest s k]
      constructor
      · rintro ⟨hs, hrest⟩
        intro i hi
        by_cases hi0 : i = 0
        · rw [hi0]
          exact hs
        · have hip : i - 1 < rest.length := by omega
          have hget : (s :: rest)[i]! = rest[i - 1]! := by
            match i with
            | 0 => omega
            | (n + 1) =>
              show (s :: rest)[n + 1]! = rest[n]!
              rw [List.getElem!_cons_succ]
          have := hrest (i - 1) hip
          rw [hget]
          exact this
      · intro hall
        refine ⟨hall 0 (by omega), ?_⟩
        intro i hi
        have hgt : i + 1 < (s :: rest).length := by omega
        have := hall (i + 1) hgt
        have hget : (s :: rest)[i + 1]! = rest[i]! := List.getElem!_cons_succ
        exact hget ▸ this
    · intro h
      rw [setEqB_iff]
      intro k
      rw [interAll_contains rest s k, h k]
      constructor
      · rintro ⟨hs, hrest⟩
        intro i hi
        by_cases hi0 : i = 0
        · rw [hi0]
          exact hs
        · have hip : i - 1 < rest.length := by omega
          have hget : (s :: rest)[i]! = rest[i - 1]! := by
            match i with
            | 0 => omega
            | (n + 1) =>
              show (s :: rest)[n + 1]! = rest[n]!
              rw [List.getElem!_cons_succ]
          have := hrest (i - 1) hip
          rw [hget]
          exact this
      · intro hall
        refine ⟨hall 0 (by omega), ?_⟩
        intro i hi
        have hgt : i + 1 < (s :: rest).length := by omega
        have := hall (i + 1) hgt
        have hget : (s :: rest)[i + 1]! = rest[i]! := List.getElem!_cons_succ
        exact hget ▸ this

/-! ## Sliding window helper -/

/-- Windows of a list: `windowsB l w check` checks `check` on every
    window of `w.toNat` consecutive elements starting at positions
    `p` with `p + w ≤ l.length`; a nonpositive width makes it
    vacuously true (no windows, per the `.mzn` range
    `lx-1..ux-window_size` being empty). -/
private def windowsB {α : Type} (l : List α) (w : Int) (check : List α → Bool) : Bool :=
  if 0 < w then
    (List.range (l.length + 1 - w.toNat)).all
      (fun p => check ((l.drop p).take w.toNat))
  else
    true

private theorem windowsB_iff {α : Type} (l : List α) (w : Int) (check : List α → Bool) :
    windowsB l w check = true ↔
      ∀ p : Nat, (p : Int) + w ≤ l.length → 0 < w →
        check ((l.drop p).take w.toNat) = true := by
  unfold windowsB
  by_cases hw : 0 < w
  · rw [if_pos (by omega)]
    constructor
    · intro h p hp _
      have hlen : p < l.length + 1 - w.toNat := by omega
      have hmem : p ∈ List.range (l.length + 1 - w.toNat) :=
        List.mem_range.mpr hlen
      exact List.all_eq_true.mp h p hmem
    · intro h
      refine List.all_eq_true.mpr ?_
      intro p hp
      have hmem : p < l.length + 1 - w.toNat := List.mem_range.mp hp
      exact h p (by omega) hw
  · rw [if_neg hw]
    constructor
    · intro h p hp hwpos
      exact absurd hwpos hw
    · intro h
      trivial
/-! ## fzn_sliding_sum -/

/-- `fzn_sliding_sum(low, up, window_size, xs)`: the sum of every
    window of `window_size` consecutive elements belongs to
    `[low, up]` (vacuously true if `window_size ≤ 0` — no windows). -/
def slidingSumProp (low up w : Int) (xs : List Int) : Prop :=
  ∀ p : Nat, (p : Int) + w ≤ xs.length → 0 < w →
    low ≤ ((xs.drop p).take w.toNat).sum ∧ ((xs.drop p).take w.toNat).sum ≤ up

/-- Boolean twin of `slidingSumProp`. -/
def slidingSumB (low up w : Int) (xs : List Int) : Bool :=
  windowsB xs w (fun win => decide (low ≤ win.sum ∧ win.sum ≤ up))

theorem slidingSumB_iff (low up w : Int) (xs : List Int) :
    slidingSumB low up w xs = true ↔ slidingSumProp low up w xs := by
  rw [slidingSumB, windowsB_iff]
  constructor
  · intro h p hp hwpos
    exact of_decide_eq_true (h p hp hwpos)
  · intro h p hp hwpos
    exact decide_eq_true (h p hp hwpos)

/-! ## fzn_sliding_among_int -/

/-- `fzn_sliding_among_int(low, up, window_size, xs, values)`: every
    window of `window_size` consecutive elements contains between `low`
    and `up` elements in `values`. -/
def slidingAmongIntProp (low up w : Int) (xs : List Int) (S : IntSetValue) : Prop :=
  ∀ p : Nat, (p : Int) + w ≤ xs.length → 0 < w →
    low ≤ (((xs.drop p).take w.toNat).filter (fun x => setMemB S x)).length ∧
      (((xs.drop p).take w.toNat).filter (fun x => setMemB S x)).length ≤ up

/-- Boolean twin of `slidingAmongIntProp`. -/
def slidingAmongIntB (low up w : Int) (xs : List Int) (S : IntSetValue) : Bool :=
  windowsB xs w (fun win => decide (low ≤ (win.filter (fun x => setMemB S x)).length ∧
    (win.filter (fun x => setMemB S x)).length ≤ up))

theorem slidingAmongIntB_iff (low up w : Int) (xs : List Int) (S : IntSetValue) :
    slidingAmongIntB low up w xs S = true ↔ slidingAmongIntProp low up w xs S := by
  rw [slidingAmongIntB, windowsB_iff]
  constructor
  · intro h p hp hwpos
    exact of_decide_eq_true (h p hp hwpos)
  · intro h p hp hwpos
    exact decide_eq_true (h p hp hwpos)

/-! ## fzn_sliding_among_bool -/

/-- `fzn_sliding_among_bool(low, up, window_size, xs, value)`: every
    window of `window_size` consecutive booleans contains between
    `low` and `up` occurrences of `value`. -/
def slidingAmongBoolProp (low up w : Int) (xs : List Bool) (value : Bool) : Prop :=
  ∀ p : Nat, (p : Int) + w ≤ xs.length → 0 < w →
    low ≤ ((xs.drop p).take w.toNat).count value ∧
      ((xs.drop p).take w.toNat).count value ≤ up

/-- Boolean twin of `slidingAmongBoolProp`. -/
def slidingAmongBoolB (low up w : Int) (xs : List Bool) (value : Bool) : Bool :=
  windowsB xs w (fun win => decide (low ≤ win.count value ∧ win.count value ≤ up))

theorem slidingAmongBoolB_iff (low up w : Int) (xs : List Bool) (value : Bool) :
    slidingAmongBoolB low up w xs value = true ↔
      slidingAmongBoolProp low up w xs value := by
  rw [slidingAmongBoolB, windowsB_iff]
  constructor
  · intro h p hp hwpos
    exact of_decide_eq_true (h p hp hwpos)
  · intro h p hp hwpos
    exact decide_eq_true (h p hp hwpos)

/-! ## The interpretations -/

/-- Mathematical interpretations of the set-related and
    mathematical global-constraint predicates.  A wrong argument shape
    yields `False`. -/
def setMathInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_disjoint" => fun args =>
    match twoSets args with
    | some (s, t) => disjointProp s t
    | none => False
  | "fzn_set_member" => fun args =>
    match setAndInt args with
    | some (s, i) => setMemberProp s i
    | none => False
  | "fzn_partition_set" => fun args =>
    match setArrAndSet args with
    | some (xs, u) => partitionSetProp xs u
    | none => False
  | "fzn_at_most1" => fun args =>
    match oneSetArr args with
    | some xs => atMost1Prop xs
    | none => False
  | "fzn_sum_set" => fun args =>
    match sumSetArgs args with
    | some (vs, ws, sel, tot) => sumSetProp vs ws sel tot
    | none => False
  | "fzn_sum_pred" => fun args =>
    match sumPredArgs args with
    | some (idx, ss, cs, tot) => sumPredProp idx ss cs tot
    | none => False
  | "fzn_range" => fun args =>
    match intArrSetSet args with
    | some (xs, dom, img) => rangeProp xs dom img
    | none => False
  | "fzn_roots" => fun args =>
    match intArrSetSet args with
    | some (xs, pre, img) => rootsProp xs pre img
    | none => False
  | "fzn_array_int_union" => fun args =>
    match intArrAndSet args with
    | some (xs, y) => arrayIntUnionProp xs y
    | none => False
  | "fzn_array_set_union" => fun args =>
    match setArrAndOneSet args with
    | some (xs, z) => arraySetUnionProp xs z
    | none => False
  | "fzn_array_set_intersect" => fun args =>
    match setArrAndOneSet args with
    | some (xs, z) => arraySetIntersectProp xs z
    | none => False
  | "fzn_sliding_sum" => fun args =>
    match slidingSumArgs args with
    | some (l, u, w, xs) => slidingSumProp l u w xs
    | none => False
  | "fzn_sliding_among_int" => fun args =>
    match slidingAmongIntArgs args with
    | some (l, u, w, xs, S) => slidingAmongIntProp l u w xs S
    | none => False
  | "fzn_sliding_among_bool" => fun args =>
    match slidingAmongBoolArgs args with
    | some (l, u, w, xs, b) => slidingAmongBoolProp l u w xs b
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `setMathInterp`**: computes the truth of the
    set-related and mathematical interpretations; `false` on a wrong
    shape. -/
def setMathInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_disjoint" => fun args =>
    match twoSets args with
    | some (s, t) => disjointB s t
    | none => false
  | "fzn_set_member" => fun args =>
    match setAndInt args with
    | some (s, i) => setMemberB s i
    | none => false
  | "fzn_partition_set" => fun args =>
    match setArrAndSet args with
    | some (xs, u) => partitionSetB xs u
    | none => false
  | "fzn_at_most1" => fun args =>
    match oneSetArr args with
    | some xs => atMost1B xs
    | none => false
  | "fzn_sum_set" => fun args =>
    match sumSetArgs args with
    | some (vs, ws, sel, tot) => sumSetB vs ws sel tot
    | none => false
  | "fzn_sum_pred" => fun args =>
    match sumPredArgs args with
    | some (idx, ss, cs, tot) => sumPredB idx ss cs tot
    | none => false
  | "fzn_range" => fun args =>
    match intArrSetSet args with
    | some (xs, dom, img) => rangeB xs dom img
    | none => false
  | "fzn_roots" => fun args =>
    match intArrSetSet args with
    | some (xs, pre, img) => rootsB xs pre img
    | none => false
  | "fzn_array_int_union" => fun args =>
    match intArrAndSet args with
    | some (xs, y) => arrayIntUnionB xs y
    | none => false
  | "fzn_array_set_union" => fun args =>
    match setArrAndOneSet args with
    | some (xs, z) => arraySetUnionB xs z
    | none => false
  | "fzn_array_set_intersect" => fun args =>
    match setArrAndOneSet args with
    | some (xs, z) => arraySetIntersectB xs z
    | none => false
  | "fzn_sliding_sum" => fun args =>
    match slidingSumArgs args with
    | some (l, u, w, xs) => slidingSumB l u w xs
    | none => false
  | "fzn_sliding_among_int" => fun args =>
    match slidingAmongIntArgs args with
    | some (l, u, w, xs, S) => slidingAmongIntB l u w xs S
    | none => false
  | "fzn_sliding_among_bool" => fun args =>
    match slidingAmongBoolArgs args with
    | some (l, u, w, xs, b) => slidingAmongBoolB l u w xs b
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_disjoint_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_disjoint") args = true ↔
      setMathInterp (Ident.mk "fzn_disjoint") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_disjoint") args
      = match twoSets args with
      | some (s, t) => disjointB s t
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_disjoint") args
      = match twoSets args with
      | some (s, t) => disjointProp s t
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoSets args with
  | none => simp
  | some p =>
    obtain ⟨s, t⟩ := p
    simp only
    exact disjointB_iff s t

theorem fzn_set_member_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_set_member") args = true ↔
      setMathInterp (Ident.mk "fzn_set_member") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_set_member") args
      = match setAndInt args with
      | some (s, i) => setMemberB s i
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_set_member") args
      = match setAndInt args with
      | some (s, i) => setMemberProp s i
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : setAndInt args with
  | none => simp
  | some p =>
    obtain ⟨s, i⟩ := p
    simp only
    exact setMemberB_iff s i

theorem fzn_partition_set_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_partition_set") args = true ↔
      setMathInterp (Ident.mk "fzn_partition_set") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_partition_set") args
      = match setArrAndSet args with
      | some (xs, u) => partitionSetB xs u
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_partition_set") args
      = match setArrAndSet args with
      | some (xs, u) => partitionSetProp xs u
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : setArrAndSet args with
  | none => simp
  | some p =>
    obtain ⟨xs, u⟩ := p
    simp only
    exact partitionSetB_iff xs u

theorem fzn_at_most1_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_at_most1") args = true ↔
      setMathInterp (Ident.mk "fzn_at_most1") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_at_most1") args
      = match oneSetArr args with
      | some xs => atMost1B xs
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_at_most1") args
      = match oneSetArr args with
      | some xs => atMost1Prop xs
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : oneSetArr args with
  | none => simp
  | some xs =>
    simp only
    exact atMost1B_iff xs

theorem fzn_sum_set_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_sum_set") args = true ↔
      setMathInterp (Ident.mk "fzn_sum_set") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_sum_set") args
      = match sumSetArgs args with
      | some (vs, ws, sel, tot) => sumSetB vs ws sel tot
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_sum_set") args
      = match sumSetArgs args with
      | some (vs, ws, sel, tot) => sumSetProp vs ws sel tot
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : sumSetArgs args with
  | none => simp
  | some p =>
    obtain ⟨vs, ws, sel, tot⟩ := p
    simp only
    exact sumSetB_iff vs ws sel tot

theorem fzn_sum_pred_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_sum_pred") args = true ↔
      setMathInterp (Ident.mk "fzn_sum_pred") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_sum_pred") args
      = match sumPredArgs args with
      | some (idx, ss, cs, tot) => sumPredB idx ss cs tot
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_sum_pred") args
      = match sumPredArgs args with
      | some (idx, ss, cs, tot) => sumPredProp idx ss cs tot
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : sumPredArgs args with
  | none => simp
  | some p =>
    obtain ⟨idx, ss, cs, tot⟩ := p
    simp only
    exact sumPredB_iff idx ss cs tot

theorem fzn_range_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_range") args = true ↔
      setMathInterp (Ident.mk "fzn_range") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_range") args
      = match intArrSetSet args with
      | some (xs, dom, img) => rangeB xs dom img
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_range") args
      = match intArrSetSet args with
      | some (xs, dom, img) => rangeProp xs dom img
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : intArrSetSet args with
  | none => simp
  | some p =>
    obtain ⟨xs, dom, img⟩ := p
    simp only
    exact rangeB_iff xs dom img

theorem fzn_roots_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_roots") args = true ↔
      setMathInterp (Ident.mk "fzn_roots") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_roots") args
      = match intArrSetSet args with
      | some (xs, pre, img) => rootsB xs pre img
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_roots") args
      = match intArrSetSet args with
      | some (xs, pre, img) => rootsProp xs pre img
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : intArrSetSet args with
  | none => simp
  | some p =>
    obtain ⟨xs, pre, img⟩ := p
    simp only
    exact rootsB_iff xs pre img

theorem fzn_array_int_union_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_array_int_union") args = true ↔
      setMathInterp (Ident.mk "fzn_array_int_union") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_array_int_union") args
      = match intArrAndSet args with
      | some (xs, y) => arrayIntUnionB xs y
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_array_int_union") args
      = match intArrAndSet args with
      | some (xs, y) => arrayIntUnionProp xs y
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : intArrAndSet args with
  | none => simp
  | some p =>
    obtain ⟨xs, y⟩ := p
    simp only
    exact arrayIntUnionB_iff xs y

theorem fzn_array_set_union_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_array_set_union") args = true ↔
      setMathInterp (Ident.mk "fzn_array_set_union") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_array_set_union") args
      = match setArrAndOneSet args with
      | some (xs, z) => arraySetUnionB xs z
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_array_set_union") args
      = match setArrAndOneSet args with
      | some (xs, z) => arraySetUnionProp xs z
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : setArrAndOneSet args with
  | none => simp
  | some p =>
    obtain ⟨xs, z⟩ := p
    simp only
    exact arraySetUnionB_iff xs z

theorem fzn_array_set_intersect_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_array_set_intersect") args = true ↔
      setMathInterp (Ident.mk "fzn_array_set_intersect") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_array_set_intersect") args
      = match setArrAndOneSet args with
      | some (xs, z) => arraySetIntersectB xs z
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_array_set_intersect") args
      = match setArrAndOneSet args with
      | some (xs, z) => arraySetIntersectProp xs z
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : setArrAndOneSet args with
  | none => simp
  | some p =>
    obtain ⟨xs, z⟩ := p
    simp only
    exact arraySetIntersectB_iff xs z

theorem fzn_sliding_sum_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_sliding_sum") args = true ↔
      setMathInterp (Ident.mk "fzn_sliding_sum") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_sliding_sum") args
      = match slidingSumArgs args with
      | some (l, u, w, xs) => slidingSumB l u w xs
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_sliding_sum") args
      = match slidingSumArgs args with
      | some (l, u, w, xs) => slidingSumProp l u w xs
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : slidingSumArgs args with
  | none => simp
  | some p =>
    obtain ⟨l, u, w, xs⟩ := p
    simp only
    exact slidingSumB_iff l u w xs

theorem fzn_sliding_among_int_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_sliding_among_int") args = true ↔
      setMathInterp (Ident.mk "fzn_sliding_among_int") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_sliding_among_int") args
      = match slidingAmongIntArgs args with
      | some (l, u, w, xs, S) => slidingAmongIntB l u w xs S
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_sliding_among_int") args
      = match slidingAmongIntArgs args with
      | some (l, u, w, xs, S) => slidingAmongIntProp l u w xs S
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : slidingAmongIntArgs args with
  | none => simp
  | some p =>
    obtain ⟨l, u, w, xs, S⟩ := p
    simp only
    exact slidingAmongIntB_iff l u w xs S

theorem fzn_sliding_among_bool_iff (args : List Value) :
    setMathInterpB (Ident.mk "fzn_sliding_among_bool") args = true ↔
      setMathInterp (Ident.mk "fzn_sliding_among_bool") args := by
  have hB : ∀ args, setMathInterpB (Ident.mk "fzn_sliding_among_bool") args
      = match slidingAmongBoolArgs args with
      | some (l, u, w, xs, b) => slidingAmongBoolB l u w xs b
      | none => false
      := fun _ => rfl
  have hI : ∀ args, setMathInterp (Ident.mk "fzn_sliding_among_bool") args
      = match slidingAmongBoolArgs args with
      | some (l, u, w, xs, b) => slidingAmongBoolProp l u w xs b
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : slidingAmongBoolArgs args with
  | none => simp
  | some p =>
    obtain ⟨l, u, w, xs, b⟩ := p
    simp only
    exact slidingAmongBoolB_iff l u w xs b

end LeanFzn.Semantics.Globals.SetMath
