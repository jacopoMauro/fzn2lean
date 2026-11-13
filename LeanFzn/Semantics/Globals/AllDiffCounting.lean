import LeanFzn.Semantics.Globals.Common
open LeanFzn.Semantics


/-!
# All-different and counting global constraints

Mathematical interpretations (`allDiffInterp`) and executable Boolean
twins (`allDiffInterpB`) for the all-different family of global
constraints of the pinned MiniZinc 2.10.1 FlatZinc tree:
`fzn_all_different_int`, `fzn_all_different_set`, `fzn_all_disjoint`,
`fzn_all_equal_int`, `fzn_all_equal_set`, `fzn_alldifferent_except`,
`fzn_alldifferent_except_0` and `fzn_symmetric_all_different`.  Each
predicate name gets a per-name agreement theorem `<name>_iff` proving
that the Boolean twin is `true` exactly when the mathematical
interpretation holds, following the `lexSortInterp` pattern of
`LexSort.lean`.

The interpretive decisions specific to this family (extensional set
equality for the set-typed variants, the occurrence-bound reading of
the `except` variants, and the involutive form of
`symmetric_all_different`) are recorded in
`specification/flatzinc_specification_assumptions.md`, G7–G9.

Semantics per the MiniZinc 2.10.1 handbook, Section 4.2.2.1
("All-Different and related constraints"):

* `all_different` — "Constrain the elements in the array xs to be
  pairwise different" (integers; for sets, pairwise extensionally
  different).
* `all_disjoint` — "Constrain the array of sets of integers xs to be
  pairwise disjoint."
* `all_equal` — "Constrain the elements of the array xs to be all
  equal" (integers; for sets, extensionally equal).
* `all_different_except` — "Constrain the elements of the array xs to
  be pairwise different except for those values that appear in the
  set except": for all i < j, xs[i] = xs[j] → xs[i] ∈ S, i.e. every
  value outside `S` occurs at most once.
* `all_different_except_0` — "... pairwise different except for those
  elements that are assigned the value 0": every nonzero value occurs
  at most once.
* `symmetric_all_different` — "Requires the array of integers xs to
  be all different, and for all i, xs[i]=j → xs[j]=i": `xs` is a
  symmetric permutation of `1..n`.

The argument decoders of the counting family (`fzn_nvalue`,
`fzn_among`, `fzn_count_*`, ...) live here as well so the counting
interpretations can reuse them.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.AllDiffCounting

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

/-! ## Small helpers -/

/-- Decode `[.array xs]` into the list of its integers. -/
def oneIntArr (args : List Value) : Option (List Int) :=
  match args with
  | [.array xs] => valueInts xs
  | _ => none

/-- Decode `[.array xs]` into the list of its sets. -/
def oneSetArr (args : List Value) : Option (List IntSetValue) :=
  match args with
  | [.array xs] => valueSets xs
  | _ => none

/-- Decode `[.array xs, .setOfInt except]`. -/
def arrAndSet (args : List Value) : Option (List Int × IntSetValue) :=
  match args with
  | [.array xs, .setOfInt e] =>
      match valueInts xs with
      | some l => some (l, e)
      | none => none
  | _ => none

/-- Decode `[.int n, .array xs]`. -/
def intAndArr (args : List Value) : Option (Int × List Int) :=
  match args with
  | [.int n, .array xs] =>
      match valueInts xs with
      | some l => some (n, l)
      | none => none
  | _ => none

/-- Decode `[.int n, .array xs, .int value]`. -/
def intArrInt (args : List Value) : Option (Int × List Int × Int) :=
  match args with
  | [.int n, .array xs, .int v] =>
      match valueInts xs with
      | some l => some (n, l, v)
      | none => none
  | _ => none

/-- Decode `[.array xs, .int value, .int n]`. -/
def arrIntInt (args : List Value) : Option (List Int × Int × Int) :=
  match args with
  | [.array xs, .int v, .int n] =>
      match valueInts xs with
      | some l => some (l, v, n)
      | none => none
  | _ => none

/-- Decode three int arrays `[.array c, .array cov, .array xs]`. -/
def threeIntArrs (args : List Value) :
    Option (List Int × List Int × List Int) :=
  match args with
  | [.array a, .array b, .array c] =>
      match valueInts a, valueInts b, valueInts c with
      | some la, some lb, some lc => some (la, lb, lc)
      | _, _, _ => none
  | _ => none

/-- Decode `[.array xs, .array cov, .array count]`. -/
def threeIntArrs' (args : List Value) :
    Option (List Int × List Int × List Int) :=
  match args with
  | [.array a, .array b, .array c] =>
      match valueInts a, valueInts b, valueInts c with
      | some la, some lb, some lc => some (la, lb, lc)
      | _, _, _ => none
  | _ => none

/-- Decode `[.array xs, .array cov, .array lo, .array hi]`. -/
def fourIntArrs (args : List Value) :
    Option (List Int × List Int × List Int × List Int) :=
  match args with
  | [.array a, .array b, .array c, .array d] =>
      match valueInts a, valueInts b, valueInts c, valueInts d with
      | some la, some lb, some lc, some ld => some (la, lb, lc, ld)
      | _, _, _, _ => none
  | _ => none

/-- Decode `[.array xs, .setOfInt value, .int n]` for the set-counting
    predicates: sets are decoded as a list, the set value as a set, the
    count as an integer. -/
def setCountArgs (args : List Value) :
    Option (List IntSetValue × IntSetValue × Int) :=
  match args with
  | [.array xs, .setOfInt v, .int n] =>
      match valueSets xs with
      | some ss => some (ss, v, n)
      | none => none
  | _ => none

/-- Decode `[.int n, .array xs, .setOfInt value]`. -/
def atLeastSetArgs (args : List Value) :
    Option (Int × List IntSetValue × IntSetValue) :=
  match args with
  | [.int n, .array xs, .setOfInt v] =>
      match valueSets xs with
      | some ss => some (n, ss, v)
      | none => none
  | _ => none

/-- Positional view of a list of sets: the (0-based) `i`-th set when
    in range. -/
def setAt (ss : List IntSetValue) (i : Nat) : Option IntSetValue := ss[i]?

/-- Positional view of a list of integers: the (0-based) `i`-th
    integer when in range. -/
def intAt (xs : List Int) (i : Nat) : Option Int := xs[i]?

/-! ## Pairwise-distinctness bridge for decoded integer lists

`valuesAllDifferent` (from `FznStdLib`) checks pairwise distinctness
through `Value.eqB`; the all-different predicates are stated over the
*decoded* integer list.  The bridge is:

* `intPairwiseDistinct` (Prop): `∀ v, intCount l v ≤ 1`.
* `intPairwiseDistinctB` (Bool): `valuesAllDifferent (toVals l)`.

Both agree with each other (and hence with `List.Nodup l`, which says
the same thing positionally). -/

/-- Decode a list of integers into a list of values. -/
def toVals : List Int → List Value
  | [] => []
  | x :: xs => .int x :: toVals xs

private theorem toVals_length (l : List Int) : (toVals l).length = l.length := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [toVals, List.length_cons, ih]

private theorem valueInts_toVals (l : List Int) : valueInts (toVals l) = some l := by
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [toVals, valueInts, ih, Option.map_some]

/-- `Value.eqB` on encoded integers is equality of the decoded
    integers. -/
theorem eqB_int_iff {x y : Int} :
    (Value.int x).eqB (Value.int y) = true ↔ x = y := by
  simp only [Value.eqB, beq_iff_eq]

theorem valuesAllDifferent_cons {x : Int} {xs : List Int} :
    valuesAllDifferent (toVals (x :: xs)) = true ↔
      ((toVals xs).any (fun y => (Value.int x).eqB y) = false ∧
        valuesAllDifferent (toVals xs) = true) := by
  simp only [toVals, valuesAllDifferent, Bool.and_eq_true, Bool.not_eq_true']

theorem mem_toVals_iff {y : Value} {xs : List Int} :
    y ∈ toVals xs ↔ ∃ w : Int, w ∈ xs ∧ y = Value.int w := by
  induction xs with
  | nil =>
      simp only [toVals, List.not_mem_nil, false_iff]
      rintro ⟨w, hw, _⟩
      cases hw
  | cons z zs ih =>
      constructor
      · intro hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact ⟨z, List.mem_cons_self, rfl⟩
        · obtain ⟨w, hw, rfl⟩ := ih.mp hy'
          exact ⟨w, List.mem_cons.mpr (Or.inr hw), rfl⟩
      · rintro ⟨w, hw, rfl⟩
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact List.mem_cons_self
        · exact List.mem_cons.mpr (Or.inr (ih.mpr ⟨w, hw', rfl⟩))

/-- The occurrences of `v` in `x :: xs` when the head equals `v`. -/
theorem count_cons_eq {x v : Int} {xs : List Int} (h : x = v) :
    intCount (x :: xs) v = intCount xs v + 1 := by
  rw [intCount, intCount, List.count_cons, h]
  simp

/-- The occurrences of `v` in `x :: xs` when the head differs from `v`. -/
theorem count_cons_ne {x v : Int} {xs : List Int} (h : x ≠ v) :
    intCount (x :: xs) v = intCount xs v := by
  rw [intCount, intCount, List.count_cons]
  simp [h]

/-- Occurrence counts only grow along `::`. -/
theorem intCount_cons_ge {x v : Int} {xs : List Int} :
    intCount xs v ≤ intCount (x :: xs) v := by
  by_cases hxeq : x = v
  · have h1 : intCount (x :: xs) v = intCount xs v + 1 := count_cons_eq hxeq
    omega
  · have h1 : intCount (x :: xs) v = intCount xs v := count_cons_ne hxeq
    omega

/-- Occurrence bounds pass to the tail. -/
theorem count_tail_le_one {x : Int} {xs : List Int}
    (h : ∀ v : Int, intCount (x :: xs) v ≤ 1) : ∀ v : Int, intCount xs v ≤ 1 := by
  intro v
  by_cases hxeq : x = v
  · have h1 : intCount (x :: xs) v = intCount xs v + 1 := count_cons_eq hxeq
    have h2 := h v
    omega
  · have h1 : intCount (x :: xs) v = intCount xs v := count_cons_ne hxeq
    rw [← h1]
    exact h v

/-- The pairwise distinctness of a value list implies the pairwise
    distinctness of its decoded integers, counted by occurrences. -/
private theorem intPairwiseDistinct_of_valuesAllDifferent {l : List Int}
    (h : valuesAllDifferent (toVals l) = true) : ∀ v : Int, intCount l v ≤ 1 := by
  induction l with
  | nil => intro v; exact Nat.zero_le _
  | cons x xs ih =>
    intro v
    rw [valuesAllDifferent_cons] at h
    obtain ⟨hany, hxs⟩ := h
    by_cases hmem : v ∈ xs
    · -- x ≠ v, otherwise the head would duplicate an element of xs
      have hxnv : x ≠ v := by
        intro hcon
        have hany' : ((toVals xs).any fun y => (Value.int x).eqB y) = true :=
          List.any_eq_true.mpr ⟨Value.int v,
            mem_toVals_iff.mpr ⟨v, hmem, rfl⟩, eqB_int_iff.mpr hcon⟩
        rw [hany] at hany'
        simp at hany'
      have hcount : intCount xs v ≤ 1 := ih hxs v
      rw [count_cons_ne hxnv]
      exact hcount
    · have hv : intCount xs v = 0 := by
        unfold intCount
        exact List.count_eq_zero.mpr hmem
      by_cases hxeq : x = v
      · have h1 : intCount (x :: xs) v = intCount xs v + 1 := count_cons_eq hxeq
        omega
      · have h1 : intCount (x :: xs) v = intCount xs v := count_cons_ne hxeq
        omega

private theorem valuesAllDifferent_of_intPairwiseDistinct {l : List Int}
    (h : ∀ v : Int, intCount l v ≤ 1) : valuesAllDifferent (toVals l) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [valuesAllDifferent_cons]
    refine ⟨?_, ih (count_tail_le_one h)⟩
    cases hany : (toVals xs).any (fun y => (Value.int x).eqB y) with
    | false => rfl
    | true =>
        rw [List.any_eq_true] at hany
        obtain ⟨y, hy, hyeq⟩ := hany
        obtain ⟨w, hw, rfl⟩ := mem_toVals_iff.mp hy
        rw [eqB_int_iff] at hyeq
        -- x = w and w ∈ xs, so x has a second occurrence in xs
        have hcount : intCount (x :: xs) x ≥ 2 := by
          have h1 : intCount (x :: xs) x = intCount xs x + 1 := count_cons_eq rfl
          have hmem : x ∈ xs := hyeq ▸ hw
          have hpos : 0 < intCount xs x := List.count_pos_iff.mpr hmem
          omega
        have := h x
        omega

theorem intPairwiseDistinctB_iff (l : List Int) :
    valuesAllDifferent (toVals l) = true ↔ ∀ v : Int, intCount l v ≤ 1 := by
  constructor
  · exact intPairwiseDistinct_of_valuesAllDifferent
  · exact valuesAllDifferent_of_intPairwiseDistinct

/-- The fast sort-based twin agrees with the count-based
    distinctness. -/
theorem intPairwiseDistinctB_fast_iff (l : List Int) :
    intsAllDifferentFast l = true ↔ ∀ v : Int, intCount l v ≤ 1 :=
  ⟨fun h => List.nodup_iff_count.mp ((intsAllDifferentFast_iff l).mp h),
   fun h => (intsAllDifferentFast_iff l).mpr (List.nodup_iff_count.mpr h)⟩

/-! ## Except-0 bridge -/

private theorem eqB_int0_false_iff {x : Int} :
    (Value.int x).eqB (Value.int 0) = false ↔ x ≠ 0 := by
  have hdec : (Value.int x).eqB (Value.int 0) = decide (x = 0) := rfl
  rw [hdec]
  simp [decide_eq_false_iff_not]

private theorem not_eqB_int0_true_iff {x : Int} :
    (!(Value.int x).eqB (Value.int 0)) = true ↔ x ≠ 0 := by
  rw [Bool.not_eq_true']
  exact eqB_int0_false_iff

private theorem valuesAllDiffExcept0_cons {x : Int} {xs : List Int} :
    valuesAllDifferentExcept0 (toVals (x :: xs)) = true ↔
      (((toVals xs).any (fun y =>
        !((Value.int x).eqB (Value.int 0)) &&
         !(y.eqB (Value.int 0)) && (Value.int x).eqB y)) = false ∧
        valuesAllDifferentExcept0 (toVals xs) = true) := by
  show valuesAllDifferentExcept0 (Value.int x :: toVals xs) = true ↔ ?_
  rw [show valuesAllDifferentExcept0 (Value.int x :: toVals xs) =
    (!(((toVals xs).any (fun y =>
        !((Value.int x).eqB (Value.int 0)) &&
         !(y.eqB (Value.int 0)) && (Value.int x).eqB y)))
         && valuesAllDifferentExcept0 (toVals xs)) from rfl,
    Bool.and_eq_true, Bool.not_eq_true']

private theorem count_of_valuesAllDifferentExcept0 {l : List Int}
    (h : valuesAllDifferentExcept0 (toVals l) = true) :
    ∀ v : Int, v ≠ 0 → intCount l v ≤ 1 := by
  induction l with
  | nil => intro v _; exact Nat.zero_le _
  | cons x xs ih =>
    intro v hv
    rw [valuesAllDiffExcept0_cons] at h
    obtain ⟨hany, hxs⟩ := h
    by_cases hmem : v ∈ xs
    · by_cases hxeq : x = v
      · -- x = v ≠ 0 and v ∈ xs: the head duplicates a nonzero element
        exfalso
        have hany' : ((toVals xs).any (fun y =>
            !((Value.int x).eqB (Value.int 0)) &&
             !(y.eqB (Value.int 0)) && (Value.int x).eqB y)) = true :=
          List.any_eq_true.mpr ⟨Value.int v, mem_toVals_iff.mpr ⟨v, hmem, rfl⟩,
            by
              simp only [Bool.and_eq_true, not_eqB_int0_true_iff, eqB_int_iff]
              exact ⟨⟨by rw [hxeq]; exact hv, hv⟩, hxeq⟩⟩
        rw [hany] at hany'
        simp at hany'
      · have h1 : intCount (x :: xs) v = intCount xs v := count_cons_ne hxeq
        rw [h1]
        exact ih hxs v hv
    · have hv0 : intCount xs v = 0 := by
        unfold intCount
        exact List.count_eq_zero.mpr hmem
      by_cases hxeq : x = v
      · have h1 : intCount (x :: xs) v = intCount xs v + 1 := count_cons_eq hxeq
        omega
      · have h1 : intCount (x :: xs) v = intCount xs v := count_cons_ne hxeq
        omega

private theorem valuesAllDifferentExcept0_of_count {l : List Int}
    (h : ∀ v : Int, v ≠ 0 → intCount l v ≤ 1) :
    valuesAllDifferentExcept0 (toVals l) = true := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    rw [valuesAllDiffExcept0_cons]
    refine ⟨?_, ih ?_⟩
    · cases hany : (toVals xs).any (fun y =>
        !((Value.int x).eqB (Value.int 0)) &&
         !(y.eqB (Value.int 0)) && (Value.int x).eqB y) with
      | false => rfl
      | true =>
          exfalso
          rw [List.any_eq_true] at hany
          obtain ⟨y, hy, hyeq⟩ := hany
          obtain ⟨w, hw, rfl⟩ := mem_toVals_iff.mp hy
          simp only [Bool.and_eq_true, not_eqB_int0_true_iff, eqB_int_iff] at hyeq
          obtain ⟨⟨hxne0, _hwne0⟩, hxeq⟩ := hyeq
          -- x = w ≠ 0 and w ∈ xs, so x has a second occurrence
          have hcount : intCount (x :: xs) x ≥ 2 := by
            have h1 : intCount (x :: xs) x = intCount xs x + 1 := count_cons_eq rfl
            have hmem : x ∈ xs := hxeq ▸ hw
            have hpos : 0 < intCount xs x := List.count_pos_iff.mpr hmem
            omega
          have := h x hxne0
          omega
    · intro v hv
      have hmono : intCount xs v ≤ intCount (x :: xs) v := intCount_cons_ge
      have := h v hv
      omega

/-- `fzn_alldifferent_except_0`: every nonzero value occurs at most
    once ("pairwise different except for those elements that are
    assigned the value 0"). -/
def allDiffExcept0Prop (l : List Int) : Prop :=
  ∀ v : Int, v ≠ 0 → intCount l v ≤ 1

/-- Boolean twin of `allDiffExcept0Prop`: drop the zeros and use the
    sort-based distinctness check. -/
def allDiffExcept0B (l : List Int) : Bool :=
  intsAllDifferentFast (l.filter (fun v => v != 0))

theorem intCount_filter_ne_zero {v : Int} (hv : v ≠ 0) :
    ∀ (l : List Int), intCount (l.filter (fun x => x != 0)) v = intCount l v := by
  intro l
  -- `intCount` is definitionally `List.count` with swapped arguments
  show List.count v (List.filter (fun y => y != 0) l) = List.count v l
  induction l with
  | nil => rfl
  | cons x xs ih =>
      rw [List.filter_cons]
      by_cases hx : x != 0
      · rw [if_pos hx, List.count_cons, List.count_cons, ih]
      · rw [if_neg hx, List.count_cons]
        have hx0 : x = 0 := by simpa using hx
        have hxv : (x == v) = false := by
          cases h : x == v with
          | true =>
              exact absurd (beq_iff_eq.mp h) (by
                intro heq
                exact hv (by rw [← heq, hx0]))
          | false => rfl
        rw [hxv, ih]
        simp

theorem allDiffExcept0B_iff (l : List Int) :
    allDiffExcept0B l = true ↔ allDiffExcept0Prop l := by
  rw [show allDiffExcept0B l = intsAllDifferentFast (l.filter (fun v => v != 0))
      from rfl, intPairwiseDistinctB_fast_iff]
  constructor
  · intro h v hv
    rw [← intCount_filter_ne_zero hv l]
    exact h v
  · intro h v
    by_cases hv : v = 0
    · subst hv
      -- filtering for `!= 0` can never keep a 0
      have hfilt : (List.filter (fun x => x != 0) l).count (0 : Int) = 0 := by
        rw [List.count_eq_zero]
        intro hmem
        -- the destructuring itself derives the contradiction
        -- (the filter predicate is false at 0)
        obtain ⟨_, _, _⟩ := List.mem_filter.mp hmem
      unfold intCount
      rw [hfilt]
      omega
    · rw [intCount_filter_ne_zero (fun hcon => hv hcon) l]
      exact h v hv

/-! ## Extensional set helpers -/

/-- Boolean twin of "no shared element" between two sets, checking the
    elements of `a` against `b`. -/
def setDisjB (a b : IntSetValue) : Bool :=
  (setElems a).all (fun k => !setMemB b k)

private theorem setMemB_false_iff {s : IntSetValue} {i : Int} :
    setMemB s i = false ↔ ¬ s.Contains i := by
  unfold setMemB
  exact decide_eq_false_iff_not

private theorem not_true_iff_false (b : Bool) : (!b) = true ↔ b = false := by
  cases b <;> simp

theorem setDisjB_iff {a b : IntSetValue} :
    setDisjB a b = true ↔ ∀ k, a.Contains k → ¬ b.Contains k := by
  constructor
  · intro h k hk
    have himem : k ∈ setElems a := setElems_mem_iff.mp hk
    have h2 := List.all_eq_true.mp h k himem
    rw [not_true_iff_false, setMemB_false_iff] at h2
    exact h2
  · intro h
    refine List.all_eq_true.mpr ?_
    intro x hx
    rw [not_true_iff_false, setMemB_false_iff]
    exact h x (setElems_mem_iff.mpr hx)

private theorem setEqB_false_iff {a b : IntSetValue} :
    setEqB a b = false ↔ ¬ (∀ i, a.Contains i ↔ b.Contains i) := by
  constructor
  · intro h hcon
    have h' : setEqB a b = true := setEqB_iff.mpr hcon
    rw [h] at h'
    simp at h'
  · intro h
    by_cases hb : setEqB a b = true
    · exact absurd (setEqB_iff.mp hb) h
    · exact Bool.not_eq_true _ |>.mp hb

/-! ## Set-counting helper -/

/-- Number of positions of `xs` whose set is extensionally equal to `v`. -/
def setEqCountB (xs : List IntSetValue) (v : IntSetValue) : Nat :=
  (xs.filter (setEqB · v)).length

/-! ## Prop/Bool twins for the all-different family -/

/-- `fzn_all_equal_int`: all elements equal (vacuously true when
    empty). -/
def allEqualIntProp (l : List Int) : Prop :=
  ∀ i j : Nat, i < l.length → j < l.length → l[i]! = l[j]!

/-- Boolean twin of `allEqualIntProp`: every position holds the first
    element. -/
def allEqualIntB (l : List Int) : Bool :=
  (List.range l.length).all (fun i => l[i]! == l[0]!)

theorem allEqualIntB_iff (l : List Int) :
    allEqualIntB l = true ↔ allEqualIntProp l := by
  constructor
  · intro h i j hi hj
    have h0 : (0 : Nat) < l.length := by omega
    have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
    have hj' := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    simp only [beq_iff_eq] at hi' hj'
    rw [hi', ← hj']
  · intro h
    refine List.all_eq_true.mpr ?_
    intro i hi
    simp only [beq_iff_eq]
    have h0 : (0 : Nat) < l.length := by
      have := List.mem_range.mp hi
      omega
    exact h i 0 (List.mem_range.mp hi) h0

/-- `fzn_all_equal_set`: all sets extensionally equal. -/
def allEqualSetProp (ss : List IntSetValue) : Prop :=
  ∀ i j : Nat, i < ss.length → j < ss.length →
    ∀ k, ss[i]!.Contains k ↔ ss[j]!.Contains k

/-- Boolean twin of `allEqualSetProp`: every set is extensionally
    equal to the first. -/
def allEqualSetB (ss : List IntSetValue) : Bool :=
  (List.range ss.length).all (fun i => setEqB ss[i]! ss[0]!)

theorem allEqualSetB_iff (ss : List IntSetValue) :
    allEqualSetB ss = true ↔ allEqualSetProp ss := by
  constructor
  · intro h i j hi hj k
    have h0 : (0 : Nat) < ss.length := by omega
    have hi' := List.all_eq_true.mp h i (List.mem_range.mpr hi)
    have hj' := List.all_eq_true.mp h j (List.mem_range.mpr hj)
    rw [setEqB_iff] at hi' hj'
    exact (hi' k).trans (hj' k).symm
  · intro h
    refine List.all_eq_true.mpr ?_
    intro i hi
    simp only [List.mem_range] at hi
    rw [setEqB_iff]
    have h0 : (0 : Nat) < ss.length := by omega
    exact h i 0 hi h0

/-- `fzn_all_different_set`: no two sets are extensionally equal. -/
def allDiffSetProp (ss : List IntSetValue) : Prop :=
  ∀ i j : Nat, i < j → j < ss.length →
    ¬ ∀ k, ss[i]!.Contains k ↔ ss[j]!.Contains k

/-- Boolean twin of `allDiffSetProp`: for every pair of positions,
    the later set differs from the earlier one. -/
def allDiffSetB (ss : List IntSetValue) : Bool :=
  (List.range ss.length).all (fun i2 =>
    (List.range i2).all (fun j2 => !(setEqB ss[i2]! ss[j2]!)))

theorem allDiffSetB_iff (ss : List IntSetValue) :
    allDiffSetB ss = true ↔ allDiffSetProp ss := by
  constructor
  · intro h i j hij hjlen hcon
    have hjle : j < ss.length := hjlen
    have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hjle)
    have h2 : (!(setEqB ss[j]! ss[i]!)) = true :=
      List.all_eq_true.mp h1 i (List.mem_range.mpr hij)
    rw [not_true_iff_false, setEqB_false_iff] at h2
    exact h2 (fun k => (hcon k).symm)
  · intro h
    refine List.all_eq_true.mpr ?_
    intro i2 hi2
    simp only [List.mem_range] at hi2
    refine List.all_eq_true.mpr ?_
    intro j2 hj2
    simp only [List.mem_range] at hj2
    rw [not_true_iff_false, setEqB_false_iff]
    intro hcon
    exact h j2 i2 hj2 (by omega) (fun k => (hcon k).symm)

/-- `fzn_all_disjoint`: the sets are pairwise disjoint (no integer is
    in two of them). -/
def allDisjointProp (ss : List IntSetValue) : Prop :=
  ∀ i j : Nat, i < j → j < ss.length →
    ∀ k, ¬ (ss[i]!.Contains k ∧ ss[j]!.Contains k)

/-- Boolean twin of `allDisjointProp`: for every pair of positions,
    the later set shares no element with the earlier one. -/
def allDisjointB (ss : List IntSetValue) : Bool :=
  (List.range ss.length).all (fun i2 =>
    (List.range i2).all (fun j2 => setDisjB ss[i2]! ss[j2]!))

theorem allDisjointB_iff (ss : List IntSetValue) :
    allDisjointB ss = true ↔ allDisjointProp ss := by
  constructor
  · intro h i j hij hjlen k hk
    have h1 := List.all_eq_true.mp h j (List.mem_range.mpr hjlen)
    have h2 : setDisjB ss[j]! ss[i]! = true :=
      List.all_eq_true.mp h1 i (List.mem_range.mpr hij)
    rw [setDisjB_iff] at h2
    exact h2 k hk.2 hk.1
  · intro h
    refine List.all_eq_true.mpr ?_
    intro i2 hi2
    simp only [List.mem_range] at hi2
    refine List.all_eq_true.mpr ?_
    intro j2 hj2
    simp only [List.mem_range] at hj2
    rw [setDisjB_iff]
    intro k hk hk2
    exact h j2 i2 hj2 (by omega) k ⟨hk2, hk⟩

/-! ## All-different except a set of values -/

/-- The elements of `l` that are not in `S`. -/
private def dropInSet (S : IntSetValue) : List Int → List Int
  | [] => []
  | x :: xs => if setMemB S x then dropInSet S xs else x :: dropInSet S xs

private theorem intCount_dropInSet_eq {S : IntSetValue} {v : Int}
    (hv : ¬ S.Contains v) : ∀ l : List Int,
    intCount (dropInSet S l) v = intCount l v := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : setMemB S x = true
    · have hxne : x ≠ v := by
        intro heq
        rw [heq] at hx
        exact hv (setMemB_iff.mp hx)
      have hdrop : dropInSet S (x :: xs) = dropInSet S xs := by
        show (if setMemB S x then dropInSet S xs else x :: dropInSet S xs)
            = dropInSet S xs
        rw [if_pos hx]
      have h1 : intCount (x :: xs) v = intCount xs v := count_cons_ne hxne
      rw [hdrop, h1]
      exact ih
    · have hxf : setMemB S x = false := by
        cases hb : setMemB S x with
        | false => rfl
        | true => exact absurd hb hx
      have hdrop : dropInSet S (x :: xs) = x :: dropInSet S xs := by
        show (if setMemB S x then dropInSet S xs else x :: dropInSet S xs)
            = x :: dropInSet S xs
        rw [hxf]
        rfl
      rw [hdrop]
      by_cases hxeq : x = v
      · have h1 : intCount (x :: dropInSet S xs) v
              = intCount (dropInSet S xs) v + 1 := count_cons_eq hxeq
        have h2 : intCount (x :: xs) v = intCount xs v + 1 := count_cons_eq hxeq
        rw [h1, h2, ih]
      · have h1 : intCount (x :: dropInSet S xs) v = intCount (dropInSet S xs) v :=
          count_cons_ne hxeq
        have h2 : intCount (x :: xs) v = intCount xs v := count_cons_ne hxeq
        rw [h1, h2]
        exact ih

private theorem intCount_dropInSet_eq_zero {S : IntSetValue} {v : Int}
    (hv : S.Contains v) : ∀ l : List Int,
    intCount (dropInSet S l) v = 0 := by
  intro l
  induction l with
  | nil => rfl
  | cons x xs ih =>
    by_cases hx : setMemB S x = true
    · have hdrop : dropInSet S (x :: xs) = dropInSet S xs := by
        show (if setMemB S x then dropInSet S xs else x :: dropInSet S xs)
            = dropInSet S xs
        rw [if_pos hx]
      rw [hdrop]
      exact ih
    · have hxf : setMemB S x = false := by
        cases hb : setMemB S x with
        | false => rfl
        | true => exact absurd hb hx
      have hxne : x ≠ v := by
        intro heq
        have h1 : setMemB S v = false := by rw [← heq]; exact hxf
        have h2 : setMemB S v = true := setMemB_iff.mpr hv
        rw [h1] at h2
        simp at h2
      have hdrop : dropInSet S (x :: xs) = x :: dropInSet S xs := by
        show (if setMemB S x then dropInSet S xs else x :: dropInSet S xs)
            = x :: dropInSet S xs
        rw [hxf]
        rfl
      rw [hdrop]
      have h1 : intCount (x :: dropInSet S xs) v = intCount (dropInSet S xs) v :=
        count_cons_ne hxne
      rw [h1]
      exact ih

/-- `fzn_alldifferent_except`: "Constrain the elements of the array
    xs to be pairwise different except for those values that appear in
    the set except" — every value outside `S` occurs at most once
    (equivalent to the pairwise form `∀ i < j, l[i]! = l[j]! →
    S.Contains l[i]!`). -/
def allDiffExceptProp (l : List Int) (S : IntSetValue) : Prop :=
  ∀ v : Int, ¬ S.Contains v → intCount l v ≤ 1

/-- Boolean twin of `allDiffExceptProp`: drop the elements of `S`,
    then check pairwise distinctness (sort-based). -/
def allDiffExceptB (l : List Int) (S : IntSetValue) : Bool :=
  intsAllDifferentFast (dropInSet S l)

theorem allDiffExceptB_iff (l : List Int) (S : IntSetValue) :
    allDiffExceptB l S = true ↔ allDiffExceptProp l S := by
  rw [show allDiffExceptB l S = intsAllDifferentFast (dropInSet S l) from rfl,
    intPairwiseDistinctB_fast_iff]
  constructor
  · intro h v hv
    rw [← intCount_dropInSet_eq hv l]
    exact h v
  · intro h v
    by_cases hv : S.Contains v
    · rw [intCount_dropInSet_eq_zero hv l]
      exact Nat.zero_le _
    · rw [intCount_dropInSet_eq hv l]
      exact h v hv

/-! ## Symmetric all-different -/

/-- `fzn_symmetric_all_different`: `xs` is all different, every entry
    is a position `1..n`, and `xs[xs[i]-1] = i` (0-based: the value at
    the index pointed to by `xs[i]` points back).  This is the
    handbook's "all different, and for all i, xs[i]=j → xs[j]=i". -/
def symmetricAllDiffProp (xs : List Int) : Prop :=
  (∀ v : Int, intCount xs v ≤ 1) ∧
    ∀ i : Nat, i < xs.length →
      1 ≤ xs[i]! ∧ xs[i]! ≤ xs.length ∧
        xs[(xs[i]! - 1).toNat]! = (i : Int) + 1

/-- Boolean twin of `symmetricAllDiffProp` (fast sort-based
    distinctness). -/
def symmetricAllDiffB (xs : List Int) : Bool :=
  intsAllDifferentFast xs &&
  (List.range xs.length).all (fun i =>
    decide (1 ≤ xs[i]! ∧ xs[i]! ≤ xs.length ∧
      xs[(xs[i]! - 1).toNat]! = (i : Int) + 1))

theorem symmetricAllDiffB_iff (xs : List Int) :
    symmetricAllDiffB xs = true ↔ symmetricAllDiffProp xs := by
  constructor
  · intro h
    unfold symmetricAllDiffB at h
    rw [Bool.and_eq_true] at h
    obtain ⟨hall, hrange⟩ := h
    refine ⟨(intPairwiseDistinctB_fast_iff xs).mp hall, ?_⟩
    intro i hi
    have hmem := List.all_eq_true.mp hrange i (List.mem_range.mpr hi)
    rw [decide_eq_true_iff] at hmem
    exact hmem
  · rintro ⟨hcount, hidx⟩
    show (intsAllDifferentFast xs &&
      (List.range xs.length).all (fun i =>
        decide (1 ≤ xs[i]! ∧ xs[i]! ≤ xs.length ∧
          xs[(xs[i]! - 1).toNat]! = (i : Int) + 1))) = true
    rw [Bool.and_eq_true]
    refine ⟨(intPairwiseDistinctB_fast_iff xs).mpr hcount, List.all_eq_true.mpr (fun i hi => by
      simp only [List.mem_range] at hi
      exact decide_eq_true (hidx i hi))⟩

/-! ## The interpretations -/

/-- Mathematical interpretations of the all-different family of
    global-constraint predicates.  A wrong argument shape yields
    `False`. -/
def allDiffInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_all_different_int" => fun args =>
    match oneIntArr args with
    | some l => (∀ v : Int, intCount l v ≤ 1)
    | none => False
  | "fzn_all_different_set" => fun args =>
    match oneSetArr args with
    | some ss => allDiffSetProp ss
    | none => False
  | "fzn_all_disjoint" => fun args =>
    match oneSetArr args with
    | some ss => allDisjointProp ss
    | none => False
  | "fzn_all_equal_int" => fun args =>
    match oneIntArr args with
    | some l => allEqualIntProp l
    | none => False
  | "fzn_all_equal_set" => fun args =>
    match oneSetArr args with
    | some ss => allEqualSetProp ss
    | none => False
  | "fzn_alldifferent_except" => fun args =>
    match arrAndSet args with
    | some (l, S) => allDiffExceptProp l S
    | none => False
  | "fzn_alldifferent_except_0" => fun args =>
    match oneIntArr args with
    | some l => allDiffExcept0Prop l
    | none => False
  | "fzn_symmetric_all_different" => fun args =>
    match oneIntArr args with
    | some xs => symmetricAllDiffProp xs
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `allDiffInterp`**: computes the truth of the
    all-different interpretations; `false` on a wrong shape.  The
    integer cases use the sort-based `intsAllDifferentFast` (its
    agreement with `valuesAllDifferent (toVals l)` is
    `valuesAllDifferentFast_iff` in `FznStdLib`). -/
def allDiffInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_all_different_int" => fun args =>
    match oneIntArr args with
    | some l => intsAllDifferentFast l
    | none => false
  | "fzn_all_different_set" => fun args =>
    match oneSetArr args with
    | some ss => allDiffSetB ss
    | none => false
  | "fzn_all_disjoint" => fun args =>
    match oneSetArr args with
    | some ss => allDisjointB ss
    | none => false
  | "fzn_all_equal_int" => fun args =>
    match oneIntArr args with
    | some l => allEqualIntB l
    | none => false
  | "fzn_all_equal_set" => fun args =>
    match oneSetArr args with
    | some ss => allEqualSetB ss
    | none => false
  | "fzn_alldifferent_except" => fun args =>
    match arrAndSet args with
    | some (l, S) => allDiffExceptB l S
    | none => false
  | "fzn_alldifferent_except_0" => fun args =>
    match oneIntArr args with
    | some l => allDiffExcept0B l
    | none => false
  | "fzn_symmetric_all_different" => fun args =>
    match oneIntArr args with
    | some xs => symmetricAllDiffB xs
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_all_different_int_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_all_different_int") args = true ↔
      allDiffInterp (Ident.mk "fzn_all_different_int") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : oneIntArr args with
  | none => simp
  | some l =>
    simp only
    exact intPairwiseDistinctB_fast_iff l

theorem fzn_all_different_set_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_all_different_set") args = true ↔
      allDiffInterp (Ident.mk "fzn_all_different_set") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : oneSetArr args with
  | none => simp
  | some ss =>
    simp only
    exact allDiffSetB_iff ss

theorem fzn_all_disjoint_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_all_disjoint") args = true ↔
      allDiffInterp (Ident.mk "fzn_all_disjoint") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : oneSetArr args with
  | none => simp
  | some ss =>
    simp only
    exact allDisjointB_iff ss

theorem fzn_all_equal_int_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_all_equal_int") args = true ↔
      allDiffInterp (Ident.mk "fzn_all_equal_int") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : oneIntArr args with
  | none => simp
  | some l =>
    simp only
    exact allEqualIntB_iff l

theorem fzn_all_equal_set_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_all_equal_set") args = true ↔
      allDiffInterp (Ident.mk "fzn_all_equal_set") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : oneSetArr args with
  | none => simp
  | some ss =>
    simp only
    exact allEqualSetB_iff ss

theorem fzn_alldifferent_except_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_alldifferent_except") args = true ↔
      allDiffInterp (Ident.mk "fzn_alldifferent_except") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : arrAndSet args with
  | none => simp
  | some p =>
    obtain ⟨l, S⟩ := p
    simp only
    exact allDiffExceptB_iff l S

theorem fzn_alldifferent_except_0_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_alldifferent_except_0") args = true ↔
      allDiffInterp (Ident.mk "fzn_alldifferent_except_0") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : oneIntArr args with
  | none => simp
  | some l =>
    simp only
    exact allDiffExcept0B_iff l

theorem fzn_symmetric_all_different_iff (args : List Value) :
    allDiffInterpB (Ident.mk "fzn_symmetric_all_different") args = true ↔
      allDiffInterp (Ident.mk "fzn_symmetric_all_different") args := by
  simp only [allDiffInterp, allDiffInterpB]
  cases h : oneIntArr args with
  | none => simp
  | some xs =>
    simp only
    exact symmetricAllDiffB_iff xs

end LeanFzn.Semantics.Globals.AllDiffCounting
