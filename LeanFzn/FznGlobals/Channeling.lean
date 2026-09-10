import LeanFzn.FznGlobals.Common

/-!
# Channeling and member global constraints

Mathematical interpretations (`channelingInterp`) and executable Boolean
twins (`channelingInterpB`) for the channeling and array-related
member/write global-constraint predicates of the pinned MiniZinc 2.10.0
FlatZinc tree.  Each predicate name gets a per-name agreement theorem
`fzn_<name>_iff` proving that the Boolean twin is `true` exactly when
the mathematical interpretation holds, following the `lexSortInterp`
pattern of `LexSort.lean`.

Semantics per the MiniZinc 2.10.0 handbook, Section 4.2.2.4
("Channeling constraints"), 4.2.2.6 ("Array-related constraints") and
4.2.2.8 ("Mathematical constraints"), cross-checked against the pinned
tree's decompositions (`share/minizinc/std/fzn_*.mzn`):

* `inverse` — "Constrains two arrays of int variables, f and invf, to
  represent inverse functions.  All the values in each array must be
  within the index set of the other array."  The decomposition is
  `forall i in index_set(f) (f[i] in index_set(invf) /\ invf[f[i]] ==
  i) /\ forall j in index_set(invf) (...)`: with 1-based arrays this is
  `y[x[i]] = i` and `x[y[j]] = j` plus the range conditions.
* `inverse_in_range` — "If the i th variable of the collection xs is
  assigned to j and if j is in the index set of ys then the j th
  variable of the collection ys is assigned to i.  Conversely ...".
  The in-range guards make this *weaker* than `inverse`: assignments
  outside the other array's index range make the implications vacuous
  (the `redundant_constraint` strengthenings of the decomposition do
  not change the semantics).
* `int_set_channel` — "(ints[i] = j) <-> (i in sets[j])", plus the
  range conditions `ints[i] in index_set(sets)` and
  `sets[j] subset index_set(ints)` of the decomposition.
* `link_set_to_booleans` — "Constrains the array of Booleans bs to be
  a representation of the set s : i in s <-> bs[i]".
* `member` — "Requires that y occurs in the array x".
* `arg_val` — "Returns the index of the value value in the array xs.
  When breaking ties the least index is returned.  Note that this
  function forces the value value to occur in xs."  (The FlatZinc
  decomposition via `fzn_maximum_arg_bool` indeed makes the predicate
  false when the value is absent.)
* `write` — "Creates a new array O from an input array I with a change
  at position i to take value v"; the decomposition is
  `forall j in index_set(I) (O[j] = if j = i then v else I[j] endif)`
  with "O ... same index set as I".  (Out-of-range `i` therefore leaves
  `O` equal to `I` positionally.)
* `writes` — "Creates a new array O from an input array I with a
  simultaneous change at positions P to values V"; the decomposition
  is `forall j in index_set(P) (O[P[j]] = V[j])` plus "unwritten
  positions keep their value", with P and V sharing an index set and
  O the index set of I.

All FlatZinc arrays are 1-based; the twins realize this with 0-based
`List` indices plus a `+1` shift, guarding bounds explicitly.

The interpretive decisions specific to this family (the guarded-vs-
unguarded distinction between `inverse_in_range` and `inverse`,
`arg_val` forcing occurrence and returning the least index, the
totality of `write` vs the partiality of `writes`) are recorded in
`specification/flatzinc_specification_assumptions.md`, G14–G16.
-/

namespace LeanFzn.Globals.Channeling

open LeanFzn LeanFzn.Globals LeanFzn.Solution

/-! ## Argument decoders

The public decoders of `AllDiffCounting.lean` cover the counting
family; the shapes specific to this family get their own (private)
decoders here, matching the frozen `globalsSig` signatures. -/

/-- Decode two integer-array arguments. -/
private def twoIntArrays (args : List Value) : Option (List Int × List Int) :=
  match args with
  | [.array xs, .array ys] =>
      match valueInts xs, valueInts ys with
      | some a, some b => some (a, b)
      | _, _ => none
  | _ => none

/-- Decode a single integer-array argument. -/
private def oneIntArray (args : List Value) : Option (List Int) :=
  match args with
  | [.array xs] => valueInts xs
  | _ => none

/-- Decode a single boolean-array argument. -/
private def oneBoolArray (args : List Value) : Option (List Bool) :=
  match args with
  | [.array xs] => valueBools xs
  | _ => none

/-- Decode a single set-array argument. -/
private def oneSetArray (args : List Value) : Option (List IntSetValue) :=
  match args with
  | [.array xs] => valueSets xs
  | _ => none

/-- Decode (int array, set array) arguments. -/
private def intAndSetArrays (args : List Value) :
    Option (List Int × List IntSetValue) :=
  match args with
  | [.array xs, .array ss] =>
      match valueInts xs, valueSets ss with
      | some a, some b => some (a, b)
      | _, _ => none
  | _ => none

/-- Decode (set, bool array) arguments. -/
private def setAndBoolArray (args : List Value) :
    Option (IntSetValue × List Bool) :=
  match args with
  | [.setOfInt s, .array bs] =>
      match valueBools bs with
      | some l => some (s, l)
      | none => none
  | _ => none

/-- Decode (int array, int) arguments (member). -/
private def arrayAndInt (args : List Value) : Option (List Int × Int) :=
  match args with
  | [.array xs, .int y] => (valueInts xs).map (fun a => (a, y))
  | _ => none

/-- Decode (bool array, bool) arguments. -/
private def arrayAndBool (args : List Value) : Option (List Bool × Bool) :=
  match args with
  | [.array xs, .bool y] => (valueBools xs).map (fun a => (a, y))
  | _ => none

/-- Decode (set array, set) arguments (member). -/
private def arrayAndSet (args : List Value) :
    Option (List IntSetValue × IntSetValue) :=
  match args with
  | [.array xs, .setOfInt y] =>
      match valueSets xs with
      | some l => some (l, y)
      | none => none
  | _ => none

/-- Decode (int array, int, int) arguments (arg_val). -/
private def arrayIntInt (args : List Value) : Option (List Int × Int × Int) :=
  match args with
  | [.array xs, .int y, .int i] =>
      match valueInts xs with
      | some l => some (l, y, i)
      | none => none
  | _ => none

/-- Decode (bool array, bool, int) arguments (arg_val). -/
private def arrayBoolInt (args : List Value) : Option (List Bool × Bool × Int) :=
  match args with
  | [.array xs, .bool y, .int i] =>
      match valueBools xs with
      | some l => some (l, y, i)
      | none => none
  | _ => none

/-- Decode (int array, int, int, int array) arguments (write). -/
private def writeArgs (args : List Value) :
    Option (List Int × Int × Int × List Int) :=
  match args with
  | [.array xs, .int i, .int v, .array ys] =>
      match valueInts xs, valueInts ys with
      | some a, some b => some (a, i, v, b)
      | _, _ => none
  | _ => none

/-- Decode (int array, int array, int array, int array) arguments
    (writes). -/
private def writesArgs (args : List Value) :
    Option (List Int × List Int × List Int × List Int) :=
  match args with
  | [.array a, .array b, .array c, .array d] =>
      match valueInts a, valueInts b, valueInts c, valueInts d with
      | some la, some lb, some lc, some ld => some (la, lb, lc, ld)
      | _, _, _, _ => none
  | _ => none

/-! ## Small list helpers -/

/-- List membership as a bounded position with `getElem!`. -/
private theorem mem_iff_ex_get! {α : Type} [Inhabited α] {l : List α} {v : α} :
    v ∈ l ↔ ∃ i, i < l.length ∧ l[i]! = v := by
  induction l with
  | nil => simp
  | cons a ls ih =>
      constructor
      · intro h
        rcases List.mem_cons.mp h with rfl | hv
        · exact ⟨0, by simp, rfl⟩
        · obtain ⟨i, hi, hget⟩ := ih.mp hv
          refine ⟨i + 1, by simp only [List.length_cons]; omega, ?_⟩
          rw [List.getElem!_cons_succ]
          exact hget
      · rintro ⟨i, hi, hv⟩
        cases i with
        | zero =>
            rw [List.getElem!_cons_zero] at hv
            exact List.mem_cons.mpr (Or.inl hv.symm)
        | succ i' =>
            rw [List.getElem!_cons_succ] at hv
            refine List.mem_cons.mpr (Or.inr (ih.mpr ⟨i', ?_, hv⟩))
            simp only [List.length_cons] at hi
            omega

/-! ## First-occurrence helper

`firstIdx` of `LexSort.lean` is private, so a small first-occurrence
helper (over any type with decidable equality) is provided here,
together with the two spec lemmas the `arg_val` family needs. -/

/-- The least 0-based index `i` with `xs[i]! = v`; `none` if there is
    none. -/
private def firstOcc {α : Type} [DecidableEq α] (v : α) : List α → Option Nat
  | [] => none
  | x :: rest => if x = v then some 0 else (firstOcc v rest).map (· + 1)

/-- `firstOcc` returns an in-bounds least index holding the value. -/
private theorem firstOcc_eq_iff {α : Type} [DecidableEq α] [Inhabited α] :
    ∀ (xs : List α) (v : α) (i : Nat),
      firstOcc v xs = some i ↔
        i < xs.length ∧ xs[i]! = v ∧ ∀ k, k < i → xs[k]! ≠ v := by
  intro xs
  induction xs with
  | nil => intro v i; simp [firstOcc]
  | cons x rest ih =>
      intro v i
      by_cases hxv : x = v
      · have heq : firstOcc v (x :: rest) = some 0 := by
          simp only [firstOcc]
          rw [if_pos hxv]
        rw [heq]
        constructor
        · intro h
          injection h with hi
          subst hi
          refine ⟨by simp, by rw [List.getElem!_cons_zero]; exact hxv, ?_⟩
          intro k hk
          exact absurd hk (Nat.not_lt_zero k)
        · rintro ⟨hi, hget, hleast⟩
          have : i = 0 := by
            cases Nat.eq_zero_or_pos i with
            | inl h => exact h
            | inr hpos =>
                have h0 : (x :: rest)[0]! = v := by
                  rw [List.getElem!_cons_zero]; exact hxv
                exact absurd h0 (hleast 0 hpos)
          subst this
          rfl
      · have heq : firstOcc v (x :: rest) = (firstOcc v rest).map (· + 1) := by
          simp only [firstOcc]
          rw [if_neg hxv]
        rw [heq, Option.map_eq_some_iff]
        constructor
        · rintro ⟨i', hiss, hsum⟩
          obtain ⟨hi'len, hget', hleast'⟩ := (ih v i').mp hiss
          subst hsum
          refine ⟨by simp only [List.length_cons]; omega, ?_, ?_⟩
          · rw [List.getElem!_cons_succ]
            exact hget'
          · intro k hk
            cases k with
            | zero =>
                rw [List.getElem!_cons_zero]
                exact hxv
            | succ k' =>
                rw [List.getElem!_cons_succ]
                exact hleast' k' (by omega)
        · rintro ⟨hi, hget, hleast⟩
          have hne0 : i ≠ 0 := by
            intro h0
            rw [h0] at hget
            rw [List.getElem!_cons_zero] at hget
            exact hxv hget
          obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
          have hget' : rest[i']! = v := by
            rw [List.getElem!_cons_succ] at hget
            exact hget
          have hleast' : ∀ k, k < i' → rest[k]! ≠ v := by
            intro k hk
            have hg := hleast (k + 1) (by omega)
            rw [List.getElem!_cons_succ] at hg
            exact hg
          exact ⟨i', (ih v i').mpr ⟨by simp only [List.length_cons] at hi; omega,
            hget', hleast'⟩, rfl⟩

/-- `firstOcc` is `none` exactly when the value is absent. -/
private theorem firstOcc_eq_none_iff {α : Type} [DecidableEq α] [Inhabited α] :
    ∀ (xs : List α) (v : α),
      firstOcc v xs = none ↔ ∀ i, i < xs.length → xs[i]! ≠ v := by
  intro xs
  induction xs with
  | nil => intro v; simp [firstOcc]
  | cons x rest ih =>
      intro v
      by_cases hxv : x = v
      · constructor
        · intro h i _
          have hs : firstOcc v (x :: rest) = some 0 := by
            simp only [firstOcc]
            rw [if_pos hxv]
          rw [h] at hs
          simp at hs
        · intro h
          have h0 : (x :: rest)[0]! ≠ v := h 0 (by simp)
          rw [List.getElem!_cons_zero] at h0
          exact absurd hxv h0
      · have heq : firstOcc v (x :: rest) = (firstOcc v rest).map (· + 1) := by
          simp only [firstOcc]
          rw [if_neg hxv]
        rw [heq, Option.map_eq_none_iff, ih v]
        constructor
        · intro h i hi
          cases i with
          | zero => rw [List.getElem!_cons_zero]; exact hxv
          | succ i' =>
              rw [List.getElem!_cons_succ]
              exact h i' (by simp only [List.length_cons] at hi; omega)
        · intro h i hi
          have hsucc : (x :: rest)[i + 1]! ≠ v :=
            h (i + 1) (by
              simp only [List.length_cons]
              omega)
          rw [List.getElem!_cons_succ] at hsucc
          exact hsucc

/-! ## `fzn_inverse` -/

/-- `fzn_inverse(x, y)` (handbook 4.2.2.4): x and y represent inverse
    functions; every value of each array is within the index range of
    the other, and looking up through one array undoes the other
    (1-based indices; 0-based Lean form: `y[x[i]! - 1]! = i + 1`). -/
def inverseProp (x y : List Int) : Prop :=
  (∀ i : Nat, i < x.length → 1 ≤ x[i]! ∧ x[i]! ≤ y.length) ∧
  (∀ j : Nat, j < y.length → 1 ≤ y[j]! ∧ y[j]! ≤ x.length) ∧
  (∀ i : Nat, i < x.length → y[(x[i]! - 1).toNat]! = (i : Int) + 1) ∧
  (∀ j : Nat, j < y.length → x[(y[j]! - 1).toNat]! = (j : Int) + 1)

/-- Boolean twin of `inverseProp`. -/
def inverseB (x y : List Int) : Bool :=
  (List.range x.length).all (fun i =>
    decide (1 ≤ x[i]! ∧ x[i]! ≤ y.length)) &&
  (List.range y.length).all (fun j =>
    decide (1 ≤ y[j]! ∧ y[j]! ≤ x.length)) &&
  (List.range x.length).all (fun i =>
    decide (y[(x[i]! - 1).toNat]! = (i : Int) + 1)) &&
  (List.range y.length).all (fun j =>
    decide (x[(y[j]! - 1).toNat]! = (j : Int) + 1))

theorem inverseB_iff (x y : List Int) :
    inverseB x y = true ↔ inverseProp x y := by
  simp only [inverseB, inverseProp, Bool.and_eq_true, decide_eq_true_iff,
    List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-! ## `fzn_inverse_in_range`

Handbook 4.2.2.4: "If the i th variable of the collection xs is
assigned to j and if j is in the index set of ys then the j th
variable of the collection ys is assigned to i.  Conversely, if the
j th variable of the collection ys is assigned to i and if i is in the
index set of xs then the i th variable of the collection xs is
assigned to j."

Unlike `inverse`, the conditions are guarded: a value outside the
other array's index range makes the corresponding implication vacuous,
so e.g. `xs = [5, 6], ys = [3, 4]` satisfies `inverse_in_range` (both
directions vacuous) but not `inverse`.  The two predicates therefore
genuinely differ; the `redundant_constraint` strengthenings in the
pinned decomposition do not change the semantics. -/

/-- `fzn_inverse_in_range(x, y)`: the guarded inverse conditions of the
    handbook (both directions, each guarded by the index range of the
    other array). -/
def inverseInRangeProp (x y : List Int) : Prop :=
  (∀ i : Nat, i < x.length →
      1 ≤ x[i]! ∧ x[i]! ≤ y.length → y[(x[i]! - 1).toNat]! = (i : Int) + 1) ∧
  (∀ j : Nat, j < y.length →
      1 ≤ y[j]! ∧ y[j]! ≤ x.length → x[(y[j]! - 1).toNat]! = (j : Int) + 1)

/-- Boolean twin of `inverseInRangeProp`. -/
def inverseInRangeB (x y : List Int) : Bool :=
  (List.range x.length).all (fun i =>
    decide (1 ≤ x[i]! ∧ x[i]! ≤ y.length →
      y[(x[i]! - 1).toNat]! = (i : Int) + 1)) &&
  (List.range y.length).all (fun j =>
    decide (1 ≤ y[j]! ∧ y[j]! ≤ x.length →
      x[(y[j]! - 1).toNat]! = (j : Int) + 1))

theorem inverseInRangeB_iff (x y : List Int) :
    inverseInRangeB x y = true ↔ inverseInRangeProp x y := by
  simp only [inverseInRangeB, inverseInRangeProp, Bool.and_eq_true,
    decide_eq_true_iff, List.all_eq_true, List.mem_range]

/-! ## `fzn_int_set_channel` -/

/-- `fzn_int_set_channel(ints, sets)` (handbook 4.2.2.4):
    "(ints[i] = j) <-> (i in sets[j])", plus the decomposition's range
    conditions: every `ints[i]` is an index of `sets` and every
    `sets[j]` only contains indices of `ints` (all 1-based). -/
def intSetChannelProp (xs : List Int) (ss : List IntSetValue) : Prop :=
  (∀ i : Nat, i < xs.length → 1 ≤ xs[i]! ∧ xs[i]! ≤ ss.length) ∧
  (∀ j : Nat, j < ss.length →
      ∀ k, ss[j]!.Contains k → 1 ≤ k ∧ k ≤ xs.length) ∧
  (∀ i : Nat, i < xs.length → ∀ j : Nat, j < ss.length →
      (xs[i]! = (j : Int) + 1 ↔ ss[j]!.Contains ((i : Int) + 1)))

/-- Boolean twin of `intSetChannelProp`. -/
def intSetChannelB (xs : List Int) (ss : List IntSetValue) : Bool :=
  (List.range xs.length).all (fun i =>
    decide (1 ≤ xs[i]! ∧ xs[i]! ≤ ss.length)) &&
  (List.range ss.length).all (fun j =>
    (setElems ss[j]!).all (fun k =>
      decide (1 ≤ k ∧ k ≤ xs.length))) &&
  (List.range xs.length).all (fun i =>
    (List.range ss.length).all (fun j =>
      decide (xs[i]! = (j : Int) + 1 ↔ ss[j]!.Contains ((i : Int) + 1))))

theorem intSetChannelB_iff (xs : List Int) (ss : List IntSetValue) :
    intSetChannelB xs ss = true ↔ intSetChannelProp xs ss := by
  simp only [intSetChannelB, intSetChannelProp, Bool.and_eq_true,
    decide_eq_true_iff, List.all_eq_true, List.mem_range, ← setElems_mem_iff]
  constructor
  · rintro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨⟨h1, h2⟩, h3⟩

/-! ## `fzn_link_set_to_booleans` -/

/-- `fzn_link_set_to_booleans(s, bs)` (handbook 4.2.2.4): "Constrains
    the array of Booleans bs to be a representation of the set s :
    i in s <-> bs[i]" — the i-th Boolean (1-based) is true exactly
    when i is in the set. -/
def linkSetBoolsProp (s : IntSetValue) (bs : List Bool) : Prop :=
  ∀ i : Nat, i < bs.length → (bs[i]! = true ↔ s.Contains ((i : Int) + 1))

/-- Boolean twin of `linkSetBoolsProp`. -/
def linkSetBoolsB (s : IntSetValue) (bs : List Bool) : Bool :=
  (List.range bs.length).all (fun i =>
    decide (bs[i]! = true ↔ s.Contains ((i : Int) + 1)))

theorem linkSetBoolsB_iff (s : IntSetValue) (bs : List Bool) :
    linkSetBoolsB s bs = true ↔ linkSetBoolsProp s bs := by
  simp only [linkSetBoolsB, linkSetBoolsProp, List.all_eq_true,
    List.mem_range, decide_eq_true_iff]

/-! ## Members -/

/-- `fzn_member_int(x, e)` (handbook 4.2.2.6): "Requires that y occurs
    in the array x" — `e` is one of the (0-based) positions' values. -/
def memberIntProp (xs : List Int) (e : Int) : Prop :=
  ∃ i, i < xs.length ∧ xs[i]! = e

/-- Boolean twin of `memberIntProp`. -/
def memberIntB (xs : List Int) (e : Int) : Bool :=
  xs.contains e

theorem memberIntB_iff (xs : List Int) (e : Int) :
    memberIntB xs e = true ↔ memberIntProp xs e := by
  simp only [memberIntB, memberIntProp, List.contains_iff_mem, mem_iff_ex_get!]

/-- `fzn_member_bool(x, e)`: `e` occurs in the boolean array `x`. -/
def memberBoolProp (bs : List Bool) (e : Bool) : Prop :=
  ∃ i, i < bs.length ∧ bs[i]! = e

/-- Boolean twin of `memberBoolProp`. -/
def memberBoolB (bs : List Bool) (e : Bool) : Bool :=
  bs.contains e

theorem memberBoolB_iff (bs : List Bool) (e : Bool) :
    memberBoolB bs e = true ↔ memberBoolProp bs e := by
  simp only [memberBoolB, memberBoolProp, List.contains_iff_mem, mem_iff_ex_get!]

/-- `fzn_member_set(x, e)`: the set `e` occurs in the array of sets
    `x` (extensional set equality at some position). -/
def memberSetProp (ss : List IntSetValue) (e : IntSetValue) : Prop :=
  ∃ i, i < ss.length ∧ ∀ k, ss[i]!.Contains k ↔ e.Contains k

/-- Boolean twin of `memberSetProp`. -/
def memberSetB (ss : List IntSetValue) (e : IntSetValue) : Bool :=
  (List.range ss.length).any (fun i => setEqB ss[i]! e)

theorem memberSetB_iff (ss : List IntSetValue) (e : IntSetValue) :
    memberSetB ss e = true ↔ memberSetProp ss e := by
  simp only [memberSetB, memberSetProp, List.any_eq_true, List.mem_range,
    setEqB_iff]

/-! ## `fzn_arg_val_int` / `fzn_arg_val_bool`

Handbook 4.2.2.8: "Returns the index of the value value in the array
xs.  When breaking ties the least index is returned.  Note that this
function forces the value value to occur in xs."  The FlatZinc
decompositions (`fzn_arg_val_int` via `fzn_maximum_arg_bool`, and
`fzn_arg_val_bool` via the maximum/minimum arg on booleans) realize
exactly this: the index is the least 1-based position holding the
value, and the predicate is false when the value is absent. -/

/-- `fzn_arg_val_int(x, e, i)`: `i` is the least 1-based position of
    `e` in `x` (so `e` occurs at `x[i-1]` and nowhere earlier). -/
def argValIntProp (xs : List Int) (e i : Int) : Prop :=
  ∃ j, j < xs.length ∧ xs[j]! = e ∧ i = (j : Int) + 1 ∧
    ∀ k, k < j → xs[k]! ≠ e

/-- Boolean twin of `argValIntProp` (via the first-occurrence
    helper). -/
def argValIntB (xs : List Int) (e i : Int) : Bool :=
  match firstOcc e xs with
  | some j => decide (i = (j : Int) + 1)
  | none => false

theorem argValIntB_iff (xs : List Int) (e i : Int) :
    argValIntB xs e i = true ↔ argValIntProp xs e i := by
  unfold argValIntB
  cases ho : firstOcc e xs with
  | none =>
      show false = true ↔ _
      constructor
      · intro hf
        exact absurd hf (by simp)
      · rintro ⟨j, hjlen, hjval, _, hleast⟩
        have hs : firstOcc e xs = some j :=
          (firstOcc_eq_iff xs e j).mpr ⟨hjlen, hjval, hleast⟩
        rw [ho] at hs
        simp at hs
  | some j =>
      show decide (i = (j : Int) + 1) = true ↔ _
      rw [decide_eq_true_iff]
      constructor
      · intro hieq
        obtain ⟨h1, h2, h3⟩ := (firstOcc_eq_iff xs e j).mp ho
        exact ⟨j, h1, h2, hieq, h3⟩
      · rintro ⟨j', hjlen, hjval, hieq, hleast⟩
        have hs : firstOcc e xs = some j' :=
          (firstOcc_eq_iff xs e j').mpr ⟨hjlen, hjval, hleast⟩
        rw [ho] at hs
        have hjj : j = j' := Option.some.inj hs
        subst hjj
        exact hieq

/-- `fzn_arg_val_bool(x, e, i)`: `i` is the least 1-based position of
    `e` in the boolean array `x`. -/
def argValBoolProp (bs : List Bool) (e : Bool) (i : Int) : Prop :=
  ∃ j, j < bs.length ∧ bs[j]! = e ∧ i = (j : Int) + 1 ∧
    ∀ k, k < j → bs[k]! ≠ e

/-- Boolean twin of `argValBoolProp`. -/
def argValBoolB (bs : List Bool) (e : Bool) (i : Int) : Bool :=
  match firstOcc e bs with
  | some j => decide (i = (j : Int) + 1)
  | none => false

theorem argValBoolB_iff (bs : List Bool) (e : Bool) (i : Int) :
    argValBoolB bs e i = true ↔ argValBoolProp bs e i := by
  unfold argValBoolB
  cases ho : firstOcc e bs with
  | none =>
      show false = true ↔ _
      constructor
      · intro hf
        exact absurd hf (by simp)
      · rintro ⟨j, hjlen, hjval, _, hleast⟩
        have hs : firstOcc e bs = some j :=
          (firstOcc_eq_iff bs e j).mpr ⟨hjlen, hjval, hleast⟩
        rw [ho] at hs
        simp at hs
  | some j =>
      show decide (i = (j : Int) + 1) = true ↔ _
      rw [decide_eq_true_iff]
      constructor
      · intro hieq
        obtain ⟨h1, h2, h3⟩ := (firstOcc_eq_iff bs e j).mp ho
        exact ⟨j, h1, h2, hieq, h3⟩
      · rintro ⟨j', hjlen, hjval, hieq, hleast⟩
        have hs : firstOcc e bs = some j' :=
          (firstOcc_eq_iff bs e j').mpr ⟨hjlen, hjval, hleast⟩
        rw [ho] at hs
        have hjj : j = j' := Option.some.inj hs
        subst hjj
        exact hieq

/-! ## `fzn_write` / `fzn_writes` -/

/-- `fzn_write(x, i, e, y)` (handbook 4.2.2.6): "Creates a new array
    O from an input array I with a change at position i to take value
    v", with O of the same index set as I.  The decomposition is
    `forall j in index_set(I) (O[j] = if j = i then v else I[j])`
    (1-based): every position keeps its value except (1-based) `i`,
    which becomes `e`.  An out-of-range `i` therefore leaves `y` equal
    to `x` positionally (the decomposition is total). -/
def writeProp (xs : List Int) (i v : Int) (ys : List Int) : Prop :=
  xs.length = ys.length ∧
  ∀ j, j < xs.length → ys[j]! = (if ((j : Int) + 1) = i then v else xs[j]!)

/-- Boolean twin of `writeProp`. -/
def writeB (xs : List Int) (i v : Int) (ys : List Int) : Bool :=
  decide (xs.length = ys.length) &&
  (List.range xs.length).all (fun j =>
    decide (ys[j]! = (if ((j : Int) + 1) = i then v else xs[j]!)))

theorem writeB_iff (xs : List Int) (i v : Int) (ys : List Int) :
    writeB xs i v ys = true ↔ writeProp xs i v ys := by
  simp only [writeB, writeProp, Bool.and_eq_true, decide_eq_true_iff,
    List.all_eq_true, List.mem_range]

/-- `fzn_writes(x, idx, elem, y)` (handbook 4.2.2.6): "Creates a new
    array O from an input array I with a simultaneous change at
    positions P to values V".  The decomposition is
    `forall j in index_set(P) (O[P[j]] = V[j])` together with
    "positions of I that no P[j] points to keep their value"; P and V
    share an index set and O the index set of I.  A `P[j]` outside the
    index range of O makes the (partial) array access undefined, so
    the predicate is false. -/
def writesProp (xs ps vs ys : List Int) : Prop :=
  xs.length = ys.length ∧ ps.length = vs.length ∧
  (∀ j, j < ps.length → 1 ≤ ps[j]! ∧ ps[j]! ≤ ys.length ∧
      ys[(ps[j]! - 1).toNat]! = vs[j]!) ∧
  (∀ i, i < xs.length →
      (∀ j, j < ps.length → ps[j]! ≠ (i : Int) + 1) → ys[i]! = xs[i]!)

/-- Boolean twin of `writesProp`. -/
def writesB (xs ps vs ys : List Int) : Bool :=
  decide (xs.length = ys.length) &&
  decide (ps.length = vs.length) &&
  (List.range ps.length).all (fun j =>
    decide (1 ≤ ps[j]! ∧ ps[j]! ≤ ys.length ∧
      ys[(ps[j]! - 1).toNat]! = vs[j]!)) &&
  (List.range xs.length).all (fun i =>
    decide ((List.range ps.length).all (fun j =>
        decide (ps[j]! ≠ (i : Int) + 1)) = true →
      ys[i]! = xs[i]!))

theorem writesB_iff (xs ps vs ys : List Int) :
    writesB xs ps vs ys = true ↔ writesProp xs ps vs ys := by
  simp only [writesB, writesProp, Bool.and_eq_true, decide_eq_true_iff,
    List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-! ## The interpretations -/

/-- Mathematical interpretations of the channeling/member global
    constraints.  A wrong argument shape yields `False`. -/
def channelingInterp : LeanFzn.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_inverse" => fun args =>
    match twoIntArrays args with
    | some (a, b) => inverseProp a b
    | none => False
  | "fzn_inverse_in_range" => fun args =>
    match twoIntArrays args with
    | some (a, b) => inverseInRangeProp a b
    | none => False
  | "fzn_int_set_channel" => fun args =>
    match intAndSetArrays args with
    | some (a, b) => intSetChannelProp a b
    | none => False
  | "fzn_link_set_to_booleans" => fun args =>
    match setAndBoolArray args with
    | some (s, b) => linkSetBoolsProp s b
    | none => False
  | "fzn_member_int" => fun args =>
    match arrayAndInt args with
    | some (a, e) => memberIntProp a e
    | none => False
  | "fzn_member_bool" => fun args =>
    match arrayAndBool args with
    | some (a, e) => memberBoolProp a e
    | none => False
  | "fzn_member_set" => fun args =>
    match arrayAndSet args with
    | some (a, e) => memberSetProp a e
    | none => False
  | "fzn_arg_val_int" => fun args =>
    match arrayIntInt args with
    | some (a, e, i) => argValIntProp a e i
    | none => False
  | "fzn_arg_val_bool" => fun args =>
    match arrayBoolInt args with
    | some (a, e, i) => argValBoolProp a e i
    | none => False
  | "fzn_write" => fun args =>
    match writeArgs args with
    | some (a, i, v, b) => writeProp a i v b
    | none => False
  | "fzn_writes" => fun args =>
    match writesArgs args with
    | some (a, p, v, b) => writesProp a p v b
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `channelingInterp`**: computes the truth of
    the channeling/member interpretations; `false` on a wrong
    shape. -/
def channelingInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_inverse" => fun args =>
    match twoIntArrays args with
    | some (a, b) => inverseB a b
    | none => false
  | "fzn_inverse_in_range" => fun args =>
    match twoIntArrays args with
    | some (a, b) => inverseInRangeB a b
    | none => false
  | "fzn_int_set_channel" => fun args =>
    match intAndSetArrays args with
    | some (a, b) => intSetChannelB a b
    | none => false
  | "fzn_link_set_to_booleans" => fun args =>
    match setAndBoolArray args with
    | some (s, b) => linkSetBoolsB s b
    | none => false
  | "fzn_member_int" => fun args =>
    match arrayAndInt args with
    | some (a, e) => memberIntB a e
    | none => false
  | "fzn_member_bool" => fun args =>
    match arrayAndBool args with
    | some (a, e) => memberBoolB a e
    | none => false
  | "fzn_member_set" => fun args =>
    match arrayAndSet args with
    | some (a, e) => memberSetB a e
    | none => false
  | "fzn_arg_val_int" => fun args =>
    match arrayIntInt args with
    | some (a, e, i) => argValIntB a e i
    | none => false
  | "fzn_arg_val_bool" => fun args =>
    match arrayBoolInt args with
    | some (a, e, i) => argValBoolB a e i
    | none => false
  | "fzn_write" => fun args =>
    match writeArgs args with
    | some (a, i, v, b) => writeB a i v b
    | none => false
  | "fzn_writes" => fun args =>
    match writesArgs args with
    | some (a, p, v, b) => writesB a p v b
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_inverse_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_inverse") args = true ↔
      channelingInterp (Ident.mk "fzn_inverse") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : twoIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact inverseB_iff a b

theorem fzn_inverse_in_range_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_inverse_in_range") args = true ↔
      channelingInterp (Ident.mk "fzn_inverse_in_range") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : twoIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact inverseInRangeB_iff a b

theorem fzn_int_set_channel_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_int_set_channel") args = true ↔
      channelingInterp (Ident.mk "fzn_int_set_channel") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : intAndSetArrays args with
  | none => simp
  | some p =>
    obtain ⟨a, b⟩ := p
    simp only
    exact intSetChannelB_iff a b

theorem fzn_link_set_to_booleans_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_link_set_to_booleans") args = true ↔
      channelingInterp (Ident.mk "fzn_link_set_to_booleans") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : setAndBoolArray args with
  | none => simp
  | some p =>
    obtain ⟨s, b⟩ := p
    simp only
    exact linkSetBoolsB_iff s b

theorem fzn_member_int_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_member_int") args = true ↔
      channelingInterp (Ident.mk "fzn_member_int") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : arrayAndInt args with
  | none => simp
  | some p =>
    obtain ⟨a, e⟩ := p
    simp only
    exact memberIntB_iff a e

theorem fzn_member_bool_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_member_bool") args = true ↔
      channelingInterp (Ident.mk "fzn_member_bool") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : arrayAndBool args with
  | none => simp
  | some p =>
    obtain ⟨a, e⟩ := p
    simp only
    exact memberBoolB_iff a e

theorem fzn_member_set_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_member_set") args = true ↔
      channelingInterp (Ident.mk "fzn_member_set") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : arrayAndSet args with
  | none => simp
  | some p =>
    obtain ⟨a, e⟩ := p
    simp only
    exact memberSetB_iff a e

theorem fzn_arg_val_int_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_arg_val_int") args = true ↔
      channelingInterp (Ident.mk "fzn_arg_val_int") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : arrayIntInt args with
  | none => simp
  | some p =>
    obtain ⟨a, e, i⟩ := p
    simp only
    exact argValIntB_iff a e i

theorem fzn_arg_val_bool_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_arg_val_bool") args = true ↔
      channelingInterp (Ident.mk "fzn_arg_val_bool") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : arrayBoolInt args with
  | none => simp
  | some p =>
    obtain ⟨a, e, i⟩ := p
    simp only
    exact argValBoolB_iff a e i

theorem fzn_write_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_write") args = true ↔
      channelingInterp (Ident.mk "fzn_write") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : writeArgs args with
  | none => simp
  | some p =>
    obtain ⟨a, i, v, b⟩ := p
    simp only
    exact writeB_iff a i v b

theorem fzn_writes_iff (args : List Value) :
    channelingInterpB (Ident.mk "fzn_writes") args = true ↔
      channelingInterp (Ident.mk "fzn_writes") args := by
  simp only [channelingInterp, channelingInterpB]
  cases h : writesArgs args with
  | none => simp
  | some p =>
    obtain ⟨a, p', v, b⟩ := p
    simp only
    exact writesB_iff a p' v b

end LeanFzn.Globals.Channeling
