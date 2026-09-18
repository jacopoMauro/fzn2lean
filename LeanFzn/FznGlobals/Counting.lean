import LeanFzn.FznGlobals.AllDiffCounting

/-!
# Counting global constraints

Mathematical interpretations (`countingInterp`) and executable Boolean
twins (`countingInterpB`) for the counting family of global
constraints of the pinned MiniZinc 2.10.0 FlatZinc tree (32
`fzn_*` names), following the `lexSortInterp` pattern of
`LexSort.lean`.  Each predicate name gets a per-name agreement theorem
`fzn_<name>_iff` proving that the Boolean twin is `true` exactly when
the mathematical interpretation holds.

The interpretive decisions specific to this family (the inequality
orientations of the `count_*` and deprecated `at_least/at_most/exactly`
variants, extensional equality for the set-valued variants, and the
closedness distinctions of the `global_cardinality` family) are
recorded in `specification/flatzinc_specification_assumptions.md`,
G10–G11.

Semantics per the MiniZinc 2.10.0 handbook, Section 4.2.2.4 ("Counting
Constraints", `lib-globals-counting.html`), cross-checked against the
pinned stdlib decompositions (`share/minizinc/std/fzn_*.mzn`) and the
deprecated-globals page for the `at_least/at_most/exactly` int
variants and `global_cardinality_low_up[_closed]`:

* `nvalue` — "Requires that the number of distinct values in xs is n".
* `among` — "Requires exactly n variables in xs to take one of the
  values in values".
* `at_least` (deprecated; `fzn_at_least_int`) — "Requires at least n
  variables in xs to take the value value", i.e.
  `count(i in xs)(i=value) >= n`.
* `at_most` — "... at most n ...", i.e. `count(i in xs)(i=value) <= n`.
* `exactly` — "... exactly n ...", i.e. `count(i in xs)(i=value) = n`.
* `count_eq` — "Constrains n to be the number of occurrences of value
  in xs".
* `count_geq` — "Constrains n to be greater than or equal to the number
  of occurrences of value in xs" (the stdlib decomposes `fzn_count_geq`
  to `z <= n`, where `z = count(xs, value)`).
* `count_gt` — "Constrains n to be strictly greater than the number of
  occurrences of value in xs" (`z < n`).
* `count_leq` — "Constrains n to be less than or equal to the number
  of occurrences of value in xs" (`z >= n`).
* `count_lt` — "Constrains n to be strictly less than the number of
  occurrences of value in xs" (`z > n`).
* `count_neq` — "Constrains n to be not equal to the number of
  occurrences of value in xs" (`z != n`).
* `distribute` — "Requires that count[i] is the number of occurrences
  of cover[i] in xs.  The values in cover need not be distinct."  (The
  `fzn_distribute` argument order is `count, cover, xs`.)
* `global_cardinality` — "Requires that the number of occurrences of
  cover[i] in xs is count[i]".  Values of `xs` outside `cover` are
  unconstrained.
* `global_cardinality_closed` — same, plus "The elements of xs must
  take their values from cover".
* `global_cardinality_low_up` (deprecated) — "Requires that for all i,
  the value cover[i] appears at least lower_bound[i] and at most
  upper_bound[i] times in the array x" (not closed).
* `global_cardinality_low_up_closed` — same, plus "The elements of x
  must take their values from cover".

Set variants (counting positions whose set is *extensionally* equal
to the given set, per the stdlib decompositions
`fzn_count_eq_set.mzn`, `fzn_at_least_set.mzn`, ... which all sum
`x_i == value` with set equality):

* `count_eq_set` — n = number of positions of `xs` whose set is
  extensionally equal to `value`.
* `count_geq_set` — that number ≤ n (n ≥ count).
* `count_gt_set` — that number < n.
* `count_leq_set` — that number ≥ n (n ≤ count).
* `count_lt_set` — that number > n.
* `count_neq_set` — that number ≠ n.
* `at_least_set` — "Requires at least n variables in xs to take the
  value value": the number of positions of `xs` extensionally equal to
  `value` is ≥ n.
* `at_most_set` — ... at most n ...
* `exactly_set` — ... exactly n ...
-/

namespace LeanFzn.Globals.Counting

open LeanFzn LeanFzn.Globals LeanFzn.Globals.AllDiffCounting LeanFzn.Solution

/-! ## Additional argument decoders

`AllDiffCounting` already provides `intAndArr`, `intArrInt`,
`arrIntInt`, `threeIntArrs`, `fourIntArrs`, `setCountArgs`,
`atLeastSetArgs`.  The `among` signature
(`var int n, array of var int, par set of int`) needs one more. -/

/-- Decode `[.int n, .array xs, .setOfInt S]` (the `fzn_among` shape). -/
def intArrSet (args : List Value) : Option (Int × List Int × IntSetValue) :=
  match args with
  | [.int n, .array xs, .setOfInt S] =>
      match valueInts xs with
      | some l => some (n, l, S)
      | none => none
  | _ => none

/-! ## Counting helpers with iff bridges -/

/-- Number of distinct values of an integer list: the length of the
    duplicate-free view (each value with a positive occurrence count
    is kept exactly once). -/
def nvalueCount (l : List Int) : Nat := l.eraseDups.length

/-- `nvalueCount` counts exactly the values occurring in `l`. -/
theorem mem_eraseDups_iff_count_pos {l : List Int} {v : Int} :
    v ∈ l.eraseDups ↔ 0 < intCount l v := by
  rw [show (v ∈ l.eraseDups) ↔ (v ∈ l) from List.mem_eraseDups, intCount,
    show (0 < List.count v l) ↔ (v ∈ l) from List.count_pos_iff]

/-- Number of elements of an integer list that are members of `S`. -/
def amongCount (l : List Int) (S : IntSetValue) : Nat :=
  (l.filter (fun x => setMemB S x)).length

/-- `amongCount` counts exactly the elements of `l` that are
    contained in `S`: the filtered list holds the elements of `l`
    that `S` contains. -/
theorem mem_filter_amongCount {l : List Int} {S : IntSetValue} {x : Int} :
    x ∈ l.filter (fun x => setMemB S x) ↔ (x ∈ l ∧ S.Contains x) := by
  simp only [List.mem_filter, setMemB_iff]

/-- `fzn_among`: n equals the number of positions of `xs` whose value
    is a member of `S` ("Requires exactly n variables in xs to take
    one of the values in values"). -/
def amongProp (l : List Int) (S : IntSetValue) (n : Int) : Prop :=
  n = (amongCount l S : Int)

/-- Boolean twin of `amongProp`. -/
def amongB (l : List Int) (S : IntSetValue) (n : Int) : Bool :=
  decide (n = (amongCount l S : Int))

theorem amongB_iff (l : List Int) (S : IntSetValue) (n : Int) :
    amongB l S n = true ↔ amongProp l S n := decide_eq_true_iff

/-- `fzn_at_least_int`: at least `n` occurrences of `v` in `l`. -/
def atLeastIntProp (n : Int) (l : List Int) (v : Int) : Prop :=
  (n : Int) ≤ (intCount l v : Int)

/-- `fzn_at_most_int`: at most `n` occurrences of `v` in `l`. -/
def atMostIntProp (n : Int) (l : List Int) (v : Int) : Prop :=
  (intCount l v : Int) ≤ n

/-- `fzn_exactly_int`: exactly `n` occurrences of `v` in `l`. -/
def exactlyIntProp (n : Int) (l : List Int) (v : Int) : Prop :=
  (intCount l v : Int) = n

/-! ## Occurrence-comparison Boolean twins

Each is the `decide` of its Prop, so the iff lemma is
`decide_eq_true_iff`. -/

/-- `fzn_count_eq`: n = the number of occurrences of `v` in `l`. -/
def countEqProp (l : List Int) (v : Int) (n : Int) : Prop :=
  (n : Int) = (intCount l v : Int)

/-- `fzn_count_geq`: "Constrains n to be greater than or equal to the
    number of occurrences" — the count is at most `n`. -/
def countGeqProp (l : List Int) (v : Int) (n : Int) : Prop :=
  (intCount l v : Int) ≤ n

/-- `fzn_count_gt`: "Constrains n to be strictly greater than the
    number of occurrences" — the count is strictly less than `n`. -/
def countGtProp (l : List Int) (v : Int) (n : Int) : Prop :=
  (intCount l v : Int) < n

/-- `fzn_count_leq`: "Constrains n to be less than or equal to the
    number of occurrences" — the count is at least `n`. -/
def countLeqProp (l : List Int) (v : Int) (n : Int) : Prop :=
  (n : Int) ≤ (intCount l v : Int)

/-- `fzn_count_lt`: "Constrains n to be strictly less than the number
    of occurrences" — the count is strictly greater than `n`. -/
def countLtProp (l : List Int) (v : Int) (n : Int) : Prop :=
  (n : Int) < (intCount l v : Int)

/-- `fzn_count_neq`: the count differs from `n`. -/
def countNeqProp (l : List Int) (v : Int) (n : Int) : Prop :=
  (intCount l v : Int) ≠ n

/-! ## Set-counting helpers -/

/-- Number of positions of `ss` whose set is extensionally equal to
    `v` (the count of the `count_*_set` family). -/
def setEqCount (ss : List IntSetValue) (v : IntSetValue) : Nat :=
  setEqCountB ss v

/-- `fzn_count_eq_set`-family Prop: `n` relates to the number of
    positions of `ss` whose set is extensionally equal to `v`. -/
def setCountEqProp (ss : List IntSetValue) (v : IntSetValue) (n : Int) : Prop :=
  (n : Int) = (setEqCount ss v : Int)

def setCountGeqProp (ss : List IntSetValue) (v : IntSetValue) (n : Int) : Prop :=
  (setEqCount ss v : Int) ≤ n

def setCountGtProp (ss : List IntSetValue) (v : IntSetValue) (n : Int) : Prop :=
  (setEqCount ss v : Int) < n

def setCountLeqProp (ss : List IntSetValue) (v : IntSetValue) (n : Int) : Prop :=
  (n : Int) ≤ (setEqCount ss v : Int)

def setCountLtProp (ss : List IntSetValue) (v : IntSetValue) (n : Int) : Prop :=
  (n : Int) < (setEqCount ss v : Int)

def setCountNeqProp (ss : List IntSetValue) (v : IntSetValue) (n : Int) : Prop :=
  (setEqCount ss v : Int) ≠ n

/-- `fzn_at_least_set`: at least `n` positions of `ss` are
    extensionally equal to `v`. -/
def atLeastSetProp (n : Int) (ss : List IntSetValue) (v : IntSetValue) : Prop :=
  (n : Int) ≤ (setEqCount ss v : Int)

/-- `fzn_at_most_set`: at most `n` positions of `ss` are
    extensionally equal to `v`. -/
def atMostSetProp (n : Int) (ss : List IntSetValue) (v : IntSetValue) : Prop :=
  (setEqCount ss v : Int) ≤ n

/-- `fzn_exactly_set`: exactly `n` positions of `ss` are
    extensionally equal to `v`. -/
def exactlySetProp (n : Int) (ss : List IntSetValue) (v : IntSetValue) : Prop :=
  (setEqCount ss v : Int) = n

/-- Boolean twin of `atLeastSetProp`. -/
def atLeastSetB (n : Int) (ss : List IntSetValue) (v : IntSetValue) : Bool :=
  decide ((n : Int) ≤ (setEqCount ss v : Int))

/-- Boolean twin of `atMostSetProp`. -/
def atMostSetB (n : Int) (ss : List IntSetValue) (v : IntSetValue) : Bool :=
  decide ((setEqCount ss v : Int) ≤ n)

/-- Boolean twin of `exactlySetProp`. -/
def exactlySetB (n : Int) (ss : List IntSetValue) (v : IntSetValue) : Bool :=
  decide ((setEqCount ss v : Int) = n)

theorem atLeastSetB_iff (n : Int) (ss : List IntSetValue) (v : IntSetValue) :
    atLeastSetB n ss v = true ↔ atLeastSetProp n ss v := decide_eq_true_iff

theorem atMostSetB_iff (n : Int) (ss : List IntSetValue) (v : IntSetValue) :
    atMostSetB n ss v = true ↔ atMostSetProp n ss v := decide_eq_true_iff

theorem exactlySetB_iff (n : Int) (ss : List IntSetValue) (v : IntSetValue) :
    exactlySetB n ss v = true ↔ exactlySetProp n ss v := decide_eq_true_iff

/-! ## Array cardinality helpers (distribute, global_cardinality) -/

/-- `fzn_distribute(count, cover, xs)`: `count[i]` is the number of
    occurrences of `cover[i]` in `xs` ("The values in cover need not
    be distinct"). -/
def distributeProp (count cover xs : List Int) : Prop :=
  ∀ i : Nat, i < cover.length →
    (count[i]! : Int) = (intCount xs cover[i]! : Int)

/-- Boolean twin of `distributeProp`. -/
def distributeB (count cover xs : List Int) : Bool :=
  (List.range cover.length).all (fun i =>
    decide ((count[i]! : Int) = (intCount xs cover[i]! : Int)))

theorem distributeB_iff (count cover xs : List Int) :
    distributeB count cover xs = true ↔ distributeProp count cover xs := by
  simp only [distributeB, distributeProp, List.all_eq_true, List.mem_range,
    decide_eq_true_iff]

/-- `fzn_global_cardinality(xs, cover, counts)`: for each `i`, the
    number of occurrences of `cover[i]` in `xs` is `counts[i]`.  Values
    of `xs` outside `cover` are unconstrained. -/
def gccProp (xs cover counts : List Int) : Prop :=
  ∀ i : Nat, i < cover.length →
    (intCount xs cover[i]! : Int) = (counts[i]! : Int)

/-- Boolean twin of `gccProp`. -/
def gccB (xs cover counts : List Int) : Bool :=
  (List.range cover.length).all (fun i =>
    decide ((intCount xs cover[i]! : Int) = (counts[i]! : Int)))

theorem gccB_iff (xs cover counts : List Int) :
    gccB xs cover counts = true ↔ gccProp xs cover counts := by
  simp only [gccB, gccProp, List.all_eq_true, List.mem_range, decide_eq_true_iff]

/-- `fzn_global_cardinality_closed(xs, cover, counts)`: the
    global-cardinality condition plus "The elements of xs must take
    their values from cover". -/
def gccClosedProp (xs cover counts : List Int) : Prop :=
  gccProp xs cover counts ∧ ∀ j : Nat, j < xs.length → xs[j]! ∈ cover

/-- Boolean twin of `gccClosedProp`. -/
def gccClosedB (xs cover counts : List Int) : Bool :=
  gccB xs cover counts &&
  (List.range xs.length).all (fun j => decide (xs[j]! ∈ cover))

theorem gccClosedB_iff (xs cover counts : List Int) :
    gccClosedB xs cover counts = true ↔ gccClosedProp xs cover counts := by
  simp only [gccClosedB, gccClosedProp, gccB, gccProp, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, decide_eq_true_iff]

/-- `fzn_global_cardinality_low_up(xs, cover, low, up)`: for each
    `i`, the value `cover[i]` appears at least `low[i]` and at most
    `up[i]` times in `xs` (deprecated, NOT closed: elements of `xs`
    outside `cover` are unconstrained). -/
def gccLowUpProp (xs cover low up : List Int) : Prop :=
  ∀ i : Nat, i < cover.length →
    (low[i]! : Int) ≤ (intCount xs cover[i]! : Int) ∧
      (intCount xs cover[i]! : Int) ≤ (up[i]! : Int)

/-- Boolean twin of `gccLowUpProp`. -/
def gccLowUpB (xs cover low up : List Int) : Bool :=
  (List.range cover.length).all (fun i =>
    decide ((low[i]! : Int) ≤ (intCount xs cover[i]! : Int) ∧
      (intCount xs cover[i]! : Int) ≤ (up[i]! : Int)))

theorem gccLowUpB_iff (xs cover low up : List Int) :
    gccLowUpB xs cover low up = true ↔ gccLowUpProp xs cover low up := by
  simp only [gccLowUpB, gccLowUpProp, List.all_eq_true, List.mem_range,
    decide_eq_true_iff]

/-- `fzn_global_cardinality_low_up_closed(xs, cover, low, up)`: the
    low/up condition plus "The elements of x must take their values
    from cover". -/
def gccLowUpClosedProp (xs cover low up : List Int) : Prop :=
  gccLowUpProp xs cover low up ∧ ∀ j : Nat, j < xs.length → xs[j]! ∈ cover

/-- Boolean twin of `gccLowUpClosedProp`. -/
def gccLowUpClosedB (xs cover low up : List Int) : Bool :=
  gccLowUpB xs cover low up &&
  (List.range xs.length).all (fun j => decide (xs[j]! ∈ cover))

theorem gccLowUpClosedB_iff (xs cover low up : List Int) :
    gccLowUpClosedB xs cover low up = true ↔ gccLowUpClosedProp xs cover low up := by
  simp only [gccLowUpClosedB, gccLowUpClosedProp, gccLowUpB, gccLowUpProp,
    Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_iff]

/-! ## The interpretations -/

/-- Mathematical interpretations of the counting family of
    global-constraint predicates.  A wrong argument shape yields
    `False`. -/
def countingInterp : LeanFzn.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_nvalue" => fun args =>
    match intAndArr args with
    | some (n, l) => n = (nvalueCount l : Int)
    | none => False
  | "fzn_among" => fun args =>
    match intArrSet args with
    | some (n, l, S) => amongProp l S n
    | none => False
  | "fzn_at_least_int" => fun args =>
    match intArrInt args with
    | some (n, l, v) => atLeastIntProp n l v
    | none => False
  | "fzn_at_most_int" => fun args =>
    match intArrInt args with
    | some (n, l, v) => atMostIntProp n l v
    | none => False
  | "fzn_exactly_int" => fun args =>
    match intArrInt args with
    | some (n, l, v) => exactlyIntProp n l v
    | none => False
  | "fzn_count_eq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countEqProp l v n
    | none => False
  | "fzn_count_eq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countEqProp l v n
    | none => False
  | "fzn_count_geq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countGeqProp l v n
    | none => False
  | "fzn_count_geq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countGeqProp l v n
    | none => False
  | "fzn_count_gt" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countGtProp l v n
    | none => False
  | "fzn_count_gt_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countGtProp l v n
    | none => False
  | "fzn_count_leq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countLeqProp l v n
    | none => False
  | "fzn_count_leq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countLeqProp l v n
    | none => False
  | "fzn_count_lt" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countLtProp l v n
    | none => False
  | "fzn_count_lt_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countLtProp l v n
    | none => False
  | "fzn_count_neq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countNeqProp l v n
    | none => False
  | "fzn_count_neq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => countNeqProp l v n
    | none => False
  | "fzn_distribute" => fun args =>
    match threeIntArrs args with
    | some (count, cover, xs) => distributeProp count cover xs
    | none => False
  | "fzn_global_cardinality" => fun args =>
    match threeIntArrs args with
    | some (xs, cover, counts) => gccProp xs cover counts
    | none => False
  | "fzn_global_cardinality_closed" => fun args =>
    match threeIntArrs args with
    | some (xs, cover, counts) => gccClosedProp xs cover counts
    | none => False
  | "fzn_global_cardinality_low_up" => fun args =>
    match fourIntArrs args with
    | some (xs, cover, low, up) => gccLowUpProp xs cover low up
    | none => False
  | "fzn_global_cardinality_low_up_closed" => fun args =>
    match fourIntArrs args with
    | some (xs, cover, low, up) => gccLowUpClosedProp xs cover low up
    | none => False
  | "fzn_count_eq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => setCountEqProp ss v n
    | none => False
  | "fzn_count_eq_set_par" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => setCountEqProp ss v n
    | none => False
  | "fzn_count_geq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => setCountGeqProp ss v n
    | none => False
  | "fzn_count_gt_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => setCountGtProp ss v n
    | none => False
  | "fzn_count_leq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => setCountLeqProp ss v n
    | none => False
  | "fzn_count_lt_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => setCountLtProp ss v n
    | none => False
  | "fzn_count_neq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => setCountNeqProp ss v n
    | none => False
  | "fzn_at_least_set" => fun args =>
    match atLeastSetArgs args with
    | some (n, ss, v) => atLeastSetProp n ss v
    | none => False
  | "fzn_at_most_set" => fun args =>
    match atLeastSetArgs args with
    | some (n, ss, v) => atMostSetProp n ss v
    | none => False
  | "fzn_exactly_set" => fun args =>
    match atLeastSetArgs args with
    | some (n, ss, v) => exactlySetProp n ss v
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `countingInterp`**: computes the truth of the
    counting interpretations; `false` on a wrong shape. -/
def countingInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_nvalue" => fun args =>
    match intAndArr args with
    | some (n, l) => decide (n = (nvalueCount l : Int))
    | none => false
  | "fzn_among" => fun args =>
    match intArrSet args with
    | some (n, l, S) => amongB l S n
    | none => false
  | "fzn_at_least_int" => fun args =>
    match intArrInt args with
    | some (n, l, v) => decide ((n : Int) ≤ (intCount l v : Int))
    | none => false
  | "fzn_at_most_int" => fun args =>
    match intArrInt args with
    | some (n, l, v) => decide ((intCount l v : Int) ≤ n)
    | none => false
  | "fzn_exactly_int" => fun args =>
    match intArrInt args with
    | some (n, l, v) => decide ((intCount l v : Int) = n)
    | none => false
  | "fzn_count_eq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((n : Int) = (intCount l v : Int))
    | none => false
  | "fzn_count_eq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((n : Int) = (intCount l v : Int))
    | none => false
  | "fzn_count_geq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((intCount l v : Int) ≤ n)
    | none => false
  | "fzn_count_geq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((intCount l v : Int) ≤ n)
    | none => false
  | "fzn_count_gt" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((intCount l v : Int) < n)
    | none => false
  | "fzn_count_gt_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((intCount l v : Int) < n)
    | none => false
  | "fzn_count_leq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((n : Int) ≤ (intCount l v : Int))
    | none => false
  | "fzn_count_leq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((n : Int) ≤ (intCount l v : Int))
    | none => false
  | "fzn_count_lt" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((n : Int) < (intCount l v : Int))
    | none => false
  | "fzn_count_lt_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((n : Int) < (intCount l v : Int))
    | none => false
  | "fzn_count_neq" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((intCount l v : Int) ≠ n)
    | none => false
  | "fzn_count_neq_par" => fun args =>
    match arrIntInt args with
    | some (l, v, n) => decide ((intCount l v : Int) ≠ n)
    | none => false
  | "fzn_distribute" => fun args =>
    match threeIntArrs args with
    | some (count, cover, xs) => distributeB count cover xs
    | none => false
  | "fzn_global_cardinality" => fun args =>
    match threeIntArrs args with
    | some (xs, cover, counts) => gccB xs cover counts
    | none => false
  | "fzn_global_cardinality_closed" => fun args =>
    match threeIntArrs args with
    | some (xs, cover, counts) => gccClosedB xs cover counts
    | none => false
  | "fzn_global_cardinality_low_up" => fun args =>
    match fourIntArrs args with
    | some (xs, cover, low, up) => gccLowUpB xs cover low up
    | none => false
  | "fzn_global_cardinality_low_up_closed" => fun args =>
    match fourIntArrs args with
    | some (xs, cover, low, up) => gccLowUpClosedB xs cover low up
    | none => false
  | "fzn_count_eq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => decide ((n : Int) = (setEqCount ss v : Int))
    | none => false
  | "fzn_count_eq_set_par" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => decide ((n : Int) = (setEqCount ss v : Int))
    | none => false
  | "fzn_count_geq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => decide ((setEqCount ss v : Int) ≤ n)
    | none => false
  | "fzn_count_gt_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => decide ((setEqCount ss v : Int) < n)
    | none => false
  | "fzn_count_leq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => decide ((n : Int) ≤ (setEqCount ss v : Int))
    | none => false
  | "fzn_count_lt_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => decide ((n : Int) < (setEqCount ss v : Int))
    | none => false
  | "fzn_count_neq_set" => fun args =>
    match setCountArgs args with
    | some (ss, v, n) => decide ((setEqCount ss v : Int) ≠ n)
    | none => false
  | "fzn_at_least_set" => fun args =>
    match atLeastSetArgs args with
    | some (n, ss, v) => atLeastSetB n ss v
    | none => false
  | "fzn_at_most_set" => fun args =>
    match atLeastSetArgs args with
    | some (n, ss, v) => atMostSetB n ss v
    | none => false
  | "fzn_exactly_set" => fun args =>
    match atLeastSetArgs args with
    | some (n, ss, v) => exactlySetB n ss v
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_nvalue_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_nvalue") args = true ↔
      countingInterp (Ident.mk "fzn_nvalue") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_nvalue") args
      = match intAndArr args with
  | some (n, l) => decide (n = (nvalueCount l : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_nvalue") args
      = match intAndArr args with
  | some (n, l) => n = (nvalueCount l : Int)
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : intAndArr args with
  | none => simp
  | some p =>
    obtain ⟨n, l⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_among_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_among") args = true ↔
      countingInterp (Ident.mk "fzn_among") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_among") args
      = match intArrSet args with
  | some (n, l, S) => amongB l S n
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_among") args
      = match intArrSet args with
  | some (n, l, S) => amongProp l S n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : intArrSet args with
  | none => simp
  | some p =>
    obtain ⟨n, l, S⟩ := p
    simp only
    exact amongB_iff l S n

theorem fzn_at_least_int_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_at_least_int") args = true ↔
      countingInterp (Ident.mk "fzn_at_least_int") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_at_least_int") args
      = match intArrInt args with
  | some (n, l, v) => decide ((n : Int) ≤ (intCount l v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_at_least_int") args
      = match intArrInt args with
  | some (n, l, v) => atLeastIntProp n l v
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : intArrInt args with
  | none => simp
  | some p =>
    obtain ⟨n, l, v⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_at_most_int_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_at_most_int") args = true ↔
      countingInterp (Ident.mk "fzn_at_most_int") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_at_most_int") args
      = match intArrInt args with
  | some (n, l, v) => decide ((intCount l v : Int) ≤ n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_at_most_int") args
      = match intArrInt args with
  | some (n, l, v) => atMostIntProp n l v
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : intArrInt args with
  | none => simp
  | some p =>
    obtain ⟨n, l, v⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_exactly_int_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_exactly_int") args = true ↔
      countingInterp (Ident.mk "fzn_exactly_int") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_exactly_int") args
      = match intArrInt args with
  | some (n, l, v) => decide ((intCount l v : Int) = n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_exactly_int") args
      = match intArrInt args with
  | some (n, l, v) => exactlyIntProp n l v
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : intArrInt args with
  | none => simp
  | some p =>
    obtain ⟨n, l, v⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_eq_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_eq") args = true ↔
      countingInterp (Ident.mk "fzn_count_eq") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_eq") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((n : Int) = (intCount l v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_eq") args
      = match arrIntInt args with
  | some (l, v, n) => countEqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_eq_par_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_eq_par") args = true ↔
      countingInterp (Ident.mk "fzn_count_eq_par") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_eq_par") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((n : Int) = (intCount l v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_eq_par") args
      = match arrIntInt args with
  | some (l, v, n) => countEqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_geq_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_geq") args = true ↔
      countingInterp (Ident.mk "fzn_count_geq") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_geq") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((intCount l v : Int) ≤ n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_geq") args
      = match arrIntInt args with
  | some (l, v, n) => countGeqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_geq_par_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_geq_par") args = true ↔
      countingInterp (Ident.mk "fzn_count_geq_par") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_geq_par") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((intCount l v : Int) ≤ n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_geq_par") args
      = match arrIntInt args with
  | some (l, v, n) => countGeqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_gt_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_gt") args = true ↔
      countingInterp (Ident.mk "fzn_count_gt") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_gt") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((intCount l v : Int) < n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_gt") args
      = match arrIntInt args with
  | some (l, v, n) => countGtProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_gt_par_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_gt_par") args = true ↔
      countingInterp (Ident.mk "fzn_count_gt_par") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_gt_par") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((intCount l v : Int) < n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_gt_par") args
      = match arrIntInt args with
  | some (l, v, n) => countGtProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_leq_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_leq") args = true ↔
      countingInterp (Ident.mk "fzn_count_leq") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_leq") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((n : Int) ≤ (intCount l v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_leq") args
      = match arrIntInt args with
  | some (l, v, n) => countLeqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_leq_par_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_leq_par") args = true ↔
      countingInterp (Ident.mk "fzn_count_leq_par") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_leq_par") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((n : Int) ≤ (intCount l v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_leq_par") args
      = match arrIntInt args with
  | some (l, v, n) => countLeqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_lt_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_lt") args = true ↔
      countingInterp (Ident.mk "fzn_count_lt") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_lt") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((n : Int) < (intCount l v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_lt") args
      = match arrIntInt args with
  | some (l, v, n) => countLtProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_lt_par_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_lt_par") args = true ↔
      countingInterp (Ident.mk "fzn_count_lt_par") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_lt_par") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((n : Int) < (intCount l v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_lt_par") args
      = match arrIntInt args with
  | some (l, v, n) => countLtProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_neq_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_neq") args = true ↔
      countingInterp (Ident.mk "fzn_count_neq") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_neq") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((intCount l v : Int) ≠ n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_neq") args
      = match arrIntInt args with
  | some (l, v, n) => countNeqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_neq_par_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_neq_par") args = true ↔
      countingInterp (Ident.mk "fzn_count_neq_par") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_neq_par") args
      = match arrIntInt args with
  | some (l, v, n) => decide ((intCount l v : Int) ≠ n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_neq_par") args
      = match arrIntInt args with
  | some (l, v, n) => countNeqProp l v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : arrIntInt args with
  | none => simp
  | some p =>
    obtain ⟨l, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_distribute_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_distribute") args = true ↔
      countingInterp (Ident.mk "fzn_distribute") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_distribute") args
      = match threeIntArrs args with
  | some (count, cover, xs) => distributeB count cover xs
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_distribute") args
      = match threeIntArrs args with
  | some (count, cover, xs) => distributeProp count cover xs
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : threeIntArrs args with
  | none => simp
  | some p =>
    obtain ⟨count, cover, xs⟩ := p
    simp only
    exact distributeB_iff count cover xs

theorem fzn_global_cardinality_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_global_cardinality") args = true ↔
      countingInterp (Ident.mk "fzn_global_cardinality") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_global_cardinality") args
      = match threeIntArrs args with
  | some (xs, cover, counts) => gccB xs cover counts
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_global_cardinality") args
      = match threeIntArrs args with
  | some (xs, cover, counts) => gccProp xs cover counts
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : threeIntArrs args with
  | none => simp
  | some p =>
    obtain ⟨xs, cover, counts⟩ := p
    simp only
    exact gccB_iff xs cover counts

theorem fzn_global_cardinality_closed_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_global_cardinality_closed") args = true ↔
      countingInterp (Ident.mk "fzn_global_cardinality_closed") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_global_cardinality_closed") args
      = match threeIntArrs args with
  | some (xs, cover, counts) => gccClosedB xs cover counts
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_global_cardinality_closed") args
      = match threeIntArrs args with
  | some (xs, cover, counts) => gccClosedProp xs cover counts
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : threeIntArrs args with
  | none => simp
  | some p =>
    obtain ⟨xs, cover, counts⟩ := p
    simp only
    exact gccClosedB_iff xs cover counts

theorem fzn_global_cardinality_low_up_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_global_cardinality_low_up") args = true ↔
      countingInterp (Ident.mk "fzn_global_cardinality_low_up") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_global_cardinality_low_up") args
      = match fourIntArrs args with
  | some (xs, cover, low, up) => gccLowUpB xs cover low up
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_global_cardinality_low_up") args
      = match fourIntArrs args with
  | some (xs, cover, low, up) => gccLowUpProp xs cover low up
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : fourIntArrs args with
  | none => simp
  | some p =>
    obtain ⟨xs, cover, low, up⟩ := p
    simp only
    exact gccLowUpB_iff xs cover low up

theorem fzn_global_cardinality_low_up_closed_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_global_cardinality_low_up_closed") args = true ↔
      countingInterp (Ident.mk "fzn_global_cardinality_low_up_closed") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_global_cardinality_low_up_closed") args
      = match fourIntArrs args with
  | some (xs, cover, low, up) => gccLowUpClosedB xs cover low up
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_global_cardinality_low_up_closed") args
      = match fourIntArrs args with
  | some (xs, cover, low, up) => gccLowUpClosedProp xs cover low up
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : fourIntArrs args with
  | none => simp
  | some p =>
    obtain ⟨xs, cover, low, up⟩ := p
    simp only
    exact gccLowUpClosedB_iff xs cover low up

theorem fzn_count_eq_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_eq_set") args = true ↔
      countingInterp (Ident.mk "fzn_count_eq_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_eq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => decide ((n : Int) = (setEqCount ss v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_eq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => setCountEqProp ss v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : setCountArgs args with
  | none => simp
  | some p =>
    obtain ⟨ss, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_eq_set_par_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_eq_set_par") args = true ↔
      countingInterp (Ident.mk "fzn_count_eq_set_par") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_eq_set_par") args
      = match setCountArgs args with
  | some (ss, v, n) => decide ((n : Int) = (setEqCount ss v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_eq_set_par") args
      = match setCountArgs args with
  | some (ss, v, n) => setCountEqProp ss v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : setCountArgs args with
  | none => simp
  | some p =>
    obtain ⟨ss, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_geq_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_geq_set") args = true ↔
      countingInterp (Ident.mk "fzn_count_geq_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_geq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => decide ((setEqCount ss v : Int) ≤ n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_geq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => setCountGeqProp ss v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : setCountArgs args with
  | none => simp
  | some p =>
    obtain ⟨ss, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_gt_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_gt_set") args = true ↔
      countingInterp (Ident.mk "fzn_count_gt_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_gt_set") args
      = match setCountArgs args with
  | some (ss, v, n) => decide ((setEqCount ss v : Int) < n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_gt_set") args
      = match setCountArgs args with
  | some (ss, v, n) => setCountGtProp ss v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : setCountArgs args with
  | none => simp
  | some p =>
    obtain ⟨ss, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_leq_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_leq_set") args = true ↔
      countingInterp (Ident.mk "fzn_count_leq_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_leq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => decide ((n : Int) ≤ (setEqCount ss v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_leq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => setCountLeqProp ss v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : setCountArgs args with
  | none => simp
  | some p =>
    obtain ⟨ss, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_lt_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_lt_set") args = true ↔
      countingInterp (Ident.mk "fzn_count_lt_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_lt_set") args
      = match setCountArgs args with
  | some (ss, v, n) => decide ((n : Int) < (setEqCount ss v : Int))
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_lt_set") args
      = match setCountArgs args with
  | some (ss, v, n) => setCountLtProp ss v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : setCountArgs args with
  | none => simp
  | some p =>
    obtain ⟨ss, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_count_neq_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_count_neq_set") args = true ↔
      countingInterp (Ident.mk "fzn_count_neq_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_count_neq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => decide ((setEqCount ss v : Int) ≠ n)
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_count_neq_set") args
      = match setCountArgs args with
  | some (ss, v, n) => setCountNeqProp ss v n
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : setCountArgs args with
  | none => simp
  | some p =>
    obtain ⟨ss, v, n⟩ := p
    simp only
    exact decide_eq_true_iff

theorem fzn_at_least_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_at_least_set") args = true ↔
      countingInterp (Ident.mk "fzn_at_least_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_at_least_set") args
      = match atLeastSetArgs args with
  | some (n, ss, v) => atLeastSetB n ss v
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_at_least_set") args
      = match atLeastSetArgs args with
  | some (n, ss, v) => atLeastSetProp n ss v
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : atLeastSetArgs args with
  | none => simp
  | some p =>
    obtain ⟨n, ss, v⟩ := p
    simp only
    exact atLeastSetB_iff n ss v

theorem fzn_at_most_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_at_most_set") args = true ↔
      countingInterp (Ident.mk "fzn_at_most_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_at_most_set") args
      = match atLeastSetArgs args with
  | some (n, ss, v) => atMostSetB n ss v
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_at_most_set") args
      = match atLeastSetArgs args with
  | some (n, ss, v) => atMostSetProp n ss v
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : atLeastSetArgs args with
  | none => simp
  | some p =>
    obtain ⟨n, ss, v⟩ := p
    simp only
    exact atMostSetB_iff n ss v

theorem fzn_exactly_set_iff (args : List Value) :
    countingInterpB (Ident.mk "fzn_exactly_set") args = true ↔
      countingInterp (Ident.mk "fzn_exactly_set") args := by
  have hB : ∀ args, countingInterpB (Ident.mk "fzn_exactly_set") args
      = match atLeastSetArgs args with
  | some (n, ss, v) => exactlySetB n ss v
  | none => false := fun _ => rfl
  have hI : ∀ args, countingInterp (Ident.mk "fzn_exactly_set") args
      = match atLeastSetArgs args with
  | some (n, ss, v) => exactlySetProp n ss v
  | none => False := fun _ => rfl
  rw [hB args, hI args]
  cases h : atLeastSetArgs args with
  | none => simp
  | some p =>
    obtain ⟨n, ss, v⟩ := p
    simp only
    exact exactlySetB_iff n ss v

end LeanFzn.Globals.Counting
