import LeanFzn.FznGlobals.Common

/-!
# Packing, scheduling, extensional (table), and if-then-else global constraints

Mathematical interpretations (`packSchedInterp`) and executable Boolean
twins (`packSchedInterpB`) for the packing, scheduling, extensional and
if-then-else families of global-constraint predicates of the pinned
MiniZinc 2.10.0 FlatZinc tree (17 `fzn_*` names), following the
`lexSortInterp` pattern of `LexSort.lean`.  Each predicate name gets a
per-name agreement theorem `fzn_<name>_iff` proving that the Boolean
twin is `true` exactly when the mathematical interpretation holds.

Semantics per the MiniZinc 2.10.0 handbook, Section 4.2.2.9 ("Packing
constraints": `bin_packing`, `bin_packing_capa`, `bin_packing_load`,
`knapsack`, `diffn`, `diffn_nonstrict`), 4.2.2.10 ("Scheduling
constraints": `disjunctive`, `disjunctive_strict`, `cumulative`),
4.2.2.11 ("Extensional constraints": `table`), and the array-related
if-then-else decompositions of the pinned tree, cross-checked against
the pinned stdlib decompositions (`share/minizinc/std/fzn_*.mzn`).
Where a semantic decision went beyond a literal reading of the
handbook text, it is recorded in
`specification/flatzinc_specification_assumptions.md` (G-series
entries); the individual decisions are:

* `diffn` (strict) treats two rectangles as overlapping when their
  open projections intersect on *both* axes, so touching edges are
  allowed; `diffn_nonstrict` additionally allows single-point
  (zero-area) overlaps.
* `geost_nonoverlap_k` follows the `k`-dimensional decomposition
  restricted to pairwise axis-aligned non-overlap of two objects
  (the `fzn_geost` family itself is unsupported and reported).
* `cumulative` checks the resource usage at the finite set of task
  start and end times only (the usage function is constant between
  event points), plus a `0 ≤ capacity` guard that captures negative
  resource amounts.
* `table_int` reads the flat tuple array as rows of `|xs|` columns;
  `xs = []` is vacuously satisfied.
* `if_then_else[_var]_{int,bool,set}` follow the decomposition's
  `firstTrue` selection: the first true of the condition array
  selects the branch; when no condition is true the shared length
  check is the whole constraint (vacuous satisfaction), matching the
  total (non-partial) `fzn_if_then_else` decomposition rather than
  the partial `fzn_if_then_else_partiality` variant (unsupported,
  reported).

All FlatZinc arrays are 1-based; the twins realize this with 0-based
`List` indices plus a `+1` shift where positions appear in the
semantics, guarding bounds explicitly.  Decoding a wrong argument
shape yields `False` (interpretation) / `false` (twin).

The overlap conventions of `diffn`/`disjunctive`, the event-point
reading of `cumulative`, the table row shape, and the if-then-else
fallback behavior are recorded in
`specification/flatzinc_specification_assumptions.md`, G17–G20.
-/

namespace LeanFzn.Globals.PackSched

open LeanFzn LeanFzn.Globals

/-! ## Typed decoders for argument lists -/

private def ints1 (args : List Value) : Option (List Int) :=
  match args with
  | [.array xs] => valueInts xs
  | _ => none

private def ints2 (args : List Value) : Option (List Int × List Int) :=
  match args with
  | [.array a, .array b] => do
    let x ← valueInts a
    let y ← valueInts b
    return (x, y)
  | _ => none

private def ints3 (args : List Value) : Option (List Int × List Int × List Int) :=
  match args with
  | [.array a, .array b, .array c] => do
    let x ← valueInts a
    let y ← valueInts b
    let z ← valueInts c
    return (x, y, z)
  | _ => none

private def ints4 (args : List Value) :
    Option (List Int × List Int × List Int × List Int) :=
  match args with
  | [.array a, .array b, .array c, .array d] => do
    let x ← valueInts a
    let y ← valueInts b
    let z ← valueInts c
    let w ← valueInts d
    return (x, y, z, w)
  | _ => none

private def intInts2 (args : List Value) : Option (Int × List Int × List Int) :=
  match args with
  | [.int c, .array a, .array b] => do
    let x ← valueInts a
    let y ← valueInts b
    return (c, x, y)
  | _ => none

private def ints3Int (args : List Value) : Option (List Int × List Int × List Int × Int) :=
  match args with
  | [.array a, .array b, .array c, .int n] => do
    let x ← valueInts a
    let y ← valueInts b
    let z ← valueInts c
    return (x, y, z, n)
  | _ => none

private def ints3IntInt (args : List Value) :
    Option (List Int × List Int × List Int × Int × Int) :=
  match args with
  | [.array a, .array b, .array c, .int n1, .int n2] => do
    let x ← valueInts a
    let y ← valueInts b
    let z ← valueInts c
    return (x, y, z, n1, n2)
  | _ => none

private def boolsIntsInt (args : List Value) : Option (List Bool × List Int × Int) :=
  match args with
  | [.array cs, .array xs, .int y] => do
    let c ← valueBools cs
    let x ← valueInts xs
    return (c, x, y)
  | _ => none

private def boolsBoolsBool (args : List Value) : Option (List Bool × List Bool × Bool) :=
  match args with
  | [.array cs, .array xs, .bool y] => do
    let c ← valueBools cs
    let x ← valueBools xs
    return (c, x, y)
  | _ => none

private def boolsSetsSet (args : List Value) :
    Option (List Bool × List IntSetValue × IntSetValue) :=
  match args with
  | [.array cs, .array xs, .setOfInt y] => do
    let c ← valueBools cs
    let x ← valueSets xs
    return (c, x, y)
  | _ => none

/-! ## Small list helpers -/

private theorem lt_succ_cons {α : Type} {a : α} {l : List α} {i : Nat} (hi : i < l.length) :
    i + 1 < (a :: l).length := by
  rw [List.length_cons]
  omega

private theorem mem_iff_getD {l : List Int} {v : Int} :
    v ∈ l ↔ ∃ i, i < l.length ∧ l.getD i 0 = v := by
  induction l with
  | nil => simp
  | cons a ls ih =>
    simp only [List.mem_cons, ih]
    constructor
    · rintro (rfl | ⟨i, hi, hv⟩)
      · exact ⟨0, by simp, rfl⟩
      · exact ⟨i + 1, by rw [List.length_cons]; omega, hv⟩
    · rintro ⟨i, hi, hv⟩
      cases i with
      | zero =>
        have hv2 : a = v := hv
        exact Or.inl hv2.symm
      | succ i' =>
        have hv2 : ls.getD i' 0 = v := hv
        exact Or.inr ⟨i', by rw [List.length_cons] at hi; omega, hv2⟩

private theorem foldl_max_ge_init : ∀ (l : List Int) (a : Int), a ≤ List.foldl max a l := by
  intro l
  induction l with
  | nil => intro a; exact Int.le_refl a
  | cons y ys ih =>
    intro a
    show a ≤ List.foldl max (max a y) ys
    exact Int.le_trans (Int.le_max_left a y) (ih (max a y))

private theorem foldl_max_ge_mem :
    ∀ (l : List Int) (a x : Int), x ∈ l → x ≤ List.foldl max a l := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx (by simp)
  | cons y ys ih =>
    intro a x hx
    show x ≤ List.foldl max (max a y) ys
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Int.le_trans (Int.le_max_right a x) (foldl_max_ge_init ys (max a x))
    · exact ih (max a y) x hm

private theorem foldl_max_mem_or_eq : ∀ (l : List Int) (a : Int),
    List.foldl max a l = a ∨ List.foldl max a l ∈ l := by
  intro l
  induction l with
  | nil => intro a; exact Or.inl rfl
  | cons y ys ih =>
    intro a
    show List.foldl max (max a y) ys = a ∨ List.foldl max (max a y) ys ∈ y :: ys
    rcases ih (max a y) with heq | hm
    · rcases Int.le_total a y with hle | hge
      · exact Or.inr (by rw [heq, Int.max_eq_right hle]; exact List.mem_cons_self)
      · exact Or.inl (by rw [heq, Int.max_eq_left hge])
    · exact Or.inr (List.mem_cons_of_mem y hm)

private theorem foldl_min_le_init : ∀ (l : List Int) (a : Int), List.foldl min a l ≤ a := by
  intro l
  induction l with
  | nil => intro a; exact Int.le_refl a
  | cons y ys ih =>
    intro a
    show List.foldl min (min a y) ys ≤ a
    exact Int.le_trans (ih (min a y)) (Int.min_le_left a y)

private theorem foldl_min_le_mem :
    ∀ (l : List Int) (a x : Int), x ∈ l → List.foldl min a l ≤ x := by
  intro l
  induction l with
  | nil => intro _ x hx; exact absurd hx (by simp)
  | cons y ys ih =>
    intro a x hx
    show List.foldl min (min a y) ys ≤ x
    rcases List.mem_cons.mp hx with rfl | hm
    · exact Int.le_trans (foldl_min_le_init ys (min a x)) (Int.min_le_right a x)
    · exact ih (min a y) x hm

/-! ## Packing: `fzn_bin_packing` -/

/-- `fzn_bin_packing(capacity, bin, weight)`: for every bin value `b`
    occurring in `bin`, the total weight of the items assigned to `b` is
    at most `capacity` (weights and capacity are assumed nonnegative). -/
def binPackingProp (capacity : Int) (bin weight : List Int) : Prop :=
  bin.length = weight.length ∧
    ∀ b ∈ bin,
      ((((bin.zip weight).filter (fun q => decide (q.1 = b))).map (·.2)) |>.sum) ≤ capacity

/-- Boolean twin of `binPackingProp`. -/
def binPackingB (capacity : Int) (bin weight : List Int) : Bool :=
  decide (bin.length = weight.length) &&
    bin.all (fun b => decide
      (((((bin.zip weight).filter (fun q => decide (q.1 = b))).map (·.2)) |>.sum) ≤ capacity))

private theorem binPackingB_iff (capacity : Int) (bin weight : List Int) :
    binPackingB capacity bin weight = true ↔ binPackingProp capacity bin weight := by
  unfold binPackingB binPackingProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]

/-! ## Packing: `fzn_bin_packing_capa` -/

/-- `fzn_bin_packing_capa(capacity, bin, weight)`: every bin index is in
    `1..|capacity|` and, for every bin `b` of `1..|capacity|`, the total
    weight of the items assigned to `b` is at most `capacity[b-1]`. -/
def binPackingCapaProp (capacity bin weight : List Int) : Prop :=
  bin.length = weight.length ∧
    (∀ i, i < bin.length → 1 ≤ bin.getD i 0 ∧ bin.getD i 0 ≤ capacity.length) ∧
    (∀ b, b < capacity.length →
      ((((bin.zip weight).filter (fun q => decide (q.1 = ((b + 1 : Nat) : Int)))).map (·.2)) |>.sum)
        ≤ capacity.getD b 0)

/-- Boolean twin of `binPackingCapaProp`. -/
def binPackingCapaB (capacity bin weight : List Int) : Bool :=
  decide (bin.length = weight.length) &&
    bin.all (fun v => decide (1 ≤ v ∧ v ≤ capacity.length)) &&
    (List.range capacity.length).all (fun b =>
      decide (((((bin.zip weight).filter (fun q => decide (q.1 = ((b + 1 : Nat) : Int)))).map (·.2))
        |>.sum) ≤ capacity.getD b 0))

private theorem binPackingCapaB_iff (capacity bin weight : List Int) :
    binPackingCapaB capacity bin weight = true ↔ binPackingCapaProp capacity bin weight := by
  unfold binPackingCapaB binPackingCapaProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.mem_range, List.all_eq_true]
  constructor
  · rintro ⟨⟨hlen, hbin⟩, hrange⟩
    refine ⟨hlen, fun i hi => ?_, fun b hb => hrange b hb⟩
    exact hbin _ (mem_iff_getD.mpr ⟨i, hi, rfl⟩)
  · rintro ⟨hlen, hmid, hrange⟩
    refine ⟨⟨hlen, fun v hv => ?_⟩, fun b hb => ?_⟩
    · obtain ⟨i, hi, hv⟩ := mem_iff_getD.mp hv
      rw [← hv]
      exact hmid i hi
    · exact hrange b hb

/-! ## Packing: `fzn_bin_packing_load` -/

/-- `fzn_bin_packing_load(load, bin, weight)`: every bin index is in
    `1..|load|` and, for every bin `b` of `1..|load|`, the load variable
    `load[b-1]` equals the total weight of the items assigned to `b`. -/
def binPackingLoadProp (load bin weight : List Int) : Prop :=
  bin.length = weight.length ∧
    (∀ i, i < bin.length → 1 ≤ bin.getD i 0 ∧ bin.getD i 0 ≤ load.length) ∧
    (∀ b, b < load.length →
      load.getD b 0 =
        ((((bin.zip weight).filter (fun q => decide (q.1 = ((b + 1 : Nat) : Int)))).map (·.2)) |>.sum))

/-- Boolean twin of `binPackingLoadProp`. -/
def binPackingLoadB (load bin weight : List Int) : Bool :=
  decide (bin.length = weight.length) &&
    bin.all (fun v => decide (1 ≤ v ∧ v ≤ load.length)) &&
    (List.range load.length).all (fun b =>
      decide (load.getD b 0 =
        ((((bin.zip weight).filter (fun q => decide (q.1 = ((b + 1 : Nat) : Int)))).map (·.2)) |>.sum)))

private theorem binPackingLoadB_iff (load bin weight : List Int) :
    binPackingLoadB load bin weight = true ↔ binPackingLoadProp load bin weight := by
  unfold binPackingLoadB binPackingLoadProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.mem_range, List.all_eq_true]
  constructor
  · rintro ⟨⟨hlen, hbin⟩, hrange⟩
    refine ⟨hlen, fun i hi => ?_, fun b hb => hrange b hb⟩
    exact hbin _ (mem_iff_getD.mpr ⟨i, hi, rfl⟩)
  · rintro ⟨hlen, hmid, hrange⟩
    refine ⟨⟨hlen, fun v hv => ?_⟩, fun b hb => ?_⟩
    · obtain ⟨i, hi, hv⟩ := mem_iff_getD.mp hv
      rw [← hv]
      exact hmid i hi
    · exact hrange b hb

/-! ## Packing: `fzn_knapsack` -/

/-- `fzn_knapsack(weight, profit, xs, total_weight, total_profit)`:
    `total_weight` is the weighted sum of the selected items by `weight`
    and `total_profit` their weighted sum by `profit`. -/
def knapsackProp (weight profit xs : List Int) (tw tp : Int) : Prop :=
  weight.length = profit.length ∧ weight.length = xs.length ∧
    tw = (((xs.zip weight).map (fun p => p.1 * p.2)) |>.sum) ∧
    tp = (((xs.zip profit).map (fun p => p.1 * p.2)) |>.sum)

/-- Boolean twin of `knapsackProp`. -/
def knapsackB (weight profit xs : List Int) (tw tp : Int) : Bool :=
  decide (weight.length = profit.length) && decide (weight.length = xs.length) &&
    decide (tw = (((xs.zip weight).map (fun p => p.1 * p.2)) |>.sum)) &&
    decide (tp = (((xs.zip profit).map (fun p => p.1 * p.2)) |>.sum))

private theorem knapsackB_iff (weight profit xs : List Int) (tw tp : Int) :
    knapsackB weight profit xs tw tp = true ↔ knapsackProp weight profit xs tw tp := by
  unfold knapsackB knapsackProp
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, h4⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩

/-! ## Packing: `fzn_diffn` and `fzn_diffn_nonstrict` -/

/-- `fzn_diffn(x, y, dx, dy)`: the rectangles `[x[i], x[i]+dx[i]) ×
    `[y[i], y[i]+dy[i])` are pairwise non-overlapping. -/
def diffnProp (x y dx dy : List Int) : Prop :=
  x.length = y.length ∧ x.length = dx.length ∧ x.length = dy.length ∧
    ∀ i j : Nat, i < j → j < x.length →
      x.getD i 0 + dx.getD i 0 ≤ x.getD j 0 ∨ y.getD i 0 + dy.getD i 0 ≤ y.getD j 0 ∨
        x.getD j 0 + dx.getD j 0 ≤ x.getD i 0 ∨ y.getD j 0 + dy.getD j 0 ≤ y.getD i 0

/-- Boolean twin of `diffnProp`. -/
def diffnB (x y dx dy : List Int) : Bool :=
  decide (x.length = y.length) && decide (x.length = dx.length) &&
    decide (x.length = dy.length) &&
    (List.range x.length).all (fun j => (List.range j).all (fun i =>
      decide (x.getD i 0 + dx.getD i 0 ≤ x.getD j 0 ∨ y.getD i 0 + dy.getD i 0 ≤ y.getD j 0 ∨
        x.getD j 0 + dx.getD j 0 ≤ x.getD i 0 ∨ y.getD j 0 + dy.getD j 0 ≤ y.getD i 0)))

private theorem diffnB_iff (x y dx dy : List Int) :
    diffnB x y dx dy = true ↔ diffnProp x y dx dy := by
  unfold diffnB diffnProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun i j hij hjn => h4 j hjn i hij⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun j hj i hi => h4 i j hi hj⟩

/-- `fzn_diffn_nonstrict(x, y, dx, dy)`: as `fzn_diffn`, but rectangles
    with a zero side in either rectangle may touch or coincide. -/
def diffnNonstrictProp (x y dx dy : List Int) : Prop :=
  x.length = y.length ∧ x.length = dx.length ∧ x.length = dy.length ∧
    ∀ i j : Nat, i < j → j < x.length →
      dx.getD i 0 = 0 ∨ dx.getD j 0 = 0 ∨ dy.getD i 0 = 0 ∨ dy.getD j 0 = 0 ∨
        x.getD i 0 + dx.getD i 0 ≤ x.getD j 0 ∨ y.getD i 0 + dy.getD i 0 ≤ y.getD j 0 ∨
          x.getD j 0 + dx.getD j 0 ≤ x.getD i 0 ∨ y.getD j 0 + dy.getD j 0 ≤ y.getD i 0

/-- Boolean twin of `diffnNonstrictProp`. -/
def diffnNonstrictB (x y dx dy : List Int) : Bool :=
  decide (x.length = y.length) && decide (x.length = dx.length) &&
    decide (x.length = dy.length) &&
    (List.range x.length).all (fun j => (List.range j).all (fun i =>
      decide (dx.getD i 0 = 0 ∨ dx.getD j 0 = 0 ∨ dy.getD i 0 = 0 ∨ dy.getD j 0 = 0 ∨
        x.getD i 0 + dx.getD i 0 ≤ x.getD j 0 ∨ y.getD i 0 + dy.getD i 0 ≤ y.getD j 0 ∨
          x.getD j 0 + dx.getD j 0 ≤ x.getD i 0 ∨ y.getD j 0 + dy.getD j 0 ≤ y.getD i 0)))

private theorem diffnNonstrictB_iff (x y dx dy : List Int) :
    diffnNonstrictB x y dx dy = true ↔ diffnNonstrictProp x y dx dy := by
  unfold diffnNonstrictB diffnNonstrictProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun i j hij hjn => h4 j hjn i hij⟩
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun j hj i hi => h4 i j hi hj⟩

/-! ## Packing: `fzn_geost_nonoverlap_k` -/

/-- `fzn_geost_nonoverlap_k(x1, w1, x2, w2)`: the two `k`-dimensional
    boxes with origins `x1`, `x2` and sizes `w1`, `w2` are separated in
    some dimension. -/
def geostNonoverlapKProp (x1 w1 x2 w2 : List Int) : Prop :=
  x1.length = w1.length ∧ x1.length = x2.length ∧ x1.length = w2.length ∧
    ∃ j : Nat, j < x1.length ∧
      (x1.getD j 0 + w1.getD j 0 ≤ x2.getD j 0 ∨ x2.getD j 0 + w2.getD j 0 ≤ x1.getD j 0)

/-- Boolean twin of `geostNonoverlapKProp`. -/
def geostNonoverlapKB (x1 w1 x2 w2 : List Int) : Bool :=
  decide (x1.length = w1.length) && decide (x1.length = x2.length) &&
    decide (x1.length = w2.length) &&
    (List.range x1.length).any (fun j =>
      decide (x1.getD j 0 + w1.getD j 0 ≤ x2.getD j 0 ∨ x2.getD j 0 + w2.getD j 0 ≤ x1.getD j 0))

private theorem geostNonoverlapKB_iff (x1 w1 x2 w2 : List Int) :
    geostNonoverlapKB x1 w1 x2 w2 = true ↔ geostNonoverlapKProp x1 w1 x2 w2 := by
  unfold geostNonoverlapKB geostNonoverlapKProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.any_eq_true, List.mem_range,
    decide_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, j, hj, hd⟩
    exact ⟨h1, h2, h3, j, hj, hd⟩
  · rintro ⟨h1, h2, h3, j, hj, hd⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, j, hj, hd⟩

/-! ## Scheduling: `fzn_disjunctive` and `fzn_disjunctive_strict` -/

/-- `fzn_disjunctive(start, duration)`: tasks with positive duration do
    not overlap in time. -/
def disjunctiveProp (start dur : List Int) : Prop :=
  start.length = dur.length ∧
    ∀ i j : Nat, i < j → j < start.length →
      dur.getD i 0 = 0 ∨ dur.getD j 0 = 0 ∨
        start.getD i 0 + dur.getD i 0 ≤ start.getD j 0 ∨
        start.getD j 0 + dur.getD j 0 ≤ start.getD i 0

/-- Boolean twin of `disjunctiveProp`. -/
def disjunctiveB (start dur : List Int) : Bool :=
  decide (start.length = dur.length) &&
    (List.range start.length).all (fun j => (List.range j).all (fun i =>
      decide (dur.getD i 0 = 0 ∨ dur.getD j 0 = 0 ∨
        start.getD i 0 + dur.getD i 0 ≤ start.getD j 0 ∨
        start.getD j 0 + dur.getD j 0 ≤ start.getD i 0)))

private theorem disjunctiveB_iff (start dur : List Int) :
    disjunctiveB start dur = true ↔ disjunctiveProp start dur := by
  unfold disjunctiveB disjunctiveProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hlen, h4⟩
    exact ⟨hlen, fun i j hij hjn => h4 j hjn i hij⟩
  · rintro ⟨hlen, h4⟩
    exact ⟨hlen, fun j hj i hi => h4 i j hi hj⟩

/-- `fzn_disjunctive_strict(start, duration)`: all tasks (including
    zero-duration ones) are pairwise non-overlapping. -/
def disjunctiveStrictProp (start dur : List Int) : Prop :=
  start.length = dur.length ∧
    ∀ i j : Nat, i < j → j < start.length →
      start.getD i 0 + dur.getD i 0 ≤ start.getD j 0 ∨
      start.getD j 0 + dur.getD j 0 ≤ start.getD i 0

/-- Boolean twin of `disjunctiveStrictProp`. -/
def disjunctiveStrictB (start dur : List Int) : Bool :=
  decide (start.length = dur.length) &&
    (List.range start.length).all (fun j => (List.range j).all (fun i =>
      decide (start.getD i 0 + dur.getD i 0 ≤ start.getD j 0 ∨
        start.getD j 0 + dur.getD j 0 ≤ start.getD i 0)))

private theorem disjunctiveStrictB_iff (start dur : List Int) :
    disjunctiveStrictB start dur = true ↔ disjunctiveStrictProp start dur := by
  unfold disjunctiveStrictB disjunctiveStrictProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hlen, h4⟩
    exact ⟨hlen, fun i j hij hjn => h4 j hjn i hij⟩
  · rintro ⟨hlen, h4⟩
    exact ⟨hlen, fun j hj i hi => h4 i j hi hj⟩

/-! ## Scheduling: `fzn_cumulative` -/

/-- Resource usage at time `t`: the sum of the resource amounts of the
    tasks whose half-open time window `[start, start+duration)` contains
    `t` (tasks with mismatched arrays contribute nothing). -/
private def cumul : List Int → List Int → List Int → Int → Int
  | s :: ss, d :: ds, r :: rs, t =>
      (if s ≤ t ∧ t < s + d then r else 0) + cumul ss ds rs t
  | _, _, _, _ => 0

/-- The completion times `start[i] + duration[i]` of all tasks. -/
private def taskEnds (start dur : List Int) : List Int :=
  (List.range start.length).map (fun i => start.getD i 0 + dur.getD i 0)

private theorem cumul_eq_zero_of_all_gt (t : Int) : ∀ (S D R : List Int),
    (∀ i, i < S.length → ¬ (S.getD i 0 ≤ t)) → cumul S D R t = 0 := by
  intro S
  induction S with
  | nil => intro D R _; rfl
  | cons s S' ih =>
    intro D R h
    cases D with
    | nil => rfl
    | cons d D' =>
      cases R with
      | nil => rfl
      | cons r R' =>
        simp only [cumul]
        have h0 : ¬ (s ≤ t ∧ t < s + d) := fun hc => h 0 (by simp) hc.1
        simp only [cumul, if_neg h0]
        rw [Int.zero_add]
        exact ih D' R' (fun i hi hle => h (i + 1) (lt_succ_cons hi) hle)

set_option maxHeartbeats 1000000 in
private theorem cumul_congr (t b : Int) : ∀ (S D R : List Int),
    (∀ i, i < S.length →
      ((S.getD i 0 ≤ t ∧ t < S.getD i 0 + D.getD i 0) ↔
        (S.getD i 0 ≤ b ∧ b < S.getD i 0 + D.getD i 0))) →
    cumul S D R t = cumul S D R b := by
  intro S
  induction S with
  | nil => intro D R _; rfl
  | cons s S' ih =>
    intro D R h
    cases D with
    | nil => cases R <;> rfl
    | cons d D' =>
      cases R with
      | nil => rfl
      | cons r R' =>
        simp only [cumul]
        have h0 := h 0 (by simp)
        by_cases hactive : s ≤ t ∧ t < s + d
        · have hb : s ≤ b ∧ b < s + d := h0.mp hactive
          rw [if_pos hactive, if_pos hb, ih D' R' (fun i hi => h (i + 1) (lt_succ_cons hi))]
        · have hb : ¬ (s ≤ b ∧ b < s + d) := fun hc => hactive (h0.mpr hc)
          rw [if_neg hactive, if_neg hb, ih D' R' (fun i hi => h (i + 1) (lt_succ_cons hi))]

/-- `fzn_cumulative(start, duration, resource, capacity)`: at every time
    point the total resource usage of the running tasks is at most
    `capacity`. -/
def cumulativeProp (start dur res : List Int) (capacity : Int) : Prop :=
  start.length = dur.length ∧ start.length = res.length ∧
    ∀ t : Int, cumul start dur res t ≤ capacity

/-- Boolean twin of `cumulativeProp`.  Besides the start times, the
    completion times are checked as well: the usage function is constant
    between event points, so the two finite families of checkpoints
    together with the `0 ≤ capacity` guard capture the universal
    quantifier (this matters when some resource amounts are negative). -/
def cumulativeB (start dur res : List Int) (capacity : Int) : Bool :=
  decide (start.length = dur.length) && decide (start.length = res.length) &&
    decide (0 ≤ capacity) &&
    start.all (fun s => decide (cumul start dur res s ≤ capacity)) &&
    (taskEnds start dur).all (fun e => decide (cumul start dur res e ≤ capacity))

set_option maxHeartbeats 1000000 in
private theorem cumulativeB_iff (start dur res : List Int) (capacity : Int) :
    cumulativeB start dur res capacity = true ↔ cumulativeProp start dur res capacity := by
  unfold cumulativeB cumulativeProp
  simp only [Bool.and_eq_true, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨⟨⟨hlen1, hlen2⟩, hcapD⟩, hstarts⟩, hends⟩
    have hcap0 : 0 ≤ capacity := hcapD
    refine ⟨hlen1, hlen2, fun t => ?_⟩
    by_cases hsome : ∃ e, e ∈ start ++ taskEnds start dur ∧ e ≤ t
    · obtain ⟨x0, hx0mem, hx0le⟩ := hsome
      have hne : (start ++ taskEnds start dur).filter (fun e => decide (e ≤ t)) ≠ [] :=
        List.ne_nil_of_mem (List.mem_filter.mpr ⟨hx0mem, decide_eq_true hx0le⟩)
      obtain ⟨b0, bs, hfilt⟩ : ∃ x xs,
          (start ++ taskEnds start dur).filter (fun e => decide (e ≤ t)) = x :: xs := by
        cases hf : (start ++ taskEnds start dur).filter (fun e => decide (e ≤ t)) with
        | nil => exact absurd hf hne
        | cons y ys => exact ⟨y, ys, rfl⟩
      have hbin : List.foldl max b0 bs ∈ b0 :: bs := by
        rcases foldl_max_mem_or_eq bs b0 with heq | hm
        · exact List.mem_cons.mpr (Or.inl heq)
        · exact List.mem_cons.mpr (Or.inr hm)
      have hbfilt : List.foldl max b0 bs ∈
          (start ++ taskEnds start dur).filter (fun e => decide (e ≤ t)) := by
        rw [hfilt]; exact hbin
      have hble : List.foldl max b0 bs ≤ t := of_decide_eq_true (List.mem_filter.mp hbfilt).2
      have hbcap : cumul start dur res (List.foldl max b0 bs) ≤ capacity := by
        rcases List.mem_append.mp (List.mem_filter.mp hbfilt).1 with hm | hm
        · exact of_decide_eq_true (List.all_eq_true.mp hstarts _ hm)
        · exact of_decide_eq_true (List.all_eq_true.mp hends _ hm)
      have hcongr : cumul start dur res t = cumul start dur res (List.foldl max b0 bs) := by
        refine cumul_congr t (List.foldl max b0 bs) start dur res (fun i hi => ?_)
        have hb0le : b0 ≤ List.foldl max b0 bs := foldl_max_ge_init bs b0
        constructor
        · rintro ⟨hsi, hti⟩
          have hble2 : List.foldl max b0 bs ≤ t := hble
          refine ⟨?_, by omega⟩
          have hsimem : start.getD i 0 ∈ start := mem_iff_getD.mpr ⟨i, hi, rfl⟩
          have hsi2 : start.getD i 0 ≤ t := hsi
          have hsifilt : start.getD i 0 ∈ b0 :: bs := by
            rw [← hfilt]
            exact List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl hsimem), decide_eq_true hsi⟩
          rcases List.mem_cons.mp hsifilt with heq | hm
          · rw [heq]; exact hb0le
          · exact foldl_max_ge_mem bs b0 _ hm
        · rintro ⟨hsi, hbi⟩
          have hielem : start.getD i 0 + dur.getD i 0 ∈ taskEnds start dur :=
            List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
          by_cases hiet : start.getD i 0 + dur.getD i 0 ≤ t
          · have hiefilt : start.getD i 0 + dur.getD i 0 ∈ b0 :: bs := by
              rw [← hfilt]
              exact List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inr hielem), decide_eq_true hiet⟩
            have hiele : start.getD i 0 + dur.getD i 0 ≤ List.foldl max b0 bs := by
              rcases List.mem_cons.mp hiefilt with heq | hm
              · rw [heq]; exact hb0le
              · exact foldl_max_ge_mem bs b0 _ hm
            omega
          · omega
      rw [hcongr]
      exact hbcap
    · have hzero : cumul start dur res t = 0 :=
        cumul_eq_zero_of_all_gt t start dur res (fun i hi hsi =>
          hsome ⟨start.getD i 0,
            List.mem_append.mpr (Or.inl (mem_iff_getD.mpr ⟨i, hi, rfl⟩)), hsi⟩)
      rw [hzero]
      exact hcap0
  · rintro ⟨hlen1, hlen2, hall⟩
    have hzero : cumul start dur res (List.foldl min 0 start - 1) = 0 := by
      refine cumul_eq_zero_of_all_gt _ _ _ _ (fun i hi hsi => ?_)
      have hmem : start.getD i 0 ∈ start := mem_iff_getD.mpr ⟨i, hi, rfl⟩
      have hle := foldl_min_le_mem start 0 (start.getD i 0) hmem
      omega
    have hcap : 0 ≤ capacity := by
      have h1 := hall (List.foldl min 0 start - 1)
      rw [hzero] at h1
      exact h1
    have hs : start.all (fun s => decide (cumul start dur res s ≤ capacity)) = true :=
      List.all_eq_true.mpr (fun s _ => decide_eq_true (hall s))
    have he : (taskEnds start dur).all (fun e => decide (cumul start dur res e ≤ capacity)) = true :=
      List.all_eq_true.mpr (fun e he => by
        obtain ⟨i, _, heq⟩ := List.mem_map.mp he
        rw [← heq]
        exact decide_eq_true (hall _))
    simp only [Bool.and_eq_true, decide_eq_true_iff, hs, he, hlen1,
      and_true, true_and]
    exact ⟨hlen1 ▸ hlen2, hcap⟩

/-! ## Extensional: `fzn_table_int` -/

/-- `fzn_table_int(xs, tuples)`: `tuples` is the row-major flattening of
    a matrix with row width `|xs|`, and `xs` equals one complete row
    (an empty `xs` matches trivially). -/
def tableIntProp (xs tuples : List Int) : Prop :=
  ∃ r : Nat, r * xs.length + xs.length ≤ tuples.length ∧
    ∀ j : Nat, j < xs.length → tuples[r * xs.length + j]? = xs[j]?

/-- Boolean twin of `tableIntProp`. -/
def tableIntB (xs tuples : List Int) : Bool :=
  match xs.length with
  | 0 => true
  | w + 1 =>
    (List.range (tuples.length / (w + 1))).any (fun r =>
      (List.range (w + 1)).all (fun j => decide (tuples[r * (w + 1) + j]? = xs[j]?)))

private theorem tableIntB_iff (xs tuples : List Int) :
    tableIntB xs tuples = true ↔ tableIntProp xs tuples := by
  unfold tableIntB tableIntProp
  cases hn : xs.length with
  | zero =>
    simp only [hn]
    constructor
    · intro _
      exact ⟨0, by omega, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · intro _
      trivial
  | succ w =>
    simp only [hn]
    constructor
    · intro h
      rw [List.any_eq_true] at h
      obtain ⟨r, hr, hall⟩ := h
      have hr' : r < tuples.length / (w + 1) := List.mem_range.mp hr
      refine ⟨r, ?_, fun j hj => of_decide_eq_true
        (List.all_eq_true.mp hall j (List.mem_range.mpr hj))⟩
      have h1 : r + 1 ≤ tuples.length / (w + 1) := by omega
      have h2 := (Nat.le_div_iff_mul_le (k := w + 1) (by omega)).mp h1
      have h3 : (r + 1) * (w + 1) = r * (w + 1) + (w + 1) := Nat.succ_mul r (w + 1)
      omega
    · rintro ⟨r, hrle, hrow⟩
      have h2 : (r + 1) * (w + 1) ≤ tuples.length := by
        have h3 : (r + 1) * (w + 1) = r * (w + 1) + (w + 1) := Nat.succ_mul r (w + 1)
        omega
      have h1 : r < tuples.length / (w + 1) :=
        (Nat.le_div_iff_mul_le (k := w + 1) (by omega)).mpr h2
      refine List.any_eq_true.mpr ⟨r, List.mem_range.mpr h1, ?_⟩
      refine List.all_eq_true.mpr (fun j hj => ?_)
      exact decide_eq_true (hrow j (List.mem_range.mp hj))

/-! ## If-then-else family -/

/-- 0-based index of the first `true` of a boolean list, if any. -/
private def firstTrue : List Bool → Option Nat
  | [] => none
  | b :: rest => if b then some 0 else (firstTrue rest).map (· + 1)

private theorem firstTrue_sound : ∀ (c : List Bool) {i : Nat}, firstTrue c = some i →
    i < c.length ∧ c.getD i false = true ∧ ∀ j : Nat, j < i → c.getD j false = false := by
  intro c
  induction c with
  | nil => intro i h; exact absurd h (by simp [firstTrue])
  | cons b rest ih =>
    intro i h
    simp only [firstTrue] at h
    by_cases hb : b = true
    · rw [if_pos hb] at h
      have hi : i = 0 := (Option.some.inj h).symm
      subst hi
      exact ⟨by simp, hb, fun j hj => absurd hj (Nat.not_lt_zero j)⟩
    · have hb' : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd rfl hb
      rw [if_neg hb] at h
      cases hm : firstTrue rest with
      | none => rw [hm] at h; simp at h
      | some k =>
        rw [hm] at h
        simp at h
        subst h
        obtain ⟨hlt, htr, hbf⟩ := ih hm
        refine ⟨by rw [List.length_cons]; omega, ?_, ?_⟩
        · have h2 : rest.getD k false = true := htr
          exact h2
        · intro j hj
          cases j with
          | zero => exact hb'
          | succ j' => exact hbf j' (by omega)

private theorem firstTrue_complete : ∀ (c : List Bool) (i : Nat), i < c.length →
    c.getD i false = true → (∀ j : Nat, j < i → c.getD j false = false) →
    firstTrue c = some i := by
  intro c
  induction c with
  | nil => intro i hi _ _; exact absurd hi (by simp)
  | cons b rest ih =>
    intro i hi htrue hbefore
    simp only [firstTrue]
    cases i with
    | zero =>
      have hb : b = true := htrue
      rw [if_pos hb]
    | succ i' =>
      have hb' : b = false := hbefore 0 (by omega)
      rw [if_neg (by rw [hb']; exact fun h => Bool.noConfusion h : ¬ (b = true))]
      have hilt : i' < rest.length := by
        have h3 := hi
        rw [List.length_cons] at h3
        omega
      have htr : rest.getD i' false = true := htrue
      have hrest : firstTrue rest = some i' :=
        ih i' hilt htr (fun j hj => hbefore (j + 1) (by omega))
      simp [hrest]

private theorem firstTrue_none : ∀ (c : List Bool), firstTrue c = none →
    ∀ i : Nat, i < c.length → c.getD i false = false := by
  intro c
  induction c with
  | nil => intro h _ hi; exact absurd hi (by simp)
  | cons b rest ih =>
    intro h i hi
    simp only [firstTrue] at h
    by_cases hb : b = true
    · rw [if_pos hb] at h
      simp at h
    · rw [if_neg hb] at h
      have hb' : b = false := by
        cases b with
        | false => rfl
        | true => exact absurd rfl hb
      cases hm : firstTrue rest with
      | none =>
        rw [hm] at h
        simp at h
        cases i with
        | zero => exact hb' ▸ rfl
        | succ i' =>
          have h2 := ih hm i' (by have h3 := hi; rw [List.length_cons] at h3; omega)
          exact h2
      | some k => rw [hm] at h; simp at h

/-- Mathematical meaning shared by all six `fzn_if_then_else_*`
    predicates: `y` equals the `x`-entry selected by the first true
    condition (0-based index `i`), and there is no constraint when all
    conditions are false. -/
private def iteGenProp {α : Type} (fallback : α) (eqv : α → α → Prop)
    (c : List Bool) (x : List α) (y : α) : Prop :=
  c.length = x.length ∧
    ∀ i : Nat, i < c.length →
      ((∀ j : Nat, j < i → c.getD j false = false) ∧ c.getD i false = true) →
      eqv y (x.getD i fallback)

/-- Boolean twin of `iteGenProp`. -/
private def iteGenB {α : Type} (fallback : α) (eqB : α → α → Bool)
    (c : List Bool) (x : List α) (y : α) : Bool :=
  decide (c.length = x.length) &&
    ((firstTrue c).map (fun i => eqB y (x.getD i fallback))).getD true

set_option maxHeartbeats 1000000 in
private theorem iteGenB_iff {α : Type} (fallback : α) (eqv : α → α → Prop)
    (eqB : α → α → Bool) (hEq : ∀ a b, eqB a b = true ↔ eqv a b)
    (c : List Bool) (x : List α) (y : α) :
    iteGenB fallback eqB c x y = true ↔ iteGenProp fallback eqv c x y := by
  unfold iteGenB iteGenProp
  cases hf : firstTrue c with
  | none =>
    simp only [decide_eq_true_iff, hf, Option.map_none,
      Option.getD_none, Bool.and_true]
    constructor
    · intro hl
      refine ⟨hl, fun i hi hcon => ?_⟩
      have h9 := firstTrue_none c hf i hi
      rw [h9] at hcon
      exact Bool.noConfusion hcon.2
    · intro h
      exact h.1
  | some i =>
    obtain ⟨hilt, hitrue, hbefore⟩ := firstTrue_sound c hf
    simp only [Bool.and_eq_true, decide_eq_true_iff, hf, Option.map_some,
      Option.getD_some]
    constructor
    · rintro ⟨hlen, hb⟩
      refine ⟨hlen, fun i' hi' hcon => ?_⟩
      have hfe : firstTrue c = some i' := firstTrue_complete c i' hi' hcon.2 hcon.1
      rw [hf] at hfe
      have hii : i' = i := (Option.some.inj hfe).symm
      subst hii
      exact (hEq _ _).mp hb
    · rintro ⟨hlen, hall⟩
      exact ⟨hlen, (hEq _ _).mpr (hall i hilt ⟨hbefore, hitrue⟩)⟩

/-- `fzn_if_then_else_int(c, x, y)` (and its `_var_int` twin). -/
def iteIntProp (c : List Bool) (x : List Int) (y : Int) : Prop :=
  iteGenProp 0 (fun a b => a = b) c x y

def iteIntB (c : List Bool) (x : List Int) (y : Int) : Bool :=
  iteGenB 0 (fun a b => decide (a = b)) c x y

private theorem iteIntB_iff (c : List Bool) (x : List Int) (y : Int) :
    iteIntB c x y = true ↔ iteIntProp c x y :=
  iteGenB_iff 0 (fun a b => a = b) (fun a b => decide (a = b))
    (fun _ _ => decide_eq_true_iff) c x y

/-- `fzn_if_then_else_bool(c, x, y)` (and its `_var_bool` twin). -/
def iteBoolProp (c : List Bool) (x : List Bool) (y : Bool) : Prop :=
  iteGenProp false (fun a b => a = b) c x y

def iteBoolB (c : List Bool) (x : List Bool) (y : Bool) : Bool :=
  iteGenB false (fun a b => decide (a = b)) c x y

private theorem iteBoolB_iff (c : List Bool) (x : List Bool) (y : Bool) :
    iteBoolB c x y = true ↔ iteBoolProp c x y :=
  iteGenB_iff false (fun a b => a = b) (fun a b => decide (a = b))
    (fun _ _ => decide_eq_true_iff) c x y

/-- `fzn_if_then_else_set(c, x, y)` (and its `_var_set` twin); set
    equality is extensional. -/
def iteSetProp (c : List Bool) (x : List IntSetValue) (y : IntSetValue) : Prop :=
  iteGenProp (.enumeration []) (fun a b => ∀ v, a.Contains v ↔ b.Contains v) c x y

def iteSetB (c : List Bool) (x : List IntSetValue) (y : IntSetValue) : Bool :=
  iteGenB (.enumeration []) setEqB c x y

private theorem iteSetB_iff (c : List Bool) (x : List IntSetValue) (y : IntSetValue) :
    iteSetB c x y = true ↔ iteSetProp c x y := by
  unfold iteSetB iteSetProp
  exact iteGenB_iff _ _ _ (fun a b => setEqB_iff) c x y

/-! ## The interpretations -/

/-- Mathematical interpretations of the packing, scheduling, table and
    if-then-else global constraints; a wrong argument shape yields
    `False`. -/
def packSchedInterp : LeanFzn.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_bin_packing" => fun args =>
    match intInts2 args with
    | some (c, bin, wt) => binPackingProp c bin wt
    | none => False
  | "fzn_bin_packing_capa" => fun args =>
    match ints3 args with
    | some (capa, bin, wt) => binPackingCapaProp capa bin wt
    | none => False
  | "fzn_bin_packing_load" => fun args =>
    match ints3 args with
    | some (load, bin, wt) => binPackingLoadProp load bin wt
    | none => False
  | "fzn_knapsack" => fun args =>
    match ints3IntInt args with
    | some (w, p, xs, tw, tp) => knapsackProp w p xs tw tp
    | none => False
  | "fzn_diffn" => fun args =>
    match ints4 args with
    | some (x, y, dx, dy) => diffnProp x y dx dy
    | none => False
  | "fzn_diffn_nonstrict" => fun args =>
    match ints4 args with
    | some (x, y, dx, dy) => diffnNonstrictProp x y dx dy
    | none => False
  | "fzn_geost_nonoverlap_k" => fun args =>
    match ints4 args with
    | some (x1, w1, x2, w2) => geostNonoverlapKProp x1 w1 x2 w2
    | none => False
  | "fzn_disjunctive" => fun args =>
    match ints2 args with
    | some (s, d) => disjunctiveProp s d
    | none => False
  | "fzn_disjunctive_strict" => fun args =>
    match ints2 args with
    | some (s, d) => disjunctiveStrictProp s d
    | none => False
  | "fzn_cumulative" => fun args =>
    match ints3Int args with
    | some (s, d, r, cap) => cumulativeProp s d r cap
    | none => False
  | "fzn_table_int" => fun args =>
    match ints2 args with
    | some (xs, ts) => tableIntProp xs ts
    | none => False
  | "fzn_if_then_else_int" | "fzn_if_then_else_var_int" => fun args =>
    match boolsIntsInt args with
    | some (c, x, y) => iteIntProp c x y
    | none => False
  | "fzn_if_then_else_bool" | "fzn_if_then_else_var_bool" => fun args =>
    match boolsBoolsBool args with
    | some (c, x, y) => iteBoolProp c x y
    | none => False
  | "fzn_if_then_else_set" | "fzn_if_then_else_var_set" => fun args =>
    match boolsSetsSet args with
    | some (c, x, y) => iteSetProp c x y
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `packSchedInterp`**: computes the truth of the
    interpretations above; `false` on a wrong shape. -/
def packSchedInterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_bin_packing" => fun args =>
    match intInts2 args with
    | some (c, bin, wt) => binPackingB c bin wt
    | none => false
  | "fzn_bin_packing_capa" => fun args =>
    match ints3 args with
    | some (capa, bin, wt) => binPackingCapaB capa bin wt
    | none => false
  | "fzn_bin_packing_load" => fun args =>
    match ints3 args with
    | some (load, bin, wt) => binPackingLoadB load bin wt
    | none => false
  | "fzn_knapsack" => fun args =>
    match ints3IntInt args with
    | some (w, p, xs, tw, tp) => knapsackB w p xs tw tp
    | none => false
  | "fzn_diffn" => fun args =>
    match ints4 args with
    | some (x, y, dx, dy) => diffnB x y dx dy
    | none => false
  | "fzn_diffn_nonstrict" => fun args =>
    match ints4 args with
    | some (x, y, dx, dy) => diffnNonstrictB x y dx dy
    | none => false
  | "fzn_geost_nonoverlap_k" => fun args =>
    match ints4 args with
    | some (x1, w1, x2, w2) => geostNonoverlapKB x1 w1 x2 w2
    | none => false
  | "fzn_disjunctive" => fun args =>
    match ints2 args with
    | some (s, d) => disjunctiveB s d
    | none => false
  | "fzn_disjunctive_strict" => fun args =>
    match ints2 args with
    | some (s, d) => disjunctiveStrictB s d
    | none => false
  | "fzn_cumulative" => fun args =>
    match ints3Int args with
    | some (s, d, r, cap) => cumulativeB s d r cap
    | none => false
  | "fzn_table_int" => fun args =>
    match ints2 args with
    | some (xs, ts) => tableIntB xs ts
    | none => false
  | "fzn_if_then_else_int" | "fzn_if_then_else_var_int" => fun args =>
    match boolsIntsInt args with
    | some (c, x, y) => iteIntB c x y
    | none => false
  | "fzn_if_then_else_bool" | "fzn_if_then_else_var_bool" => fun args =>
    match boolsBoolsBool args with
    | some (c, x, y) => iteBoolB c x y
    | none => false
  | "fzn_if_then_else_set" | "fzn_if_then_else_var_set" => fun args =>
    match boolsSetsSet args with
    | some (c, x, y) => iteSetB c x y
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

set_option maxHeartbeats 1000000 in
theorem bin_packing_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_bin_packing") args = true ↔
      packSchedInterp (Ident.mk "fzn_bin_packing") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_bin_packing") args
      = match intInts2 args with
      | some (c, bin, wt) => binPackingB c bin wt
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_bin_packing") args
      = match intInts2 args with
      | some (c, bin, wt) => binPackingProp c bin wt
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : intInts2 args with
  | none => simp
  | some p =>
    obtain ⟨c, bin, wt⟩ := p
    simp only
    exact binPackingB_iff c bin wt

set_option maxHeartbeats 1000000 in
theorem bin_packing_capa_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_bin_packing_capa") args = true ↔
      packSchedInterp (Ident.mk "fzn_bin_packing_capa") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_bin_packing_capa") args
      = match ints3 args with
      | some (capa, bin, wt) => binPackingCapaB capa bin wt
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_bin_packing_capa") args
      = match ints3 args with
      | some (capa, bin, wt) => binPackingCapaProp capa bin wt
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints3 args with
  | none => simp
  | some p =>
    obtain ⟨capa, bin, wt⟩ := p
    simp only
    exact binPackingCapaB_iff capa bin wt

set_option maxHeartbeats 1000000 in
theorem bin_packing_load_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_bin_packing_load") args = true ↔
      packSchedInterp (Ident.mk "fzn_bin_packing_load") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_bin_packing_load") args
      = match ints3 args with
      | some (load, bin, wt) => binPackingLoadB load bin wt
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_bin_packing_load") args
      = match ints3 args with
      | some (load, bin, wt) => binPackingLoadProp load bin wt
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints3 args with
  | none => simp
  | some p =>
    obtain ⟨load, bin, wt⟩ := p
    simp only
    exact binPackingLoadB_iff load bin wt

set_option maxHeartbeats 1000000 in
theorem knapsack_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_knapsack") args = true ↔
      packSchedInterp (Ident.mk "fzn_knapsack") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_knapsack") args
      = match ints3IntInt args with
      | some (w, p, xs, tw, tp) => knapsackB w p xs tw tp
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_knapsack") args
      = match ints3IntInt args with
      | some (w, p, xs, tw, tp) => knapsackProp w p xs tw tp
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints3IntInt args with
  | none => simp
  | some p =>
    obtain ⟨w, p, xs, tw, tp⟩ := p
    simp only
    exact knapsackB_iff w p xs tw tp

set_option maxHeartbeats 1000000 in
theorem diffn_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_diffn") args = true ↔
      packSchedInterp (Ident.mk "fzn_diffn") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_diffn") args
      = match ints4 args with
      | some (x, y, dx, dy) => diffnB x y dx dy
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_diffn") args
      = match ints4 args with
      | some (x, y, dx, dy) => diffnProp x y dx dy
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints4 args with
  | none => simp
  | some p =>
    obtain ⟨x, y, dx, dy⟩ := p
    simp only
    exact diffnB_iff x y dx dy

set_option maxHeartbeats 1000000 in
theorem diffn_nonstrict_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_diffn_nonstrict") args = true ↔
      packSchedInterp (Ident.mk "fzn_diffn_nonstrict") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_diffn_nonstrict") args
      = match ints4 args with
      | some (x, y, dx, dy) => diffnNonstrictB x y dx dy
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_diffn_nonstrict") args
      = match ints4 args with
      | some (x, y, dx, dy) => diffnNonstrictProp x y dx dy
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints4 args with
  | none => simp
  | some p =>
    obtain ⟨x, y, dx, dy⟩ := p
    simp only
    exact diffnNonstrictB_iff x y dx dy

set_option maxHeartbeats 1000000 in
theorem geost_nonoverlap_k_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_geost_nonoverlap_k") args = true ↔
      packSchedInterp (Ident.mk "fzn_geost_nonoverlap_k") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_geost_nonoverlap_k") args
      = match ints4 args with
      | some (x1, w1, x2, w2) => geostNonoverlapKB x1 w1 x2 w2
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_geost_nonoverlap_k") args
      = match ints4 args with
      | some (x1, w1, x2, w2) => geostNonoverlapKProp x1 w1 x2 w2
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints4 args with
  | none => simp
  | some p =>
    obtain ⟨x1, w1, x2, w2⟩ := p
    simp only
    exact geostNonoverlapKB_iff x1 w1 x2 w2

set_option maxHeartbeats 1000000 in
theorem disjunctive_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_disjunctive") args = true ↔
      packSchedInterp (Ident.mk "fzn_disjunctive") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_disjunctive") args
      = match ints2 args with
      | some (s, d) => disjunctiveB s d
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_disjunctive") args
      = match ints2 args with
      | some (s, d) => disjunctiveProp s d
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints2 args with
  | none => simp
  | some p =>
    obtain ⟨s, d⟩ := p
    simp only
    exact disjunctiveB_iff s d

set_option maxHeartbeats 1000000 in
theorem disjunctive_strict_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_disjunctive_strict") args = true ↔
      packSchedInterp (Ident.mk "fzn_disjunctive_strict") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_disjunctive_strict") args
      = match ints2 args with
      | some (s, d) => disjunctiveStrictB s d
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_disjunctive_strict") args
      = match ints2 args with
      | some (s, d) => disjunctiveStrictProp s d
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints2 args with
  | none => simp
  | some p =>
    obtain ⟨s, d⟩ := p
    simp only
    exact disjunctiveStrictB_iff s d

set_option maxHeartbeats 1000000 in
theorem cumulative_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_cumulative") args = true ↔
      packSchedInterp (Ident.mk "fzn_cumulative") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_cumulative") args
      = match ints3Int args with
      | some (s, d, r, cap) => cumulativeB s d r cap
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_cumulative") args
      = match ints3Int args with
      | some (s, d, r, cap) => cumulativeProp s d r cap
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints3Int args with
  | none => simp
  | some p =>
    obtain ⟨s, d, r, cap⟩ := p
    simp only
    exact cumulativeB_iff s d r cap

set_option maxHeartbeats 1000000 in
theorem table_int_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_table_int") args = true ↔
      packSchedInterp (Ident.mk "fzn_table_int") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_table_int") args
      = match ints2 args with
      | some (xs, ts) => tableIntB xs ts
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_table_int") args
      = match ints2 args with
      | some (xs, ts) => tableIntProp xs ts
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : ints2 args with
  | none => simp
  | some p =>
    obtain ⟨xs, ts⟩ := p
    simp only
    exact tableIntB_iff xs ts

set_option maxHeartbeats 1000000 in
theorem if_then_else_int_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_if_then_else_int") args = true ↔
      packSchedInterp (Ident.mk "fzn_if_then_else_int") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_if_then_else_int") args
      = match boolsIntsInt args with
      | some (c, x, y) => iteIntB c x y
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_if_then_else_int") args
      = match boolsIntsInt args with
      | some (c, x, y) => iteIntProp c x y
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boolsIntsInt args with
  | none => simp
  | some p =>
    obtain ⟨c, x, y⟩ := p
    simp only
    exact iteIntB_iff c x y

set_option maxHeartbeats 1000000 in
theorem if_then_else_bool_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_if_then_else_bool") args = true ↔
      packSchedInterp (Ident.mk "fzn_if_then_else_bool") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_if_then_else_bool") args
      = match boolsBoolsBool args with
      | some (c, x, y) => iteBoolB c x y
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_if_then_else_bool") args
      = match boolsBoolsBool args with
      | some (c, x, y) => iteBoolProp c x y
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boolsBoolsBool args with
  | none => simp
  | some p =>
    obtain ⟨c, x, y⟩ := p
    simp only
    exact iteBoolB_iff c x y

set_option maxHeartbeats 1000000 in
theorem if_then_else_set_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_if_then_else_set") args = true ↔
      packSchedInterp (Ident.mk "fzn_if_then_else_set") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_if_then_else_set") args
      = match boolsSetsSet args with
      | some (c, x, y) => iteSetB c x y
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_if_then_else_set") args
      = match boolsSetsSet args with
      | some (c, x, y) => iteSetProp c x y
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boolsSetsSet args with
  | none => simp
  | some p =>
    obtain ⟨c, x, y⟩ := p
    simp only
    exact iteSetB_iff c x y

set_option maxHeartbeats 1000000 in
theorem if_then_else_var_int_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_if_then_else_var_int") args = true ↔
      packSchedInterp (Ident.mk "fzn_if_then_else_var_int") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_if_then_else_var_int") args
      = match boolsIntsInt args with
      | some (c, x, y) => iteIntB c x y
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_if_then_else_var_int") args
      = match boolsIntsInt args with
      | some (c, x, y) => iteIntProp c x y
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boolsIntsInt args with
  | none => simp
  | some p =>
    obtain ⟨c, x, y⟩ := p
    simp only
    exact iteIntB_iff c x y

set_option maxHeartbeats 1000000 in
theorem if_then_else_var_bool_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_if_then_else_var_bool") args = true ↔
      packSchedInterp (Ident.mk "fzn_if_then_else_var_bool") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_if_then_else_var_bool") args
      = match boolsBoolsBool args with
      | some (c, x, y) => iteBoolB c x y
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_if_then_else_var_bool") args
      = match boolsBoolsBool args with
      | some (c, x, y) => iteBoolProp c x y
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boolsBoolsBool args with
  | none => simp
  | some p =>
    obtain ⟨c, x, y⟩ := p
    simp only
    exact iteBoolB_iff c x y

set_option maxHeartbeats 1000000 in
theorem if_then_else_var_set_iff (args : List Value) :
    packSchedInterpB (Ident.mk "fzn_if_then_else_var_set") args = true ↔
      packSchedInterp (Ident.mk "fzn_if_then_else_var_set") args := by
  have hB : ∀ args, packSchedInterpB (Ident.mk "fzn_if_then_else_var_set") args
      = match boolsSetsSet args with
      | some (c, x, y) => iteSetB c x y
      | none => false
      := fun _ => rfl
  have hI : ∀ args, packSchedInterp (Ident.mk "fzn_if_then_else_var_set") args
      = match boolsSetsSet args with
      | some (c, x, y) => iteSetProp c x y
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : boolsSetsSet args with
  | none => simp
  | some p =>
    obtain ⟨c, x, y⟩ := p
    simp only
    exact iteSetB_iff c x y

end LeanFzn.Globals.PackSched
