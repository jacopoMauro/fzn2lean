/-
Purpose: Packing, scheduling, table and conditional predicate semantics and Boolean agreement.
Dependencies: Globals.Common and shared semantic helpers supply values and finite-array operations.
DAG: Shared semantics -> this family -> Globals dispatch and checker correctness.
-/
import LeanFzn.Semantics.Globals.Common
open LeanFzn.Semantics


/-!
# Packing, scheduling, extensional (table), and if-then-else global constraints

Mathematical interpretations (`packSchedInterp`) and executable Boolean
twins (`packSchedInterpB`) for the packing, scheduling, extensional and
if-then-else families of global-constraint predicates of the pinned
MiniZinc 2.10.1 FlatZinc tree (17 `fzn_*` names), following the
`lexSortInterp` pattern of `LexSort.lean`.  Each predicate name gets a
per-name agreement theorem `fzn_<name>_iff` proving that the Boolean
twin is `true` exactly when the mathematical interpretation holds.

Semantics per the MiniZinc 2.10.1 handbook, Section 4.2.2.9 ("Packing
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
  restricted to pairwise axis-aligned non-overlap of two objects.
  The `fzn_geost` family itself lives in `Sched2.lean` and reads the
  `xs`/`rect_*` arguments as flat row-major `k`-column matrices
  (SC-03).
* `cumulative` checks the resource usage at the finite set of task
  start and end times only (the usage function is constant between
  event points), plus a `0 ≤ capacity` guard that captures negative
  resource amounts.
* `table_int` reads the flat tuple array as rows of `|xs|` columns;
  `xs` must be nonempty (the upstream `min`/`max` over an empty index
  set is undefined → false) and `|tuples|` must be a multiple of
  `|xs|` (SC-03).
* `if_then_else[_var]_{int,bool,set}` follow the decomposition's
  `firstTrue` selection: the first true of the condition array
  selects the branch and only that `x` entry is read; when no
  condition is true the constraint is vacuous and no `x` entry is
  read.  This matches the total (non-partial) `fzn_if_then_else`
  decomposition rather than the partial
  `fzn_if_then_else_partiality` variant (unsupported, reported).
* `diffn`, `diffn_nonstrict`, `geost_nonoverlap_k`, `disjunctive`
  and `disjunctive_strict` follow MiniZinc's three-valued array-access
  semantics: a loop over an empty index set is vacuous, and a true
  disjunct or existential witness masks a missing entry in a later
  branch.  They therefore carry per-iteration access premises rather
  than unconditional parallel-array length gates.

All FlatZinc arrays are 1-based; the twins realize this with 0-based
`List` indices plus a `+1` shift where positions appear in the
semantics, guarding bounds explicitly.  Decoding a wrong argument
shape yields `False` (interpretation) / `false` (twin).

The overlap conventions of `diffn`/`disjunctive`, the event-point
reading of `cumulative`, the table row shape, and the if-then-else
fallback behavior are recorded in
`specification/flatzinc_specification_assumptions.md`, G17–G20.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.PackSched

open LeanFzn LeanFzn.Semantics.Globals

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

/-- `fzn_bin_packing(capacity, bin, weight)`: transcribed from
    `fzn_bin_packing.mzn` lines 1-8.

    - `length(bin) = 0` is true regardless of `weight` and `capacity`
      (line 2: the body is not evaluated).
    - Otherwise the raw decomposition sums `weight` over
      `index_set(bin)`, so `bin.length = weight.length` is the restricted
      domain on which the occupied-bin load identity is exact; every
      unoccupied declared domain value then has load `0`, and line 6
      reduces to `0 ≤ capacity`.  The declared bounds `lb_array(bin)` /
      `ub_array(bin)` are not recoverable from a decoded `Value`, so the
      row stays `restricted`.
    - This restricted domain also assumes `0 ≤ capacity` and nonnegative
      weights; both are enforced here so that the unoccupied-bin case is
      exactly the `0 ≤ capacity` side condition.

    For every bin value `b` occurring in `bin`, the total weight of the
    items assigned to `b` is at most `capacity`. -/
def binPackingProp (capacity : Int) (bin weight : List Int) : Prop :=
  bin = [] ∨
    (bin.length = weight.length ∧ 0 ≤ capacity ∧ (∀ w ∈ weight, 0 ≤ w) ∧
      -- `zip` is guarded by the `bin.length = weight.length` conjunct;
      -- `filter` only reads the paired entries.
      ∀ b ∈ bin,
        ((((bin.zip weight).filter (fun q => decide (q.1 = b))).map (·.2)) |>.sum) ≤ capacity)

/-- Boolean twin of `binPackingProp`. -/
def binPackingB (capacity : Int) (bin weight : List Int) : Bool :=
  if bin = [] then true
  else
    decide (bin.length = weight.length) && decide (0 ≤ capacity) &&
      weight.all (fun w => decide (0 ≤ w)) &&
      -- `bin.all` is only reached with the `bin.length = weight.length`
      -- conjunct true; `zip`/`filter` then pair every item with its weight.
      bin.all (fun b => decide
        (((((bin.zip weight).filter (fun q => decide (q.1 = b))).map (·.2)) |>.sum) ≤ capacity))

private theorem binPackingB_iff (capacity : Int) (bin weight : List Int) :
    binPackingB capacity bin weight = true ↔ binPackingProp capacity bin weight := by
  unfold binPackingB binPackingProp
  by_cases hb : bin = []
  · subst hb
    simp
  · rw [if_neg hb]
    simp only [hb, false_or, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
    constructor
    · rintro ⟨⟨⟨hlen, hcap⟩, hw⟩, hball⟩
      exact ⟨hlen, hcap, hw, hball⟩
    · rintro ⟨hlen, hcap, hw, hball⟩
      exact ⟨⟨⟨hlen, hcap⟩, hw⟩, hball⟩

/-! ## Packing: `fzn_bin_packing_capa` -/

/-- `fzn_bin_packing_capa(capacity, bin, weight)`: transcribed from
    `fzn_bin_packing_capa.mzn` lines 1-11.

    - Line 6 reads `weight[i]` for `i ∈ index_set(bin)`, so
      `bin.length ≤ weight.length`; a longer `weight` is unused.
    - Line 7 compares every `bin[i]` with `index_set(capacity)`
      (`1..capacity.length` in the 1-based ABI).
    - Lines 9-10 run over all of `index_set(capacity)` and only read
      `weight[i]` over `index_set(bin)`.

    Every bin index is in `1..|capacity|` and, for every bin `b` of
    `1..|capacity|`, the total weight of the items assigned to `b` is at
    most `capacity[b-1]`. -/
def binPackingCapaProp (capacity bin weight : List Int) : Prop :=
  -- `zip` is safe because `bin.length ≤ weight.length`; it keeps every bin item.
  bin.length ≤ weight.length ∧
    -- `bin.getD i 0` is guarded by the binder `i < bin.length`.
    (∀ i, i < bin.length → 1 ≤ bin.getD i 0 ∧ bin.getD i 0 ≤ capacity.length) ∧
    -- `capacity.getD b 0` is guarded by the binder `b < capacity.length`.
    (∀ b, b < capacity.length →
      ((((bin.zip weight).filter (fun q => decide (q.1 = ((b + 1 : Nat) : Int)))).map (·.2)) |>.sum)
        ≤ capacity.getD b 0)

/-- Boolean twin of `binPackingCapaProp`. -/
def binPackingCapaB (capacity bin weight : List Int) : Bool :=
  decide (bin.length ≤ weight.length) &&
    bin.all (fun v => decide (1 ≤ v ∧ v ≤ capacity.length)) &&
    (List.range capacity.length).all (fun b =>
      -- `b < capacity.length` from `List.mem_range` guards `capacity.getD b 0`.
      -- `zip` is guarded by the leading `bin.length ≤ weight.length` conjunct.
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

/-- `fzn_bin_packing_load(load, bin, weight)`: transcribed from
    `fzn_bin_packing_load.mzn` lines 1-10.

    - Line 6 sums all of `load` and all of `weight`:
      `sum(load) = sum(weight)` is an explicit conjunct.
    - Line 8 requires `bin[i] ∈ 1..load.length` for `i ∈ index_set(bin)`.
    - Line 10 forces every `load[b]` to the bin-prefix sum, reading
      `weight[i]` only over `index_set(bin)`, hence
      `bin.length ≤ weight.length` (a longer `weight` only matters
      through the total sum).

    Every bin index is in `1..|load|` and, for every bin `b` of
    `1..|load|`, the load variable `load[b-1]` equals the total weight of
    the items assigned to `b`. -/
def binPackingLoadProp (load bin weight : List Int) : Prop :=
  -- `zip` is safe because `bin.length ≤ weight.length`; it keeps every bin item.
  bin.length ≤ weight.length ∧
    load.sum = weight.sum ∧
    -- `bin.getD i 0` is guarded by the binder `i < bin.length`.
    (∀ i, i < bin.length → 1 ≤ bin.getD i 0 ∧ bin.getD i 0 ≤ load.length) ∧
    -- `load.getD b 0` is guarded by the binder `b < load.length`.
    (∀ b, b < load.length →
      load.getD b 0 =
        ((((bin.zip weight).filter (fun q => decide (q.1 = ((b + 1 : Nat) : Int)))).map (·.2)) |>.sum))

/-- Boolean twin of `binPackingLoadProp`. -/
def binPackingLoadB (load bin weight : List Int) : Bool :=
  decide (bin.length ≤ weight.length) && decide (load.sum = weight.sum) &&
    bin.all (fun v => decide (1 ≤ v ∧ v ≤ load.length)) &&
    (List.range load.length).all (fun b =>
      -- `b < load.length` from `List.mem_range` guards `load.getD b 0`.
      -- `zip` is guarded by the leading `bin.length ≤ weight.length` conjunct.
      decide (load.getD b 0 =
        ((((bin.zip weight).filter (fun q => decide (q.1 = ((b + 1 : Nat) : Int)))).map (·.2)) |>.sum)))

private theorem binPackingLoadB_iff (load bin weight : List Int) :
    binPackingLoadB load bin weight = true ↔ binPackingLoadProp load bin weight := by
  unfold binPackingLoadB binPackingLoadProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.mem_range, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨hlen, hsum⟩, hbin⟩, hrange⟩
    refine ⟨hlen, hsum, fun i hi => ?_, fun b hb => hrange b hb⟩
    exact hbin _ (mem_iff_getD.mpr ⟨i, hi, rfl⟩)
  · rintro ⟨hlen, hsum, hmid, hrange⟩
    refine ⟨⟨⟨hlen, hsum⟩, fun v hv => ?_⟩, fun b hb => ?_⟩
    · obtain ⟨i, hi, hv⟩ := mem_iff_getD.mp hv
      rw [← hv]
      exact hmid i hi
    · exact hrange b hb

/-! ## Packing: `fzn_knapsack` -/

/-- `fzn_knapsack(weight, profit, xs, total_weight, total_profit)`:
    transcribed from `fzn_knapsack.mzn` lines 1-12.

    - Line 8 requires `xs[i] ≥ 0` over **all** of `index_set(xs)`.
    - Lines 11-12 sum over all of `index_set(profit)` / `index_set(weight)`
      and read `xs[i]` there, hence only `weight.length ≤ xs.length` and
      `profit.length ≤ xs.length` are needed; the two parameter arrays
      need not have equal length, and trailing `xs` entries are unused
      except for nonnegativity.
    - `total_weight ≥ 0` and `total_profit ≥ 0` (lines 9-10).

    `total_weight` is the weighted sum of the selected items by `weight`
    and `total_profit` their weighted sum by `profit`. -/
def knapsackProp (weight profit xs : List Int) (tw tp : Int) : Prop :=
  weight.length ≤ xs.length ∧ profit.length ≤ xs.length ∧
    (∀ x ∈ xs, 0 ≤ x) ∧ 0 ≤ tw ∧ 0 ≤ tp ∧
    -- `xs.getD i 0` is guarded by `i < weight.length ≤ xs.length`;
    -- `weight.getD i 0` by `i < weight.length` from `List.mem_range`.
    tw = ((List.range weight.length).map
      (fun i => xs.getD i 0 * weight.getD i 0)).sum ∧
    -- `xs.getD i 0` is guarded by `i < profit.length ≤ xs.length`;
    -- `profit.getD i 0` by `i < profit.length` from `List.mem_range`.
    tp = ((List.range profit.length).map
      (fun i => xs.getD i 0 * profit.getD i 0)).sum

/-- Boolean twin of `knapsackProp`. -/
def knapsackB (weight profit xs : List Int) (tw tp : Int) : Bool :=
  decide (weight.length ≤ xs.length) && decide (profit.length ≤ xs.length) &&
    xs.all (fun x => decide (0 ≤ x)) && decide (0 ≤ tw) && decide (0 ≤ tp) &&
    -- `i < weight.length` from `List.mem_range` guards `weight.getD i 0`;
    -- `weight.length ≤ xs.length` guards `xs.getD i 0`.
    decide (tw = ((List.range weight.length).map
      (fun i => xs.getD i 0 * weight.getD i 0)).sum) &&
    -- `i < profit.length` from `List.mem_range` guards `profit.getD i 0`;
    -- `profit.length ≤ xs.length` guards `xs.getD i 0`.
    decide (tp = ((List.range profit.length).map
      (fun i => xs.getD i 0 * profit.getD i 0)).sum)

private theorem knapsackB_iff (weight profit xs : List Int) (tw tp : Int) :
    knapsackB weight profit xs tw tp = true ↔ knapsackProp weight profit xs tw tp := by
  simp [knapsackB, knapsackProp, List.all_eq_true, and_assoc]

/-! ## Packing: `fzn_diffn` and `fzn_diffn_nonstrict` -/

/-- The raw `fzn_diffn.mzn` disjunction at one pair `i < j`, with
    MiniZinc's three-valued array-access semantics: a disjunct is usable
    only when every entry it reads exists, and an existing true disjunct
    makes the whole disjunction true even if an earlier disjunct was
    undefined (written `true ∨ undefined = true` in MiniZinc).  The four
    raw disjuncts read, in order,
    `x[i],dx[i],x[j]`, `y[i],dy[i],y[j]`, `x[j],dx[j],x[i]`,
    `y[j],dy[j],y[i]`.  The `x` entries exist because `i < j <
    x.length`. -/
private def diffnPairProp (x y dx dy : List Int) (i j : Nat) : Prop :=
  (i < dx.length ∧ x.getD i 0 + dx.getD i 0 ≤ x.getD j 0) ∨
  (i < y.length ∧ j < y.length ∧ i < dy.length ∧
    y.getD i 0 + dy.getD i 0 ≤ y.getD j 0) ∨
  (j < dx.length ∧ x.getD j 0 + dx.getD j 0 ≤ x.getD i 0) ∨
  (i < y.length ∧ j < y.length ∧ j < dy.length ∧
    y.getD j 0 + dy.getD j 0 ≤ y.getD i 0)

/-- Boolean twin of `diffnPairProp`. -/
private def diffnPairB (x y dx dy : List Int) (i j : Nat) : Bool :=
  (decide (i < dx.length) && decide (x.getD i 0 + dx.getD i 0 ≤ x.getD j 0)) ||
  (decide (i < y.length) && decide (j < y.length) && decide (i < dy.length) &&
    decide (y.getD i 0 + dy.getD i 0 ≤ y.getD j 0)) ||
  (decide (j < dx.length) && decide (x.getD j 0 + dx.getD j 0 ≤ x.getD i 0)) ||
  (decide (i < y.length) && decide (j < y.length) && decide (j < dy.length) &&
    decide (y.getD j 0 + dy.getD j 0 ≤ y.getD i 0))

private theorem diffnPairB_iff (x y dx dy : List Int) (i j : Nat) :
    diffnPairB x y dx dy i j = true ↔ diffnPairProp x y dx dy i j := by
  simp only [diffnPairB, diffnPairProp, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_iff, and_assoc, or_assoc]

/-- `fzn_diffn(x, y, dx, dy)`: transcribed from `fzn_diffn.mzn` lines 1-9.
    The pair loop runs over `index_set(x)`, so it is vacuous when
    `x.length ≤ 1` and no parallel-array entry is read.  For a nonempty
    pair `i < j < x.length`, each disjunct reads only its own entries;
    a true disjunct masks a missing entry in a later disjunct (and an
    undefined earlier disjunct does not mask a true later one), exactly
    as MiniZinc's three-valued disjunction.  There is therefore no
    unconditional length gate on `y`, `dx` or `dy`; longer trailing
    arrays are unused.

    The rectangles `[x[i], x[i]+dx[i]) × [y[i], y[i]+dy[i])` are pairwise
    non-overlapping. -/
def diffnProp (x y dx dy : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < x.length → diffnPairProp x y dx dy i j

/-- Boolean twin of `diffnProp`. -/
def diffnB (x y dx dy : List Int) : Bool :=
  (List.range x.length).all (fun j => (List.range j).all (fun i =>
    diffnPairB x y dx dy i j))

private theorem diffnB_iff (x y dx dy : List Int) :
    diffnB x y dx dy = true ↔ diffnProp x y dx dy := by
  unfold diffnB diffnProp
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h i j hij hjn
    exact (diffnPairB_iff x y dx dy i j).mp (h j hjn i hij)
  · intro h j hj i hi
    exact (diffnPairB_iff x y dx dy i j).mpr (h i j hi hj)

/-- The raw `fzn_diffn_nonstrict.mzn` disjunction at one pair `i < j`,
    with the same three-valued access rule as `diffnPairProp`.  The
    zero-side tests read only `dx[i]`, `dx[j]`, `dy[i]`, `dy[j]`
    respectively. -/
private def diffnNonstrictPairProp (x y dx dy : List Int) (i j : Nat) : Prop :=
  (i < dx.length ∧ dx.getD i 0 = 0) ∨
  (j < dx.length ∧ dx.getD j 0 = 0) ∨
  (i < dy.length ∧ dy.getD i 0 = 0) ∨
  (j < dy.length ∧ dy.getD j 0 = 0) ∨
  (i < dx.length ∧ x.getD i 0 + dx.getD i 0 ≤ x.getD j 0) ∨
  (i < y.length ∧ j < y.length ∧ i < dy.length ∧
    y.getD i 0 + dy.getD i 0 ≤ y.getD j 0) ∨
  (j < dx.length ∧ x.getD j 0 + dx.getD j 0 ≤ x.getD i 0) ∨
  (i < y.length ∧ j < y.length ∧ j < dy.length ∧
    y.getD j 0 + dy.getD j 0 ≤ y.getD i 0)

/-- Boolean twin of `diffnNonstrictPairProp`. -/
private def diffnNonstrictPairB (x y dx dy : List Int) (i j : Nat) : Bool :=
  (decide (i < dx.length) && decide (dx.getD i 0 = 0)) ||
  (decide (j < dx.length) && decide (dx.getD j 0 = 0)) ||
  (decide (i < dy.length) && decide (dy.getD i 0 = 0)) ||
  (decide (j < dy.length) && decide (dy.getD j 0 = 0)) ||
  (decide (i < dx.length) && decide (x.getD i 0 + dx.getD i 0 ≤ x.getD j 0)) ||
  (decide (i < y.length) && decide (j < y.length) && decide (i < dy.length) &&
    decide (y.getD i 0 + dy.getD i 0 ≤ y.getD j 0)) ||
  (decide (j < dx.length) && decide (x.getD j 0 + dx.getD j 0 ≤ x.getD i 0)) ||
  (decide (i < y.length) && decide (j < y.length) && decide (j < dy.length) &&
    decide (y.getD j 0 + dy.getD j 0 ≤ y.getD i 0))

private theorem diffnNonstrictPairB_iff (x y dx dy : List Int) (i j : Nat) :
    diffnNonstrictPairB x y dx dy i j = true ↔
      diffnNonstrictPairProp x y dx dy i j := by
  simp only [diffnNonstrictPairB, diffnNonstrictPairProp, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_iff, and_assoc, or_assoc]

/-- `fzn_diffn_nonstrict(x, y, dx, dy)`: transcribed from
    `fzn_diffn_nonstrict.mzn` lines 1-16.  The pair loop is vacuous for
    `x.length ≤ 1`; for a nonempty pair each of the eight disjuncts reads
    only its own entries, so a true disjunct masks a missing later entry
    and there is no unconditional length gate.

    As `fzn_diffn`, but rectangles with a zero side in either rectangle
    may touch or coincide. -/
def diffnNonstrictProp (x y dx dy : List Int) : Prop :=
  ∀ i j : Nat, i < j → j < x.length → diffnNonstrictPairProp x y dx dy i j

/-- Boolean twin of `diffnNonstrictProp`. -/
def diffnNonstrictB (x y dx dy : List Int) : Bool :=
  (List.range x.length).all (fun j => (List.range j).all (fun i =>
    diffnNonstrictPairB x y dx dy i j))

private theorem diffnNonstrictB_iff (x y dx dy : List Int) :
    diffnNonstrictB x y dx dy = true ↔ diffnNonstrictProp x y dx dy := by
  unfold diffnNonstrictB diffnNonstrictProp
  simp only [List.all_eq_true, List.mem_range]
  constructor
  · intro h i j hij hjn
    exact (diffnNonstrictPairB_iff x y dx dy i j).mp (h j hjn i hij)
  · intro h j hj i hi
    exact (diffnNonstrictPairB_iff x y dx dy i j).mpr (h i j hi hj)

/-! ## Packing: `fzn_geost_nonoverlap_k` -/

/-- The raw `fzn_geost_nonoverlap_k.mzn` body at one dimension `j`, with
    the same three-valued access rule as `diffnPairProp`.  `x1[j]` exists
    because `j < x1.length`; the first disjunct also reads `w1[j]` and
    `x2[j]`, the second `x2[j]` and `w2[j]`. -/
private def geostNonoverlapKBodyProp (x1 w1 x2 w2 : List Int) (j : Nat) : Prop :=
  (j < w1.length ∧ j < x2.length ∧
    x1.getD j 0 + w1.getD j 0 ≤ x2.getD j 0) ∨
  (j < x2.length ∧ j < w2.length ∧
    x2.getD j 0 + w2.getD j 0 ≤ x1.getD j 0)

/-- Boolean twin of `geostNonoverlapKBodyProp`. -/
private def geostNonoverlapKBodyB (x1 w1 x2 w2 : List Int) (j : Nat) : Bool :=
  (decide (j < w1.length) && decide (j < x2.length) &&
    decide (x1.getD j 0 + w1.getD j 0 ≤ x2.getD j 0)) ||
  (decide (j < x2.length) && decide (j < w2.length) &&
    decide (x2.getD j 0 + w2.getD j 0 ≤ x1.getD j 0))

private theorem geostNonoverlapKBodyB_iff (x1 w1 x2 w2 : List Int) (j : Nat) :
    geostNonoverlapKBodyB x1 w1 x2 w2 j = true ↔
      geostNonoverlapKBodyProp x1 w1 x2 w2 j := by
  simp only [geostNonoverlapKBodyB, geostNonoverlapKBodyProp, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_iff, and_assoc]

/-- `fzn_geost_nonoverlap_k(x1, w1, x2, w2)`: transcribed from
    `fzn_geost_nonoverlap_k.mzn` lines 1-8.  The `exists` runs over
    `index_set(x1)`; an early `j` whose disjunction is true makes the
    existential true without reading the later `w1`/`x2`/`w2` entries.
    There is therefore no unconditional length gate, and longer trailing
    arrays are unused.

    The two `k`-dimensional boxes with origins `x1`, `x2` and sizes `w1`,
    `w2` are separated in some dimension. -/
def geostNonoverlapKProp (x1 w1 x2 w2 : List Int) : Prop :=
  ∃ j : Nat, j < x1.length ∧ geostNonoverlapKBodyProp x1 w1 x2 w2 j

/-- Boolean twin of `geostNonoverlapKProp`. -/
def geostNonoverlapKB (x1 w1 x2 w2 : List Int) : Bool :=
  (List.range x1.length).any (fun j => geostNonoverlapKBodyB x1 w1 x2 w2 j)

private theorem geostNonoverlapKB_iff (x1 w1 x2 w2 : List Int) :
    geostNonoverlapKB x1 w1 x2 w2 = true ↔ geostNonoverlapKProp x1 w1 x2 w2 := by
  unfold geostNonoverlapKB geostNonoverlapKProp
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨j, hj, hd⟩
    exact ⟨j, hj, (geostNonoverlapKBodyB_iff x1 w1 x2 w2 j).mp hd⟩
  · rintro ⟨j, hj, hd⟩
    exact ⟨j, hj, (geostNonoverlapKBodyB_iff x1 w1 x2 w2 j).mpr hd⟩

/-! ## Scheduling: `fzn_disjunctive` and `fzn_disjunctive_strict` -/

/-- The raw `fzn_disjunctive.mzn` pair disjunction at `i < j`, with the
    same three-valued access rule as `diffnPairProp`.  The first two
    disjuncts read only `duration`; the two separation disjuncts both
    need `start[i]` and `start[j]`. -/
private def disjunctivePairProp (start dur : List Int) (i j : Nat) : Prop :=
  dur.getD i 0 = 0 ∨ dur.getD j 0 = 0 ∨
    (i < start.length ∧ j < start.length ∧
      (start.getD i 0 + dur.getD i 0 ≤ start.getD j 0 ∨
       start.getD j 0 + dur.getD j 0 ≤ start.getD i 0))

/-- Boolean twin of `disjunctivePairProp`. -/
private def disjunctivePairB (start dur : List Int) (i j : Nat) : Bool :=
  decide (dur.getD i 0 = 0) || decide (dur.getD j 0 = 0) ||
    (decide (i < start.length) && decide (j < start.length) &&
      (decide (start.getD i 0 + dur.getD i 0 ≤ start.getD j 0) ||
       decide (start.getD j 0 + dur.getD j 0 ≤ start.getD i 0)))

private theorem disjunctivePairB_iff (start dur : List Int) (i j : Nat) :
    disjunctivePairB start dur i j = true ↔
      disjunctivePairProp start dur i j := by
  simp only [disjunctivePairB, disjunctivePairProp, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_iff, and_assoc, or_assoc]

/-- `fzn_disjunctive(start, duration)`: transcribed from
    `fzn_disjunctive.mzn` lines 1-5.  Both loops use
    `index_set(duration)`.  The pair loop is vacuous for
    `dur.length ≤ 1`, and for a nonempty pair a zero duration on either
    task makes the disjunction true without reading `start`; hence there
    is no unconditional length gate and trailing `start` entries are
    unused.

    Tasks with positive duration do not overlap in time. -/
def disjunctiveProp (start dur : List Int) : Prop :=
  (∀ d ∈ dur, 0 ≤ d) ∧
    ∀ i j : Nat, i < j → j < dur.length → disjunctivePairProp start dur i j

/-- Boolean twin of `disjunctiveProp`. -/
def disjunctiveB (start dur : List Int) : Bool :=
  dur.all (fun d => decide (0 ≤ d)) &&
    (List.range dur.length).all (fun j => (List.range j).all (fun i =>
      disjunctivePairB start dur i j))

private theorem disjunctiveB_iff (start dur : List Int) :
    disjunctiveB start dur = true ↔ disjunctiveProp start dur := by
  unfold disjunctiveB disjunctiveProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hnonneg, h4⟩
    exact ⟨hnonneg, fun i j hij hjn =>
      (disjunctivePairB_iff start dur i j).mp (h4 j hjn i hij)⟩
  · rintro ⟨hnonneg, h4⟩
    exact ⟨hnonneg, fun j hj i hi =>
      (disjunctivePairB_iff start dur i j).mpr (h4 i j hi hj)⟩

/-- The raw `fzn_disjunctive_strict.mzn` pair disjunction at `i < j`;
    both disjuncts need `start[i]` and `start[j]`. -/
private def disjunctiveStrictPairProp (start dur : List Int) (i j : Nat) : Prop :=
  i < start.length ∧ j < start.length ∧
    (start.getD i 0 + dur.getD i 0 ≤ start.getD j 0 ∨
     start.getD j 0 + dur.getD j 0 ≤ start.getD i 0)

/-- Boolean twin of `disjunctiveStrictPairProp`. -/
private def disjunctiveStrictPairB (start dur : List Int) (i j : Nat) : Bool :=
  decide (i < start.length) && decide (j < start.length) &&
    (decide (start.getD i 0 + dur.getD i 0 ≤ start.getD j 0) ||
     decide (start.getD j 0 + dur.getD j 0 ≤ start.getD i 0))

private theorem disjunctiveStrictPairB_iff (start dur : List Int) (i j : Nat) :
    disjunctiveStrictPairB start dur i j = true ↔
      disjunctiveStrictPairProp start dur i j := by
  simp only [disjunctiveStrictPairB, disjunctiveStrictPairProp, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_iff, and_assoc]

/-- `fzn_disjunctive_strict(start, duration)`: transcribed from
    `fzn_disjunctive_strict.mzn` lines 1-9.  The nonnegativity and pair
    loops run over `index_set(duration)`; the pair loop is vacuous for
    `dur.length ≤ 1`, so no `start` entry is needed then.  For a
    nonempty pair both separation disjuncts read `start[i]` and
    `start[j]`, so there is no unconditional length gate.

    All tasks (including zero-duration ones) are pairwise
    non-overlapping. -/
def disjunctiveStrictProp (start dur : List Int) : Prop :=
  (∀ d ∈ dur, 0 ≤ d) ∧
    ∀ i j : Nat, i < j → j < dur.length → disjunctiveStrictPairProp start dur i j

/-- Boolean twin of `disjunctiveStrictProp`. -/
def disjunctiveStrictB (start dur : List Int) : Bool :=
  dur.all (fun d => decide (0 ≤ d)) &&
    (List.range dur.length).all (fun j => (List.range j).all (fun i =>
      disjunctiveStrictPairB start dur i j))

private theorem disjunctiveStrictB_iff (start dur : List Int) :
    disjunctiveStrictB start dur = true ↔ disjunctiveStrictProp start dur := by
  unfold disjunctiveStrictB disjunctiveStrictProp
  simp only [Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true, List.mem_range]
  constructor
  · rintro ⟨hnonneg, h4⟩
    exact ⟨hnonneg, fun i j hij hjn =>
      (disjunctiveStrictPairB_iff start dur i j).mp (h4 j hjn i hij)⟩
  · rintro ⟨hnonneg, h4⟩
    exact ⟨hnonneg, fun j hj i hi =>
      (disjunctiveStrictPairB_iff start dur i j).mpr (h4 i j hi hj)⟩

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
        simp only [if_neg h0]
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

/-- `Tasks` is empty, in value form: no task has positive duration and
    resource. -/
private def noSelectedTask (start dur res : List Int) : Bool :=
  (List.range start.length).all
    (fun i => !(decide (0 < dur.getD i 0 ∧ 0 < res.getD i 0)))

/-- `fzn_cumulative(start, duration, resource, capacity)` transcribed from
    `fzn_cumulative.mzn`, with the contract of the `cumulative` wrapper:

    - the three arrays have the same length (wrapper `index_set` assert);
    - all durations and resources are nonnegative (wrapper `assert`);
    - with `Tasks = {i | duration[i] > 0 ∧ resource[i] > 0}` (the value
      form of `ub(...) > 0`), if `Tasks` is empty then
      `length(start) = 0 ∨ capacity ≥ 0`, and otherwise the usage of the
      selected tasks is at most `capacity` at every time. -/
def cumulativeProp (start dur res : List Int) (capacity : Int) : Prop :=
  start.length = dur.length ∧ start.length = res.length ∧
    (∀ d ∈ dur, 0 ≤ d) ∧ (∀ r ∈ res, 0 ≤ r) ∧
    (noSelectedTask start dur res = true ∨
        ∀ t : Int, cumul start dur res t ≤ capacity) ∧
    (noSelectedTask start dur res = true →
        start.length = 0 ∨ 0 ≤ capacity)

/-- Boolean twin of `cumulativeProp`, obtained by deciding the Prop with the
    universal time quantifier replaced by its equivalent finite checkpoint
    form. -/
def cumulativeB (start dur res : List Int) (capacity : Int) : Bool :=
  decide (start.length = dur.length) && decide (start.length = res.length) &&
    dur.all (fun d => decide (0 ≤ d)) && res.all (fun r => decide (0 ≤ r)) &&
    if noSelectedTask start dur res then
      decide (start.length = 0) || decide (0 ≤ capacity)
    else
      (start.all (fun s => decide (cumul start dur res s ≤ capacity)) &&
        (taskEnds start dur).all (fun e =>
          decide (cumul start dur res e ≤ capacity)))

/-- The checkpoint reduction: within capacity at every start and completion
    time implies within capacity at every time (the usage is constant between
    event points). Nonnegativity of the values is not needed for this
    direction. -/
private theorem cumul_checkpoints (start dur res : List Int) (capacity : Int)
    (hstarts : start.all (fun s => decide (cumul start dur res s ≤ capacity)) = true)
    (hends : (taskEnds start dur).all
      (fun e => decide (cumul start dur res e ≤ capacity)) = true)
    (hcap : 0 ≤ capacity) :
    ∀ t : Int, cumul start dur res t ≤ capacity := by
  intro t
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
    have hble : List.foldl max b0 bs ≤ t :=
      of_decide_eq_true (List.mem_filter.mp hbfilt).2
    have hbcap : cumul start dur res (List.foldl max b0 bs) ≤ capacity := by
      rcases List.mem_append.mp (List.mem_filter.mp hbfilt).1 with hm | hm
      · exact of_decide_eq_true (List.all_eq_true.mp hstarts _ hm)
      · exact of_decide_eq_true (List.all_eq_true.mp hends _ hm)
    have hcongr : cumul start dur res t = cumul start dur res (List.foldl max b0 bs) := by
      refine cumul_congr t (List.foldl max b0 bs) start dur res (fun i hi => ?_)
      have hb0le : b0 ≤ List.foldl max b0 bs := foldl_max_ge_init bs b0
      constructor
      · rintro ⟨hsi, hti⟩
        refine ⟨?_, by omega⟩
        have hsimem : start.getD i 0 ∈ start := mem_iff_getD.mpr ⟨i, hi, rfl⟩
        have hsifilt : start.getD i 0 ∈ b0 :: bs := by
          rw [← hfilt]
          exact List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inl hsimem),
            decide_eq_true hsi⟩
        rcases List.mem_cons.mp hsifilt with heq | hm
        · rw [heq]; exact hb0le
        · exact foldl_max_ge_mem bs b0 _ hm
      · rintro ⟨hsi, hbi⟩
        have hielem : start.getD i 0 + dur.getD i 0 ∈ taskEnds start dur :=
          List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
        by_cases hiet : start.getD i 0 + dur.getD i 0 ≤ t
        · have hiefilt : start.getD i 0 + dur.getD i 0 ∈ b0 :: bs := by
            rw [← hfilt]
            exact List.mem_filter.mpr ⟨List.mem_append.mpr (Or.inr hielem),
              decide_eq_true hiet⟩
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
    exact hcap

/-- Under nonnegative resources, the cumulative usage is nonnegative. -/
private theorem cumul_nonneg (t : Int) : ∀ (start dur res : List Int),
    (∀ r ∈ res, 0 ≤ r) → 0 ≤ cumul start dur res t := by
  intro start
  induction start with
  | nil => intro dur res _; exact by simp [cumul]
  | cons s0 st ih =>
    intro dur res hres
    cases dur with
    | nil => exact by simp [cumul]
    | cons d0 dt =>
      cases res with
      | nil => exact by simp [cumul]
      | cons r0 rt =>
        simp only [cumul]
        by_cases hact : s0 ≤ t ∧ t < s0 + d0
        · rw [if_pos hact]
          have h0 : 0 ≤ r0 := hres r0 (List.mem_cons_self ..)
          have h1 : 0 ≤ cumul st dt rt t :=
            ih dt rt (fun r hr => hres r (List.mem_cons_of_mem _ hr))
          omega
        · rw [if_neg hact]
          rw [Int.zero_add]
          exact ih dt rt (fun r hr => hres r (List.mem_cons_of_mem _ hr))

/-- `noSelectedTask = false` means some task has positive duration and
    resource. -/
private theorem not_noSelectedTask {start dur res : List Int}
    (h : noSelectedTask start dur res = false) :
    ∃ i, i < start.length ∧ 0 < dur.getD i 0 ∧ 0 < res.getD i 0 := by
  unfold noSelectedTask at h
  obtain ⟨i, hi, hnot⟩ := List.all_eq_false.mp h
  simp only [List.mem_range] at hi
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hnot
  exact ⟨i, hi, Classical.not_not.mp hnot⟩

/-- If some task is selected, the usage is nonnegative somewhere, so the
    capacity must be nonnegative. -/
private theorem capacity_nonneg_of_selected {start dur res : List Int}
    {capacity : Int} (hnr : ∀ r ∈ res, 0 ≤ r)
    (hs : ∀ s ∈ start, cumul start dur res s ≤ capacity)
    (hsel : noSelectedTask start dur res = false) : 0 ≤ capacity := by
  obtain ⟨i, hi, _⟩ := not_noSelectedTask hsel
  exact Int.le_trans (cumul_nonneg _ start dur res hnr)
    (hs _ (mem_iff_getD.mpr ⟨i, hi, rfl⟩))

private theorem cumulativeB_iff (start dur res : List Int) (capacity : Int) :
    cumulativeB start dur res capacity = true ↔ cumulativeProp start dur res capacity := by
  unfold cumulativeB cumulativeProp
  by_cases hsel : noSelectedTask start dur res = true
  · rw [hsel]
    simp only [ite_true, Bool.and_eq_true, decide_eq_true_iff, List.all_eq_true]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2, Or.inl trivial, fun _ => ?_⟩
      simp only [Bool.or_eq_true, decide_eq_true_iff] at h2
      exact h2
    · rintro ⟨hlen1, hlen2, hnD, hnR, _, hcap⟩
      exact ⟨⟨⟨⟨hlen1, hlen2⟩, hnD⟩, hnR⟩, by
        simp only [Bool.or_eq_true, decide_eq_true_iff]
        exact hcap trivial⟩
  · have hsel' : noSelectedTask start dur res = false := by
      cases h : noSelectedTask start dur res with
      | false => rfl
      | true => exact absurd h hsel
    rw [hsel']
    simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true,
      decide_eq_true_iff, List.all_eq_true]
    constructor
    · rintro ⟨⟨⟨⟨hlen1, hlen2⟩, hnD⟩, hnR⟩, ⟨hs, he⟩⟩
      refine ⟨hlen1, hlen2, hnD, hnR, Or.inr ?_, False.elim⟩
      exact cumul_checkpoints start dur res capacity
        (List.all_eq_true.mpr (fun s hs' => decide_eq_true (hs s hs')))
        (List.all_eq_true.mpr (fun e he' => decide_eq_true (he e he')))
        (capacity_nonneg_of_selected hnR (fun s hs' => hs s hs') hsel')
    · rintro ⟨hlen1, hlen2, hnD, hnR, hcase, _⟩
      rcases hcase with hbad | hall
      · exact hbad.elim
      · refine ⟨⟨⟨⟨hlen1, hlen2⟩, hnD⟩, hnR⟩, ⟨?_, ?_⟩⟩
        · exact fun s _ => hall s
        · exact fun e _ => hall e

/-! ## Extensional: `fzn_table_int` -/

/-- `fzn_table_int(xs, tuples)` under the flat FlatZinc ABI (SC-03):
    `tuples` is the row-major flattening of a matrix with `|xs|` columns
    (`columns = |xs|`, `rows = |tuples| / |xs|`) and `xs` equals one
    complete row.

    The upstream decomposition (`fzn_table_int.mzn` lines 8–15) takes
    `min`/`max` of `index_set(xs)` and `index_set_1of2(tuples)`, so an
    empty `xs` (or an empty tuple matrix) makes the constraint
    undefined, i.e. **false**; an empty `xs` no longer matches
    vacuously. The divisibility conjunct rejects a flat tuple array
    that is not the flattening of any matrix with `|xs|` columns. -/
def tableIntProp (xs tuples : List Int) : Prop :=
  0 < xs.length ∧
    tuples.length % xs.length = 0 ∧
    ∃ r : Nat, r < tuples.length / xs.length ∧
      ∀ j : Nat, j < xs.length →
        tuples.getD (r * xs.length + j) 0 = xs.getD j 0

/-- Boolean twin of `tableIntProp`. -/
def tableIntB (xs tuples : List Int) : Bool :=
  decide (0 < xs.length) && decide (tuples.length % xs.length = 0) &&
    (List.range (tuples.length / xs.length)).any (fun r =>
      (List.range xs.length).all (fun j =>
        decide (tuples.getD (r * xs.length + j) 0 = xs.getD j 0)))

private theorem tableIntB_iff (xs tuples : List Int) :
    tableIntB xs tuples = true ↔ tableIntProp xs tuples := by
  unfold tableIntB tableIntProp
  simp only [Bool.and_eq_true, List.any_eq_true, List.all_eq_true,
    List.mem_range, decide_eq_true_iff]
  constructor
  · rintro ⟨⟨hpos, hdiv⟩, r, hr, hall⟩
    exact ⟨hpos, hdiv, r, hr, hall⟩
  · rintro ⟨hpos, hdiv, r, hr, hall⟩
    exact ⟨⟨hpos, hdiv⟩, r, hr, hall⟩

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

/-- Mathematical meaning shared by the `int` and `set`
    `fzn_if_then_else_*` predicates: if the first true condition is at
    0-based index `i`, then `x[i]` is read and `y` equals it; when all
    conditions are false no `x` entry is read and there is no constraint.
    For these element types an out-of-bounds `x[i]` makes the equality
    undefined, hence false, so the selected index must exist.  The `bool`
    rows use `iteBoolProp` below: MiniZinc 2.10.1 turns an out-of-bounds
    bool into `false` at the subexpression level, so a missing selected
    entry is the defined equality `y = false`.

    The `d` guard in `fzn_if_then_else_{int,bool,set}.mzn` line 7 makes
    the implication body read `x[i]` only at the first true `c` index.
    There is therefore no unconditional `c.length ≤ x.length` gate, and
    trailing `x` entries are unused. -/
private def iteGenProp {α : Type} (fallback : α) (eqv : α → α → Prop)
    (c : List Bool) (x : List α) (y : α) : Prop :=
  match firstTrue c with
  | none => True
  | some i => i < x.length ∧ eqv y (x.getD i fallback)

/-- Boolean twin of `iteGenProp`. -/
private def iteGenB {α : Type} (fallback : α) (eqB : α → α → Bool)
    (c : List Bool) (x : List α) (y : α) : Bool :=
  match firstTrue c with
  | none => true
  | some i => decide (i < x.length) && eqB y (x.getD i fallback)

private theorem iteGenB_iff {α : Type} (fallback : α) (eqv : α → α → Prop)
    (eqB : α → α → Bool) (hEq : ∀ a b, eqB a b = true ↔ eqv a b)
    (c : List Bool) (x : List α) (y : α) :
    iteGenB fallback eqB c x y = true ↔ iteGenProp fallback eqv c x y := by
  unfold iteGenB iteGenProp
  cases hf : firstTrue c with
  | none => simp
  | some i =>
    simp only [Bool.and_eq_true, decide_eq_true_iff, hEq]

/-- `fzn_if_then_else_int(c, x, y)` (and its `_var_int` twin). -/
def iteIntProp (c : List Bool) (x : List Int) (y : Int) : Prop :=
  iteGenProp 0 (fun a b => a = b) c x y

def iteIntB (c : List Bool) (x : List Int) (y : Int) : Bool :=
  iteGenB 0 (fun a b => decide (a = b)) c x y

private theorem iteIntB_iff (c : List Bool) (x : List Int) (y : Int) :
    iteIntB c x y = true ↔ iteIntProp c x y :=
  iteGenB_iff 0 (fun a b => a = b) (fun a b => decide (a = b))
    (fun _ _ => decide_eq_true_iff) c x y

/-- `fzn_if_then_else_bool(c, x, y)` (and its `_var_bool` twin).
    Unlike `int`/`set`, MiniZinc 2.10.1 turns an out-of-bounds bool into
    `false` at the subexpression level ("undefined result becomes false in
    Boolean context"), so a missing selected `x[i]` is the defined
    constraint `y = false` rather than an undefined equality.  All other
    entries of `x` are still unread, and an all-false `c` leaves `y`
    unrestricted. -/
def iteBoolProp (c : List Bool) (x : List Bool) (y : Bool) : Prop :=
  match firstTrue c with
  | none => True
  | some i => y = x.getD i false

def iteBoolB (c : List Bool) (x : List Bool) (y : Bool) : Bool :=
  match firstTrue c with
  | none => true
  | some i => y == x.getD i false

private theorem iteBoolB_iff (c : List Bool) (x : List Bool) (y : Bool) :
    iteBoolB c x y = true ↔ iteBoolProp c x y := by
  unfold iteBoolB iteBoolProp
  cases firstTrue c with
  | none => simp
  | some i => simp

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
def packSchedInterp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
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

/-- `fzn_bin_packing` decodes the same shapes. -/
theorem intInts2_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (intInts2 vs).isSome = (intInts2 ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a1 b1 ha1 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool => rfl
              | int => rfl
              | setOfInt => rfl
              | @array a2 b2 ha2 =>
                cases ht3 with
                | cons _ _ => rfl
                | nil =>
                  simp only [intInts2]
                  have hx1 := valueInts_isSome_sameShape ha1
                  have hx2 := valueInts_isSome_sameShape ha2
                  cases h1 : valueInts a1 with
                  | none =>
                    cases h2 : valueInts b1 with
                    | none => rfl
                    | some _ => simp [h1, h2] at hx1
                  | some _ =>
                    cases h2 : valueInts b1 with
                    | none => simp [h1, h2] at hx1
                    | some _ =>
                      cases h3 : valueInts a2 with
                      | none =>
                        cases h4 : valueInts b2 with
                        | none => rfl
                        | some _ => simp [h3, h4] at hx2
                      | some _ =>
                        cases h4 : valueInts b2 with
                        | none => simp [h3, h4] at hx2
                        | some _ => rfl
      | setOfInt => rfl
      | array => rfl


/-- `fzn_bin_packing_capa`/`fzn_bin_packing_load` decode the same shapes. -/
theorem ints3_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (ints3 vs).isSome = (ints3 ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool => rfl
              | int => rfl
              | setOfInt => rfl
              | @array a3 b3 ha3 =>
                cases ht3 with
                | cons _ _ => rfl
                | nil =>
                  simp only [ints3]
                  have hx1 := valueInts_isSome_sameShape ha1
                  have hx2 := valueInts_isSome_sameShape ha2
                  have hx3 := valueInts_isSome_sameShape ha3
                  cases h1 : valueInts a1 with
                  | none =>
                    cases h2 : valueInts b1 with
                    | none => rfl
                    | some _ => simp [h1, h2] at hx1
                  | some _ =>
                    cases h2 : valueInts b1 with
                    | none => simp [h1, h2] at hx1
                    | some _ =>
                      cases h3 : valueInts a2 with
                      | none =>
                        cases h4 : valueInts b2 with
                        | none => rfl
                        | some _ => simp [h3, h4] at hx2
                      | some _ =>
                        cases h4 : valueInts b2 with
                        | none => simp [h3, h4] at hx2
                        | some _ =>
                          cases h5 : valueInts a3 with
                          | none =>
                            cases h6 : valueInts b3 with
                            | none => rfl
                            | some _ => simp [h5, h6] at hx3
                          | some _ =>
                            cases h6 : valueInts b3 with
                            | none => simp [h5, h6] at hx3
                            | some _ => rfl


/-- `fzn_diffn`/`fzn_diffn_nonstrict`/`fzn_geost_nonoverlap_k` decode the same shapes. -/
theorem ints4_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (ints4 vs).isSome = (ints4 ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool => rfl
              | int => rfl
              | setOfInt => rfl
              | @array a3 b3 ha3 =>
                cases ht3 with
                | nil => rfl
                | cons hv4 ht4 =>
                  cases hv4 with
                  | bool => rfl
                  | int => rfl
                  | setOfInt => rfl
                  | @array a4 b4 ha4 =>
                    cases ht4 with
                    | cons _ _ => rfl
                    | nil =>
                      simp only [ints4]
                      have hx1 := valueInts_isSome_sameShape ha1
                      have hx2 := valueInts_isSome_sameShape ha2
                      have hx3 := valueInts_isSome_sameShape ha3
                      have hx4 := valueInts_isSome_sameShape ha4
                      cases h1 : valueInts a1 with
                      | none =>
                        cases h2 : valueInts b1 with
                        | none => rfl
                        | some _ => simp [h1, h2] at hx1
                      | some _ =>
                        cases h2 : valueInts b1 with
                        | none => simp [h1, h2] at hx1
                        | some _ =>
                          cases h3 : valueInts a2 with
                          | none =>
                            cases h4 : valueInts b2 with
                            | none => rfl
                            | some _ => simp [h3, h4] at hx2
                          | some _ =>
                            cases h4 : valueInts b2 with
                            | none => simp [h3, h4] at hx2
                            | some _ =>
                              cases h5 : valueInts a3 with
                              | none =>
                                cases h6 : valueInts b3 with
                                | none => rfl
                                | some _ => simp [h5, h6] at hx3
                              | some _ =>
                                cases h6 : valueInts b3 with
                                | none => simp [h5, h6] at hx3
                                | some _ =>
                                  cases h7 : valueInts a4 with
                                  | none =>
                                    cases h8 : valueInts b4 with
                                    | none => rfl
                                    | some _ => simp [h7, h8] at hx4
                                  | some _ =>
                                    cases h8 : valueInts b4 with
                                    | none => simp [h7, h8] at hx4
                                    | some _ => rfl


/-- `fzn_cumulative` decodes the same shapes. -/
theorem ints3Int_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (ints3Int vs).isSome = (ints3Int ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool => rfl
              | int => rfl
              | setOfInt => rfl
              | @array a3 b3 ha3 =>
                cases ht3 with
                | nil => rfl
                | cons hv4 ht4 =>
                  cases hv4 with
                  | bool => rfl
                  | int =>
                    cases ht4 with
                    | cons _ _ => rfl
                    | nil =>
                      simp only [ints3Int]
                      have hx1 := valueInts_isSome_sameShape ha1
                      have hx2 := valueInts_isSome_sameShape ha2
                      have hx3 := valueInts_isSome_sameShape ha3
                      cases h1 : valueInts a1 with
                      | none =>
                        cases h2 : valueInts b1 with
                        | none => rfl
                        | some _ => simp [h1, h2] at hx1
                      | some _ =>
                        cases h2 : valueInts b1 with
                        | none => simp [h1, h2] at hx1
                        | some _ =>
                          cases h3 : valueInts a2 with
                          | none =>
                            cases h4 : valueInts b2 with
                            | none => rfl
                            | some _ => simp [h3, h4] at hx2
                          | some _ =>
                            cases h4 : valueInts b2 with
                            | none => simp [h3, h4] at hx2
                            | some _ =>
                              cases h5 : valueInts a3 with
                              | none =>
                                cases h6 : valueInts b3 with
                                | none => rfl
                                | some _ => simp [h5, h6] at hx3
                              | some _ =>
                                cases h6 : valueInts b3 with
                                | none => simp [h5, h6] at hx3
                                | some _ => rfl
                  | setOfInt => rfl
                  | array => rfl


/-- `fzn_knapsack` decodes the same shapes. -/
theorem ints3IntInt_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (ints3IntInt vs).isSome = (ints3IntInt ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool => rfl
              | int => rfl
              | setOfInt => rfl
              | @array a3 b3 ha3 =>
                cases ht3 with
                | nil => rfl
                | cons hv4 ht4 =>
                  cases hv4 with
                  | bool => rfl
                  | int =>
                    cases ht4 with
                    | nil => rfl
                    | cons hv5 ht5 =>
                      cases hv5 with
                      | bool => rfl
                      | int =>
                        cases ht5 with
                        | cons _ _ => rfl
                        | nil =>
                          simp only [ints3IntInt]
                          have hx1 := valueInts_isSome_sameShape ha1
                          have hx2 := valueInts_isSome_sameShape ha2
                          have hx3 := valueInts_isSome_sameShape ha3
                          cases h1 : valueInts a1 with
                          | none =>
                            cases h2 : valueInts b1 with
                            | none => rfl
                            | some _ => simp [h1, h2] at hx1
                          | some _ =>
                            cases h2 : valueInts b1 with
                            | none => simp [h1, h2] at hx1
                            | some _ =>
                              cases h3 : valueInts a2 with
                              | none =>
                                cases h4 : valueInts b2 with
                                | none => rfl
                                | some _ => simp [h3, h4] at hx2
                              | some _ =>
                                cases h4 : valueInts b2 with
                                | none => simp [h3, h4] at hx2
                                | some _ =>
                                  cases h5 : valueInts a3 with
                                  | none =>
                                    cases h6 : valueInts b3 with
                                    | none => rfl
                                    | some _ => simp [h5, h6] at hx3
                                  | some _ =>
                                    cases h6 : valueInts b3 with
                                    | none => simp [h5, h6] at hx3
                                    | some _ => rfl
                      | setOfInt => rfl
                      | array => rfl
                  | setOfInt => rfl
                  | array => rfl


/-- `fzn_disjunctive`/`fzn_disjunctive_strict`/`fzn_table_int` decode the same shapes. -/
theorem ints2_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (ints2 vs).isSome = (ints2 ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | cons _ _ => rfl
            | nil =>
              simp only [ints2]
              have hx1 := valueInts_isSome_sameShape ha1
              have hx2 := valueInts_isSome_sameShape ha2
              cases h1 : valueInts a1 with
              | none =>
                cases h2 : valueInts b1 with
                | none => rfl
                | some _ => simp [h1, h2] at hx1
              | some _ =>
                cases h2 : valueInts b1 with
                | none => simp [h1, h2] at hx1
                | some _ =>
                  cases h3 : valueInts a2 with
                  | none =>
                    cases h4 : valueInts b2 with
                    | none => rfl
                    | some _ => simp [h3, h4] at hx2
                  | some _ =>
                    cases h4 : valueInts b2 with
                    | none => simp [h3, h4] at hx2
                    | some _ => rfl


/-- `fzn_if_then_else_int` decodes the same shapes. -/
theorem boolsIntsInt_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (boolsIntsInt vs).isSome = (boolsIntsInt ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool => rfl
              | int =>
                cases ht3 with
                | cons _ _ => rfl
                | nil =>
                  simp only [boolsIntsInt]
                  have hx1 := valueBools_isSome_sameShape ha1
                  have hx2 := valueInts_isSome_sameShape ha2
                  cases h1 : valueBools a1 with
                  | none =>
                    cases h2 : valueBools b1 with
                    | none => rfl
                    | some _ => simp [h1, h2] at hx1
                  | some _ =>
                    cases h2 : valueBools b1 with
                    | none => simp [h1, h2] at hx1
                    | some _ =>
                      cases h3 : valueInts a2 with
                      | none =>
                        cases h4 : valueInts b2 with
                        | none => rfl
                        | some _ => simp [h3, h4] at hx2
                      | some _ =>
                        cases h4 : valueInts b2 with
                        | none => simp [h3, h4] at hx2
                        | some _ => rfl
              | setOfInt => rfl
              | array => rfl


/-- `fzn_if_then_else_bool` decodes the same shapes. -/
theorem boolsBoolsBool_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (boolsBoolsBool vs).isSome = (boolsBoolsBool ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool =>
                cases ht3 with
                | cons _ _ => rfl
                | nil =>
                  simp only [boolsBoolsBool]
                  have hx1 := valueBools_isSome_sameShape ha1
                  have hx2 := valueBools_isSome_sameShape ha2
                  cases h1 : valueBools a1 with
                  | none =>
                    cases h2 : valueBools b1 with
                    | none => rfl
                    | some _ => simp [h1, h2] at hx1
                  | some _ =>
                    cases h2 : valueBools b1 with
                    | none => simp [h1, h2] at hx1
                    | some _ =>
                      cases h3 : valueBools a2 with
                      | none =>
                        cases h4 : valueBools b2 with
                        | none => rfl
                        | some _ => simp [h3, h4] at hx2
                      | some _ =>
                        cases h4 : valueBools b2 with
                        | none => simp [h3, h4] at hx2
                        | some _ => rfl
              | int => rfl
              | setOfInt => rfl
              | array => rfl


/-- `fzn_if_then_else_set` decodes the same shapes. -/
theorem boolsSetsSet_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (boolsSetsSet vs).isSome = (boolsSetsSet ws).isSome := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  rcases vs with _ | ⟨v0, vs1⟩
  · cases hshape
    rfl
  · cases hshape with
    | cons hv1 ht1 =>
      cases hv1 with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | @array a1 b1 ha1 =>
        cases ht1 with
        | nil => rfl
        | cons hv2 ht2 =>
          cases hv2 with
          | bool => rfl
          | int => rfl
          | setOfInt => rfl
          | @array a2 b2 ha2 =>
            cases ht2 with
            | nil => rfl
            | cons hv3 ht3 =>
              cases hv3 with
              | bool => rfl
              | int => rfl
              | setOfInt =>
                cases ht3 with
                | cons _ _ => rfl
                | nil =>
                  simp only [boolsSetsSet]
                  have hx1 := valueBools_isSome_sameShape ha1
                  have hx2 := valueSets_isSome_sameShape ha2
                  cases h1 : valueBools a1 with
                  | none =>
                    cases h2 : valueBools b1 with
                    | none => rfl
                    | some _ => simp [h1, h2] at hx1
                  | some _ =>
                    cases h2 : valueBools b1 with
                    | none => simp [h1, h2] at hx1
                    | some _ =>
                      cases h3 : valueSets a2 with
                      | none =>
                        cases h4 : valueSets b2 with
                        | none => rfl
                        | some _ => simp [h3, h4] at hx2
                      | some _ =>
                        cases h4 : valueSets b2 with
                        | none => simp [h3, h4] at hx2
                        | some _ => rfl
              | array => rfl

/-! ## Decodability gate -/

/-- Lengths of the array arguments, in order (non-array actual arguments,
    e.g. scalar outputs, are skipped).  Array lengths are the only
    argument-shape information a static gate may inspect, and they are
    invariant under `ArgsAgree`. -/
private def arrayLens : List Value → List Nat
  | [] => []
  | .array xs :: rest => xs.length :: arrayLens rest
  | _ :: rest => arrayLens rest

/-- `arrayLens` is invariant under shape agreement (`ArgsAgree`). -/
private theorem arrayLens_eq_of_sameShapeList :
    ∀ {vs ws : List Value}, Value.SameShapeList vs ws →
      arrayLens vs = arrayLens ws := by
  intro vs ws h
  induction h with
  | nil => rfl
  | cons hx hxs ih =>
    cases hx with
    | bool => exact ih
    | int => exact ih
    | setOfInt => exact ih
    | array harr =>
      simp only [arrayLens]
      rw [ListSameShape.length_eq harr, ih]

/-- Boolean decodability gate of the packing, scheduling, table and
    if-then-else families: the `isSome` of the very decoder
    `packSchedInterp` uses, together with the static length relations
    that are unconditional in the raw decompositions:

    - `bin_packing`: `bin.length = 0 ∨ bin.length = weight.length`
      (the nonempty branch sums `bin` and `weight` in lockstep);
    - `bin_packing_capa` / `bin_packing_load`: `bin.length ≤ weight.length`;
    - `knapsack`: `weight.length ≤ xs.length ∧ profit.length ≤ xs.length`.

    Every other shape condition in this family is value-dependent or
    vacuous and therefore belongs to the interpreter, not to a static
    gate: `diffn`/`diffn_nonstrict` and `disjunctive`/`disjunctive_strict`
    have empty pair loops and masked disjuncts, `geost_nonoverlap_k` and
    the six `if_then_else_*` predicates read only the witnessing
    dimension / first true index.  Those rows are still decodable; the
    interpreter may return `false` for a call whose selected entries are
    missing.  Value-level conditions (index ranges, nonnegativity, sums)
    likewise stay in the interpreters: they can be genuinely false
    rather than undecodable.  The gate is `true` outside the family. -/
def packSchedDecodes (n : String) (args : List Value) : Bool :=
  match n with
  | "fzn_bin_packing" => (intInts2 args).isSome &&
      (match arrayLens args with
       | [bl, wl] => decide (bl = 0 ∨ bl = wl)
       | _ => false)
  | "fzn_bin_packing_capa" => (ints3 args).isSome &&
      (match arrayLens args with
       | [_, bl, wl] => decide (bl ≤ wl)
       | _ => false)
  | "fzn_bin_packing_load" => (ints3 args).isSome &&
      (match arrayLens args with
       | [_, bl, wl] => decide (bl ≤ wl)
       | _ => false)
  | "fzn_knapsack" => (ints3IntInt args).isSome &&
      (match arrayLens args with
       | [wl, pl, xl] => decide (wl ≤ xl ∧ pl ≤ xl)
       | _ => false)
  | "fzn_diffn" => (ints4 args).isSome
  | "fzn_diffn_nonstrict" => (ints4 args).isSome
  | "fzn_geost_nonoverlap_k" => (ints4 args).isSome
  | "fzn_disjunctive" => (ints2 args).isSome
  | "fzn_disjunctive_strict" => (ints2 args).isSome
  | "fzn_cumulative" => (ints3Int args).isSome
  | "fzn_table_int" => (ints2 args).isSome
  | "fzn_if_then_else_int" => (boolsIntsInt args).isSome
  | "fzn_if_then_else_var_int" => (boolsIntsInt args).isSome
  | "fzn_if_then_else_bool" => (boolsBoolsBool args).isSome
  | "fzn_if_then_else_var_bool" => (boolsBoolsBool args).isSome
  | "fzn_if_then_else_set" => (boolsSetsSet args).isSome
  | "fzn_if_then_else_var_set" => (boolsSetsSet args).isSome
  | _ => true

/-- The decodability gate is invariant under `ArgsAgree`. -/
theorem packSchedDecodes_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) (n : String) :
    packSchedDecodes n vs = packSchedDecodes n ws := by
  have hlens : arrayLens vs = arrayLens ws :=
    arrayLens_eq_of_sameShapeList (ArgsAgree.sameShape h)
  unfold packSchedDecodes
  split
  · simp only [intInts2_isSome_agree h, hlens]
  · simp only [ints3_isSome_agree h, hlens]
  · simp only [ints3_isSome_agree h, hlens]
  · simp only [ints3IntInt_isSome_agree h, hlens]
  · simp only [ints4_isSome_agree h]
  · simp only [ints4_isSome_agree h]
  · simp only [ints4_isSome_agree h]
  · simp only [ints2_isSome_agree h]
  · simp only [ints2_isSome_agree h]
  · exact ints3Int_isSome_agree h
  · exact ints2_isSome_agree h
  · simp only [boolsIntsInt_isSome_agree h]
  · simp only [boolsIntsInt_isSome_agree h]
  · simp only [boolsBoolsBool_isSome_agree h]
  · simp only [boolsBoolsBool_isSome_agree h]
  · simp only [boolsSetsSet_isSome_agree h]
  · simp only [boolsSetsSet_isSome_agree h]
  · rfl

end LeanFzn.Semantics.Globals.PackSched
