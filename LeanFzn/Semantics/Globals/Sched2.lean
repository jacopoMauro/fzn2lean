/-
Purpose: Extended scheduling, geometric, write and partiality predicate semantics.
Dependencies: Globals.Common supplies shared values and finite-array helpers.
DAG: Shared semantics -> this family -> Globals dispatch and checker correctness.
-/
import LeanFzn.Semantics.Globals.Common
open LeanFzn.Semantics


/-!
# Scheduling, geometric, and remaining global constraints

Mathematical interpretations (`sched2Interp`) and executable Boolean
twins (`sched2InterpB`) for the remaining encodable predicates of the
pinned MiniZinc 2.10.1 tree, per the decompositions recorded in
`specification/flatzinc_specification_assumptions.md`, G26, G30–G32:

* `fzn_cumulatives(start, duration, resource, machine, bound,
  is_upper_bound, min_machine)` and `fzn_cumulatives_decomp` (7 resp.
  6 args): event-point resource checking (G26).
* `fzn_geost(k, rect_size, rect_offset, shape, xs, kind)` and the
  `bb`/`smallest_bb` variants (G30): k-dimensional non-overlap of
  shape-selected objects. `rect_size`/`rect_offset`/`xs` are flat
  row-major `k`-column matrices (the FlatZinc ABI, SC-03); the
  admissibility gates (`k ≥ 0`, `|xs| ≥ |kind|·k`, kind indices in
  `1..|shape|`, every shape rectangle id a real matrix row, and
  `|lower|,|upper| ≥ k`) are stated in `geostGates`/`geostBbGates`.
  `has_bounds(kind)` is a wrapper assertion on the variable domains, not
  a value constraint.
* `fzn_diffn_nonoverlap_k(x1, w1, x2, w2)`: 1-D per-axis
  non-overlap.  `fzn_diffn_k` / `fzn_diffn_nonstrict_k` are **not**
  supported at the FlatZinc ABI: upstream takes `array [int,int]`
  arguments whose dimension count `index_set_2of2(box_posn)` is not a
  FlatZinc argument, so a flat call is rejected.  The nested
  `List (List Int)` interpretation (G30/G24) is a project-internal
  extension and is **not** FlatZinc ABI.
* `fzn_writes_seq(I, P, V, O)` (G31): last-write-wins.
* `fzn_if_then_else_partiality(c, def, b)` (G32): definedness of the
  first-true conditional.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.Sched2

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

/-! ## cumulatives -/

/-- Length/range admissibility gate of `fzn_cumulatives` and
    `fzn_cumulatives_decomp`, read off `fzn_cumulatives_decomp.mzn`:

    * `Tasks = index_set(start)` (line 11).  `duration[i]`, `resource[i]`
      and `machine[i]` are read for every `i ∈ Tasks` (lines 16–42), and
      `start[j]`, `duration[j]`, `machine[j]` for every `j ∈ Tasks`
      (lines 12–47).  Hence `start.length ≤ duration.length`,
      `start.length ≤ resource.length` and
      `start.length ≤ machine.length` are required; trailing entries of
      the longer arrays are never read and are accepted.
    * `bound[machine[j]]` is read at lines 44–47 for every `j ∈ Tasks`, so
      the machine value must satisfy `1 ≤ machine[j] ≤ bound.length`
      (trailing `bound` entries are unread).  `machine` is the
      **normalized** list: `cumulativesArgs` maps every entry to
      `m - min_machine + 1` for `fzn_cumulatives` (`fzn_cumulatives.mzn`
      comment lines 3–5: `min_machine` is the first machine of the
      `bound` index set).  `fzn_cumulatives_decomp` has no `min_machine`
      argument and is used unchanged.
    * An empty `start` is vacuously true upstream for any other lengths. -/
def cumulativesShapeB (start duration resource machine bound : List Int) :
    Bool :=
  decide (start.length ≤ duration.length ∧
      start.length ≤ resource.length ∧ start.length ≤ machine.length) &&
    (List.range start.length).all (fun i =>
      -- `i < start.length ≤ machine.length` by the length conjunct above,
      -- so the `machine.getD i 0` read is in range: the default is never
      -- used.
      decide (1 ≤ machine.getD i 0 ∧
        machine.getD i 0 ≤ (bound.length : Int)))

/-- Prop twin of `cumulativesShapeB`. -/
abbrev cumulativesShape (start duration resource machine bound : List Int) :
    Prop :=
  (start.length ≤ duration.length ∧ start.length ≤ resource.length ∧
    start.length ≤ machine.length) ∧
    (∀ i, i < start.length →
      1 ≤ machine.getD i 0 ∧ machine.getD i 0 ≤ (bound.length : Int))

theorem cumulativesShapeB_iff (start duration resource machine bound :
    List Int) :
    cumulativesShapeB start duration resource machine bound = true ↔
      cumulativesShape start duration resource machine bound := by
  simp only [cumulativesShapeB, cumulativesShape, Bool.and_eq_true,
    List.all_eq_true, List.mem_range, decide_eq_true_iff]

/-- Does task `i` (start `si`, duration `di`) run on machine `mi`
    at time `t` (half-open interval)? -/
private def taskAt (si di mi t mach : Int) : Bool :=
  decide (si ≤ t ∧ t < si + di ∧ mi = mach)

/-- The event-point loads of machine `m`'s j-th check.  Every `getD` below
    is protected by `cumulativesShape`: the fold index satisfies
    `i < start.length` and the checked index `j < start.length`, and the
    length conjuncts `start.length ≤ duration.length`,
    `start.length ≤ resource.length`, `start.length ≤ machine.length` put
    those arrays in range there. -/
private def eventLoads (start duration resource machine : List Int) (j : Nat) :
    Int × Int :=
  let loadAt (t : Int) : Int :=
    (List.range start.length).foldl (fun acc i =>
      -- `i < start.length ≤ duration/resource/machine.length`
      -- (cumulativesShape), so these reads use no default.
      if taskAt (start.getD i 0) (duration.getD i 0) (machine.getD i 0) t
          -- `j < start.length ≤ machine.length` (cumulativesShape).
          (machine.getD j 0) then
        acc + resource.getD i 0 else acc) 0
  -- `j < start.length ≤ start/duration.length` (cumulativesShape).
  (loadAt (start.getD j 0), loadAt (start.getD j 0 + duration.getD j 0))

/-- The cover guards of machine `j`'s check.  Same protection as
    `eventLoads`: every `getD` is bounded by the length conjuncts of
    `cumulativesShape`. -/
private def eventCovers (start duration machine : List Int) (j : Nat) :
    Bool × Bool :=
  let coverAt (t : Int) : Bool :=
    (List.range start.length).any (fun i =>
      -- `i < start.length ≤ duration/machine.length` (cumulativesShape).
      taskAt (start.getD i 0) (duration.getD i 0) (machine.getD i 0) t
        -- `j < start.length ≤ machine.length` (cumulativesShape).
        (machine.getD j 0))
  -- `j < start.length ≤ start/duration.length` (cumulativesShape).
  (coverAt (start.getD j 0), coverAt (start.getD j 0 + duration.getD j 0))

/-- `bound[machine[j]]` (1-based), read at
    `fzn_cumulatives_decomp.mzn` lines 44–47.  `cumulativesShape` gives
    `1 ≤ machine[j] ≤ bound.length` (and `j < start.length ≤
    machine.length` for the inner read), so the index `machine[j] - 1`
    is in `0..bound.length-1` and the default is never used. -/
private def boundAt (machine bound : List Int) (j : Nat) : Int :=
  bound.getD ((machine.getD j 0) - 1).toNat 0

/-- The four upstream implications of `fzn_cumulatives_decomp.mzn` lines
    44–47 at the event points, without the shape gate (which is the
    separate conjunct `cumulativesShape`).  `j` ranges over
    `Tasks = index_set(start)`. -/
private def cumulativesCoreProp (start duration resource machine bound :
    List Int) (isUpper : Bool) : Prop :=
  (List.range start.length).all (fun j =>
    (isUpper = true ∧ (eventCovers start duration machine j).1 = true →
      (eventLoads start duration resource machine j).1 ≤ boundAt machine bound j) ∧
    (isUpper = true ∧ (eventCovers start duration machine j).2 = true →
      (eventLoads start duration resource machine j).2 ≤ boundAt machine bound j) ∧
    (isUpper = false ∧ (eventCovers start duration machine j).1 = true →
      boundAt machine bound j ≤ (eventLoads start duration resource machine j).1) ∧
    (isUpper = false ∧ (eventCovers start duration machine j).2 = true →
      boundAt machine bound j ≤ (eventLoads start duration resource machine j).2)) = true

/-- Boolean twin of `cumulativesCoreProp`. -/
private def cumulativesCoreB (start duration resource machine bound : List Int)
    (isUpper : Bool) : Bool :=
  (List.range start.length).all (fun j =>
    (!(isUpper && (eventCovers start duration machine j).1) ||
        decide ((eventLoads start duration resource machine j).1 ≤
          boundAt machine bound j)) &&
    (!(isUpper && (eventCovers start duration machine j).2) ||
        decide ((eventLoads start duration resource machine j).2 ≤
          boundAt machine bound j)) &&
    (!(!isUpper && (eventCovers start duration machine j).1) ||
        decide (boundAt machine bound j ≤
          (eventLoads start duration resource machine j).1)) &&
    (!(!isUpper && (eventCovers start duration machine j).2) ||
        decide (boundAt machine bound j ≤
          (eventLoads start duration resource machine j).2)))

/-- `fzn_cumulatives`: event-point resource check (G26), shape-gated. -/
def cumulativesProp (start duration resource machine bound : List Int)
    (isUpper : Bool) : Prop :=
  cumulativesShape start duration resource machine bound ∧
    cumulativesCoreProp start duration resource machine bound isUpper

/-- Boolean twin of `cumulativesProp`. -/
def cumulativesB (start duration resource machine bound : List Int)
    (isUpper : Bool) : Bool :=
  cumulativesShapeB start duration resource machine bound &&
    cumulativesCoreB start duration resource machine bound isUpper

private theorem cumulativesCoreB_iff
    (start duration resource machine bound : List Int) (isUpper : Bool) :
    cumulativesCoreB start duration resource machine bound isUpper = true ↔
      cumulativesCoreProp start duration resource machine bound isUpper := by
  cases isUpper with
  | false =>
    simp only [cumulativesCoreB, cumulativesCoreProp, Bool.and_eq_true,
      List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_iff, Bool.and_eq_true, Bool.true_and, Bool.false_and,
      Bool.not_false]
    constructor
    · intro h x hx
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h x hx
      refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
      · rintro ⟨hf, _⟩; exact Bool.noConfusion hf
      · rintro ⟨hf, _⟩; exact Bool.noConfusion hf
      · rintro ⟨_, hc⟩
        rcases h3 with hfalse | hle
        · exact absurd hc (by rw [hfalse]; simp)
        · exact hle
      · rintro ⟨_, hc⟩
        rcases h4 with hfalse | hle
        · exact absurd hc (by rw [hfalse]; simp)
        · exact hle
    · intro h x hx
      obtain ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩ := h x hx
      refine ⟨⟨⟨Or.inl (by simp), Or.inl (by simp)⟩, ?_⟩, ?_⟩
      · by_cases hc : (eventCovers start duration machine x).1 = true
        · exact Or.inr (h3 ⟨trivial, hc⟩)
        · exact Or.inl (by simpa using hc)
      · by_cases hc : (eventCovers start duration machine x).2 = true
        · exact Or.inr (h4 ⟨trivial, hc⟩)
        · exact Or.inl (by simpa using hc)
  | true =>
    simp only [cumulativesCoreB, cumulativesCoreProp, Bool.and_eq_true,
      List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_true_iff, Bool.and_eq_true, Bool.true_and, Bool.not_true]
    constructor
    · intro h x hx
      obtain ⟨⟨h1, h2⟩, h3⟩ := h x hx
      refine ⟨?_, ⟨?_, ⟨?_, ?_⟩⟩⟩
      · rintro ⟨_, hc⟩
        rcases h1.1 with hfalse | hle
        · exact absurd hc (by rw [hfalse]; simp)
        · exact hle
      · rintro ⟨_, hc⟩
        rcases h1.2 with hfalse | hle
        · exact absurd hc (by rw [hfalse]; simp)
        · exact hle
      · rintro ⟨hf, _⟩; exact Bool.noConfusion hf
      · rintro ⟨hf, _⟩; exact Bool.noConfusion hf
    · intro h x hx
      obtain ⟨h1, ⟨h2, ⟨h3, h4⟩⟩⟩ := h x hx
      refine ⟨⟨⟨?_, ?_⟩, Or.inl (by simp)⟩, Or.inl (by simp)⟩
      · by_cases hc : (eventCovers start duration machine x).1 = true
        · exact Or.inr (h1 ⟨trivial, hc⟩)
        · exact Or.inl (by simpa using hc)
      · by_cases hc : (eventCovers start duration machine x).2 = true
        · exact Or.inr (h2 ⟨trivial, hc⟩)
        · exact Or.inl (by simpa using hc)

theorem cumulativesB_iff (start duration resource machine bound : List Int)
    (isUpper : Bool) :
    cumulativesB start duration resource machine bound isUpper = true ↔
      cumulativesProp start duration resource machine bound isUpper := by
  simp only [cumulativesB, cumulativesProp, Bool.and_eq_true,
    cumulativesShapeB_iff, cumulativesCoreB_iff]

/-! ## geost -/

/-- The rectangle indices of shape `s` (empty when out of range). -/
private def rectsOf (shape : List IntSetValue) (s : Int) : List Int :=
  setElems (shape.getD (s - 1).toNat (.enumeration []))

/-- Row-major entry of a flat k-column matrix. -/
private def matAt (flat : List Int) (k : Int) (row col : Int) : Int :=
  flat.getD (((row - 1) * k + (col - 1)).toNat) 0

/-- Are boxes `(x1, w1)` and `(x2, w2)` (per-axis position and size
    lists) separated on at least one axis (open overlap: touching
    allowed)? -/
private def boxesSeparated (x1 w1 x2 w2 : List Int) : Bool :=
  (List.range x1.length).any (fun j =>
    decide (x1.getD j 0 + w1.getD j 0 ≤ x2.getD j 0 ∨
      x2.getD j 0 + w2.getD j 0 ≤ x1.getD j 0))

/-- The per-axis origin of object `o`'s rectangle `r` in dimension
    `j` (0-based axis list). -/
private def objCoord (rectOffset : List Int) (k : Int) (xs : List Int)
    (o : Nat) (r : Int) (j : Nat) : Int :=
  xs.getD (o * k.toNat + j) 0 + matAt rectOffset k r (Int.ofNat j + 1)

/-- The per-axis size of rectangle `r` in dimension `j`. -/
private def rectDim (rectSize : List Int) (k : Int) (r : Int) (j : Nat) :
    Int :=
  matAt rectSize k r (Int.ofNat j + 1)

/-- The per-axis lists of a rectangle. -/
private def axisList (f : Nat → Int) (k : Int) : List Int :=
  (List.range k.toNat).map f

/-- Structural admissibility of the flat `geost` ABI (SC-03), derived
    from the upstream index sets:

    * `k ≥ 0` (`DIMS = 1..k`);
    * `length(xs) ≥ length(kind) * k`: every object row `xs[o,j]`
      (`o ∈ index_set(kind)`, `j ∈ 1..k`) exists; extra trailing
      entries are never read and are accepted;
    * `kind[o] ∈ 1..length(shape)` for every object (`shape[s]` with
      `s ∈ dom(kind[o])` must exist);
    * every rectangle id `r` occurring in any `shape[s]`
      (`1 ≤ s ≤ length(shape)`) satisfies `r ≥ 1` and `r*k` does not
      exceed `length(rect_size)`/`length(rect_offset)`: the row `r` of
      each matrix must have all `k` entries.

    The last condition is deliberately stronger than upstream, which
    only reads `shape[kind[o]]` for the fixed kinds: a malformed
    rectangle id in an unused shape set is rejected (a documented
    over-rejection, so the geost rows are `restricted`). -/
def geostGates (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) : Bool :=
  decide (0 ≤ k) &&
    decide (kind.length * k.toNat ≤ xs.length) &&
    (List.range kind.length).all (fun o =>
      decide (1 ≤ kind.getD o 0 ∧ kind.getD o 0 ≤ (shape.length : Int))) &&
    (List.range shape.length).all (fun s =>
      (rectsOf shape (Int.ofNat s + 1)).all (fun r =>
        decide (1 ≤ r ∧ r.toNat * k.toNat ≤ rectSize.length ∧
          r.toNat * k.toNat ≤ rectOffset.length)))

/-- Bounding-box admissibility of the flat `geost_bb` ABI:
    `lower_bound[j]`/`upper_bound[j]` are read for `j ∈ 1..k`, so both
    arrays need at least `k` entries.  Extra entries are unread. -/
def geostBbGates (k : Int) (lower upper : List Int) : Bool :=
  decide (0 ≤ k ∧ k.toNat ≤ lower.length ∧ k.toNat ≤ upper.length)

/-- The pairwise non-overlap core: for every ordered pair of objects
    `o1 < o2` and every rectangle pair of their (in-range) kinds.
    Admissibility is checked separately by `geostGates`. -/
private def geostCore (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) : Bool :=
  (List.range kind.length).all (fun o2 =>
    (List.range kind.length).all (fun o1 =>
      !(decide (o1 < o2)) ||
        ((rectsOf shape (kind.getD o1 0)).all (fun r1 =>
          (rectsOf shape (kind.getD o2 0)).all (fun r2 =>
            boxesSeparated
              (axisList (fun j => objCoord rectOffset k xs o1 r1 j) k)
              (axisList (fun j => rectDim rectSize k r1 j) k)
              (axisList (fun j => objCoord rectOffset k xs o2 r2 j) k)
              (axisList (fun j => rectDim rectSize k r2 j) k))))))

/-- `fzn_geost`: admissible flat `k`-column matrices, and for every pair
    of objects every pair of their shape rectangles is separated. -/
def geostProp (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) : Prop :=
  geostGates k rectSize rectOffset shape xs kind = true ∧
    geostCore k rectSize rectOffset shape xs kind = true

def geostB (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) : Bool :=
  geostGates k rectSize rectOffset shape xs kind &&
    geostCore k rectSize rectOffset shape xs kind

theorem geostB_iff (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) :
    geostB k rectSize rectOffset shape xs kind = true ↔
      geostProp k rectSize rectOffset shape xs kind := by
  simp only [geostB, geostProp, Bool.and_eq_true]

/-- `fzn_geost_bb`: admissible `geost` plus per-dimension bounds over
    every possibly-used shape's rectangles; `lower_bound`/`upper_bound`
    must have `k` entries. -/
def geostBbProp (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int)
    (lower upper : List Int) : Prop :=
  geostProp k rectSize rectOffset shape xs kind ∧
    geostBbGates k lower upper = true ∧
    (List.range kind.length).all (fun o =>
      (rectsOf shape (kind.getD o 0)).all (fun r =>
        (List.range k.toNat).all (fun j =>
          decide (lower.getD j 0 ≤ objCoord rectOffset k xs o r j ∧
            objCoord rectOffset k xs o r j + rectDim rectSize k r j ≤
              upper.getD j 0)))) = true

def geostBbB (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int)
    (lower upper : List Int) : Bool :=
  geostB k rectSize rectOffset shape xs kind &&
    geostBbGates k lower upper &&
    (List.range kind.length).all (fun o =>
      (rectsOf shape (kind.getD o 0)).all (fun r =>
        (List.range k.toNat).all (fun j =>
          decide (lower.getD j 0 ≤ objCoord rectOffset k xs o r j ∧
            objCoord rectOffset k xs o r j + rectDim rectSize k r j ≤
              upper.getD j 0))))

theorem geostBbB_iff (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int)
    (lower upper : List Int) :
    geostBbB k rectSize rectOffset shape xs kind lower upper = true ↔
      geostBbProp k rectSize rectOffset shape xs kind lower upper := by
  simp only [geostBbB, geostBbProp, Bool.and_eq_true, List.all_eq_true,
    geostB_iff, decide_eq_true_iff, and_assoc]

/-- `fzn_geost_smallest_bb`: `geost_bb` plus every boundary
    touched. -/
def geostSmallestBbProp (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int)
    (lower upper : List Int) : Prop :=
  geostBbProp k rectSize rectOffset shape xs kind lower upper ∧
    (List.range k.toNat).all (fun j =>
      ((List.range kind.length).any (fun o =>
        (rectsOf shape (kind.getD o 0)).any (fun r =>
          decide (objCoord rectOffset k xs o r j = lower.getD j 0)))) &&
      ((List.range kind.length).any (fun o =>
        (rectsOf shape (kind.getD o 0)).any (fun r =>
          decide (objCoord rectOffset k xs o r j + rectDim rectSize k r j
            = upper.getD j 0)))))

def geostSmallestBbB (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int)
    (lower upper : List Int) : Bool :=
  geostBbB k rectSize rectOffset shape xs kind lower upper &&
    (List.range k.toNat).all (fun j =>
      ((List.range kind.length).any (fun o =>
        (rectsOf shape (kind.getD o 0)).any (fun r =>
          decide (objCoord rectOffset k xs o r j = lower.getD j 0)))) &&
      ((List.range kind.length).any (fun o =>
        (rectsOf shape (kind.getD o 0)).any (fun r =>
          decide (objCoord rectOffset k xs o r j + rectDim rectSize k r j
            = upper.getD j 0)))))

theorem geostSmallestBbB_iff (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int)
    (lower upper : List Int) :
    geostSmallestBbB k rectSize rectOffset shape xs kind lower upper = true ↔
      geostSmallestBbProp k rectSize rectOffset shape xs kind lower upper := by
  simp only [geostSmallestBbB, geostSmallestBbProp, Bool.and_eq_true,
    List.all_eq_true, geostBbB_iff]

/-! ## diffn_k family -/

/-- The raw `fzn_diffn_nonoverlap_k.mzn` body at one axis `j`, with the
    same three-valued access rule as `geostNonoverlapKBodyProp` and
    `diffnPairProp`.  `x1[j]` exists because `j < x1.length`; the first
    disjunct also reads `w1[j]` and `x2[j]`, the second `x2[j]` and
    `w2[j]`. -/
private def diffnNonoverlapKBodyProp (x1 w1 x2 w2 : List Int) (j : Nat) : Prop :=
  (j < w1.length ∧ j < x2.length ∧
    x1.getD j 0 + w1.getD j 0 ≤ x2.getD j 0) ∨
  (j < x2.length ∧ j < w2.length ∧
    x2.getD j 0 + w2.getD j 0 ≤ x1.getD j 0)

/-- Boolean twin of `diffnNonoverlapKBodyProp`. -/
private def diffnNonoverlapKBodyB (x1 w1 x2 w2 : List Int) (j : Nat) : Bool :=
  (decide (j < w1.length) && decide (j < x2.length) &&
    decide (x1.getD j 0 + w1.getD j 0 ≤ x2.getD j 0)) ||
  (decide (j < x2.length) && decide (j < w2.length) &&
    decide (x2.getD j 0 + w2.getD j 0 ≤ x1.getD j 0))

private theorem diffnNonoverlapKBodyB_iff (x1 w1 x2 w2 : List Int) (j : Nat) :
    diffnNonoverlapKBodyB x1 w1 x2 w2 j = true ↔
      diffnNonoverlapKBodyProp x1 w1 x2 w2 j := by
  simp only [diffnNonoverlapKBodyB, diffnNonoverlapKBodyProp, Bool.or_eq_true,
    Bool.and_eq_true, decide_eq_true_iff, and_assoc]

/-- `fzn_diffn_nonoverlap_k(x1, w1, x2, w2)`: transcribed from
    `fzn_diffn_k.mzn` line 21.  The `exists` runs over `index_set(x1)`;
    an early `j` whose disjunction is true makes the existential true
    without reading the later `w1`/`x2`/`w2` entries.  There is therefore
    no unconditional length gate, and longer trailing arrays are unused.

    The two `k`-dimensional boxes with origins `x1`, `x2` and sizes `w1`,
    `w2` are separated on some axis. -/
def diffnNonoverlapKProp (x1 w1 x2 w2 : List Int) : Prop :=
  ∃ j : Nat, j < x1.length ∧ diffnNonoverlapKBodyProp x1 w1 x2 w2 j

/-- Boolean twin of `diffnNonoverlapKProp`. -/
def diffnNonoverlapKB (x1 w1 x2 w2 : List Int) : Bool :=
  (List.range x1.length).any (fun j => diffnNonoverlapKBodyB x1 w1 x2 w2 j)

private theorem diffnNonoverlapKB_iff (x1 w1 x2 w2 : List Int) :
    diffnNonoverlapKB x1 w1 x2 w2 = true ↔
      diffnNonoverlapKProp x1 w1 x2 w2 := by
  unfold diffnNonoverlapKB diffnNonoverlapKProp
  simp only [List.any_eq_true, List.mem_range]
  constructor
  · rintro ⟨j, hj, hd⟩
    exact ⟨j, hj, (diffnNonoverlapKBodyB_iff x1 w1 x2 w2 j).mp hd⟩
  · rintro ⟨j, hj, hd⟩
    exact ⟨j, hj, (diffnNonoverlapKBodyB_iff x1 w1 x2 w2 j).mpr hd⟩

/-- `fzn_diffn_k(boxPosn, boxSize)`: nested-array matrices (rows =
    boxes); pairwise non-overlap.

    **Not FlatZinc ABI (SC-03).** Upstream declares both arguments as
    `array [int, int] of var int` and takes the dimension count from
    `index_set_2of2(box_posn)` (`fzn_diffn_k.mzn` line 7); no FlatZinc
    argument carries that width. A flat FlatZinc call is therefore
    rejected by `twoMatrices` (`none` → `false`). This nested
    interpretation is a project-internal extension only. -/
def diffnKProp (boxPosn boxSize : List (List Int)) : Prop :=
  (List.range boxPosn.length).all (fun b2 =>
    (List.range boxPosn.length).all (fun b1 =>
      (decide (b1 < b2) = false ∨
        boxesSeparated (boxPosn.getD b1 []) (boxSize.getD b1 [])
          (boxPosn.getD b2 []) (boxSize.getD b2 []) = true))) = true

def diffnKB (boxPosn boxSize : List (List Int)) : Bool :=
  (List.range boxPosn.length).all (fun b2 =>
    (List.range boxPosn.length).all (fun b1 =>
      !(decide (b1 < b2)) ||
        boxesSeparated (boxPosn.getD b1 []) (boxSize.getD b1 [])
          (boxPosn.getD b2 []) (boxSize.getD b2 [])))

theorem diffnKB_iff (boxPosn boxSize : List (List Int)) :
    diffnKB boxPosn boxSize = true ↔
      diffnKProp boxPosn boxSize := by
  simp only [diffnKB, diffnKProp, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', decide_eq_true_iff]

/-- `fzn_diffn_nonstrict_k`: as `diffn_k` but zero-size boxes are
    free.  Also **not FlatZinc ABI** (same missing dimension count
    `index_set_2of2(box_posn)`; nested extension only). -/
def diffnNonstrictKProp (boxPosn boxSize : List (List Int)) : Prop :=
  (List.range boxPosn.length).all (fun b2 =>
    (List.range boxPosn.length).all (fun b1 =>
      (decide (b1 < b2) = false ∨
        (((boxSize.getD b1 []).any (fun w => decide (w = 0)) = true ∨
          (boxSize.getD b2 []).any (fun w => decide (w = 0)) = true) ∨
          boxesSeparated (boxPosn.getD b1 []) (boxSize.getD b1 [])
            (boxPosn.getD b2 []) (boxSize.getD b2 []) = true)))) = true

def diffnNonstrictKB (boxPosn boxSize : List (List Int)) : Bool :=
  (List.range boxPosn.length).all (fun b2 =>
    (List.range boxPosn.length).all (fun b1 =>
      !(decide (b1 < b2)) ||
        ((boxSize.getD b1 []).any (fun w => decide (w = 0)) ||
          (boxSize.getD b2 []).any (fun w => decide (w = 0)) ||
          boxesSeparated (boxPosn.getD b1 []) (boxSize.getD b1 [])
            (boxPosn.getD b2 []) (boxSize.getD b2 []))))

theorem diffnNonstrictKB_iff (boxPosn boxSize : List (List Int)) :
    diffnNonstrictKB boxPosn boxSize = true ↔
      diffnNonstrictKProp boxPosn boxSize := by
  simp only [diffnNonstrictKB, diffnNonstrictKProp, List.all_eq_true,
    Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_iff]

/-! ## writes_seq -/

/-- Shape gate of `fzn_writes_seq`, read off `fzn_writes_seq.mzn` lines
    9–14:

    * when `I` is empty the outer `forall` is vacuous and its `let`
      body is never evaluated, so neither `O` nor `P` is read;
    * otherwise the outer `forall (i in index_set(I))` reads `O[i]`
      (line 14), so `I.length ≤ O.length`;
    * `Vi`/`Pi` are built over `index_set(V)` (lines 11–13) and read
      `V[j]`/`P[j]` there.  Every `V[j]` exists by construction.  A
      missing `P[j]` makes the Boolean comparison `P[j] == i` undefined,
      which MiniZinc's Boolean-context rule turns into `false`: no write
      matches, exactly as `writeAt`'s `getD j 0` default.  Hence
      `V.length ≤ P.length` is *not* required.

    Trailing `O` and `P` entries are never read and are accepted.  A `P`
    value outside the `I` range is also accepted: the comparison
    `P[j] == i` is then false for every `i`, so no write happens. -/
def writesSeqShapeB (i p v o : List Int) : Bool :=
  decide (i.length ≤ o.length)

/-- Prop twin of `writesSeqShapeB`.  (When `i = []` this is automatic, because
    no outer iteration runs and the `let` body is never evaluated.) -/
abbrev writesSeqShape (i p v o : List Int) : Prop :=
  i.length ≤ o.length

theorem writesSeqShapeB_iff (i p v o : List Int) :
    writesSeqShapeB i p v o = true ↔ writesSeqShape i p v o := by
  simp only [writesSeqShapeB, writesSeqShape, decide_eq_true_iff]

/-- The value written to the 0-based position `idx`: the **last**
    `j ∈ 0..V.length-1` with `P[j] = idx + 1`, else `I[idx]`.

    Upstream `fzn_writes_seq.mzn` lines 11–14 set
    `Vi = reverse(V) ++ [I[i]]` and
    `Pi = reverse([P[j] == i | j in index_set(V)]) ++ [true]`, then take
    `Vi[arg_max(Pi)]`.  `specification/minizinc-2.10.1/
    lib-globals-math.html` §arg_max: "When breaking ties the least index
    is returned", so the least `Pi` index is the **largest** `j` in
    `index_set(V)`, i.e. the last write; when no `P[j] == i`, the final
    `true` at index `V.length + 1` selects `I[i]`.  The `filter |> reverse
    |> head?` below returns exactly that largest `j`, and `List.range
    v.length` scans only positions that upstream's `Pi` covers.  Every
    `V[j]` read has `j < v.length`; a missing `P[j]` yields the default
    `0`, which never equals the 1-based position `idx + 1` and therefore
    models the undefined-comparison-becomes-false rule.  When `i = []`
    the scan is empty and `writeAt` is never called. -/
private def writeAt (i p v : List Int) (idx : Nat) : Int :=
  match ((List.range v.length).filter (fun j =>
    p.getD j 0 = (idx : Int) + 1)).reverse.head? with
  | some j => v.getD j 0
  | none => i.getD idx 0

/-- `fzn_writes_seq(I, P, V, O)` (G31): for each position, the last write
    wins; absent writes keep `I`.  Shape-gated by `writesSeqShape`; the
    empty-`I` case is vacuous. -/
def writesSeqProp (i p v o : List Int) : Prop :=
  writesSeqShape i p v o ∧
    (List.range i.length).all (fun idx =>
      decide (o.getD idx 0 = writeAt i p v idx)) = true

def writesSeqB (i p v o : List Int) : Bool :=
  writesSeqShapeB i p v o &&
    (List.range i.length).all (fun idx =>
      decide (o.getD idx 0 = writeAt i p v idx))

theorem writesSeqB_iff (i p v o : List Int) :
    writesSeqB i p v o = true ↔ writesSeqProp i p v o := by
  simp only [writesSeqB, writesSeqProp, Bool.and_eq_true,
    writesSeqShapeB_iff, List.all_eq_true]

/-! ## if_then_else_partiality -/

/-- The first index `i` (0-based scan) with `c[i]` true, as a
    function. -/
private def firstTrue (c : List Bool) : Option Nat :=
  match (List.range c.length).find? (fun i => c.getD i false) with
  | some i => some i
  | none => none

/-- `fzn_if_then_else_partiality(c, def, b)` (G32): with no true
    condition, `b` is unrestricted; otherwise `b = def[first true i]`.

    The `def` reads in `fzn_if_then_else_partiality.mzn` lines 8–12 are
    masked by the condition scan: entries before the first true index are
    never read, and a missing entry at the selected index behaves as the
    Boolean-false default.  There is therefore no length gate. -/
def itePartialityProp (c d : List Bool) (b : Bool) : Prop :=
  match firstTrue c with
  | none => True
  | some i => b = d.getD i false

def itePartialityB (c d : List Bool) (b : Bool) : Bool :=
  match firstTrue c with
  | none => true
  | some i => b == d.getD i false

theorem itePartialityB_iff (c d : List Bool) (b : Bool) :
    itePartialityB c d b = true ↔ itePartialityProp c d b := by
  simp only [itePartialityB, itePartialityProp]
  cases firstTrue c with
  | none => simp
  | some i => simp

/-! ## Argument decoders -/

/-- Decode five int arrays. -/
private def fiveIntArrays (args : List Value) :
    Option (List Int × List Int × List Int × List Int × List Int) :=
  match args with
  | [Value.array a1, Value.array a2, Value.array a3, Value.array a4,
     Value.array a5] =>
      match valueInts a1, valueInts a2, valueInts a3, valueInts a4,
        valueInts a5 with
      | some l1, some l2, some l3, some l4, some l5 =>
          some (l1, l2, l3, l4, l5)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode (five int arrays, bool). -/
private def fiveIntArraysAndBool (args : List Value) :
    Option (List Int × List Int × List Int × List Int × List Int × Bool) :=
  match args with
  | [Value.array a1, Value.array a2, Value.array a3, Value.array a4,
     Value.array a5, Value.bool up] =>
      match valueInts a1, valueInts a2, valueInts a3, valueInts a4,
        valueInts a5 with
      | some l1, some l2, some l3, some l4, some l5 =>
          some (l1, l2, l3, l4, l5, up)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode (five int arrays, bool, int). -/
private def cumulativesArgs (args : List Value) :
    Option (List Int × List Int × List Int × List Int × List Int ×
      Bool × Int) :=
  match args with
  | [Value.array a1, Value.array a2, Value.array a3, Value.array a4,
     Value.array a5, Value.bool up, Value.int mm] =>
      match valueInts a1, valueInts a2, valueInts a3, valueInts a4,
        valueInts a5 with
      | some l1, some l2, some l3, some l4, some l5 =>
          some (l1, l2, l3, l4.map (fun m => m - mm + 1), l5, up, mm)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode (int, array, array, array-of-sets, array, array) — the
    geost shape. -/
private def geostArgs (args : List Value) :
    Option (Int × List Int × List Int × List IntSetValue × List Int ×
      List Int) :=
  match args with
  | [Value.int k, Value.array rsArr, Value.array roArr,
     Value.array shArr, Value.array xsArr, Value.array kdArr] =>
      match valueInts rsArr, valueInts roArr,
        (shArr.mapM (fun v => match v with
          | Value.setOfInt sv => some sv
          | _ => none)), valueInts xsArr, valueInts kdArr with
      | some rs, some ro, some sh, some xsL, some kd =>
          some (k, rs, ro, sh, xsL, kd)
      | _, _, _, _, _ => none
  | _ => none

/-- Decode (int, array, array, array-of-sets, array, array, array,
    array) — the geost_bb shape. -/
private def geostBbArgs (args : List Value) :
    Option (Int × List Int × List Int × List IntSetValue × List Int ×
      List Int × List Int × List Int) :=
  match args with
  | [Value.int k, Value.array rsArr, Value.array roArr,
     Value.array shArr, Value.array xsArr, Value.array kdArr,
     Value.array loArr, Value.array upArr] =>
      match valueInts rsArr, valueInts roArr,
        (shArr.mapM (fun v => match v with
          | Value.setOfInt sv => some sv
          | _ => none)), valueInts xsArr, valueInts kdArr,
        valueInts loArr, valueInts upArr with
      | some rs, some ro, some sh, some xsL, some kd, some lo, some up =>
          some (k, rs, ro, sh, xsL, kd, lo, up)
      | _, _, _, _, _, _, _ => none
  | _ => none

/-- Decode four int arrays (diffn_nonoverlap_k). -/
private def fourIntArrays (args : List Value) :
    Option (List Int × List Int × List Int × List Int) :=
  match args with
  | [Value.array a1, Value.array a2, Value.array a3, Value.array a4] =>
      match valueInts a1, valueInts a2, valueInts a3, valueInts a4 with
      | some l1, some l2, some l3, some l4 => some (l1, l2, l3, l4)
      | _, _, _, _ => none
  | _ => none

/-- Decode two nested int-array matrices (diffn_k).  **Not FlatZinc
    ABI**: a real `.fzn` call passes 1-D arrays, for which this returns
    `none`.  The nested value representation is a project-internal
    extension only. -/
private def twoMatrices (args : List Value) :
    Option (List (List Int) × List (List Int)) :=
  match args with
  | [Value.array a1, Value.array a2] =>
      match a1, a2 with
      | [], _ => none
      | _, [] => none
      | _, _ =>
        match (a1.mapM (fun v => match v with
            | Value.array r => valueInts r
            | _ => none)),
          (a2.mapM (fun v => match v with
            | Value.array r => valueInts r
            | _ => none)) with
        | some m1, some m2 => some (m1, m2)
        | _, _ => none
  | _ => none

/-- Decode four bool arrays (if_then_else_partiality) plus a
    bool. -/
private def twoBoolArraysAndBool (args : List Value) :
    Option (List Bool × List Bool × Bool) :=
  match args with
  | [Value.array cArr, Value.array defArr, Value.bool b] =>
      match valueBools cArr, valueBools defArr with
      | some c, some d => some (c, d, b)
      | _, _ => none
  | _ => none

/-! ## The interpretations -/

/-- Mathematical interpretations; wrong shapes yield `False`. -/
def sched2Interp : LeanFzn.Semantics.PredicateInterpretation := fun x =>
  match x.name with
  | "fzn_cumulatives" => fun args =>
    match cumulativesArgs args with
    | some (s, d, r, mch, bnd, up, _) =>
        cumulativesProp s d r mch bnd up
    | none => False
  | "fzn_cumulatives_decomp" => fun args =>
    match fiveIntArraysAndBool args with
    | some (s, d, r, mch, bnd, up) =>
        cumulativesProp s d r mch bnd up
    | none => False
  | "fzn_geost" => fun args =>
    match geostArgs args with
    | some (k, rs, ro, sh, xsL, kd) => geostProp k rs ro sh xsL kd
    | none => False
  | "fzn_geost_bb" => fun args =>
    match geostBbArgs args with
    | some (k, rs, ro, sh, xsL, kd, lo, up) =>
        geostBbProp k rs ro sh xsL kd lo up
    | none => False
  | "fzn_geost_smallest_bb" => fun args =>
    match geostBbArgs args with
    | some (k, rs, ro, sh, xsL, kd, lo, up) =>
        geostSmallestBbProp k rs ro sh xsL kd lo up
    | none => False
  | "fzn_diffn_nonoverlap_k" => fun args =>
    match fourIntArrays args with
    | some (x1, w1, x2, w2) => diffnNonoverlapKProp x1 w1 x2 w2
    | none => False
  | "fzn_diffn_k" => fun args =>
    match twoMatrices args with
    | some (bp, bs) => diffnKProp bp bs
    | none => False
  | "fzn_diffn_nonstrict_k" => fun args =>
    match twoMatrices args with
    | some (bp, bs) => diffnNonstrictKProp bp bs
    | none => False
  | "fzn_writes_seq" => fun args =>
    match fourIntArrays args with
    | some (iL, pL, vL, oL) => writesSeqProp iL pL vL oL
    | none => False
  | "fzn_if_then_else_partiality" => fun args =>
    match twoBoolArraysAndBool args with
    | some (c, d, b) => itePartialityProp c d b
    | none => False
  | _ => fun _ => False

/-- **Executable twin of `sched2Interp`.** -/
def sched2InterpB : LeanFzn.Ident → List Value → Bool := fun x =>
  match x.name with
  | "fzn_cumulatives" => fun args =>
    match cumulativesArgs args with
    | some (s, d, r, mch, bnd, up, _) =>
        cumulativesB s d r mch bnd up
    | none => false
  | "fzn_cumulatives_decomp" => fun args =>
    match fiveIntArraysAndBool args with
    | some (s, d, r, mch, bnd, up) =>
        cumulativesB s d r mch bnd up
    | none => false
  | "fzn_geost" => fun args =>
    match geostArgs args with
    | some (k, rs, ro, sh, xsL, kd) => geostB k rs ro sh xsL kd
    | none => false
  | "fzn_geost_bb" => fun args =>
    match geostBbArgs args with
    | some (k, rs, ro, sh, xsL, kd, lo, up) =>
        geostBbB k rs ro sh xsL kd lo up
    | none => false
  | "fzn_geost_smallest_bb" => fun args =>
    match geostBbArgs args with
    | some (k, rs, ro, sh, xsL, kd, lo, up) =>
        geostSmallestBbB k rs ro sh xsL kd lo up
    | none => false
  | "fzn_diffn_nonoverlap_k" => fun args =>
    match fourIntArrays args with
    | some (x1, w1, x2, w2) => diffnNonoverlapKB x1 w1 x2 w2
    | none => false
  | "fzn_diffn_k" => fun args =>
    match twoMatrices args with
    | some (bp, bs) => diffnKB bp bs
    | none => false
  | "fzn_diffn_nonstrict_k" => fun args =>
    match twoMatrices args with
    | some (bp, bs) => diffnNonstrictKB bp bs
    | none => false
  | "fzn_writes_seq" => fun args =>
    match fourIntArrays args with
    | some (iL, pL, vL, oL) => writesSeqB iL pL vL oL
    | none => false
  | "fzn_if_then_else_partiality" => fun args =>
    match twoBoolArraysAndBool args with
    | some (c, d, b) => itePartialityB c d b
    | none => false
  | _ => fun _ => false

/-! ## Per-name agreement theorems -/

theorem fzn_cumulatives_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_cumulatives") args = true ↔
      sched2Interp (Ident.mk "fzn_cumulatives") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_cumulatives") args
      = match cumulativesArgs args with
      | some (s, d, r, mch, bnd, up, _) =>
          cumulativesB s d r mch bnd up
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_cumulatives") args
      = match cumulativesArgs args with
      | some (s, d, r, mch, bnd, up, _) =>
          cumulativesProp s d r mch bnd up
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : cumulativesArgs args with
  | none => simp
  | some p =>
    obtain ⟨s, d, r, mch, bnd, up, _⟩ := p
    simp only
    exact cumulativesB_iff s d r mch bnd up

theorem fzn_cumulatives_decomp_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_cumulatives_decomp") args = true ↔
      sched2Interp (Ident.mk "fzn_cumulatives_decomp") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_cumulatives_decomp") args
      = match fiveIntArraysAndBool args with
      | some (s, d, r, mch, bnd, up) =>
          cumulativesB s d r mch bnd up
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_cumulatives_decomp") args
      = match fiveIntArraysAndBool args with
      | some (s, d, r, mch, bnd, up) =>
          cumulativesProp s d r mch bnd up
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : fiveIntArraysAndBool args with
  | none => simp
  | some p =>
    obtain ⟨s, d, r, mch, bnd, up⟩ := p
    simp only
    exact cumulativesB_iff s d r mch bnd up

theorem fzn_geost_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_geost") args = true ↔
      sched2Interp (Ident.mk "fzn_geost") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_geost") args
      = match geostArgs args with
      | some (k, rs, ro, sh, xsL, kd) => geostB k rs ro sh xsL kd
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_geost") args
      = match geostArgs args with
      | some (k, rs, ro, sh, xsL, kd) => geostProp k rs ro sh xsL kd
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : geostArgs args with
  | none => simp
  | some p =>
    obtain ⟨k, rs, ro, sh, xsL, kd⟩ := p
    simp only
    exact geostB_iff k rs ro sh xsL kd

theorem fzn_geost_bb_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_geost_bb") args = true ↔
      sched2Interp (Ident.mk "fzn_geost_bb") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_geost_bb") args
      = match geostBbArgs args with
      | some (k, rs, ro, sh, xsL, kd, lo, up) =>
          geostBbB k rs ro sh xsL kd lo up
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_geost_bb") args
      = match geostBbArgs args with
      | some (k, rs, ro, sh, xsL, kd, lo, up) =>
          geostBbProp k rs ro sh xsL kd lo up
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : geostBbArgs args with
  | none => simp
  | some p =>
    obtain ⟨k, rs, ro, sh, xsL, kd, lo, up⟩ := p
    simp only
    exact geostBbB_iff k rs ro sh xsL kd lo up

theorem fzn_geost_smallest_bb_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_geost_smallest_bb") args = true ↔
      sched2Interp (Ident.mk "fzn_geost_smallest_bb") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_geost_smallest_bb") args
      = match geostBbArgs args with
      | some (k, rs, ro, sh, xsL, kd, lo, up) =>
          geostSmallestBbB k rs ro sh xsL kd lo up
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_geost_smallest_bb") args
      = match geostBbArgs args with
      | some (k, rs, ro, sh, xsL, kd, lo, up) =>
          geostSmallestBbProp k rs ro sh xsL kd lo up
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : geostBbArgs args with
  | none => simp
  | some p =>
    obtain ⟨k, rs, ro, sh, xsL, kd, lo, up⟩ := p
    simp only
    exact geostSmallestBbB_iff k rs ro sh xsL kd lo up

theorem fzn_diffn_nonoverlap_k_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_diffn_nonoverlap_k") args = true ↔
      sched2Interp (Ident.mk "fzn_diffn_nonoverlap_k") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_diffn_nonoverlap_k") args
      = match fourIntArrays args with
      | some (x1, w1, x2, w2) => diffnNonoverlapKB x1 w1 x2 w2
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_diffn_nonoverlap_k") args
      = match fourIntArrays args with
      | some (x1, w1, x2, w2) => diffnNonoverlapKProp x1 w1 x2 w2
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : fourIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨x1, w1, x2, w2⟩ := p
    simp only
    exact diffnNonoverlapKB_iff x1 w1 x2 w2

theorem fzn_diffn_k_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_diffn_k") args = true ↔
      sched2Interp (Ident.mk "fzn_diffn_k") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_diffn_k") args
      = match twoMatrices args with
      | some (bp, bs) => diffnKB bp bs
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_diffn_k") args
      = match twoMatrices args with
      | some (bp, bs) => diffnKProp bp bs
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoMatrices args with
  | none => simp
  | some p =>
    obtain ⟨bp, bs⟩ := p
    simp only
    exact diffnKB_iff bp bs

theorem fzn_diffn_nonstrict_k_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_diffn_nonstrict_k") args = true ↔
      sched2Interp (Ident.mk "fzn_diffn_nonstrict_k") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_diffn_nonstrict_k") args
      = match twoMatrices args with
      | some (bp, bs) => diffnNonstrictKB bp bs
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_diffn_nonstrict_k") args
      = match twoMatrices args with
      | some (bp, bs) => diffnNonstrictKProp bp bs
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoMatrices args with
  | none => simp
  | some p =>
    obtain ⟨bp, bs⟩ := p
    simp only
    exact diffnNonstrictKB_iff bp bs

theorem fzn_writes_seq_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_writes_seq") args = true ↔
      sched2Interp (Ident.mk "fzn_writes_seq") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_writes_seq") args
      = match fourIntArrays args with
      | some (iL, pL, vL, oL) => writesSeqB iL pL vL oL
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_writes_seq") args
      = match fourIntArrays args with
      | some (iL, pL, vL, oL) => writesSeqProp iL pL vL oL
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : fourIntArrays args with
  | none => simp
  | some p =>
    obtain ⟨iL, pL, vL, oL⟩ := p
    simp only
    exact writesSeqB_iff iL pL vL oL

theorem fzn_if_then_else_partiality_iff (args : List Value) :
    sched2InterpB (Ident.mk "fzn_if_then_else_partiality") args = true ↔
      sched2Interp (Ident.mk "fzn_if_then_else_partiality") args := by
  have hB : ∀ args, sched2InterpB (Ident.mk "fzn_if_then_else_partiality") args
      = match twoBoolArraysAndBool args with
      | some (c, d, b) => itePartialityB c d b
      | none => false
      := fun _ => rfl
  have hI : ∀ args, sched2Interp (Ident.mk "fzn_if_then_else_partiality") args
      = match twoBoolArraysAndBool args with
      | some (c, d, b) => itePartialityProp c d b
      | none => False
      := fun _ => rfl
  rw [hB args, hI args]
  cases h : twoBoolArraysAndBool args with
  | none => simp
  | some p =>
    obtain ⟨c, d, b⟩ := p
    simp only
    exact itePartialityB_iff c d b

/-! ## Nested-matrix decoding helper -/

/-- Consing a decoded column onto a decoded matrix preserves `isSome`. -/
private theorem option_bind_cons_isSome {α : Type} (o : Option (List α))
    (a : α) :
    (o.bind (fun bs => some (a :: bs))).isSome = o.isSome := by
  cases o <;> rfl

/-- Pairing two decoded matrices preserves `isSome`. -/
private theorem option_pair_pair_isSome (o1 o2 : Option (List (List Int))) :
    (match o1, o2 with
      | some m1, some m2 => some (m1, m2)
      | _, _ => none).isSome = (o1.isSome && o2.isSome) := by
  cases o1 <;> cases o2 <;> rfl

/-- The set-column map used by the `geost` decoders is `valueSets`. -/
private theorem mapM_sets_eq_valueSets (xs : List Value) :
    xs.mapM (fun v => match v with
      | Value.setOfInt sv => some sv
      | _ => none) = valueSets xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | setOfInt s =>
      simp [valueSets, List.mapM_cons, ih]
      cases valueSets xs <;> rfl
    | bool b => simp [valueSets, List.mapM_cons, ih]
    | int i => simp [valueSets, List.mapM_cons, ih]
    | array a => simp [valueSets, List.mapM_cons, ih]

/-- The set-column map used by the `geost` decoders accepts exactly the same
    shapes. -/
private theorem valueSetsMapM_isSome_sameShape {xss yss : List Value}
    (h : Value.SameShapeList xss yss) :
    (xss.mapM (fun v => match v with
       | Value.setOfInt sv => some sv
       | _ => none)).isSome =
    (yss.mapM (fun v => match v with
       | Value.setOfInt sv => some sv
       | _ => none)).isSome := by
  rw [mapM_sets_eq_valueSets, mapM_sets_eq_valueSets]
  exact valueSets_isSome_sameShape h

/-- The column map of a matrix argument accepts exactly the same shapes. -/
private theorem valueIntMatrix_isSome_sameShape {xss yss : List Value}
    (h : Value.SameShapeList xss yss) :
    (xss.mapM (fun v => match v with
       | Value.array col => valueInts col
       | _ => none)).isSome =
    (yss.mapM (fun v => match v with
       | Value.array col => valueInts col
       | _ => none)).isSome := by
  induction h with
  | nil => rfl
  | cons hxy htail ih =>
    cases hxy with
    | bool _ _ => simp [List.mapM_cons]
    | int _ _ => simp [List.mapM_cons]
    | setOfInt _ _ => simp [List.mapM_cons]
    | @array axs ays harr =>
      have hx : (valueInts axs).isSome = (valueInts ays).isSome :=
        valueInts_isSome_sameShape harr
      cases h1 : valueInts axs with
      | none =>
        have h2 : valueInts ays = none := by
          have : (valueInts ays).isSome = false := by rw [← hx, h1]; rfl
          simpa using this
        simp [List.mapM_cons, h1, h2]
      | some a =>
        have h2 : (valueInts ays).isSome = true := by rw [← hx, h1]; rfl
        obtain ⟨a', ha'⟩ := Option.isSome_iff_exists.mp h2
        simp only [List.mapM_cons]
        rw [h1, ha']
        change (Option.bind (some a) (fun b =>
            Option.bind (List.mapM (fun v => match v with
              | Value.array col => valueInts col
              | _ => none) _) (fun bs => some (b :: bs)))).isSome =
          (Option.bind (some a') (fun b =>
            Option.bind (List.mapM (fun v => match v with
              | Value.array col => valueInts col
              | _ => none) _) (fun bs => some (b :: bs)))).isSome
        rw [Option.bind_some, Option.bind_some]
        rw [option_bind_cons_isSome, option_bind_cons_isSome]
        exact ih

/-- `fzn_cumulatives` decodes the same shapes. -/
theorem cumulativesArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (cumulativesArgs vs).isSome = (cumulativesArgs ws).isSome := by
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
                    | nil => rfl
                    | cons hv5 ht5 =>
                      cases hv5 with
                      | bool => rfl
                      | int => rfl
                      | setOfInt => rfl
                      | @array a5 b5 ha5 =>
                        cases ht5 with
                        | nil => rfl
                        | cons hv6 ht6 =>
                          cases hv6 with
                          | bool =>
                            cases ht6 with
                            | nil => rfl
                            | cons hv7 ht7 =>
                              cases hv7 with
                              | bool => rfl
                              | int =>
                                cases ht7 with
                                | cons _ _ => rfl
                                | nil =>
                                  simp only [cumulativesArgs]
                                  have hx1 := valueInts_isSome_sameShape ha1
                                  have hx2 := valueInts_isSome_sameShape ha2
                                  have hx3 := valueInts_isSome_sameShape ha3
                                  have hx4 := valueInts_isSome_sameShape ha4
                                  have hx5 := valueInts_isSome_sameShape ha5
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
                                                | some _ =>
                                                  cases h9 : valueInts a5 with
                                                  | none =>
                                                    cases h10 : valueInts b5 with
                                                    | none => rfl
                                                    | some _ => simp [h9, h10] at hx5
                                                  | some _ =>
                                                    cases h10 : valueInts b5 with
                                                    | none => simp [h9, h10] at hx5
                                                    | some _ => rfl
                              | setOfInt => rfl
                              | array => rfl
                          | int => rfl
                          | setOfInt => rfl
                          | array => rfl


/-- `fzn_cumulatives_decomp` decodes the same shapes. -/
theorem fiveIntArraysAndBool_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (fiveIntArraysAndBool vs).isSome = (fiveIntArraysAndBool ws).isSome := by
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
                    | nil => rfl
                    | cons hv5 ht5 =>
                      cases hv5 with
                      | bool => rfl
                      | int => rfl
                      | setOfInt => rfl
                      | @array a5 b5 ha5 =>
                        cases ht5 with
                        | nil => rfl
                        | cons hv6 ht6 =>
                          cases hv6 with
                          | bool =>
                            cases ht6 with
                            | cons _ _ => rfl
                            | nil =>
                              simp only [fiveIntArraysAndBool]
                              have hx1 := valueInts_isSome_sameShape ha1
                              have hx2 := valueInts_isSome_sameShape ha2
                              have hx3 := valueInts_isSome_sameShape ha3
                              have hx4 := valueInts_isSome_sameShape ha4
                              have hx5 := valueInts_isSome_sameShape ha5
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
                                            | some _ =>
                                              cases h9 : valueInts a5 with
                                              | none =>
                                                cases h10 : valueInts b5 with
                                                | none => rfl
                                                | some _ => simp [h9, h10] at hx5
                                              | some _ =>
                                                cases h10 : valueInts b5 with
                                                | none => simp [h9, h10] at hx5
                                                | some _ => rfl
                          | int => rfl
                          | setOfInt => rfl
                          | array => rfl


/-- `fzn_geost` decodes the same shapes. -/
theorem geostArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (geostArgs vs).isSome = (geostArgs ws).isSome := by
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
                | nil => rfl
                | cons hv4 ht4 =>
                  cases hv4 with
                  | bool => rfl
                  | int => rfl
                  | setOfInt => rfl
                  | @array a3 b3 ha3 =>
                    cases ht4 with
                    | nil => rfl
                    | cons hv5 ht5 =>
                      cases hv5 with
                      | bool => rfl
                      | int => rfl
                      | setOfInt => rfl
                      | @array a4 b4 ha4 =>
                        cases ht5 with
                        | nil => rfl
                        | cons hv6 ht6 =>
                          cases hv6 with
                          | bool => rfl
                          | int => rfl
                          | setOfInt => rfl
                          | @array a5 b5 ha5 =>
                            cases ht6 with
                            | cons _ _ => rfl
                            | nil =>
                              simp only [geostArgs]
                              have hx1 := valueInts_isSome_sameShape ha1
                              have hx2 := valueInts_isSome_sameShape ha2
                              have hx3 := valueSetsMapM_isSome_sameShape ha3
                              have hx4 := valueInts_isSome_sameShape ha4
                              have hx5 := valueInts_isSome_sameShape ha5
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
                                      cases h5 : (a3.mapM (fun v => match v with
    | Value.setOfInt sv => some sv
    | _ => none)) with
                                      | none =>
                                        cases h6 : (b3.mapM (fun v => match v with
    | Value.setOfInt sv => some sv
    | _ => none)) with
                                        | none => rfl
                                        | some _ => simp [h5, h6] at hx3
                                      | some _ =>
                                        cases h6 : (b3.mapM (fun v => match v with
    | Value.setOfInt sv => some sv
    | _ => none)) with
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
                                            | some _ =>
                                              cases h9 : valueInts a5 with
                                              | none =>
                                                cases h10 : valueInts b5 with
                                                | none => rfl
                                                | some _ => simp [h9, h10] at hx5
                                              | some _ =>
                                                cases h10 : valueInts b5 with
                                                | none => simp [h9, h10] at hx5
                                                | some _ => rfl
      | setOfInt => rfl
      | array => rfl


/-- `fzn_geost_bb`/`fzn_geost_smallest_bb` decode the same shapes. -/
theorem geostBbArgs_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (geostBbArgs vs).isSome = (geostBbArgs ws).isSome := by
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
                | nil => rfl
                | cons hv4 ht4 =>
                  cases hv4 with
                  | bool => rfl
                  | int => rfl
                  | setOfInt => rfl
                  | @array a3 b3 ha3 =>
                    cases ht4 with
                    | nil => rfl
                    | cons hv5 ht5 =>
                      cases hv5 with
                      | bool => rfl
                      | int => rfl
                      | setOfInt => rfl
                      | @array a4 b4 ha4 =>
                        cases ht5 with
                        | nil => rfl
                        | cons hv6 ht6 =>
                          cases hv6 with
                          | bool => rfl
                          | int => rfl
                          | setOfInt => rfl
                          | @array a5 b5 ha5 =>
                            cases ht6 with
                            | nil => rfl
                            | cons hv7 ht7 =>
                              cases hv7 with
                              | bool => rfl
                              | int => rfl
                              | setOfInt => rfl
                              | @array a6 b6 ha6 =>
                                cases ht7 with
                                | nil => rfl
                                | cons hv8 ht8 =>
                                  cases hv8 with
                                  | bool => rfl
                                  | int => rfl
                                  | setOfInt => rfl
                                  | @array a7 b7 ha7 =>
                                    cases ht8 with
                                    | cons _ _ => rfl
                                    | nil =>
                                      simp only [geostBbArgs]
                                      have hx1 := valueInts_isSome_sameShape ha1
                                      have hx2 := valueInts_isSome_sameShape ha2
                                      have hx3 := valueSetsMapM_isSome_sameShape ha3
                                      have hx4 := valueInts_isSome_sameShape ha4
                                      have hx5 := valueInts_isSome_sameShape ha5
                                      have hx6 := valueInts_isSome_sameShape ha6
                                      have hx7 := valueInts_isSome_sameShape ha7
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
                                              cases h5 : (a3.mapM (fun v => match v with
    | Value.setOfInt sv => some sv
    | _ => none)) with
                                              | none =>
                                                cases h6 : (b3.mapM (fun v => match v with
    | Value.setOfInt sv => some sv
    | _ => none)) with
                                                | none => rfl
                                                | some _ => simp [h5, h6] at hx3
                                              | some _ =>
                                                cases h6 : (b3.mapM (fun v => match v with
    | Value.setOfInt sv => some sv
    | _ => none)) with
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
                                                    | some _ =>
                                                      cases h9 : valueInts a5 with
                                                      | none =>
                                                        cases h10 : valueInts b5 with
                                                        | none => rfl
                                                        | some _ => simp [h9, h10] at hx5
                                                      | some _ =>
                                                        cases h10 : valueInts b5 with
                                                        | none => simp [h9, h10] at hx5
                                                        | some _ =>
                                                          cases h11 : valueInts a6 with
                                                          | none =>
                                                            cases h12 : valueInts b6 with
                                                            | none => rfl
                                                            | some _ => simp [h11, h12] at hx6
                                                          | some _ =>
                                                            cases h12 : valueInts b6 with
                                                            | none => simp [h11, h12] at hx6
                                                            | some _ =>
                                                              cases h13 : valueInts a7 with
                                                              | none =>
                                                                cases h14 : valueInts b7 with
                                                                | none => rfl
                                                                | some _ => simp [h13, h14] at hx7
                                                              | some _ =>
                                                                cases h14 : valueInts b7 with
                                                                | none => simp [h13, h14] at hx7
                                                                | some _ => rfl
      | setOfInt => rfl
      | array => rfl


/-- `fzn_diffn_nonoverlap_k`/`fzn_writes_seq` decode the same shapes. -/
theorem fourIntArrays_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (fourIntArrays vs).isSome = (fourIntArrays ws).isSome := by
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
                      simp only [fourIntArrays]
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


/-- `fzn_if_then_else_partiality` decodes the same shapes. -/
theorem twoBoolArraysAndBool_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (twoBoolArraysAndBool vs).isSome = (twoBoolArraysAndBool ws).isSome := by
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
                  simp only [twoBoolArraysAndBool]
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

/-- `twoMatrices` decodes the same shapes.  The decoder rejects empty inner
    arrays; shape agreement preserves their length, hence their emptiness. -/
theorem twoMatrices_isSome_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) :
    (twoMatrices vs).isSome = (twoMatrices ws).isSome := by
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
              simp only [twoMatrices]
              have hlen1 : a1.length = b1.length :=
                ListSameShape.length_eq ha1
              have hlen2 : a2.length = b2.length :=
                ListSameShape.length_eq ha2
              cases a1 with
              | nil =>
                have hb1 : b1 = [] :=
                  List.eq_nil_of_length_eq_zero (by simpa using hlen1.symm)
                subst hb1
                simp
              | cons c cs =>
                rcases b1 with _ | ⟨c', cs'⟩
                · simp at hlen1
                · cases a2 with
                  | nil =>
                    have hb2 : b2 = [] :=
                      List.eq_nil_of_length_eq_zero
                        (by simpa using hlen2.symm)
                    subst hb2
                    simp
                  | cons d ds =>
                    rcases b2 with _ | ⟨d', ds'⟩
                    · simp at hlen2
                    · have hm1 : ((c :: cs).mapM (fun v => match v with
                          | Value.array col => valueInts col
                          | _ => none)).isSome =
                          ((c' :: cs').mapM (fun v => match v with
                          | Value.array col => valueInts col
                          | _ => none)).isSome :=
                        valueIntMatrix_isSome_sameShape ha1
                      have hm2 : ((d :: ds).mapM (fun v => match v with
                          | Value.array col => valueInts col
                          | _ => none)).isSome =
                          ((d' :: ds').mapM (fun v => match v with
                          | Value.array col => valueInts col
                          | _ => none)).isSome :=
                        valueIntMatrix_isSome_sameShape ha2
                      cases h1 : ((c :: cs).mapM (fun v => match v with
                          | Value.array col => valueInts col
                          | _ => none)) with
                      | none =>
                        cases h2 : ((c' :: cs').mapM (fun v => match v with
                            | Value.array col => valueInts col
                            | _ => none)) with
                        | none => rfl
                        | some _ => simp [h1, h2] at hm1
                      | some _ =>
                        cases h2 : ((c' :: cs').mapM (fun v => match v with
                            | Value.array col => valueInts col
                            | _ => none)) with
                        | none => simp [h1, h2] at hm1
                        | some _ =>
                          cases h3 : ((d :: ds).mapM (fun v => match v with
                              | Value.array col => valueInts col
                              | _ => none)) with
                          | none =>
                            cases h4 : ((d' :: ds').mapM (fun v => match v with
                                | Value.array col => valueInts col
                                | _ => none)) with
                            | none => rfl
                            | some _ => simp [h3, h4] at hm2
                          | some _ =>
                            cases h4 : ((d' :: ds').mapM (fun v => match v with
                                | Value.array col => valueInts col
                                | _ => none)) with
                            | none => simp [h3, h4] at hm2
                            | some _ => rfl

/-! ## Decodability gate -/

/-- Length of the `k`-th argument (0-based) when it is an array, and `0`
    otherwise.  `ArgsAgree` preserves exactly this information for array
    arguments (constructor tags and lengths), so it is what a value-blind
    decodability gate may inspect. -/
private def argLen (args : List Value) (k : Nat) : Nat :=
  match args, k with
  | [], _ => 0
  | Value.array a :: _, 0 => a.length
  | _ :: _, 0 => 0
  | _ :: vs, k + 1 => argLen vs k

private theorem argLen_sameShape {vs ws : List Value}
    (h : Value.SameShapeList vs ws) (k : Nat) : argLen vs k = argLen ws k := by
  induction h generalizing k with
  | nil => cases k <;> rfl
  | cons hxy _ ih =>
    cases k with
    | zero =>
      cases hxy with
      | bool => rfl
      | int => rfl
      | setOfInt => rfl
      | array harr => simp [argLen, ListSameShape.length_eq harr]
    | succ k =>
      simp only [argLen]
      exact ih k

/-- The length conjunct of `cumulativesShape`, read on the raw argument
    list (`start`, `duration`, `resource`, `machine`).  The machine-range
    conjunct is a **value** condition: `ArgsAgree` does not fix variable
    argument values, so it stays in `cumulativesProp`/`cumulativesB` (a
    rejected value is `False` there) and is not part of this gate. -/
private def cumulativesArgShapeB (args : List Value) : Bool :=
  decide (argLen args 0 ≤ argLen args 1 ∧ argLen args 0 ≤ argLen args 2 ∧
    argLen args 0 ≤ argLen args 3)

/-- The length conjunct of `writesSeqShape`, read on the raw arguments
    `(I, P, V, O)`: only `O` must cover every `I` position.  Missing `P`
    entries are masked by the Boolean-context rule and need no gate. -/
private def writesSeqArgShapeB (args : List Value) : Bool :=
  decide (argLen args 0 ≤ argLen args 3)

private theorem cumulativesArgShapeB_agree {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    cumulativesArgShapeB vs = cumulativesArgShapeB ws := by
  simp only [cumulativesArgShapeB, argLen_sameShape h 0,
    argLen_sameShape h 1, argLen_sameShape h 2, argLen_sameShape h 3]

private theorem writesSeqArgShapeB_agree {vs ws : List Value}
    (h : Value.SameShapeList vs ws) :
    writesSeqArgShapeB vs = writesSeqArgShapeB ws := by
  simp only [writesSeqArgShapeB, argLen_sameShape h 0,
    argLen_sameShape h 3]

/-- Boolean decodability gate of the extended scheduling, geometric, write
    and partiality families: the `isSome` of the very decoders
    `sched2Interp` uses, conjoined with the remaining unconditional length
    conjuncts (`cumulativesShape`, `writesSeqShape`), and `true` outside
    the family.

    The masked-read families (`diffnNonoverlapK`, `ifThenElsePartiality`)
    need only decodability: a missing parallel entry is allowed whenever
    no evaluation point reads it.

    The value-range conjuncts of those gates (machine/`bound` indices) are
    value conditions on variable arguments, so they cannot appear here:
    `sched2Decodes_agree` must hold for `ArgsAgree`, which fixes only
    constructor tags and array lengths.  A call violating them is still
    rejected by the interpretation (`cumulativesProp` is `False`). -/
def sched2Decodes (n : String) (args : List Value) : Bool :=
  match n with
  | "fzn_cumulatives" =>
      (cumulativesArgs args).isSome && cumulativesArgShapeB args
  | "fzn_cumulatives_decomp" =>
      (fiveIntArraysAndBool args).isSome && cumulativesArgShapeB args
  | "fzn_geost" => (geostArgs args).isSome
  | "fzn_geost_bb" => (geostBbArgs args).isSome
  | "fzn_geost_smallest_bb" => (geostBbArgs args).isSome
  | "fzn_diffn_nonoverlap_k" => (fourIntArrays args).isSome
  | "fzn_writes_seq" =>
      (fourIntArrays args).isSome && writesSeqArgShapeB args
  | "fzn_diffn_k" => (twoMatrices args).isSome
  | "fzn_diffn_nonstrict_k" => (twoMatrices args).isSome
  | "fzn_if_then_else_partiality" =>
      (twoBoolArraysAndBool args).isSome
  | _ => true

/-- The decodability gate is invariant under `ArgsAgree`. -/
theorem sched2Decodes_agree {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws) (n : String) :
    sched2Decodes n vs = sched2Decodes n ws := by
  have hshape : Value.SameShapeList vs ws := ArgsAgree.sameShape h
  unfold sched2Decodes
  split
  · rw [cumulativesArgs_isSome_agree h, cumulativesArgShapeB_agree hshape]
  · rw [fiveIntArraysAndBool_isSome_agree h, cumulativesArgShapeB_agree hshape]
  · exact geostArgs_isSome_agree h
  · exact geostBbArgs_isSome_agree h
  · exact geostBbArgs_isSome_agree h
  · exact fourIntArrays_isSome_agree h
  · rw [fourIntArrays_isSome_agree h, writesSeqArgShapeB_agree hshape]
  · exact twoMatrices_isSome_agree h
  · exact twoMatrices_isSome_agree h
  · exact twoBoolArraysAndBool_isSome_agree h
  · rfl

end LeanFzn.Semantics.Globals.Sched2
