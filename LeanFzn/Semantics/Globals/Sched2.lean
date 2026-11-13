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
  shape-selected objects with flat row-major matrices.
* `fzn_diffn_nonoverlap_k(x1, w1, x2, w2)`: 1-D per-axis
  non-overlap.  `fzn_diffn_k` / `fzn_diffn_nonstrict_k` (nested-array
  matrices; G30/G24 representation caveat).
* `fzn_writes_seq(I, P, V, O)` (G31): last-write-wins.
* `fzn_if_then_else_partiality(c, def, b)` (G32): definedness of the
  first-true conditional.
-/

open LeanFzn.Semantics

open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Semantics.Globals.Sched2

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Semantics.Evaluation

/-! ## cumulatives -/

/-- Does task `i` (start `si`, duration `di`) run on machine `mi`
    at time `t` (half-open interval)? -/
private def taskAt (si di mi t mach : Int) : Bool :=
  decide (si ≤ t ∧ t < si + di ∧ mi = mach)

/-- The event-point loads of machine `m`'s j-th check. -/
private def eventLoads (start duration resource machine : List Int) (j : Nat) :
    Int × Int :=
  let loadAt (t : Int) : Int :=
    (List.range start.length).foldl (fun acc i =>
      if taskAt (start.getD i 0) (duration.getD i 0) (machine.getD i 0) t
          (machine.getD j 0) then
        acc + resource.getD i 0 else acc) 0
  (loadAt (start.getD j 0), loadAt (start.getD j 0 + duration.getD j 0))

/-- The cover guards of machine `j`'s check. -/
private def eventCovers (start duration machine : List Int) (j : Nat) :
    Bool × Bool :=
  let coverAt (t : Int) : Bool :=
    (List.range start.length).any (fun i =>
      taskAt (start.getD i 0) (duration.getD i 0) (machine.getD i 0) t
        (machine.getD j 0))
  (coverAt (start.getD j 0), coverAt (start.getD j 0 + duration.getD j 0))

/-- `fzn_cumulatives`: event-point resource check (G26). -/
def cumulativesProp (start duration resource machine bound : List Int)
    (isUpper : Bool) : Prop :=
  (List.range start.length).all (fun j =>
    (isUpper = true ∧ (eventCovers start duration machine j).1 = true →
      (eventLoads start duration resource machine j).1 ≤ bound.getD j 0) ∧
    (isUpper = true ∧ (eventCovers start duration machine j).2 = true →
      (eventLoads start duration resource machine j).2 ≤ bound.getD j 0) ∧
    (isUpper = false ∧ (eventCovers start duration machine j).1 = true →
      bound.getD j 0 ≤ (eventLoads start duration resource machine j).1) ∧
    (isUpper = false ∧ (eventCovers start duration machine j).2 = true →
      bound.getD j 0 ≤ (eventLoads start duration resource machine j).2))

/-- Boolean twin of `cumulativesProp`. -/
def cumulativesB (start duration resource machine bound : List Int)
    (isUpper : Bool) : Bool :=
  (List.range start.length).all (fun j =>
    (!(isUpper && (eventCovers start duration machine j).1) ||
        decide ((eventLoads start duration resource machine j).1 ≤
          bound.getD j 0)) &&
    (!(isUpper && (eventCovers start duration machine j).2) ||
        decide ((eventLoads start duration resource machine j).2 ≤
          bound.getD j 0)) &&
    (!(!isUpper && (eventCovers start duration machine j).1) ||
        decide (bound.getD j 0 ≤
          (eventLoads start duration resource machine j).1)) &&
    (!(!isUpper && (eventCovers start duration machine j).2) ||
        decide (bound.getD j 0 ≤
          (eventLoads start duration resource machine j).2)))

theorem cumulativesB_iff (start duration resource machine bound : List Int)
    (isUpper : Bool) :
    cumulativesB start duration resource machine bound isUpper = true ↔
      cumulativesProp start duration resource machine bound isUpper := by
  cases isUpper with
  | false =>
    simp only [cumulativesB, cumulativesProp, Bool.and_eq_true, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_iff, Bool.and_eq_true,
      Bool.true_and, Bool.false_and, Bool.not_false]
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
    simp only [cumulativesB, cumulativesProp, Bool.and_eq_true, List.all_eq_true,
      Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_iff, Bool.and_eq_true,
      Bool.true_and, Bool.not_true]
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

/-- The pairwise non-overlap core: for every ordered pair of objects
    `o1 < o2` and every rectangle pair of their (in-range) kinds. -/
private def geostCore (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) : Bool :=
  (List.range kind.length).all (fun o =>
    decide (1 ≤ kind.getD o 0 ∧
      kind.getD o 0 ≤ (shape.length : Int))) &&
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

/-- `fzn_geost`: for every pair of objects and every pair of shapes
    their kinds can take, every rectangle pair is separated. -/
def geostProp (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) : Prop :=
  geostCore k rectSize rectOffset shape xs kind = true

def geostB (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) : Bool :=
  geostCore k rectSize rectOffset shape xs kind

theorem geostB_iff (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int) :
    geostB k rectSize rectOffset shape xs kind = true ↔
      geostProp k rectSize rectOffset shape xs kind := Iff.rfl

/-- `fzn_geost_bb`: `geost` plus per-dimension bounds over every
    possibly-used shape's rectangles. -/
def geostBbProp (k : Int) (rectSize rectOffset : List Int)
    (shape : List IntSetValue) (xs : List Int) (kind : List Int)
    (lower upper : List Int) : Prop :=
  geostProp k rectSize rectOffset shape xs kind ∧
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
    geostB_iff, decide_eq_true_iff]

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

/-- `fzn_diffn_nonoverlap_k(x1, w1, x2, w2)`. -/
def diffnNonoverlapKProp (x1 w1 x2 w2 : List Int) : Prop :=
  boxesSeparated x1 w1 x2 w2 = true

def diffnNonoverlapKB (x1 w1 x2 w2 : List Int) : Bool :=
  boxesSeparated x1 w1 x2 w2

theorem diffnNonoverlapKB_iff (x1 w1 x2 w2 : List Int) :
    diffnNonoverlapKB x1 w1 x2 w2 = true ↔
      diffnNonoverlapKProp x1 w1 x2 w2 := Iff.rfl

/-- `fzn_diffn_k(boxPosn, boxSize)`: nested-array matrices (rows =
    boxes); pairwise non-overlap. -/
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
    free. -/
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

/-- `fzn_writes_seq(I, P, V, O)` (G31): for each position, the
    last write wins; absent writes keep `I`. -/
def writesSeqProp (i p v o : List Int) : Prop :=
  (List.range i.length).all (fun idx =>
    decide (o.getD idx 0 =
      match ((List.range p.length).filter (fun j =>
        p.getD j 0 = (idx : Int) + 1)).reverse.head? with
      | some j => v.getD j 0
      | none => i.getD idx 0)) = true

def writesSeqB (i p v o : List Int) : Bool :=
  (List.range i.length).all (fun idx =>
    decide (o.getD idx 0 =
      match ((List.range p.length).filter (fun j =>
        p.getD j 0 = (idx : Int) + 1)).reverse.head? with
      | some j => v.getD j 0
      | none => i.getD idx 0))

theorem writesSeqB_iff (i p v o : List Int) :
    writesSeqB i p v o = true ↔ writesSeqProp i p v o := by
  simp only [writesSeqB, writesSeqProp, List.all_eq_true]

/-! ## if_then_else_partiality -/

/-- The first index `i` (0-based scan) with `c[i]` true, as a
    function. -/
private def firstTrue (c : List Bool) : Option Nat :=
  match (List.range c.length).find? (fun i => c.getD i false) with
  | some i => some i
  | none => none

/-- `fzn_if_then_else_partiality(c, def, b)` (G32): with no true
    condition, `b = false`; otherwise `b = def[first true i]`. -/
def itePartialityProp (c d : List Bool) (b : Bool) : Prop :=
  match firstTrue c with
  | none => b = false
  | some i => b = d.getD i false

def itePartialityB (c d : List Bool) (b : Bool) : Bool :=
  match firstTrue c with
  | none => !b
  | some i => b == d.getD i false

theorem itePartialityB_iff (c d : List Bool) (b : Bool) :
    itePartialityB c d b = true ↔ itePartialityProp c d b := by
  simp only [itePartialityB, itePartialityProp]
  cases hft : firstTrue c with
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
     Value.array a5, Value.bool up, Value.int _mm] =>
      match valueInts a1, valueInts a2, valueInts a3, valueInts a4,
        valueInts a5 with
      | some l1, some l2, some l3, some l4, some l5 =>
          some (l1, l2, l3, l4, l5, up, 0)
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

/-- Decode two nested int-array matrices (diffn_k). -/
private def twoMatrices (args : List Value) :
    Option (List (List Int) × List (List Int)) :=
  match args with
  | [Value.array a1, Value.array a2] =>
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

end LeanFzn.Semantics.Globals.Sched2
