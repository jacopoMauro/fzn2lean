import LeanFzn.Solver.Propagation.Operations

/-!
# Literal clamp (U1e)

Runtime normalization of order/removal literals against the ORIGINAL slot
domains. Propagators (e.g. `int_times`) compute bounds outside the box; such a
literal is meaning-equivalent, under `a.Fits orig`, to a literal whose
threshold lies in the finite representative set
`threshPool d = ints d ++ (ints d).map (· - 1)` of the slot's original domain.
`snapLit orig` performs that normalization:

* `s ≤ k` becomes `s ≤ r`, `r` the largest pool threshold `≤ k` (or the least
  pool threshold `min - 1` when none is `≤ k`);
* `s ≠ v` with `v` outside the original integer values (root-true) becomes
  `¬ (s ≤ min - 1)` (and `¬ (s ≠ v)`, root-false, becomes `s ≤ min - 1`).

Everything else (Booleans, in-pool literals, slots outside `orig`, slots with no
integer values) is unchanged. `snapLit` is the identity on pool literals.
-/

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics LeanFzn.Solver.Core

/-- Integer values of a slot's original domain. -/
def clampInts (d : Domain) : List Int := (Dom.enum d).filterMap Value.intView

/-- Structural twin of `clampInts`: on the compact constructors it reads the
    stored integer list directly instead of materialising the `Value` list
    through `Dom.enum` (a wide hole interval would otherwise allocate a
    `Value.int` wrapper for every element on every literal clamp). -/
def clampIntsFast (d : Domain) : List Int :=
  match d.rep with
  | .small true .. => clampInts d
  | .small false off bits => Dom.smallInts off bits
  | .holes lo hi hs => Dom.holesInts lo hi hs
  | .general vs => vs.filterMap Value.intView

private theorem filterMap_intView_map_int (xs : List Int) :
    (xs.map Value.int).filterMap Value.intView = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simp [Value.intView, ih]

/-- The structural read is the enumerating read. -/
theorem clampIntsFast_eq (d : Domain) : clampIntsFast d = clampInts d := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true => rfl
          | false =>
              simp only [clampIntsFast, clampInts, Dom.enum,
                filterMap_intView_map_int]
      | holes lo hi hs =>
          simp only [clampIntsFast, clampInts, Dom.enum,
            filterMap_intView_map_int]
      | general vs => rfl

attribute [implemented_by clampIntsFast] clampInts

/-- The integer values of a dense (hole-free) `.holes` domain are exactly the
    corresponding `rangeInts` window.  This is the shape `ofIntRange` produces
    for every declared range wider than 64 values. -/
theorem clampInts_holes_nil (lo hi : Int) :
    clampInts ⟨.holes lo hi []⟩ = rangeInts lo (hi - lo + 1).toNat := by
  unfold clampInts Dom.enum
  change ((Dom.holesInts lo hi []).map Value.int).filterMap Value.intView
      = rangeInts lo (hi - lo + 1).toNat
  rw [Dom.holesInts_nil_eq_rangeInts, filterMap_intView_map_int]

/-- Threshold representatives: values and their predecessors. -/
def clampPool (ints : List Int) : List Int := ints ++ ints.map (fun i => i - 1)

/-- Least element of a nonempty list (default `0` on `[]`). -/
def clampMin (xs : List Int) : Int := xs.foldl min (xs.headD 0)

/-- The pool threshold a bound `k` is mapped to. -/
def snapBound (ints : List Int) (k : Int) : Int :=
  ((clampPool ints).filter (· ≤ k)).foldl max (clampMin (clampPool ints))

/-! ### The dense-interval closed forms

For a hole-free interval `[lo, hi]` the threshold pool is the full window
`[lo-1, hi]`: `clampMin` is `lo-1` and snapping a bound is just clamping it
into the window.  These closed forms let `snapLitFast` clamp a wide declared
range without materialising its enumeration. -/

/-- Snapping `k` against the dense interval `[lo, hi]`. -/
def denseSnapBound (lo hi k : Int) : Int := min (max k (lo - 1)) hi

private theorem foldl_max_le_of_all {l : List Int} {a B : Int} (ha : a ≤ B)
    (hl : ∀ x ∈ l, x ≤ B) : l.foldl max a ≤ B := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (Int.max_le.mpr ⟨ha, hl x (List.mem_cons_self ..)⟩)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy))

private theorem le_foldl_max_init (l : List Int) : ∀ a : Int, a ≤ l.foldl max a := by
  induction l with
  | nil => intro a; exact Int.le_refl _
  | cons x xs ih =>
      intro a
      rw [List.foldl_cons]
      exact Int.le_trans (Int.le_max_left a x) (ih _)

private theorem le_foldl_max_of_mem {l : List Int} {x : Int} (hx : x ∈ l) :
    ∀ a : Int, x ≤ l.foldl max a := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
      intro a
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Int.le_trans (Int.le_max_right a x) (le_foldl_max_init ys _)
      · exact ih hx _

private theorem foldl_min_le_init (l : List Int) : ∀ a : Int, l.foldl min a ≤ a := by
  induction l with
  | nil => intro a; exact Int.le_refl _
  | cons x xs ih =>
      intro a
      rw [List.foldl_cons]
      exact Int.le_trans (ih _) (Int.min_le_left a x)

private theorem foldl_min_ge_of_all {l : List Int} {a B : Int} (ha : B ≤ a)
    (hl : ∀ x ∈ l, B ≤ x) : B ≤ l.foldl min a := by
  induction l generalizing a with
  | nil => exact ha
  | cons x xs ih =>
      rw [List.foldl_cons]
      exact ih (Int.le_min.mpr ⟨ha, hl x (List.mem_cons_self ..)⟩)
        (fun y hy => hl y (List.mem_cons_of_mem _ hy))

private theorem foldl_min_le_of_mem {l : List Int} {x : Int} (hx : x ∈ l) :
    ∀ a : Int, l.foldl min a ≤ x := by
  induction l with
  | nil => cases hx
  | cons y ys ih =>
      intro a
      rw [List.foldl_cons]
      rcases List.mem_cons.mp hx with rfl | hx
      · exact Int.le_trans (foldl_min_le_init ys _) (Int.min_le_right a x)
      · exact ih hx _

private theorem mem_clampPool_rangeInts {lo : Int} {n : Nat} (hn : 0 < n) {x : Int} :
    x ∈ clampPool (rangeInts lo n) ↔ lo - 1 ≤ x ∧ x ≤ lo + (n : Int) - 1 := by
  unfold clampPool
  rw [List.mem_append, List.mem_map]
  constructor
  · rintro (hx | ⟨y, hy, rfl⟩)
    · rw [rangeInts_mem] at hx
      obtain ⟨k, hk, rfl⟩ := hx
      have hk' : (k : Int) < (n : Int) := by exact_mod_cast hk
      omega
    · rw [rangeInts_mem] at hy
      obtain ⟨k, hk, rfl⟩ := hy
      have hk' : (k : Int) < (n : Int) := by exact_mod_cast hk
      omega
  · rintro ⟨hlo, hhi⟩
    by_cases hlt : x < lo
    · right
      refine ⟨lo, ?_, by omega⟩
      rw [rangeInts_mem]
      exact ⟨0, hn, by omega⟩
    · left
      rw [rangeInts_mem]
      refine ⟨(x - lo).toNat, ?_, ?_⟩
      · have hcast : ((x - lo).toNat : Int) < (n : Int) := by
          rw [Int.toNat_of_nonneg (by omega : 0 ≤ x - lo)]
          omega
        exact_mod_cast hcast
      · rw [Int.toNat_of_nonneg (by omega : 0 ≤ x - lo)]
        omega

private theorem mem_rangeInts_iff {lo : Int} {n : Nat} {v : Int} :
    v ∈ rangeInts lo n ↔ lo ≤ v ∧ v ≤ lo + (n : Int) - 1 := by
  rw [rangeInts_mem]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : (k : Int) < (n : Int) := by exact_mod_cast hk
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨(v - lo).toNat, ?_, ?_⟩
    · have hcast : ((v - lo).toNat : Int) < (n : Int) := by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ v - lo)]
        omega
      exact_mod_cast hcast
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ v - lo)]
      omega

private theorem clampMin_rangeInts {lo : Int} {n : Nat} (hn : 0 < n) :
    clampMin (clampPool (rangeInts lo n)) = lo - 1 := by
  have hmem : lo - 1 ∈ clampPool (rangeInts lo n) := by
    rw [mem_clampPool_rangeInts hn]
    constructor <;> omega
  have hnonempty : clampPool (rangeInts lo n) ≠ [] := by
    intro h; rw [h] at hmem; cases hmem
  have hhead : lo - 1 ≤ (clampPool (rangeInts lo n)).headD 0 := by
    cases hp : clampPool (rangeInts lo n) with
    | nil => exact absurd hp hnonempty
    | cons x xs =>
        have hx : x ∈ clampPool (rangeInts lo n) := by
          rw [hp]; exact List.mem_cons_self ..
        exact ((mem_clampPool_rangeInts hn).mp hx).1
  unfold clampMin
  exact Int.le_antisymm (foldl_min_le_of_mem hmem _)
    (foldl_min_ge_of_all hhead
      (fun x hx => ((mem_clampPool_rangeInts hn).mp hx).1))

private theorem snapBound_rangeInts {lo : Int} {n : Nat} (hn : 0 < n) (k : Int) :
    snapBound (rangeInts lo n) k = denseSnapBound lo (lo + (n : Int) - 1) k := by
  unfold snapBound denseSnapBound
  rw [clampMin_rangeInts hn]
  apply Int.le_antisymm
  · apply foldl_max_le_of_all
    · exact Int.le_min.mpr ⟨Int.le_max_right k (lo - 1), by omega⟩
    · intro x hx
      obtain ⟨hxmem, hkx⟩ := List.mem_filter.mp hx
      have hx' := (mem_clampPool_rangeInts hn).mp hxmem
      exact Int.le_min.mpr ⟨Int.le_trans (of_decide_eq_true hkx) (Int.le_max_left k (lo - 1)), hx'.2⟩
  · by_cases hk : k < lo - 1
    · have hB : min (max k (lo - 1)) (lo + (n : Int) - 1) = lo - 1 := by
        have hm : max k (lo - 1) = lo - 1 := by
          rw [Int.max_def]; split <;> omega
        rw [hm, Int.min_def]; split <;> omega
      rw [hB]
      exact le_foldl_max_init _ (lo - 1)
    · have hk' : lo - 1 ≤ k := by omega
      by_cases hhi : lo + (n : Int) - 1 ≤ k
      · have hB : min (max k (lo - 1)) (lo + (n : Int) - 1) = lo + (n : Int) - 1 := by
          have hm : max k (lo - 1) = k := by
            rw [Int.max_def]; split <;> omega
          rw [hm, Int.min_def]; split <;> omega
        rw [hB]
        exact le_foldl_max_of_mem (List.mem_filter.mpr
          ⟨(mem_clampPool_rangeInts hn).mpr ⟨by omega, by omega⟩,
            by simpa using hhi⟩) (lo - 1)
      · have hB : min (max k (lo - 1)) (lo + (n : Int) - 1) = k := by
          have hm : max k (lo - 1) = k := by
            rw [Int.max_def]; split <;> omega
          rw [hm, Int.min_def]; split <;> omega
        rw [hB]
        exact le_foldl_max_of_mem (List.mem_filter.mpr
          ⟨(mem_clampPool_rangeInts hn).mpr ⟨by omega, by omega⟩,
            by simp⟩) (lo - 1)

/-- The clamp of one literal against the original domains. -/
def snapLit (orig : List Domain) (l : Literal) : Literal :=
  match l.atom with
  | .intLe s k =>
      match orig[s]? with
      | none => l
      | some d =>
          if (clampInts d).isEmpty then l
          else ⟨.intLe s (snapBound (clampInts d) k), l.positive⟩
  | .intNe s v =>
      match orig[s]? with
      | none => l
      | some d =>
          if (clampInts d).isEmpty ∨ v ∈ clampInts d then l
          else ⟨.intLe s (clampMin (clampPool (clampInts d))), !l.positive⟩
  | .boolEq _ _ => l

/-- Structural clamp of one literal, with a dense-interval fast path.

The reference `snapLit` reads the slot through `clampInts`, which materialises
every integer of the original domain.  On a declared range such as gbac's
`0..179280830` that list has one entry per value and the enumeration recurses
once per entry, exhausting the task stack before the search starts.  A
hole-free `.holes lo hi []` domain is exactly the dense interval `[lo, hi]`,
whose threshold pool is the whole window `[lo-1, hi]`; the closed forms below
compute the same snap without enumeration.  Every other representation takes
the reference computation. -/
def snapLitFast (orig : List Domain) (l : Literal) : Literal :=
  match l.atom with
  | .intLe s k =>
      match orig[s]? with
      | none => l
      | some d =>
          match d.rep with
          | .holes lo hi [] =>
              if lo ≤ hi then
                ⟨.intLe s (denseSnapBound lo hi k), l.positive⟩
              else l
          | _ =>
              if (clampInts d).isEmpty then l
              else ⟨.intLe s (snapBound (clampInts d) k), l.positive⟩
  | .intNe s v =>
      match orig[s]? with
      | none => l
      | some d =>
          match d.rep with
          | .holes lo hi [] =>
              if lo ≤ hi then
                (if lo ≤ v ∧ v ≤ hi then l
                 else ⟨.intLe s (lo - 1), !l.positive⟩)
              else l
          | _ =>
              if (clampInts d).isEmpty ∨ v ∈ clampInts d then l
              else ⟨.intLe s (clampMin (clampPool (clampInts d))), !l.positive⟩
  | .boolEq _ _ => l

/-- The structural clamp is the reference clamp. -/
theorem snapLitFast_eq (orig : List Domain) (l : Literal) :
    snapLitFast orig l = snapLit orig l := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | boolEq s b => rfl
  | intLe s k =>
      cases hd : orig[s]? with
      | none => simp [snapLitFast, snapLit, hd]
      | some d =>
          cases d with
          | mk rep =>
              cases rep with
              | small isBool off bits => simp [snapLitFast, snapLit, hd]
              | general vs => simp [snapLitFast, snapLit, hd]
              | holes lo hi hs =>
                  cases hs with
                  | cons h t => simp [snapLitFast, snapLit, hd]
                  | nil =>
                      by_cases hle : lo ≤ hi
                      · have hn : 0 < (hi - lo + 1).toNat := by
                          rw [← Int.pos_iff_toNat_pos]
                          omega
                        have hclamp : clampInts ⟨.holes lo hi []⟩
                            = rangeInts lo (hi - lo + 1).toNat :=
                          clampInts_holes_nil lo hi
                        have hemp : (clampInts ⟨.holes lo hi []⟩).isEmpty = false := by
                          rw [hclamp, List.isEmpty_eq_false_iff]
                          intro hnil
                          have hlen := rangeInts_length lo (hi - lo + 1).toNat
                          rw [hnil] at hlen
                          simp at hlen
                          omega
                        have hsb : snapBound (clampInts ⟨.holes lo hi []⟩) k
                            = denseSnapBound lo hi k := by
                          rw [hclamp, snapBound_rangeInts hn k]
                          unfold denseSnapBound
                          have hcast : ((hi - lo + 1).toNat : Int) = hi - lo + 1 :=
                            Int.toNat_of_nonneg (by omega)
                          rw [hcast]
                          congr 1
                          omega
                        simp only [snapLitFast, snapLit, hd, hle, if_true,
                          hemp, Bool.false_eq_true, if_false, hsb]
                      · have hzero : (hi - lo + 1).toNat = 0 := by
                          rw [Int.toNat_eq_zero]
                          omega
                        have hclamp : clampInts ⟨.holes lo hi []⟩ = [] := by
                          rw [clampInts_holes_nil, hzero]
                          rfl
                        have hemp : (clampInts ⟨.holes lo hi []⟩).isEmpty = true := by
                          rw [hclamp]; rfl
                        simp only [snapLitFast, snapLit, hd, hle, if_false, hemp, if_true]
  | intNe s v =>
      cases hd : orig[s]? with
      | none => simp [snapLitFast, snapLit, hd]
      | some d =>
          cases d with
          | mk rep =>
              cases rep with
              | small isBool off bits => simp [snapLitFast, snapLit, hd]
              | general vs => simp [snapLitFast, snapLit, hd]
              | holes lo hi hs =>
                  cases hs with
                  | cons h t => simp [snapLitFast, snapLit, hd]
                  | nil =>
                      by_cases hle : lo ≤ hi
                      · have hn : 0 < (hi - lo + 1).toNat := by
                          rw [← Int.pos_iff_toNat_pos]
                          omega
                        have hclamp : clampInts ⟨.holes lo hi []⟩
                            = rangeInts lo (hi - lo + 1).toNat :=
                          clampInts_holes_nil lo hi
                        have hemp : (clampInts ⟨.holes lo hi []⟩).isEmpty = false := by
                          rw [hclamp, List.isEmpty_eq_false_iff]
                          intro hnil
                          have hlen := rangeInts_length lo (hi - lo + 1).toNat
                          rw [hnil] at hlen
                          simp at hlen
                          omega
                        have hmem : v ∈ clampInts ⟨.holes lo hi []⟩ ↔ lo ≤ v ∧ v ≤ hi := by
                          rw [hclamp, mem_rangeInts_iff]
                          have hcast : ((hi - lo + 1).toNat : Int) = hi - lo + 1 :=
                            Int.toNat_of_nonneg (by omega)
                          rw [hcast]
                          congr 1
                          omega
                        have hmin : clampMin (clampPool (clampInts ⟨.holes lo hi []⟩)) = lo - 1 := by
                          rw [hclamp, clampMin_rangeInts hn]
                        simp only [snapLitFast, snapLit, hd, hle, if_true,
                          hemp, Bool.false_eq_true, hmem, hmin, false_or]
                      · have hzero : (hi - lo + 1).toNat = 0 := by
                          rw [Int.toNat_eq_zero]
                          omega
                        have hclamp : clampInts ⟨.holes lo hi []⟩ = [] := by
                          rw [clampInts_holes_nil, hzero]
                          rfl
                        have hemp : (clampInts ⟨.holes lo hi []⟩).isEmpty = true := by
                          rw [hclamp]; rfl
                        simp only [snapLitFast, snapLit, hd, hle, if_false, hemp, if_true,
                          true_or]

attribute [implemented_by snapLitFast] snapLit

/-- Clamp of a clause. -/
def snapClause (orig : List Domain) (c : Clause) : Clause := c.map (snapLit orig)

/-- Clamp of a propagation result. -/
def snapResult (orig : List Domain) : PropagationResult → PropagationResult
  | .stable => .stable
  | .implied l r => .implied (snapLit orig l) { r with clause := snapClause orig r.clause }
  | .conflict c => .conflict (snapClause orig c)

/-- Clamp of a propagator: same watches, clamped emissions. -/
def Propagator.clamp (orig : List Domain) (p : Propagator) : Propagator :=
  { p with run := fun st => snapResult orig (p.run st) }

/-- Clamp a registered propagator list. -/
def clampProps (orig : List Domain) (props : List Propagator) : List Propagator :=
  props.map (Propagator.clamp orig)

end LeanFzn.Solver.Propagation
