/-
File: LeanFzn/Solver/Core/CompactDomain.lean

Purpose:
  The representation core of the compact finite-domain type `Dom`: the
  constructors, denotation `enum`, canonicality `WF`, universal
  constructor `ofList` with its linear contiguous/tiny-range paths,
  membership, cardinality, bounds and Boolean presence.

  This module deliberately imports only `LeanFzn.Semantics` (never
  `Solver.Core.Types`), so that `Solver.Core.Types` can define
  `abbrev Domain := Dom` for the D2 S1 switch without an import cycle.
  The `Literal`/frame bridges, filtering and structural `filterLit`/
  `removeVal` remain in `LeanFzn.Solver.Propagation.CompactDomain`,
  which imports this module.

Dependencies:
  - LeanFzn.Semantics.ValueEquality, LeanFzn.Semantics.Globals.Common

DAG:
  LeanFzn.Semantics.* -> LeanFzn.Solver.Core.CompactDomain ->
  LeanFzn.Solver.Core.Types -> all LeanFzn.Solver approaches
-/

import LeanFzn.Semantics.ValueEquality
import LeanFzn.Semantics.Globals.Common
import LeanFzn.Solver.Core.Enumerate

namespace LeanFzn.Solver.Propagation

open LeanFzn.Semantics

/-! ## Bit helpers

The bitset window is 64 bits.  `intsToBits lo xs` packs `xs` into the
bits of `2 ^ (x - lo)`; the membership characterizations below are
stated against `Nat.testBit` (core), and the `UInt64` boundary is
crossed once, in `testBit_ofNat_uint64`. -/

/-- Pack an integer list into a bit vector indexed from `lo`: bit
    `(x - lo).toNat` is set for every `x` in the list (elements below
    `lo` collide in bit 0; all uses below satisfy `lo ≤ x`). -/
def intsToBits (lo : Int) (xs : List Int) : Nat :=
  xs.foldl (fun acc x => acc ||| 2 ^ (x - lo).toNat) 0

/-- The test bit of a packed list, with an arbitrary initial
    accumulator: bit `k` of the result is the initial bit or the
    membership of `lo + k` in the list. -/
theorem testBit_foldInts (lo : Int) (k : Nat) :
    ∀ (xs : List Int) (acc : Nat), (∀ x ∈ xs, lo ≤ x) →
      (xs.foldl (fun acc x => acc ||| 2 ^ (x - lo).toNat) acc).testBit k =
        (acc.testBit k || decide (lo + (k : Int) ∈ xs)) := by
  intro xs
  induction xs with
  | nil => intro acc _; simp
  | cons x rest ih =>
      intro acc hlo
      rw [List.foldl_cons]
      rw [ih (acc ||| 2 ^ (x - lo).toNat) (fun y hy => hlo y (List.mem_cons_of_mem _ hy))]
      rw [Nat.testBit_or, Nat.testBit_two_pow]
      have hx : lo ≤ x := hlo x List.mem_cons_self
      have hiff : (x - lo).toNat = k ↔ x = lo + (k : Int) := by
        constructor
        · intro h
          have h' : ((x - lo).toNat : Int) = (k : Int) := by exact_mod_cast h
          rw [Int.toNat_of_nonneg (by omega)] at h'
          omega
        · intro h
          subst h
          rw [show lo + (k : Int) - lo = (k : Int) by omega, Int.toNat_natCast]
      have hdec : decide ((x - lo).toNat = k) = decide (x = lo + (k : Int)) :=
        decide_eq_decide.mpr hiff
      rw [hdec]
      have hmem : decide (lo + (k : Int) ∈ x :: rest) =
          (decide (x = lo + (k : Int)) || decide (lo + (k : Int) ∈ rest)) := by
        have h1 : decide (lo + (k : Int) ∈ x :: rest) =
            decide (lo + (k : Int) = x ∨ lo + (k : Int) ∈ rest) :=
          decide_eq_decide.mpr List.mem_cons
        rw [h1, Bool.decide_or]
        rw [decide_eq_decide.mpr (show (lo + (k : Int) = x) ↔ (x = lo + (k : Int)) from
          ⟨Eq.symm, Eq.symm⟩)]
      rw [hmem, Bool.or_assoc]

/-- The test bit of a packed list is the membership of `lo + k`. -/
theorem testBit_intsToBits_eq {lo : Int} {xs : List Int}
    (hlo : ∀ x ∈ xs, lo ≤ x) (k : Nat) :
    (intsToBits lo xs).testBit k = decide (lo + (k : Int) ∈ xs) := by
  unfold intsToBits
  rw [testBit_foldInts lo k xs 0 hlo]
  simp

/-- The test bit of a packed list decides membership. -/
theorem testBit_intsToBits_iff {lo : Int} {xs : List Int}
    (hlo : ∀ x ∈ xs, lo ≤ x) (k : Nat) :
    (intsToBits lo xs).testBit k = true ↔ lo + (k : Int) ∈ xs := by
  rw [testBit_intsToBits_eq hlo k, decide_eq_true_eq]

/-- A packed list of window elements fits in 64 bits. -/
theorem foldInts_lt (lo : Int) :
    ∀ (xs : List Int) (acc : Nat), acc < 2 ^ 64 →
      (∀ x ∈ xs, lo ≤ x ∧ x - lo < 64) →
      xs.foldl (fun acc x => acc ||| 2 ^ (x - lo).toNat) acc < 2 ^ 64 := by
  intro xs
  induction xs with
  | nil => intro acc hacc _; simpa using hacc
  | cons x rest ih =>
      intro acc hacc hw
      rw [List.foldl_cons]
      apply ih
      · apply Nat.or_lt_two_pow hacc
        have hx := hw x List.mem_cons_self
        have hk : (x - lo).toNat < 64 := by
          have h' : ((x - lo).toNat : Int) < 64 := by
            rw [Int.toNat_of_nonneg (by omega)]
            exact hx.2
          exact_mod_cast h'
        exact Nat.pow_lt_pow_right (by decide) hk
      · exact fun y hy => hw y (List.mem_cons_of_mem _ hy)

/-- Packing a window list fits in 64 bits. -/
theorem intsToBits_lt (lo : Int) (xs : List Int)
    (hw : ∀ x ∈ xs, lo ≤ x ∧ x - lo < 64) : intsToBits lo xs < 2 ^ 64 := by
  unfold intsToBits
  exact foldInts_lt lo xs 0 (by decide) hw

/-- The `UInt64` view of a packed list, below `2 ^ 64`. -/
theorem toNat_ofNat_intsToBits {lo : Int} {xs : List Int}
    (hw : ∀ x ∈ xs, lo ≤ x ∧ x - lo < 64) :
    (UInt64.ofNat (intsToBits lo xs)).toNat = intsToBits lo xs := by
  rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (intsToBits_lt lo xs hw)]

/-- Test bits below 64 are unaffected by the `UInt64` wrap. -/
theorem testBit_ofNat_uint64 {n k : Nat} (hk : k < 64) :
    (UInt64.ofNat n).toNat.testBit k = n.testBit k := by
  rw [UInt64.toNat_ofNat', Nat.testBit_mod_two_pow, decide_eq_true hk, Bool.true_and]

/-- Below `2 ^ 64`, all higher test bits vanish. -/
theorem testBit_eq_false_of_lt {n k : Nat} (h : n < 2 ^ 64) (hk : 64 ≤ k) :
    n.testBit k = false := by
  obtain ⟨j, rfl⟩ : ∃ j, k = 64 + j := ⟨k - 64, by omega⟩
  rw [← Nat.testBit_shiftRight]
  rw [Nat.shiftRight_eq_div_pow, Nat.div_eq_of_lt h]
  simp

/-! ## Index scans -/

/-- The ordered scan of `[lo, lo + n)` filtered by `p`. -/
def scanInts (lo : Int) (p : Nat → Bool) : Nat → List Int
  | 0 => []
  | n + 1 => if p n then scanInts lo p n ++ [lo + (n : Int)] else scanInts lo p n

/-- Membership in the scan. -/
theorem mem_scanInts {lo : Int} {p : Nat → Bool} {x : Int} :
    ∀ {n : Nat}, x ∈ scanInts lo p n ↔ ∃ k < n, p k = true ∧ lo + (k : Int) = x := by
  intro n
  induction n with
  | zero => simp [scanInts]
  | succ n ih =>
      rw [scanInts]
      by_cases h : p n = true
      · rw [if_pos h, List.mem_append, ih]
        constructor
        · rintro (⟨k, hk, hp, hx⟩ | hx)
          · exact ⟨k, Nat.lt_succ_of_lt hk, hp, hx⟩
          · rw [List.mem_singleton] at hx
            exact ⟨n, Nat.lt_succ_self n, h, hx.symm⟩
        · rintro ⟨k, hk, hp, hx⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact Or.inl ⟨k, hk, hp, hx⟩
          · exact Or.inr (by rw [List.mem_singleton]; exact hx.symm)
      · rw [if_neg h, ih]
        constructor
        · rintro ⟨k, hk, hp, hx⟩
          exact ⟨k, Nat.lt_succ_of_lt hk, hp, hx⟩
        · rintro ⟨k, hk, hp, hx⟩
          rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
          · exact ⟨k, hk, hp, hx⟩
          · exact absurd hp h

/-- The scan is ascending. -/
theorem pairwise_scanInts (lo : Int) (p : Nat → Bool) (n : Nat) :
    (scanInts lo p n).Pairwise (fun a b => a < b) := by
  induction n with
  | zero => simp [scanInts]
  | succ n ih =>
      rw [scanInts]
      by_cases h : p n = true
      · rw [if_pos h, List.pairwise_append]
        refine ⟨ih, List.pairwise_singleton _ _, ?_⟩
        intro a ha b hb
        rw [List.mem_singleton] at hb
        subst hb
        obtain ⟨k, hk, _, rfl⟩ := mem_scanInts.mp ha
        have : (k : Int) < (n : Int) := by exact_mod_cast hk
        omega
      · rw [if_neg h]
        exact ih

/-- Two ascending integer lists with the same elements are equal. -/
theorem eq_of_pairwise_lt_of_mem_iff {l m : List Int}
    (hl : l.Pairwise (fun a b => a < b)) (hm : m.Pairwise (fun a b => a < b))
    (h : ∀ x, x ∈ l ↔ x ∈ m) : l = m := by
  induction l generalizing m with
  | nil =>
      cases m with
      | nil => rfl
      | cons y ys =>
          have : y ∈ ([] : List Int) := (h y).mpr (List.mem_cons_self ..)
          exact absurd this (by simp)
  | cons x xs ih =>
      cases m with
      | nil =>
          have : x ∈ ([] : List Int) := (h x).mp (List.mem_cons_self ..)
          exact absurd this (by simp)
      | cons y ys =>
          have hxy : x = y := by
            rcases List.mem_cons.mp ((h x).mp (List.mem_cons_self ..)) with hxy | hxys
            · exact hxy
            · have hyx : y < x := (List.pairwise_cons.mp hm).1 x hxys
              rcases List.mem_cons.mp ((h y).mpr (List.mem_cons_self ..)) with hyx' | hyxs
              · omega
              · have hxy' : x < y := (List.pairwise_cons.mp hl).1 y hyxs
                omega
          have htail : ∀ z, z ∈ xs ↔ z ∈ ys := by
            intro z
            constructor
            · intro hz
              rcases List.mem_cons.mp ((h z).mp (List.mem_cons_of_mem _ hz)) with hzy | hzys
              · exact absurd (hzy ▸ hz) (by
                  have := (List.pairwise_cons.mp hl).1 z hz
                  omega)
              · exact hzys
            · intro hz
              rcases List.mem_cons.mp ((h z).mpr (List.mem_cons_of_mem _ hz)) with hzx | hzxs
              · exact absurd (hzx ▸ hz) (by
                  have := (List.pairwise_cons.mp hm).1 z hz
                  omega)
              · exact hzxs
          have hxsys : xs = ys := ih (List.Pairwise.tail hl) (List.Pairwise.tail hm) htail
          rw [hxy, hxsys]

/-- The `filterMap` scan of `[lo, lo + n)` equals the index scan. -/
theorem range_filterMap_scanInts (lo : Int) (p : Nat → Bool) (n : Nat) :
    (List.range n).filterMap (fun k => if p k then some (lo + (k : Int)) else none) =
      scanInts lo p n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.range_succ, List.filterMap_append, ih]
      rw [scanInts]
      by_cases h : p n = true
      · rw [if_pos h, List.filterMap_cons_some (by rw [if_pos h])]
        simp
      · rw [if_neg h, List.filterMap_cons_none (by rw [if_neg h])]
        simp

/-- `filterMap` congruence. -/
theorem filterMap_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.filterMap f = l.filterMap g
  | [], _ => rfl
  | a :: t, h => by
      have ha : f a = g a := h a List.mem_cons_self
      have ht : t.filterMap f = t.filterMap g :=
        filterMap_congr (fun b hb => h b (List.mem_cons_of_mem _ hb))
      cases hf : f a with
      | none =>
          rw [List.filterMap_cons_none hf, List.filterMap_cons_none (by rw [← ha, hf]), ht]
      | some b =>
          rw [List.filterMap_cons_some hf, List.filterMap_cons_some (by rw [← ha, hf]), ht]

/-- A list partitions into its `p` and non-`p` filters. -/
theorem length_filter_add_length_filter_not {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter fun a => !(p a)).length = l.length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases h : p a = true
      · rw [List.filter_cons_of_pos h, List.filter_cons_of_neg (by simp [h])]
        simp only [List.length_cons]
        omega
      · rw [List.filter_cons_of_neg h, List.filter_cons_of_pos (by simp [h])]
        simp only [List.length_cons]
        omega

/-- Length of an `if`-guarded `filterMap`. -/
theorem length_filterMap_if {α β : Type} (l : List α) (p : α → Bool) (f : α → β) :
    (l.filterMap (fun k => if p k then some (f k) else none)).length = (l.filter p).length := by
  induction l with
  | nil => rfl
  | cons a t ih =>
      by_cases h : p a = true
      · rw [List.filterMap_cons_some (by rw [if_pos h]), List.filter_cons_of_pos h]
        simp only [List.length_cons, ih]
      · rw [List.filterMap_cons_none (by rw [if_neg h]), List.filter_cons_of_neg h, ih]

/-- The range is ascending. -/
theorem pairwise_range (n : Nat) : (List.range n).Pairwise (fun a b => a < b) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.pairwise_append]
      exact ⟨ih, List.pairwise_singleton _ _, fun a ha b hb => by
        rw [List.mem_singleton] at hb
        subst hb
        exact List.mem_range.mp ha⟩

/-- The `filterMap`-scan of an index range is ascending. -/
theorem pairwise_filterMap_range (lo : Int) (p : Nat → Bool) (n : Nat) :
    ((List.range n).filterMap fun (k : Nat) =>
      if p k then some (lo + (k : Int)) else none).Pairwise fun a b => a < b := by
  refine List.Pairwise.filterMap _ (fun a a' ha b hb b' hb' => ?_) (pairwise_range n)
  by_cases h : p a = true
  · rw [if_pos h] at hb
    obtain rfl := Option.some.inj hb
    by_cases h' : p a' = true
    · rw [if_pos h'] at hb'
      obtain rfl := Option.some.inj hb'
      have : (a : Int) < (a' : Int) := by exact_mod_cast ha
      omega
    · rw [if_neg h'] at hb'
      exact absurd hb' (by simp)
  · rw [if_neg h] at hb
    exact absurd hb (by simp)

/-- The integer list `lo, lo+1, ..., lo+n-1` (the materialized shape of
    `IntSetValue.interval`); construction is O(n) and only used for
    windows of at most 64 values. -/
def rangeInts (lo : Int) (n : Nat) : List Int :=
  (List.range n).map fun (k : Nat) => lo + (k : Int)

theorem rangeInts_pairwise (lo : Int) (n : Nat) :
    (rangeInts lo n).Pairwise fun a b => a < b := by
  unfold rangeInts
  refine List.Pairwise.map _ (fun a b hab => ?_) (pairwise_range n)
  have : (a : Int) < (b : Int) := by exact_mod_cast hab
  omega

theorem rangeInts_mem {lo : Int} {n : Nat} {x : Int} :
    x ∈ rangeInts lo n ↔ ∃ k < n, lo + (k : Int) = x := by
  unfold rangeInts
  rw [List.mem_map]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, List.mem_range.mp hk, rfl⟩
  · rintro ⟨k, hk, hk'⟩
    exact ⟨k, List.mem_range.mpr hk, hk'⟩

theorem rangeInts_length (lo : Int) (n : Nat) : (rangeInts lo n).length = n := by
  unfold rangeInts
  simp

theorem rangeInts_lo_le {lo : Int} {n : Nat} : ∀ x ∈ rangeInts lo n, lo ≤ x := by
  intro x hx
  obtain ⟨k, -, rfl⟩ := rangeInts_mem.mp hx
  omega

theorem rangeInts_all_lt {lo : Int} {n : Nat} (hn : n ≤ 64) :
    ∀ x ∈ rangeInts lo n, x - lo < 64 := by
  intro x hx
  obtain ⟨k, hk, rfl⟩ := rangeInts_mem.mp hx
  have hk' : (k : Int) < 64 := by exact_mod_cast (by omega : k < 64)
  rw [show lo + (k : Int) - lo = (k : Int) by omega]
  omega

/-- The successor decomposition of a materialized interval. -/
theorem rangeInts_cons (lo : Int) (n : Nat) :
    rangeInts lo (n + 1) = lo :: rangeInts (lo + 1) n := by
  unfold rangeInts
  rw [List.range_succ_eq_map, List.map_cons, List.map_map]
  congr 1
  · simp
  · apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply, Nat.succ_eq_add_one]
    omega

/-- The upper endpoint of a successor chain, if the whole list is one.
    Linear in the list length and allocation-free. -/
def rangeEnd? (lo : Int) : List Int → Option Int
  | [] => some lo
  | x :: xs => if x = lo + 1 then rangeEnd? x xs else none

/-- A successful chain check determines both the length and the
    materialized interval. -/
theorem rangeEnd?_spec {lo hi : Int} {xs : List Int}
    (h : rangeEnd? lo xs = some hi) :
    hi = lo + (xs.length : Int) ∧ lo :: xs = rangeInts lo (xs.length + 1) := by
  induction xs generalizing lo hi with
  | nil =>
      simp only [rangeEnd?, Option.some.injEq] at h
      subst h
      constructor
      · simp
      · simp [rangeInts]
  | cons x xs ih =>
      simp only [rangeEnd?] at h
      split at h
      · next hx =>
          obtain ⟨hhi, hlist⟩ := ih h
          constructor
          · rw [hhi, hx, List.length_cons]
            omega
          · have hlen : (x :: xs).length + 1 = xs.length + 1 + 1 := by
              rw [List.length_cons]
            rw [hlen, hlist, hx]
            exact (rangeInts_cons lo (xs.length + 1)).symm
      · simp at h

/-- The endpoint form used by `ofIntRange`'s interval shape. -/
theorem rangeEnd?_range {lo hi : Int} {xs : List Int}
    (h : rangeEnd? lo xs = some hi) :
    lo :: xs = rangeInts lo (hi - lo + 1).toNat := by
  obtain ⟨hhi, hlist⟩ := rangeEnd?_spec h
  have htoNat : (hi - lo + 1).toNat = xs.length + 1 := by
    rw [hhi]
    rw [show lo + (xs.length : Int) - lo + 1 = ((xs.length + 1 : Nat) : Int) by omega,
      Int.toNat_natCast]
  rw [htoNat, hlist]

/-- `(!b) = true` yields `b = false`. -/
theorem eq_false_of_not_eq_true {b : Bool} (h : (!b) = true) : b = false := by
  cases b <;> simp_all

/-- `(!b) = false` yields `b = true`. -/
theorem eq_true_of_not_eq_false {b : Bool} (h : (!b) = false) : b = true := by
  cases b <;> simp_all

/-! ## The compact domain type (D0 §3.4) -/

/-- Compact finite-domain representations.  This stage delivers the
    `small` bitset and the `general` fallback; the D0 `holes`
    constructor (interval + sorted holes for wide dense ranges) is
    `holes` below. -/
inductive Dom.Rep where
  /-- A 64-bit bitset over the window `offset .. offset + 63`.
      `isBool = true`: bits 0/1 denote `.bool false`/`.bool true`
      (the offset is ignored by the denotation and forced to `0` by
      `WF`; the tag keeps `Value.bool` distinct from `Value.int`).
      `isBool = false`: bit `k` denotes `.int (offset + k)`. -/
  | small (isBool : Bool) (offset : Int) (bits : UInt64)
  /-- The interval `[lo, hi]` minus the hole list `hs` (int-only, stage
      2).  `enum` is ascending; `hs` is a `List Int` (see the header
      note); `WF` requires sorted, distinct, strictly interior holes. -/
  | holes (lo hi : Int) (hs : List Int)
  /-- The general fallback: an arbitrary value list, order and
      multiplicity preserved (duplicates included). -/
  | general (vs : List Value)
  deriving Repr, BEq

/-- A compact finite domain. -/
structure Dom where
  rep : Dom.Rep
  deriving Repr, BEq

namespace Dom

/-! ### Denotation and the compact enumerations -/

/-- The Boolean values whose bit is set (bit 0 = `.bool false`,
    bit 1 = `.bool true`), in ascending order. -/
def smallBools (bits : UInt64) : List Value :=
  (List.range 2).filterMap fun k =>
    if bits.toNat.testBit k then some (.bool (k == 1)) else none

/-- The integers `off + k` whose bit `k` is set, in ascending order. -/
def smallInts (off : Int) (bits : UInt64) : List Int :=
  (List.range 64).filterMap fun k =>
    if bits.toNat.testBit k then some (off + (k : Int)) else none

/-- Compiled twin of `smallInts`: walk the bit positions downwards with an
    accumulator instead of materialising `List.range 64`.  Only set bits
    allocate a list cell. -/
def smallIntsGo (off : Int) (n : Nat) : Nat → List Int → List Int
  | 0, acc => acc
  | k+1, acc =>
      smallIntsGo off n k
        (if n.testBit k then (off + (k : Int)) :: acc else acc)

/-- Compiled twin of `smallInts` at the fixed 64-bit window. -/
def smallIntsFast (off : Int) (bits : UInt64) : List Int :=
  smallIntsGo off bits.toNat 64 []

theorem smallIntsGo_eq (off : Int) (n k : Nat) (acc : List Int) :
    smallIntsGo off n k acc =
      (List.range k).filterMap
        (fun j => if n.testBit j then some (off + (j : Int)) else none) ++ acc := by
  induction k generalizing acc with
  | zero => simp [smallIntsGo]
  | succ k ih =>
      rw [smallIntsGo, ih]
      rw [List.range_succ, List.filterMap_append]
      cases h : n.testBit k <;> simp [h]

theorem smallIntsFast_eq (off : Int) (bits : UInt64) :
    smallIntsFast off bits = smallInts off bits := by
  unfold smallIntsFast smallInts
  rw [smallIntsGo_eq]
  simp

attribute [implemented_by smallIntsFast] smallInts

/-- Membership of an integer in a hole list. -/
def memHoles (hs : List Int) (i : Int) : Bool := hs.any fun h => h == i

theorem memHoles_iff {hs : List Int} {i : Int} : memHoles hs i = true ↔ i ∈ hs := by
  unfold memHoles
  rw [List.any_eq_true]
  constructor
  · rintro ⟨h, hh, heq⟩
    rw [beq_iff_eq] at heq
    exact heq ▸ hh
  · intro hi
    exact ⟨i, hi, beq_iff_eq.mpr rfl⟩

theorem memHoles_eq_false {hs : List Int} {i : Int} : memHoles hs i = false ↔ i ∉ hs := by
  constructor
  · intro h hi
    exact absurd (memHoles_iff.mpr hi) (by rw [h]; simp)
  · intro h
    cases hb : memHoles hs i with
    | false => rfl
    | true => exact absurd (memHoles_iff.mp hb) h

/-- Linear strict-ascending check on an integer list.  The kernel
    `List.Pairwise` test used by the canonicalizers scans the whole tail at
    every step (quadratic on wide domains); this walks adjacent pairs. -/
def sortedIntsB : List Int → Bool
  | [] => true
  | [_] => true
  | x :: y :: rest => decide (x < y) && sortedIntsB (y :: rest)

theorem sortedIntsB_iff {l : List Int} :
    sortedIntsB l = true ↔ l.Pairwise (fun a b => a < b) := by
  induction l with
  | nil => simp [sortedIntsB]
  | cons x xs ih =>
      cases xs with
      | nil => simp [sortedIntsB]
      | cons y ys =>
          show (decide (x < y) && sortedIntsB (y :: ys)) = true ↔
            (x :: y :: ys).Pairwise (fun a b => a < b)
          rw [Bool.and_eq_true, ih]
          constructor
          · rintro ⟨hxy, hpw⟩
            rw [decide_eq_true_iff] at hxy
            refine List.pairwise_cons.mpr ⟨?_, hpw⟩
            intro b hb
            rcases List.mem_cons.mp hb with rfl | hb'
            · exact hxy
            · have hyb := (List.pairwise_cons.mp hpw).1 b hb'
              omega
          · intro hp
            have hhead := (List.pairwise_cons.mp hp).1
            have htail := (List.pairwise_cons.mp hp).2
            exact ⟨decide_eq_true (hhead y (List.mem_cons_self ..)), htail⟩

/-- The integers of `[lo, hi]` that are not in `hs`, ascending.
    O(span) in the interval length; the hole representation only
    materializes it through `enum`. -/
def holesInts (lo hi : Int) (hs : List Int) : List Int :=
  (List.range (hi - lo + 1).toNat).filterMap fun (k : Nat) =>
    if !(memHoles hs (lo + (k : Int))) then some (lo + (k : Int)) else none

/-- Membership in the interval-minus-holes enumeration. -/
theorem mem_holesInts {lo hi : Int} {hs : List Int} {i : Int} :
    i ∈ holesInts lo hi hs ↔ lo ≤ i ∧ i ≤ hi ∧ i ∉ hs := by
  unfold holesInts
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hkf⟩
    rw [List.mem_range] at hk
    by_cases h : (memHoles hs (lo + (k : Int))) = true
    · rw [if_neg (by simp [h])] at hkf
      exact absurd hkf (by simp)
    · rw [if_pos (by simp [h])] at hkf
      have hki : lo + (k : Int) = i := Option.some.inj hkf
      subst hki
      have hklt : (k : Int) < hi - lo + 1 := by
        rw [Int.lt_toNat] at hk
        exact hk
      refine ⟨by omega, by omega, ?_⟩
      intro hin
      exact absurd (memHoles_iff.mpr hin) (by simp [h])
  · rintro ⟨hlo, hhi, hnot⟩
    have hk : ((i - lo).toNat) < (hi - lo + 1).toNat := by
      rw [Int.toNat_lt' (by omega : 0 < (hi - lo + 1).toNat)]
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)]
      omega
    have hkval : lo + ((i - lo).toNat : Int) = i := by
      rw [Int.toNat_of_nonneg (by omega : 0 ≤ i - lo)]
      omega
    refine ⟨(i - lo).toNat, List.mem_range.mpr hk, ?_⟩
    have hcond : (!(memHoles hs (lo + ((i - lo).toNat : Int)))) = true := by
      rw [hkval]
      have hbf : memHoles hs i = false := memHoles_eq_false.mpr hnot
      rw [hbf]
      rfl
    rw [if_pos hcond, hkval]

/-- The interval enumeration is ascending. -/
theorem pairwise_holesInts (lo hi : Int) (hs : List Int) :
    (holesInts lo hi hs).Pairwise fun a b => a < b := by
  unfold holesInts
  refine List.Pairwise.filterMap _ (fun a a' ha b hb b' hb' => ?_) (pairwise_range _)
  by_cases h : (memHoles hs (lo + (a : Int))) = true
  · rw [if_neg (by simp [h])] at hb
    exact absurd hb (by simp)
  · rw [if_pos (by simp [h])] at hb
    obtain rfl := Option.some.inj hb
    by_cases h' : (memHoles hs (lo + (a' : Int))) = true
    · rw [if_neg (by simp [h'])] at hb'
      exact absurd hb' (by simp)
    · rw [if_pos (by simp [h'])] at hb'
      obtain rfl := Option.some.inj hb'
      have : (a : Int) < (a' : Int) := by exact_mod_cast ha
      omega

/-- A dense interval (no holes) enumerates exactly the corresponding
    `rangeInts` window.  This is the shape produced by `ofIntRange` for every
    declared range wider than 64 values; it lets consumers reason about (and
    compute) wide intervals without materialising them element by element. -/
theorem holesInts_nil_eq_rangeInts (lo hi : Int) :
    holesInts lo hi [] = rangeInts lo (hi - lo + 1).toNat := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_holesInts lo hi []
  · exact rangeInts_pairwise lo (hi - lo + 1).toNat
  · intro x
    rw [mem_holesInts, rangeInts_mem]
    constructor
    · rintro ⟨hxlo, hxhi, -⟩
      have hk : ((x - lo).toNat) < (hi - lo + 1).toNat := by
        rw [Int.toNat_lt' (by omega : 0 < (hi - lo + 1).toNat)]
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)]
        omega
      exact ⟨(x - lo).toNat, hk, by
        rw [Int.toNat_of_nonneg (by omega : 0 ≤ x - lo)]
        omega⟩
    · rintro ⟨k, hk, rfl⟩
      have hk' : (k : Int) < hi - lo + 1 :=
        (Int.lt_toNat (m := k) (n := hi - lo + 1)).mp hk
      exact ⟨by omega, by omega, by simp⟩

/-- Runtime twin of `holesInts`: a linear merge of the candidate window
    with the hole list.  The canonical `.holes` constructors keep the hole
    list strictly ascending (the gaps of an ascending list, or the
    deduplicated complement), so each candidate is compared against one
    list head instead of the whole list.  Non-canonical hole lists fall
    back to the reference scan, which keeps the twin equal on every
    input. -/
def holesIntsGo (n : Nat) (i : Int) (hs : List Int) : List Int :=
  match n with
  | 0 => []
  | k + 1 =>
      match hs with
      | h :: t => if i == h then holesIntsGo k (i + 1) t
          else i :: holesIntsGo k (i + 1) hs
      | [] => i :: holesIntsGo k (i + 1) []

theorem holesIntsGo_succ_nil (k : Nat) (i : Int) :
    holesIntsGo (k + 1) i [] = i :: holesIntsGo k (i + 1) [] := rfl

theorem holesIntsGo_succ_cons (k : Nat) (i h : Int) (t : List Int) :
    holesIntsGo (k + 1) i (h :: t) =
      (if i == h then holesIntsGo k (i + 1) t
       else i :: holesIntsGo k (i + 1) (h :: t)) := rfl

/-- Every emitted candidate is at least the starting point. -/
theorem holesIntsGo_all_ge (n : Nat) (i : Int) (hs : List Int) :
    ∀ x ∈ holesIntsGo n i hs, i ≤ x := by
  induction n generalizing i hs with
  | zero => intro x hx; simp [holesIntsGo] at hx
  | succ k ih =>
      cases hs with
      | nil =>
          rw [holesIntsGo_succ_nil]
          intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · omega
          · have := ih (i + 1) [] x hx
            omega
      | cons h t =>
          by_cases hcase : i = h
          · rw [holesIntsGo_succ_cons, if_pos (by simp [hcase])]
            intro x hx
            have := ih (i + 1) t x hx
            omega
          · rw [holesIntsGo_succ_cons, if_neg (by simp [hcase])]
            intro x hx
            rcases List.mem_cons.mp hx with rfl | hx
            · omega
            · have := ih (i + 1) (h :: t) x hx
              omega

/-- The merge is strictly ascending. -/
theorem holesIntsGo_pairwise (n : Nat) (i : Int) (hs : List Int) :
    (holesIntsGo n i hs).Pairwise fun a b => a < b := by
  induction n generalizing i hs with
  | zero => simp [holesIntsGo]
  | succ k ih =>
      cases hs with
      | nil =>
          rw [holesIntsGo_succ_nil]
          exact List.Pairwise.cons
            (fun b hb => by have := holesIntsGo_all_ge k (i + 1) [] b hb; omega)
            (ih (i + 1) [])
      | cons h t =>
          by_cases hcase : i = h
          · rw [holesIntsGo_succ_cons, if_pos (by simp [hcase])]
            exact ih (i + 1) t
          · rw [holesIntsGo_succ_cons, if_neg (by simp [hcase])]
            exact List.Pairwise.cons
              (fun b hb => by
                have := holesIntsGo_all_ge k (i + 1) (h :: t) b hb
                omega)
              (ih (i + 1) (h :: t))

/-- Membership in the merge, for a strictly ascending hole list all of
    whose members lie at or above the starting point. -/
theorem mem_holesIntsGo {n : Nat} {i x : Int} {hs : List Int}
    (hsort : hs.Pairwise fun a b => a < b)
    (hlow : ∀ h ∈ hs, i ≤ h) :
    x ∈ holesIntsGo n i hs ↔ i ≤ x ∧ x < i + (n : Int) ∧ x ∉ hs := by
  induction n generalizing i hs with
  | zero =>
      constructor
      · intro hx
        exact absurd hx (by simp [holesIntsGo])
      · rintro ⟨h1, h2, -⟩
        exfalso
        omega
  | succ k ih =>
      cases hs with
      | nil =>
          rw [holesIntsGo_succ_nil,
            List.mem_cons,
            ih (hs := []) List.Pairwise.nil (by simp)]
          constructor
          · rintro (rfl | ⟨h1, h2, -⟩)
            · exact ⟨by omega, by push_cast; omega, by simp⟩
            · exact ⟨by omega, by push_cast at h2 ⊢; omega, by simp⟩
          · rintro ⟨h1, h2, -⟩
            by_cases hlt : i < x
            · exact Or.inr ⟨hlt, by push_cast at h2 ⊢; omega, by simp⟩
            · have hxi : x = i := by omega
              exact Or.inl hxi
      | cons h t =>
          have ht : t.Pairwise fun a b => a < b := (List.pairwise_cons.mp hsort).2
          have hht : ∀ y ∈ t, h < y := (List.pairwise_cons.mp hsort).1
          have hih : i ≤ h := hlow h (by simp)
          by_cases hcase : i = h
          · rw [holesIntsGo_succ_cons, if_pos (by simp [hcase]),
              ih (i := i + 1) (hs := t) ht ?_]
            · constructor
              · rintro ⟨h1, h2, h3⟩
                refine ⟨by omega, by push_cast at h2 ⊢; omega, ?_⟩
                simp only [List.mem_cons, not_or]
                exact ⟨by omega, h3⟩
              · rintro ⟨h1, h2, h3⟩
                simp only [List.mem_cons, not_or] at h3
                exact ⟨by omega, by push_cast at h2 ⊢; omega, h3.2⟩
            · intro y hy
              have := hht y hy
              omega
          · have hlt : i < h := by omega
            rw [holesIntsGo_succ_cons, if_neg (by simp [hcase]),
              List.mem_cons,
              ih (i := i + 1) (hs := h :: t) hsort ?_]
            · constructor
              · rintro (hxi | ⟨h1, h2, h3⟩)
                · refine ⟨by omega, by push_cast; omega, ?_⟩
                  simp only [List.mem_cons, not_or]
                  exact ⟨by omega, fun hin => absurd (hht x hin) (by omega)⟩
                · exact ⟨by omega, by push_cast at h2 ⊢; omega, h3⟩
              · rintro ⟨h1, h2, h3⟩
                by_cases hltx : i < x
                · exact Or.inr ⟨hltx, by push_cast at h2 ⊢; omega, h3⟩
                · have hxi : x = i := by omega
                  exact Or.inl hxi
            · intro y hy
              rcases List.mem_cons.mp hy with rfl | hy
              · omega
              · have := hht y hy
                omega

/-- The window endpoint: for candidates at or above `lo`, the last one is
    `hi`. -/
theorem holesSpan_endpoint {lo hi x : Int} (hlo : lo ≤ x) :
    x < lo + ((hi - lo + 1).toNat : Int) ↔ x ≤ hi := by
  constructor
  · intro h
    by_cases hle : lo ≤ hi
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)] at h
      omega
    · exfalso
      have hz : (hi - lo + 1).toNat = 0 := Int.toNat_eq_zero.mpr (by omega)
      rw [hz] at h
      push_cast at h
      omega
  · intro h
    have hle : lo ≤ hi := by omega
    rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)]
    omega

/-- Tail-recursive runtime twin of `holesIntsGo`: emitted candidates are
    accumulated in reverse order and reversed at the end, so every recursive
    call is a tail call.  The structural version below is kept as the
    specification because its equations are the convenient ones for the
    membership and ordering proofs. -/
def holesIntsGoTR (n : Nat) (i : Int) (hs : List Int) (acc : List Int) : List Int :=
  match n with
  | 0 => acc.reverse
  | k + 1 =>
      match hs with
      | h :: t => if i == h then holesIntsGoTR k (i + 1) t acc
          else holesIntsGoTR k (i + 1) hs (i :: acc)
      | [] => holesIntsGoTR k (i + 1) [] (i :: acc)

theorem holesIntsGoTR_succ_nil (k : Nat) (i : Int) (acc : List Int) :
    holesIntsGoTR (k + 1) i [] acc = holesIntsGoTR k (i + 1) [] (i :: acc) := rfl

theorem holesIntsGoTR_succ_cons (k : Nat) (i h : Int) (t acc : List Int) :
    holesIntsGoTR (k + 1) i (h :: t) acc =
      (if i == h then holesIntsGoTR k (i + 1) t acc
       else holesIntsGoTR k (i + 1) (h :: t) (i :: acc)) := rfl

/-- The accumulator twin returns the reversed accumulator followed by the
    structural enumeration. -/
theorem holesIntsGoTR_eq (n : Nat) (i : Int) (hs : List Int) (acc : List Int) :
    holesIntsGoTR n i hs acc = acc.reverse ++ holesIntsGo n i hs := by
  induction n generalizing i hs acc with
  | zero => simp [holesIntsGoTR, holesIntsGo]
  | succ k ih =>
      cases hs with
      | nil =>
          rw [holesIntsGoTR_succ_nil, ih, holesIntsGo_succ_nil]
          simp [List.reverse_cons, List.append_assoc]
      | cons h t =>
          by_cases hcase : i = h
          · rw [holesIntsGoTR_succ_cons, if_pos (by simp [hcase]), ih,
              holesIntsGo_succ_cons, if_pos (by simp [hcase])]
          · rw [holesIntsGoTR_succ_cons, if_neg (by simp [hcase]), ih,
              holesIntsGo_succ_cons, if_neg (by simp [hcase])]
            simp [List.reverse_cons, List.append_assoc]

theorem holesIntsGoTR_nil_acc (n : Nat) (i : Int) (hs : List Int) :
    holesIntsGoTR n i hs [] = holesIntsGo n i hs := by
  rw [holesIntsGoTR_eq]
  simp

/-- Guarded runtime twin of `holesInts`. -/
def holesIntsFast (lo hi : Int) (hs : List Int) : List Int :=
  if sortedIntsB hs && hs.all (fun h => decide (lo ≤ h)) then
    holesIntsGoTR (hi - lo + 1).toNat lo hs []
  else holesInts lo hi hs

theorem holesIntsFast_eq (lo hi : Int) (hs : List Int) :
    holesIntsFast lo hi hs = holesInts lo hi hs := by
  unfold holesIntsFast
  by_cases hg : (sortedIntsB hs && hs.all (fun h => decide (lo ≤ h))) = true
  · rw [if_pos hg, holesIntsGoTR_nil_acc]
    rw [Bool.and_eq_true] at hg
    obtain ⟨hsort, hlow⟩ := hg
    have hpair : hs.Pairwise fun a b => a < b := sortedIntsB_iff.mp hsort
    have hall : ∀ h ∈ hs, lo ≤ h := by
      intro h hh
      exact of_decide_eq_true (List.all_eq_true.mp hlow h hh)
    apply eq_of_pairwise_lt_of_mem_iff
      (holesIntsGo_pairwise _ _ _) (pairwise_holesInts lo hi hs)
    intro x
    rw [mem_holesIntsGo hpair hall, mem_holesInts]
    constructor
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (holesSpan_endpoint h1).mp h2, h3⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨h1, (holesSpan_endpoint h1).mpr h2, h3⟩
  · rw [if_neg hg]

attribute [implemented_by holesIntsFast] holesInts

/-- The order- and multiplicity-preserving denotation (D0 (D2)):
    the enumerated values of the domain, ascending on the compact
    cases and exactly the stored list on `general`. -/
def enum (d : Dom) : List Value :=
  match d.rep with
  | .small true _ bits => smallBools bits
  | .small false off bits => (smallInts off bits).map Value.int
  | .holes lo hi hs => (holesInts lo hi hs).map Value.int
  | .general vs => vs

/-- Integer view of a value; mirrors `Value.intView`
    (`LeanFzn.Solver.Propagation`).  Kept as a local `def` so that the
    representation core stays importable from `Core`; the equality to
    the shared `Value.intView` is `valueIntView_eq_value_intView`. -/
def valueIntView : Value → Option Int
  | .int i => some i
  | .bool b => some (if b then 1 else 0)
  | _ => none

/-! ### Membership of the compact enumerations -/

theorem mem_smallBools {bits : UInt64} {v : Value} :
    v ∈ smallBools bits ↔
      ∃ b : Bool, v = .bool b ∧ bits.toNat.testBit (if b then 1 else 0) = true := by
  unfold smallBools
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hkf⟩
    rw [List.mem_range] at hk
    by_cases h : bits.toNat.testBit k = true
    · rw [if_pos h] at hkf
      refine ⟨k == 1, (Option.some.inj hkf).symm, ?_⟩
      cases hb : (k == 1) with
      | false =>
          have hk0 : k = 0 := by
            have hne : ¬(k = 1) := by
              intro hk1
              rw [hk1] at hb
              simp at hb
            omega
          subst hk0
          simpa using h
      | true =>
          have hk1 : k = 1 := by simpa [beq_iff_eq] using hb
          subst hk1
          simpa using h
    · rw [if_neg h] at hkf
      exact absurd hkf (by simp)
  · rintro ⟨b, rfl, hb⟩
    refine ⟨if b then 1 else 0, ?_, ?_⟩
    · cases b <;> simp
    · cases b <;> simpa using hb

theorem mem_smallBools_bool (bits : UInt64) (b : Bool) :
    (.bool b : Value) ∈ smallBools bits ↔ bits.toNat.testBit (if b then 1 else 0) = true := by
  rw [mem_smallBools]
  constructor
  · rintro ⟨b', heq, hb⟩
    rw [Value.bool.injEq] at heq
    rw [heq]
    exact hb
  · intro hb
    exact ⟨b, rfl, hb⟩

theorem eq_bool_of_mem_smallBools {bits : UInt64} {v : Value}
    (h : v ∈ smallBools bits) : ∃ b : Bool, v = .bool b := by
  rw [mem_smallBools] at h
  obtain ⟨b, hb, _⟩ := h
  exact ⟨b, hb⟩

/-- Membership of a value in the packed integer list. -/
theorem mem_smallInts {off : Int} {bits : UInt64} {x : Int} :
    x ∈ smallInts off bits ↔
      ∃ k < 64, bits.toNat.testBit k = true ∧ off + (k : Int) = x := by
  unfold smallInts
  rw [List.mem_filterMap]
  constructor
  · rintro ⟨k, hk, hkf⟩
    rw [List.mem_range] at hk
    by_cases h : bits.toNat.testBit k = true
    · rw [if_pos h] at hkf
      exact ⟨k, hk, h, Option.some.inj hkf⟩
    · rw [if_neg h] at hkf
      exact absurd hkf (by simp)
  · rintro ⟨k, hk, hp, hx⟩
    exact ⟨k, List.mem_range.mpr hk, by rw [if_pos hp, hx]⟩

/-- Membership of a window index in the packed integer list. -/
theorem mem_smallInts_iff {off : Int} {bits : UInt64} {k : Nat} (hk : k < 64) :
    off + (k : Int) ∈ smallInts off bits ↔ bits.toNat.testBit k = true := by
  rw [mem_smallInts]
  constructor
  · rintro ⟨j, _, hp, heq⟩
    have hjk : j = k := by omega
    subst hjk
    exact hp
  · intro hp
    exact ⟨k, hk, hp, rfl⟩

/-- Membership of an integer in the packed list, in `offset/bound`
    form (the `memBool` specification for the `small` integer case). -/
theorem mem_smallInts_int {off : Int} {bits : UInt64} {i : Int} :
    i ∈ smallInts off bits ↔
      off ≤ i ∧ i - off < (64 : Int) ∧ bits.toNat.testBit (i - off).toNat = true := by
  rw [mem_smallInts]
  constructor
  · rintro ⟨k, hk, hp, heq⟩
    subst heq
    refine ⟨by omega, ?_, ?_⟩
    · have hk' : (k : Int) < 64 := by exact_mod_cast hk
      omega
    · rw [show off + (k : Int) - off = (k : Int) by omega, Int.toNat_natCast]
      exact hp
  · rintro ⟨hle, hlt, hbit⟩
    refine ⟨(i - off).toNat, ?_, hbit, ?_⟩
    · have h' : ((i - off).toNat : Int) < 64 := by
        rw [Int.toNat_of_nonneg (by omega)]
        exact hlt
      exact_mod_cast h'
    · rw [Int.toNat_of_nonneg (by omega)]
      omega

/-- The packed list is ascending. -/
theorem pairwise_smallInts (off : Int) (bits : UInt64) :
    (smallInts off bits).Pairwise fun a b => a < b := by
  unfold smallInts
  refine List.Pairwise.filterMap _ (fun a a' ha b hb b' hb' => ?_) (pairwise_range 64)
  by_cases h : bits.toNat.testBit a = true
  · rw [if_pos h] at hb
    obtain rfl := Option.some.inj hb
    by_cases h' : bits.toNat.testBit a' = true
    · rw [if_pos h'] at hb'
      obtain rfl := Option.some.inj hb'
      have : (a : Int) < (a' : Int) := by exact_mod_cast ha
      omega
    · rw [if_neg h'] at hb'
      exact absurd hb' (by simp)
  · rw [if_neg h] at hb
    exact absurd hb (by simp)

/-! ### Membership of the interval-with-holes enumeration -/

/-- Membership of an `.int` value in the interval-with-holes enum. -/
theorem mem_holes_enum_int {lo hi : Int} {hs : List Int} {i : Int} :
    (Value.int i) ∈ enum ⟨.holes lo hi hs⟩ ↔ lo ≤ i ∧ i ≤ hi ∧ i ∉ hs := by
  show (Value.int i) ∈ (holesInts lo hi hs).map Value.int ↔ _
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    rw [Value.int.injEq] at heq
    rw [← heq]
    exact mem_holesInts.mp hx
  · intro h
    exact ⟨i, mem_holesInts.mpr h, rfl⟩

theorem eq_int_of_mem_holes_enum {lo hi : Int} {hs : List Int} {v : Value}
    (h : v ∈ enum ⟨.holes lo hi hs⟩) : ∃ i : Int, v = .int i := by
  change v ∈ (holesInts lo hi hs).map Value.int at h
  obtain ⟨i, -, heq⟩ := List.mem_map.mp h
  exact ⟨i, heq.symm⟩

/-- Membership of an `.int` value in a mapped integer list. -/
theorem mem_map_int {L : List Int} {i : Int} :
    (Value.int i) ∈ L.map Value.int ↔ i ∈ L := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    rw [Value.int.injEq] at heq
    rwa [← heq]
  · intro h
    exact ⟨i, h, rfl⟩

/-- Membership of a single gap segment: the integers strictly between
    `cur` and `next`. -/
theorem mem_rangeInts_gap (cur next x : Int) :
    x ∈ rangeInts (cur + 1) (next - cur - 1).toNat ↔ cur < x ∧ x < next := by
  rw [rangeInts_mem]
  constructor
  · rintro ⟨k, hk, hkx⟩
    have hn : ((next - cur - 1).toNat : Int) = next - cur - 1 := by omega
    have hk' : (k : Int) < next - cur - 1 := by
      rw [← hn]
      exact_mod_cast hk
    omega
  · rintro ⟨h1, h2⟩
    have hpos : 0 ≤ next - cur - 1 := by omega
    refine ⟨((x - cur - 1).toNat), ?_, ?_⟩
    · rw [Int.toNat_lt' (by omega : 0 < (next - cur - 1).toNat)]
      rw [Int.toNat_of_nonneg hpos]
      omega
    · rw [Int.toNat_of_nonneg (by omega : 0 ≤ x - cur - 1)]
      omega

/-- The integers strictly between consecutive entries of an ascending list
    (the complement of the list in its own span when the endpoints are
    members).  Built gap-by-gap: linear in the list plus the holes, unlike
    `holesInts` whose scan tests every span candidate against the full list
    (the quadratic constructor cost measured in PLAN P6). -/
def gaps (cur : Int) : List Int → List Int
  | [] => []
  | next :: rest =>
      if next - cur ≤ 1 then gaps next rest
      else rangeInts (cur + 1) (next - cur - 1).toNat ++ gaps next rest

theorem exists_mem_cons_gap {x v : Int} {rest : List Int} :
    (∃ u, (u = v ∨ u ∈ rest) ∧ x < u) ↔ x < v ∨ ∃ u, u ∈ rest ∧ x < u := by
  constructor
  · rintro ⟨u, hu, hxu⟩
    rcases hu with rfl | hu
    · exact Or.inl hxu
    · exact Or.inr ⟨u, hu, hxu⟩
  · rintro (h | ⟨u, hu, hxu⟩)
    · exact ⟨v, Or.inl rfl, h⟩
    · exact ⟨u, Or.inr hu, hxu⟩

theorem mem_gaps {cur x : Int} {vs : List Int}
    (hsorted : vs.Pairwise fun a b => a < b) (hcur : ∀ v ∈ vs, cur < v) :
    x ∈ gaps cur vs ↔ cur < x ∧ (∃ v ∈ vs, x < v) ∧ x ∉ vs := by
  induction vs generalizing cur with
  | nil => simp [gaps]
  | cons v rest ih =>
      have hrest : rest.Pairwise fun a b => a < b := (List.pairwise_cons.mp hsorted).2
      have hv : ∀ y ∈ rest, v < y := (List.pairwise_cons.mp hsorted).1
      have hcurv : cur < v := hcur v (by simp)
      rw [gaps]
      by_cases hgap : v - cur ≤ 1
      · rw [if_pos hgap, ih hrest hv]
        simp only [List.mem_cons, not_or]
        rw [exists_mem_cons_gap]
        constructor
        · rintro ⟨h1, h2, h3⟩
          refine ⟨by omega, Or.inr h2, by omega, h3⟩
        · rintro ⟨h1, h2, h3, h4⟩
          have hvx : v < x := by
            rcases h2 with h2v | h2
            · omega
            · omega
          exact ⟨hvx, by
            rcases h2 with h2v | h2
            · omega
            · exact h2, h4⟩
      · rw [if_neg hgap, List.mem_append, mem_rangeInts_gap, ih hrest hv]
        simp only [List.mem_cons, not_or]
        rw [exists_mem_cons_gap]
        constructor
        · rintro (⟨h1, h2⟩ | ⟨h1, h2, h3⟩)
          · refine ⟨by omega, Or.inl h2, by omega, ?_⟩
            intro hmem
            exact absurd (hv x hmem) (by omega)
          · exact ⟨by omega, Or.inr h2, by omega, h3⟩
        · rintro ⟨h1, h2, h3, h4⟩
          by_cases hxv : x < v
          · exact Or.inl ⟨h1, hxv⟩
          · refine Or.inr ⟨by omega, ?_, h4⟩
            rcases h2 with h2v | h2
            · omega
            · exact h2

theorem pairwise_gaps {cur : Int} {vs : List Int}
    (hsorted : vs.Pairwise fun a b => a < b) (hcur : ∀ v ∈ vs, cur < v) :
    (gaps cur vs).Pairwise fun a b => a < b := by
  induction vs generalizing cur with
  | nil => simp [gaps]
  | cons v rest ih =>
      have hrest : rest.Pairwise fun a b => a < b := (List.pairwise_cons.mp hsorted).2
      have hv : ∀ y ∈ rest, v < y := (List.pairwise_cons.mp hsorted).1
      have hcurv : cur < v := hcur v (by simp)
      rw [gaps]
      by_cases hgap : v - cur ≤ 1
      · rw [if_pos hgap]
        exact ih hrest hv
      · rw [if_neg hgap, List.pairwise_append]
        refine ⟨rangeInts_pairwise _ _, ih hrest hv, ?_⟩
        intro a ha b hb
        have ha' : a < v := (mem_rangeInts_gap cur v a).mp ha |>.2
        have hb' : v < b := (mem_gaps hrest hv).mp hb |>.1
        omega

/-- The last element of an ascending list is its maximum. -/
theorem getLast?_spec {l : List Int} (hsorted : l.Pairwise fun a b => a < b) {y : Int}
    (hy : l.getLast? = some y) : y ∈ l ∧ ∀ x ∈ l, x ≤ y := by
  induction l with
  | nil => simp at hy
  | cons a t ih =>
      cases t with
      | nil =>
          have hay : a = y := by simpa using hy
          subst hay
          exact ⟨List.mem_cons_self .., fun x hx =>
            by rw [List.mem_singleton] at hx; omega⟩
      | cons b u =>
          have htail : (b :: u).getLast? = some y := by
            simpa using hy
          have hsorted' : (b :: u).Pairwise fun a b => a < b := List.Pairwise.tail hsorted
          obtain ⟨hymem, hymax⟩ := ih hsorted' htail
          have hab : a < b := (List.pairwise_cons.mp hsorted).1 b (by simp)
          refine ⟨List.mem_cons_of_mem _ hymem, fun x hx => ?_⟩
          rcases List.mem_cons.mp hx with rfl | hx'
          · have hby : b ≤ y := hymax b (by simp)
            omega
          · exact hymax x hx'

/-- On a sorted list whose head is `lo` and last element is `hi`, the
    gap enumeration is exactly the `holesInts` complement. -/
theorem gaps_eq_holesInts {lo hi : Int} {xs : List Int}
    (hpair : (lo :: xs).Pairwise fun a b => a < b)
    (hl : (lo :: xs).getLast? = some hi) :
    gaps lo xs = holesInts lo hi (lo :: xs) := by
  have hrest : xs.Pairwise fun a b => a < b := (List.pairwise_cons.mp hpair).2
  have hcur : ∀ v ∈ xs, lo < v := (List.pairwise_cons.mp hpair).1
  have hlast := getLast?_spec hpair hl
  refine eq_of_pairwise_lt_of_mem_iff (pairwise_gaps hrest hcur)
    (pairwise_holesInts lo hi (lo :: xs)) ?_
  intro i
  rw [mem_gaps hrest hcur, mem_holesInts]
  constructor
  · rintro ⟨h1, ⟨v, hv, hiv⟩, h3⟩
    refine ⟨by omega, ?_, ?_⟩
    · have := hlast.2 v (List.mem_cons_of_mem _ hv)
      omega
    · rw [List.mem_cons]
      exact not_or.mpr ⟨by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩
    have h3mem : ¬ i ∈ (lo :: xs) := h3
    rw [List.mem_cons] at h3
    obtain ⟨hne_lo, hxs⟩ := not_or.mp h3
    have hmem_hi : hi ∈ (lo :: xs) := List.mem_of_getLast? hl
    have hne_hi : i ≠ hi := by
      intro h
      subst h
      exact absurd hmem_hi h3mem
    have hlt : lo < i := by omega
    have hihi : i < hi := by omega
    refine ⟨hlt, ⟨hi, ?_, hihi⟩, hxs⟩
    rw [List.mem_cons] at hmem_hi
    rcases hmem_hi with h | h
    · exfalso; omega
    · exact h

/-- A sorted list whose maximum is a member ends with that maximum. -/
theorem getLast?_eq_some_of_max {l : List Int} (hsorted : l.Pairwise fun a b => a < b)
    {y : Int} (hmem : y ∈ l) (hmax : ∀ x ∈ l, x ≤ y) : l.getLast? = some y := by
  induction l with
  | nil => simp at hmem
  | cons a t ih =>
      cases t with
      | nil =>
          rw [List.mem_singleton] at hmem
          subst hmem
          rfl
      | cons b u =>
          have hsorted' : (b :: u).Pairwise fun a b => a < b := List.Pairwise.tail hsorted
          have htail_mem : y ∈ b :: u := by
            rcases List.mem_cons.mp hmem with hay | hy'
            · exfalso
              have hab : a < b := (List.pairwise_cons.mp hsorted).1 b (by simp)
              have hby : b ≤ y := hmax b (by simp)
              omega
            · exact hy'
          have htail_max : ∀ x ∈ b :: u, x ≤ y := fun x hx => hmax x (List.mem_cons_of_mem _ hx)
          simpa using ih hsorted' htail_mem htail_max

/-- The first element of an ascending list is its minimum. -/
theorem head?_eq_of_min {l : List Int} (hsorted : l.Pairwise fun a b => a < b)
    {lo : Int} (hmem : lo ∈ l) (hmin : ∀ x ∈ l, lo ≤ x) : l.head? = some lo := by
  cases hL : l with
  | nil => rw [hL] at hmem; simp at hmem
  | cons a t =>
      have ha : lo ≤ a := hmin a (by rw [hL]; exact List.mem_cons_self ..)
      have hsorted' : (a :: t).Pairwise fun a b => a < b := by rwa [← hL]
      rcases List.mem_cons.mp (by rw [← hL]; exact hmem) with heq | hmem'
      · rw [← heq]
        rfl
      · have : a < lo := (List.pairwise_cons.mp hsorted').1 lo hmem'
        omega

/-- The interval complement is an involution on ascending lists inside
    the interval. -/
theorem holesInts_holesInts {lo hi : Int} {L : List Int}
    (hsorted : L.Pairwise fun a b => a < b)
    (hlo : ∀ x ∈ L, lo ≤ x) (hhi : ∀ x ∈ L, x ≤ hi) :
    holesInts lo hi (holesInts lo hi L) = L := by
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_holesInts ..
  · exact hsorted
  · intro x
    rw [mem_holesInts]
    constructor
    · rintro ⟨hxlo, hxhi, hxnot⟩
      by_cases hxL : x ∈ L
      · exact hxL
      · exact absurd (mem_holesInts.mpr ⟨hxlo, hxhi, hxL⟩) hxnot
    · intro hxL
      exact ⟨hlo x hxL, hhi x hxL, fun hxnot => (mem_holesInts.mp hxnot).2.2 hxL⟩

/-- Counting identity for the hole complement: the number of in-span
    integers plus the number of holes is the span.  This is the
    cardinality fact behind both the density test and the cheap
    construction guard. -/
theorem length_holesInts_add {lo hi : Int} {hs : List Int}
    (hsorted : hs.Pairwise fun a b => a < b)
    (hin : ∀ h ∈ hs, lo ≤ h ∧ h ≤ hi) :
    (holesInts lo hi hs).length + hs.length = (hi - lo + 1).toNat := by
  have hY : ((List.range (hi - lo + 1).toNat).filterMap fun (k : Nat) =>
        if memHoles hs (lo + (k : Int)) then some (lo + (k : Int)) else none) = hs := by
    apply eq_of_pairwise_lt_of_mem_iff
    · exact pairwise_filterMap_range _ _ _
    · exact hsorted
    · intro x
      rw [List.mem_filterMap]
      constructor
      · rintro ⟨k, hk, hkf⟩
        rw [List.mem_range] at hk
        by_cases h : memHoles hs (lo + (k : Int)) = true
        · rw [if_pos h] at hkf
          rw [← Option.some.inj hkf]
          exact memHoles_iff.mp h
        · rw [if_neg h] at hkf
          exact absurd hkf (by simp)
      · intro hx
        obtain ⟨hxlo, hxhi⟩ := hin x hx
        have hxk : ((x - lo).toNat) < (hi - lo + 1).toNat := by
          rw [Int.toNat_lt' (by omega : 0 < (hi - lo + 1).toNat)]
          rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)]
          omega
        refine ⟨(x - lo).toNat, List.mem_range.mpr hxk, ?_⟩
        have hkval : lo + ((x - lo).toNat : Int) = x := by
          rw [Int.toNat_of_nonneg (by omega : 0 ≤ x - lo)]
          omega
        rw [if_pos (by rw [hkval]; exact memHoles_iff.mpr hx), hkval]
  have hYlen : ((List.range (hi - lo + 1).toNat).filter
      (fun (k : Nat) => memHoles hs (lo + (k : Int)))).length = hs.length := by
    rw [← length_filterMap_if (l := List.range (hi - lo + 1).toNat)
      (p := fun (k : Nat) => memHoles hs (lo + (k : Int)))
      (f := fun k => lo + (k : Int))]
    rw [hY]
  have hp := length_filter_add_length_filter_not (List.range (hi - lo + 1).toNat)
    (fun (k : Nat) => memHoles hs (lo + (k : Int)))
  rw [List.length_range] at hp
  have hlen : (holesInts lo hi hs).length =
      ((List.range (hi - lo + 1).toNat).filter
        (fun (k : Nat) => !(memHoles hs (lo + (k : Int))))).length := by
    unfold holesInts
    rw [length_filterMap_if]
  rw [hlen]
  omega

/-! ### Decoding the `general`-shaped value lists -/

/-- Decode an all-`.int` value list. -/
def decodeInts : List Value → Option (List Int)
  | [] => some []
  | .int x :: rest => (decodeInts rest).map (x :: ·)
  | _ => none

theorem decodeInts_map (xs : List Int) : decodeInts (xs.map Value.int) = some xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, decodeInts, ih, Option.map_some]

theorem decodeInts_spec {vs : List Value} {xs : List Int} (h : decodeInts vs = some xs) :
    vs = xs.map Value.int := by
  induction vs generalizing xs with
  | nil =>
      have h' : xs = [] := (Option.some.inj h).symm
      subst h'
      rfl
  | cons v rest ih =>
      cases v with
      | int x =>
          rw [decodeInts] at h
          cases hd : decodeInts rest with
          | none => rw [hd] at h; cases h
          | some ls =>
              rw [hd] at h
              have hxs : xs = x :: ls := (Option.some.inj h).symm
              subst hxs
              rw [List.map_cons, ih hd]
      | bool b => simp [decodeInts] at h
      | setOfInt s => simp [decodeInts] at h
      | array a => simp [decodeInts] at h

/-- The canonical compact forms for the Boolean canonical lists
    (`[]` is handled by the `general` fallback). -/
def ofBoolValues? : List Value → Option Dom
  | [.bool false] => some ⟨.small true 0 1⟩
  | [.bool true] => some ⟨.small true 0 2⟩
  | [.bool false, .bool true] => some ⟨.small true 0 3⟩
  | _ => none

theorem ofBoolValues?_spec {vs : List Value} {d : Dom}
    (h : ofBoolValues? vs = some d) :
    (vs = [.bool false] ∧ d = ⟨.small true 0 1⟩) ∨
    (vs = [.bool true] ∧ d = ⟨.small true 0 2⟩) ∨
    (vs = [.bool false, .bool true] ∧ d = ⟨.small true 0 3⟩) := by
  cases vs with
  | nil => simp [ofBoolValues?] at h
  | cons v rest =>
      cases v with
      | bool b =>
          cases b with
          | false =>
              cases rest with
              | nil =>
                  exact Or.inl ⟨rfl, (Option.some.inj (by simpa [ofBoolValues?] using h)).symm⟩
              | cons w rest' =>
                  cases w with
                  | bool b2 =>
                      cases b2 with
                      | false => simp [ofBoolValues?] at h
                      | true =>
                          cases rest' with
                          | nil =>
                              exact Or.inr (Or.inr
                                ⟨rfl, (Option.some.inj (by simpa [ofBoolValues?] using h)).symm⟩)
                          | cons _ _ => simp [ofBoolValues?] at h
                  | int i => simp [ofBoolValues?] at h
                  | setOfInt s => simp [ofBoolValues?] at h
                  | array a => simp [ofBoolValues?] at h
          | true =>
              cases rest with
              | nil =>
                  exact Or.inr (Or.inl
                    ⟨rfl, (Option.some.inj (by simpa [ofBoolValues?] using h)).symm⟩)
              | cons _ _ => simp [ofBoolValues?] at h
      | int i => simp [ofBoolValues?] at h
      | setOfInt s => simp [ofBoolValues?] at h
      | array a => simp [ofBoolValues?] at h

/-- The canonical compact form for ascending, duplicate-free integer
    lists inside a 64-wide window. -/
def ofSmallInts? : List Value → Option Dom
  | .int lo :: rest =>
      match decodeInts rest with
      | some xs =>
          if sortedIntsB (lo :: xs) &&
              (lo :: xs).all (fun x => decide (x - lo < 64)) then
            some ⟨.small false lo (UInt64.ofNat (intsToBits lo (lo :: xs)))⟩
          else none
      | none => none
  | _ => none

theorem ofSmallInts?_spec {vs : List Value} {d : Dom}
    (h : ofSmallInts? vs = some d) :
    ∃ lo : Int, ∃ xs : List Int,
      vs = (lo :: xs).map Value.int ∧
      (lo :: xs).Pairwise (fun a b => a < b) ∧
      (∀ x ∈ lo :: xs, x - lo < 64) ∧
      d = ⟨.small false lo (UInt64.ofNat (intsToBits lo (lo :: xs)))⟩ := by
  cases vs with
  | nil => simp [ofSmallInts?] at h
  | cons v rest =>
      cases v with
      | int lo =>
          simp only [ofSmallInts?] at h
          cases hd : decodeInts rest with
          | none => rw [hd] at h; cases h
          | some xs =>
              rw [hd] at h
              dsimp only at h
              by_cases hcond : (sortedIntsB (lo :: xs) &&
                  (lo :: xs).all (fun x => decide (x - lo < 64))) = true
              · rw [if_pos hcond] at h
                have hd_eq := decodeInts_spec hd
                have hpair : sortedIntsB (lo :: xs) = true := by
                  have h' := hcond
                  rw [Bool.and_eq_true] at h'
                  exact h'.1
                have hall : (lo :: xs).all (fun x => decide (x - lo < 64)) = true := by
                  have h' := hcond
                  rw [Bool.and_eq_true] at h'
                  exact h'.2
                refine ⟨lo, xs, ?_, ?_, ?_, (Option.some.inj h).symm⟩
                · rw [hd_eq]; rfl
                · exact (sortedIntsB_iff).mp hpair
                · intro x hx
                  exact of_decide_eq_true (List.all_eq_true.mp hall x hx)
              · rw [if_neg hcond] at h
                exact absurd h.symm (by simp)
      | bool b => simp [ofSmallInts?] at h
      | setOfInt s => simp [ofSmallInts?] at h
      | array a => simp [ofSmallInts?] at h

/-- The canonical hole form for an ascending list `lo :: xs` with last
    element `hi`.  The holes are generated gap-by-gap (linear in the list
    plus the holes), guarded first by a cheap span bound `span <= 4 * n`
    so that sparse wide enumerations do not materialize a huge complement,
    then by the normal-form density test `#holes * 4 <= span`. -/
def mkHoles? (lo hi : Int) (xs : List Int) : Option Dom :=
  let span := (hi - lo + 1).toNat
  if decide (span ≤ 4 * (lo :: xs).length) then
    let hs := gaps lo xs
    if decide (hs.length * 4 ≤ span) then
      some ⟨.holes lo hi hs⟩
    else none
  else none

theorem mkHoles?_spec {lo hi : Int} {xs : List Int} {d : Dom}
    (h : mkHoles? lo hi xs = some d) :
    (hi - lo + 1).toNat ≤ 4 * (lo :: xs).length ∧
    (gaps lo xs).length * 4 ≤ (hi - lo + 1).toNat ∧
    d = ⟨.holes lo hi (gaps lo xs)⟩ := by
  unfold mkHoles? at h
  dsimp only at h
  by_cases hcheap : decide ((hi - lo + 1).toNat ≤ 4 * (lo :: xs).length) = true
  · rw [if_pos hcheap] at h
    by_cases hdens : decide ((gaps lo xs).length * 4 ≤ (hi - lo + 1).toNat) = true
    · rw [if_pos hdens] at h
      simp only [Option.some.injEq] at h
      exact ⟨of_decide_eq_true hcheap, of_decide_eq_true hdens, h.symm⟩
    · rw [if_neg hdens] at h
      exact absurd h.symm (by simp)
  · rw [if_neg hcheap] at h
    exact absurd h.symm (by simp)

/-- Constructor form of `mkHoles?` when the span guard and the density
    test are known and the computed complement is the expected `hs`. -/
theorem mkHoles?_eq_some {lo hi : Int} {xs hs : List Int}
    (hcheap : (hi - lo + 1).toNat ≤ 4 * (lo :: xs).length)
    (hg : gaps lo xs = hs)
    (hdens : hs.length * 4 ≤ (hi - lo + 1).toNat) :
    mkHoles? lo hi xs = some ⟨.holes lo hi hs⟩ := by
  unfold mkHoles?
  dsimp only
  rw [if_pos (decide_eq_true hcheap)]
  rw [hg, if_pos (decide_eq_true hdens)]

/-- The canonical compact form for ascending, duplicate-free integer
    lists over an interval wider than 64 with at most a quarter of the
    span missing (the stage-2 interval-with-holes case).  The holes are
    the complement of the list inside `[head, last]`; the density test
    is `holes * 4 <= span`. -/
def ofHoles? : List Value → Option Dom
  | .int lo :: rest =>
      match decodeInts rest with
      | some xs =>
          match (lo :: xs).getLast? with
          | some hi =>
              if sortedIntsB (lo :: xs) &&
                  decide (64 < (hi - lo + 1).toNat) then
                mkHoles? lo hi xs
              else none
          | none => none
      | none => none
  | _ => none

theorem ofHoles?_spec {vs : List Value} {d : Dom}
    (h : ofHoles? vs = some d) :
    ∃ lo hi : Int, ∃ xs : List Int,
      vs = (lo :: xs).map Value.int ∧
      (lo :: xs).getLast? = some hi ∧
      (lo :: xs).Pairwise (fun a b => a < b) ∧
      64 < (hi - lo + 1).toNat ∧
      (gaps lo xs).length * 4 ≤ (hi - lo + 1).toNat ∧
      d = ⟨.holes lo hi (gaps lo xs)⟩ := by
  cases vs with
  | nil => simp [ofHoles?] at h
  | cons v rest =>
      cases v with
      | int lo =>
          simp only [ofHoles?] at h
          cases hd : decodeInts rest with
          | none => rw [hd] at h; cases h
          | some xs =>
              rw [hd] at h
              dsimp only at h
              cases hl : (lo :: xs).getLast? with
              | none => rw [hl] at h; cases h
              | some hi =>
                  rw [hl] at h
                  dsimp only at h
                  by_cases hcond : (sortedIntsB (lo :: xs) &&
                      decide (64 < (hi - lo + 1).toNat)) = true
                  · rw [if_pos hcond] at h
                    obtain ⟨-, hdens, hd_eq⟩ := mkHoles?_spec h
                    have hd_eq' := decodeInts_spec hd
                    have h1 : sortedIntsB (lo :: xs) = true := by
                      have h' := hcond
                      rw [Bool.and_eq_true] at h'
                      exact h'.1
                    have h2 : decide (64 < (hi - lo + 1).toNat) = true := by
                      have h' := hcond
                      rw [Bool.and_eq_true] at h'
                      exact h'.2
                    refine ⟨lo, hi, xs, ?_, hl, ?_, ?_, hdens, hd_eq⟩
                    · rw [hd_eq']; rfl
                    · exact (sortedIntsB_iff).mp h1
                    · exact of_decide_eq_true h2
                  · rw [if_neg hcond] at h
                    exact absurd h.symm (by simp)
      | bool b => simp [ofHoles?] at h
      | setOfInt s => simp [ofHoles?] at h
      | array a => simp [ofHoles?] at h

/-- Canonicalizing constructor: for canonical inputs it enters the
    compact cases exactly, for everything else it preserves the list in
    `general`; in all cases the enumeration is the input list exactly
    (`enum_ofList`). -/
def ofList (vs : List Value) : Dom :=
  match ofBoolValues? vs with
  | some d => d
  | none =>
      match ofSmallInts? vs with
      | some d => d
      | none =>
          match ofHoles? vs with
          | some d => d
          | none => ⟨.general vs⟩

theorem ofList_eq_bool {vs : List Value} {d : Dom} (h : ofBoolValues? vs = some d) :
    ofList vs = d := by
  unfold ofList
  rw [h]

theorem ofList_eq_small {vs : List Value} {d : Dom}
    (hb : ofBoolValues? vs = none) (h : ofSmallInts? vs = some d) :
    ofList vs = d := by
  unfold ofList
  rw [hb, h]

theorem ofList_eq_holes {vs : List Value} {d : Dom}
    (h1 : ofBoolValues? vs = none) (h2 : ofSmallInts? vs = none)
    (h3 : ofHoles? vs = some d) : ofList vs = d := by
  unfold ofList
  rw [h1, h2, h3]

theorem ofList_eq_general {vs : List Value}
    (h1 : ofBoolValues? vs = none) (h2 : ofSmallInts? vs = none)
    (h3 : ofHoles? vs = none) :
    ofList vs = ⟨.general vs⟩ := by
  unfold ofList
  rw [h1, h2, h3]

/-! ### Enumeration exactness for the compact cases -/

theorem mem_smallInts_map_int {off : Int} {bits : UInt64} {i : Int} :
    (Value.int i) ∈ (smallInts off bits).map Value.int ↔ i ∈ smallInts off bits := by
  rw [List.mem_map]
  constructor
  · rintro ⟨x, hx, heq⟩
    rw [Value.int.injEq] at heq
    rw [← heq]
    exact hx
  · intro h
    exact ⟨i, h, rfl⟩

/-- The packed bits re-enumerate their canonical integer list. -/
theorem smallInts_intsToBits {lo : Int} {L : List Int}
    (hsorted : L.Pairwise fun a b => a < b)
    (hlo : ∀ x ∈ L, lo ≤ x)
    (hhi : ∀ x ∈ L, x - lo < 64) :
    smallInts lo (UInt64.ofNat (intsToBits lo L)) = L := by
  have hw : ∀ x ∈ L, lo ≤ x ∧ x - lo < 64 := fun x hx => ⟨hlo x hx, hhi x hx⟩
  have hlt : intsToBits lo L < 2 ^ 64 := intsToBits_lt lo L hw
  unfold smallInts
  rw [toNat_ofNat_intsToBits hw]
  have hpred : ∀ k : Nat,
      (if (intsToBits lo L).testBit k then some (lo + (k : Int)) else none) =
        (if decide (lo + (k : Int) ∈ L) then some (lo + (k : Int)) else none) := by
    intro k
    by_cases hk : (intsToBits lo L).testBit k = true
    · rw [if_pos hk]
      by_cases hdec : decide (lo + (k : Int) ∈ L) = true
      · rw [if_pos hdec]
      · exact absurd ((testBit_intsToBits_iff hlo k).mp hk)
          (fun hin => hdec (decide_eq_true hin))
    · rw [if_neg hk]
      by_cases hdec : decide (lo + (k : Int) ∈ L) = true
      · exact absurd ((testBit_intsToBits_iff hlo k).mpr (of_decide_eq_true hdec)) hk
      · rw [if_neg hdec]
  have hstep :
      (List.range 64).filterMap (fun (k : Nat) =>
          if (intsToBits lo L).testBit k then some (lo + (k : Int)) else none) =
        (List.range 64).filterMap (fun (k : Nat) =>
          if decide (lo + (k : Int) ∈ L) then some (lo + (k : Int)) else none) :=
    filterMap_congr (fun k _ => hpred k)
  rw [hstep, range_filterMap_scanInts]
  apply eq_of_pairwise_lt_of_mem_iff
  · exact pairwise_scanInts lo _ 64
  · exact hsorted
  · intro x
    rw [mem_scanInts]
    constructor
    · rintro ⟨k, _, hp, rfl⟩
      exact of_decide_eq_true hp
    · intro hx
      have hx0 : 0 ≤ x - lo := by have := hlo x hx; omega
      refine ⟨(x - lo).toNat, ?_, ?_, ?_⟩
      · have h' : ((x - lo).toNat : Int) < 64 := by
          rw [Int.toNat_of_nonneg hx0]
          exact hhi x hx
        exact_mod_cast h'
      · have hx' : lo + ((x - lo).toNat : Int) = x := by
          rw [Int.toNat_of_nonneg hx0]
          omega
        rw [hx']
        exact decide_eq_true_eq.mpr hx
      · rw [Int.toNat_of_nonneg hx0]
        omega

/-- Enumeration exactness for the compact integer case. -/
theorem enum_small_intsToBits {lo : Int} {L : List Int}
    (hsorted : L.Pairwise fun a b => a < b)
    (hlo : ∀ x ∈ L, lo ≤ x) (hhi : ∀ x ∈ L, x - lo < 64) :
    enum ⟨.small false lo (UInt64.ofNat (intsToBits lo L))⟩ = L.map Value.int := by
  show (smallInts lo (UInt64.ofNat (intsToBits lo L))).map Value.int = L.map Value.int
  rw [smallInts_intsToBits hsorted hlo hhi]

theorem enum_ofBoolValues? {vs : List Value} {d : Dom}
    (h : ofBoolValues? vs = some d) : enum d = vs := by
  rcases ofBoolValues?_spec h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · rfl
  · rfl
  · rfl

theorem enum_ofSmallInts? {vs : List Value} {d : Dom}
    (h : ofSmallInts? vs = some d) : enum d = vs := by
  obtain ⟨lo, xs, hvs, hsorted, hfit, rfl⟩ := ofSmallInts?_spec h
  rw [hvs]
  refine enum_small_intsToBits hsorted ?_ hfit
  intro x hx
  rcases List.mem_cons.mp hx with rfl | hx'
  · omega
  · have := (List.pairwise_cons.mp hsorted).1 x hx'
    omega

theorem enum_ofHoles? {vs : List Value} {d : Dom}
    (h : ofHoles? vs = some d) : enum d = vs := by
  obtain ⟨lo, hi, xs, hvs, hlast, hsorted, -, -, rfl⟩ := ofHoles?_spec h
  have hhi : ∀ x ∈ lo :: xs, x ≤ hi := (getLast?_spec hsorted hlast).2
  have hlo : ∀ x ∈ lo :: xs, lo ≤ x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := (List.pairwise_cons.mp hsorted).1 x hx'
      omega
  rw [hvs]
  show (holesInts lo hi (gaps lo xs)).map Value.int =
    (lo :: xs).map Value.int
  rw [gaps_eq_holesInts hsorted hlast, holesInts_holesInts hsorted hlo hhi]

/-- **Round trip (D0 obligation 2)**: `ofList` is exact — the
    enumeration of the canonicalization is the input list itself, with
    order and multiplicity. -/
@[simp] theorem enum_ofList (vs : List Value) : enum (ofList vs) = vs := by
  rcases hb : ofBoolValues? vs with _ | db
  · rcases hi : ofSmallInts? vs with _ | di
    · rcases hh : ofHoles? vs with _ | dh
      · rw [ofList_eq_general hb hi hh]; rfl
      · rw [ofList_eq_holes hb hi hh]; exact enum_ofHoles? hh
    · rw [ofList_eq_small hb hi]; exact enum_ofSmallInts? hi
  · rw [ofList_eq_bool hb]; exact enum_ofBoolValues? hb

/-- The empty domain (canonical: the `general` fallback of `[]`). -/
def empty : Dom := ofList []

instance : Inhabited Dom := ⟨empty⟩

/-- The legacy `v :: d` view: prepend `v` to the enumeration of `d`. -/
def cons (v : Value) (d : Dom) : Dom := ofList (v :: enum d)

@[simp] theorem enum_cons (v : Value) (d : Dom) : enum (cons v d) = v :: enum d :=
  enum_ofList _

theorem enum_empty : enum empty = [] := enum_ofList []

/-! ### Structural Boolean equality

`Dom` is a structure over its representation, so a Boolean test that
compares representations is sound for definitional equality.  This is
the equality the scheduling layer uses to fingerprint whole domains
(`stampEqB`); no canonicality premise is needed. -/

/-- Structural Boolean equality of compact domains, by representation. -/
def eqB : Dom → Dom → Bool
  | ⟨.small b₁ o₁ w₁⟩, ⟨.small b₂ o₂ w₂⟩ =>
      (b₁ == b₂) && (o₁ == o₂) && (w₁ == w₂)
  | ⟨.holes lo₁ hi₁ hs₁⟩, ⟨.holes lo₂ hi₂ hs₂⟩ =>
      decide (lo₁ = lo₂) && decide (hi₁ = hi₂) && decide (hs₁ = hs₂)
  | ⟨.general vs₁⟩, ⟨.general vs₂⟩ => valuesEqB vs₁ vs₂
  | _, _ => false

private theorem valuesEqB_eq_of_true {xs ys : List Value}
    (h : valuesEqB xs ys = true) : xs = ys := by
  induction xs generalizing ys with
  | nil => cases ys with
    | nil => rfl
    | cons _ _ => simp [valuesEqB] at h
  | cons x xs ih =>
      cases ys with
      | nil => simp [valuesEqB] at h
      | cons y ys =>
          simp only [valuesEqB, Bool.and_eq_true] at h
          rw [LeanFzn.Semantics.Evaluation.value_eqB_iff.mp h.1, ih h.2]

/-- `Dom.eqB` is reflexive. -/
theorem eqB_refl (d : Dom) : eqB d d = true := by
  obtain ⟨r⟩ := d
  cases r with
  | small b o w => simp [eqB]
  | holes lo hi hs => simp [eqB]
  | general vs =>
      simp only [eqB]
      induction vs with
      | nil => rfl
      | cons v vs ih =>
          simp only [valuesEqB, Bool.and_eq_true]
          exact ⟨LeanFzn.Semantics.Evaluation.value_eqB_refl v, ih⟩

/-- `Dom.eqB` is sound for domain equality. -/
theorem eqB_sound {d e : Dom} (h : eqB d e = true) : d = e := by
  obtain ⟨r₁⟩ := d
  obtain ⟨r₂⟩ := e
  cases r₁ with
  | small b₁ o₁ w₁ =>
      cases r₂ with
      | small b₂ o₂ w₂ =>
          simp only [eqB, Bool.and_eq_true] at h
          obtain ⟨⟨hb, ho⟩, hw⟩ := h
          rw [beq_iff_eq.mp hb, beq_iff_eq.mp ho, beq_iff_eq.mp hw]
      | holes _ _ _ => simp [eqB] at h
      | general _ => simp [eqB] at h
  | holes lo₁ hi₁ hs₁ =>
      cases r₂ with
      | small _ _ _ => simp [eqB] at h
      | holes lo₂ hi₂ hs₂ =>
          simp only [eqB, Bool.and_eq_true] at h
          obtain ⟨⟨hl, hh⟩, hhs⟩ := h
          rw [of_decide_eq_true hl, of_decide_eq_true hh, of_decide_eq_true hhs]
      | general _ => simp [eqB] at h
  | general vs₁ =>
      cases r₂ with
      | small _ _ _ => simp [eqB] at h
      | holes _ _ _ => simp [eqB] at h
      | general vs₂ =>
          have hvs : vs₁ = vs₂ := valuesEqB_eq_of_true (by simpa [eqB] using h)
          rw [hvs]

/-! ### Canonicality invariant -/

/-- `WF` holds exactly for the canonical representatives: the Boolean
    bitsets are in normal form (`off = 0`, `1 <= bits <= 3`), the
    integer bitsets have a nonzero bit pattern with bit 0 set (so the
    offset is the minimum), the hole intervals have sorted, distinct,
    strictly interior holes with a span above 64 and at most a quarter
    of the span missing (the `ofHoles?` normal form), and a `general`
    list is one that `ofList` leaves in `general`.  Consequences:
    `WF_ofList` (every canonicalization is normal) and
    `enum_injective_of_WF` (the enumeration determines a `WF` domain). -/
def WF (d : Dom) : Prop :=
  match d.rep with
  | .small true off bits => off = 0 ∧ 1 ≤ bits.toNat ∧ bits.toNat ≤ 3
  | .small false _ bits => bits.toNat ≠ 0 ∧ bits.toNat.testBit 0 = true
  | .holes lo hi hs =>
      hs.Pairwise (fun a b => a < b) ∧
        (∀ h ∈ hs, lo < h ∧ h < hi) ∧
        64 < (hi - lo + 1).toNat ∧
        hs.length * 4 ≤ (hi - lo + 1).toNat
  | .general vs => ofList vs = ⟨.general vs⟩

theorem WF_ofBoolValues? {vs : List Value} {d : Dom}
    (h : ofBoolValues? vs = some d) : WF d := by
  rcases ofBoolValues?_spec h with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨-, rfl⟩ <;>
    (refine ⟨rfl, ?_, ?_⟩ <;> decide)

/-- A directly constructed bitset over a window list containing its own
    offset is canonical: the packed bit pattern has bit 0 set (from the
    offset) and is nonzero. -/
theorem wf_small_intsToBits {lo : Int} {L : List Int}
    (hlo : ∀ x ∈ L, lo ≤ x) (hhi : ∀ x ∈ L, x - lo < 64) (hmem : lo ∈ L) :
    WF ⟨.small false lo (UInt64.ofNat (intsToBits lo L))⟩ := by
  have hw : ∀ x ∈ L, lo ≤ x ∧ x - lo < 64 := fun x hx => ⟨hlo x hx, hhi x hx⟩
  have h0 : (UInt64.ofNat (intsToBits lo L)).toNat.testBit 0 = true := by
    rw [toNat_ofNat_intsToBits hw, testBit_intsToBits_eq hlo 0]
    rw [show lo + ((0 : Nat) : Int) = lo by omega]
    exact decide_eq_true hmem
  refine ⟨?_, h0⟩
  intro hzero
  rw [hzero] at h0
  simp at h0

theorem WF_ofSmallInts? {vs : List Value} {d : Dom}
    (h : ofSmallInts? vs = some d) : WF d := by
  obtain ⟨lo, xs, -, hsorted, hfit, rfl⟩ := ofSmallInts?_spec h
  have hlo : ∀ x ∈ lo :: xs, lo ≤ x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := (List.pairwise_cons.mp hsorted).1 x hx'
      omega
  have hw : ∀ x ∈ lo :: xs, lo ≤ x ∧ x - lo < 64 :=
    fun x hx => ⟨hlo x hx, hfit x hx⟩
  have h0 : (UInt64.ofNat (intsToBits lo (lo :: xs))).toNat.testBit 0 = true := by
    rw [toNat_ofNat_intsToBits hw, testBit_intsToBits_eq hlo 0]
    rw [show lo + ((0 : Nat) : Int) = lo by omega]
    exact decide_eq_true (List.mem_cons_self ..)
  refine ⟨?_, h0⟩
  intro hzero
  rw [hzero] at h0
  simp at h0

theorem WF_ofHoles? {vs : List Value} {d : Dom}
    (h : ofHoles? vs = some d) : WF d := by
  obtain ⟨lo, hi, xs, -, hlast, hsorted, hspan, hdens, rfl⟩ := ofHoles?_spec h
  have hspec := getLast?_spec hsorted hlast
  have hrest : xs.Pairwise fun a b => a < b := (List.pairwise_cons.mp hsorted).2
  have hcur : ∀ v ∈ xs, lo < v := (List.pairwise_cons.mp hsorted).1
  refine ⟨pairwise_gaps hrest hcur, ?_, hspan, hdens⟩
  intro x hx
  obtain ⟨hxlo, ⟨v, hv, hxv⟩, -⟩ := (mem_gaps hrest hcur).mp hx
  refine ⟨?_, ?_⟩
  · omega
  · have := hspec.2 v (List.mem_cons_of_mem _ hv)
    omega

theorem WF_ofList (vs : List Value) : WF (ofList vs) := by
  rcases hb : ofBoolValues? vs with _ | db
  · rcases hi : ofSmallInts? vs with _ | di
    · rcases hh : ofHoles? vs with _ | dh
      · rw [ofList_eq_general hb hi hh]
        show ofList vs = ⟨.general vs⟩
        exact ofList_eq_general hb hi hh
      · rw [ofList_eq_holes hb hi hh]
        exact WF_ofHoles? hh
    · rw [ofList_eq_small hb hi]
      exact WF_ofSmallInts? hi
  · rw [ofList_eq_bool hb]
    exact WF_ofBoolValues? hb

/-- The head of a packed integer list with bit 0 set is the offset. -/
theorem head_smallInts {off : Int} {bits : UInt64}
    (h0 : bits.toNat.testBit 0 = true) :
    (smallInts off bits).head? = some off := by
  have hmem : off ∈ smallInts off bits := by
    have h := (mem_smallInts_iff (off := off) (bits := bits) (k := 0) (by decide)).mpr h0
    simpa using h
  cases hL : smallInts off bits with
  | nil => rw [hL] at hmem; exact absurd hmem (by simp)
  | cons y ys =>
      have hy : off ≤ y := by
        obtain ⟨k, -, -, heq⟩ := mem_smallInts.mp (by rw [hL]; exact List.mem_cons_self ..)
        omega
      rcases List.mem_cons.mp (by rw [← hL]; exact hmem) with hoff | hoff'
      · rw [← hoff]
        rfl
      · have hpw := pairwise_smallInts off bits
        rw [hL] at hpw
        have : y < off := (List.pairwise_cons.mp hpw).1 off hoff'
        omega

/-- The packed list of a bit-0 bitset is its head consed with its tail. -/
theorem smallInts_eq_cons {off : Int} {bits : UInt64}
    (h0 : bits.toNat.testBit 0 = true) :
    smallInts off bits = off :: (smallInts off bits).tail := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp (head_smallInts h0)
  rw [ht]
  rfl

/-- **Retraction (D0 obligation 2, compact integer case)**: the
    canonicalization of the enumeration of a normal-form bitset is the
    bitset itself. -/
theorem ofList_enum_small_false {off : Int} {bits : UInt64}
    (h0 : bits.toNat.testBit 0 = true) :
    ofList (enum ⟨.small false off bits⟩) = ⟨.small false off bits⟩ := by
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp (head_smallInts h0)
  have hen : enum ⟨.small false off bits⟩ = (off :: t).map Value.int := by
    show (smallInts off bits).map Value.int = (off :: t).map Value.int
    rw [ht]
  have hpair : (off :: t).Pairwise (fun a b => a < b) := by
    have hp := pairwise_smallInts off bits
    rwa [ht] at hp
  have hlo : ∀ x ∈ off :: t, off ≤ x := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx'
    · omega
    · have := (List.pairwise_cons.mp hpair).1 x hx'
      omega
  have hw : ∀ x ∈ off :: t, off ≤ x ∧ x - off < 64 := by
    intro x hx
    refine ⟨hlo x hx, ?_⟩
    have hxL : x ∈ smallInts off bits := by rw [ht]; exact hx
    obtain ⟨j, hj, -, heq⟩ := mem_smallInts.mp hxL
    rw [← heq, show off + (j : Int) - off = (j : Int) by omega]
    exact mod_cast hj
  have hall : (off :: t).all (fun x => decide (x - off < 64)) = true := by
    rw [List.all_eq_true]
    exact fun x hx => decide_eq_true (hw x hx).2
  have hcond : (sortedIntsB (off :: t) &&
      (off :: t).all (fun x => decide (x - off < 64))) = true := by
    rw [Bool.and_eq_true]
    exact ⟨sortedIntsB_iff.mpr hpair, hall⟩
  have hdec : decodeInts (t.map Value.int) = some t := decodeInts_map t
  have hsmall : ofSmallInts? ((off :: t).map Value.int) =
      some ⟨.small false off (UInt64.ofNat (intsToBits off (off :: t)))⟩ := by
    show ofSmallInts? (Value.int off :: t.map Value.int) = _
    unfold ofSmallInts?
    dsimp only
    rw [hdec]
    dsimp only
    rw [if_pos hcond]
  have hbits : UInt64.ofNat (intsToBits off (off :: t)) = bits := by
    apply UInt64.toNat.inj
    rw [toNat_ofNat_intsToBits hw]
    apply Nat.eq_of_testBit_eq
    intro k
    rw [testBit_intsToBits_eq hlo k]
    by_cases hk : k < 64
    · have hiff : (off + (k : Int) ∈ off :: t) ↔ (bits.toNat.testBit k = true) := by
        rw [← ht]
        exact mem_smallInts_iff hk
      rw [decide_eq_decide.mpr hiff, Bool.decide_coe]
    · have hfalse : decide (off + (k : Int) ∈ off :: t) = false := by
        rw [decide_eq_false_iff_not]
        intro hmem
        have hxL : off + (k : Int) ∈ smallInts off bits := by rw [ht]; exact hmem
        obtain ⟨j, hj, -, heq⟩ := mem_smallInts.mp hxL
        omega
      rw [hfalse]
      exact (testBit_eq_false_of_lt (UInt64.toNat_lt_size bits) (by omega)).symm
  have hbNone : ofBoolValues? ((off :: t).map Value.int) = none := by
    rw [List.map_cons]
    dsimp [ofBoolValues?]
  rw [hen, ofList_eq_small (hb := hbNone) (h := hsmall), hbits]

/-- **Retraction (D0 obligation 2, interval-with-holes case)**: the
    canonicalization of the enumeration of a normal-form hole domain is
    the hole domain itself. -/
theorem ofList_enum_holes {lo hi : Int} {hs : List Int}
    (hsorted : hs.Pairwise fun a b => a < b)
    (hin : ∀ h ∈ hs, lo < h ∧ h < hi)
    (hspan : 64 < (hi - lo + 1).toNat)
    (hdens : hs.length * 4 ≤ (hi - lo + 1).toNat) :
    ofList (enum ⟨.holes lo hi hs⟩) = ⟨.holes lo hi hs⟩ := by
  have h64 : 64 ≤ hi - lo := by
    have h := (Int.lt_toNat (m := 64) (n := hi - lo + 1)).mp hspan
    omega
  have hXhi : hi ∈ holesInts lo hi hs :=
    mem_holesInts.mpr ⟨by omega, Int.le_refl hi,
      fun hmem => absurd (hin hi hmem).2 (by omega)⟩
  have hXlo : lo ∈ holesInts lo hi hs :=
    mem_holesInts.mpr ⟨Int.le_refl lo, by omega,
      fun hmem => absurd (hin lo hmem).1 (by omega)⟩
  have hlastX : (holesInts lo hi hs).getLast? = some hi :=
    getLast?_eq_some_of_max (pairwise_holesInts lo hi hs) hXhi
      (fun x hx => (mem_holesInts.mp hx).2.1)
  have hheadX : (holesInts lo hi hs).head? = some lo :=
    head?_eq_of_min (pairwise_holesInts lo hi hs) hXlo
      (fun x hx => (mem_holesInts.mp hx).1)
  obtain ⟨t, ht⟩ := List.head?_eq_some_iff.mp hheadX
  have hpair : (lo :: t).Pairwise fun a b => a < b := by
    have hp := pairwise_holesInts lo hi hs
    rwa [ht] at hp
  have hlast : (lo :: t).getLast? = some hi := by
    have hl := hlastX
    rwa [ht] at hl
  have hmemhi : hi ∈ lo :: t := (getLast?_spec hpair hlast).1
  have hen : enum ⟨.holes lo hi hs⟩ = (lo :: t).map Value.int := by
    show (holesInts lo hi hs).map Value.int = (lo :: t).map Value.int
    rw [ht]
  have hb : ofBoolValues? ((lo :: t).map Value.int) = none := by
    rw [List.map_cons]
    dsimp [ofBoolValues?]
  have hsmall : ofSmallInts? ((lo :: t).map Value.int) = none := by
    show ofSmallInts? (Value.int lo :: t.map Value.int) = none
    simp only [ofSmallInts?]
    rw [decodeInts_map]
    dsimp only
    by_cases hcond : (sortedIntsB (lo :: t) &&
        (lo :: t).all (fun x => decide (x - lo < 64))) = true
    · rw [if_pos hcond]
      rw [Bool.and_eq_true] at hcond
      exact absurd (of_decide_eq_true (List.all_eq_true.mp hcond.2 hi hmemhi)) (by omega)
    · rw [if_neg hcond]
  have hcomp : holesInts lo hi (lo :: t) = hs := by
    rw [show lo :: t = holesInts lo hi hs from ht.symm]
    apply eq_of_pairwise_lt_of_mem_iff
    · exact pairwise_holesInts ..
    · exact hsorted
    · intro x
      rw [mem_holesInts]
      constructor
      · rintro ⟨hxlo, hxhi, hxnot⟩
        by_cases hx : x ∈ hs
        · exact hx
        · exact absurd (mem_holesInts.mpr ⟨hxlo, hxhi, hx⟩) hxnot
      · intro hx
        exact ⟨Int.le_of_lt (hin x hx).1, Int.le_of_lt (hin x hx).2,
          fun hxnot => (mem_holesInts.mp hxnot).2.2 hx⟩
  have hcheap : (hi - lo + 1).toNat ≤ 4 * (lo :: t).length := by
    have hadd := length_holesInts_add hsorted
      (fun h hh => ⟨Int.le_of_lt (hin h hh).1, Int.le_of_lt (hin h hh).2⟩)
    rw [ht] at hadd
    omega
  have hg : gaps lo t = hs := by
    rw [gaps_eq_holesInts hpair hlast, hcomp]
  have hholes : ofHoles? ((lo :: t).map Value.int) =
      some ⟨.holes lo hi hs⟩ := by
    show ofHoles? (Value.int lo :: t.map Value.int) = _
    simp only [ofHoles?]
    rw [decodeInts_map]
    dsimp only
    rw [hlast]
    dsimp only
    have hcond : (sortedIntsB (lo :: t) &&
        decide (64 < (hi - lo + 1).toNat)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨sortedIntsB_iff.mpr hpair, decide_eq_true hspan⟩
    rw [if_pos hcond]
    exact mkHoles?_eq_some hcheap hg hdens
  rw [hen]
  unfold ofList
  rw [hb, hsmall, hholes]

/-- **Retraction (D0 obligation 2)**: on the canonical representatives,
    canonicalizing the enumeration is the identity. -/
theorem ofList_enum_eq_of_WF (d : Dom) (h : WF d) : ofList (enum d) = d := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true =>
              obtain ⟨hoff, h1, h3⟩ := h
              subst hoff
              have hb : bits.toNat = 1 ∨ bits.toNat = 2 ∨ bits.toNat = 3 := by
                omega
              have hbits : bits = 1 ∨ bits = 2 ∨ bits = 3 := by
                rcases hb with h1 | h2 | h3
                · left
                  rw [← UInt64.ofNat_toNat (x := bits), h1]
                  rfl
                · right; left
                  rw [← UInt64.ofNat_toNat (x := bits), h2]
                  rfl
                · right; right
                  rw [← UInt64.ofNat_toNat (x := bits), h3]
                  rfl
              rcases hbits with rfl | rfl | rfl <;> rfl
          | false => exact ofList_enum_small_false h.2
      | holes lo hi hs => exact ofList_enum_holes h.1 h.2.1 h.2.2.1 h.2.2.2
      | general vs => exact h

/-- On `WF` domains the enumeration is injective: distinct
    representations denote distinct value lists (D0 canonicality). -/
theorem enum_injective_of_WF {d₁ d₂ : Dom} (h₁ : WF d₁) (h₂ : WF d₂)
    (h : enum d₁ = enum d₂) : d₁ = d₂ := by
  have e₁ : ofList (enum d₁) = d₁ := ofList_enum_eq_of_WF d₁ h₁
  have e₂ : ofList (enum d₂) = d₂ := ofList_enum_eq_of_WF d₂ h₂
  rw [← e₁, h, e₂]

/-! ### Compiler-shape constructions (S6 interface)

`Compiler/Domain.lean` builds each search slot from `VarDomain.values`
(`List Value`); the direct constructions below are the drop-in `Dom`
shapes, with the admissibility conditions of `ofSetElemsShape_small`/
`ofSetElemsShape_holes` stated exactly.  `ofIntRange` never
materializes a wide interval. -/

/-- The Boolean domain `[false, true]` (`VarDomain.boolDom`). -/
def ofBoolShape : Dom := ⟨.small true 0 3⟩

theorem enum_ofBoolShape : enum ofBoolShape = [.bool false, .bool true] := rfl

theorem WF_ofBoolShape : WF ofBoolShape := by
  refine ⟨rfl, ?_, ?_⟩ <;> decide

theorem ofBoolShape_eq_ofList : ofBoolShape = ofList [.bool false, .bool true] := rfl

/-- Direct construction for `IntSetValue.interval lo hi` (the compiler's
    `var lo..hi` shape, which `varDomain` currently materializes via
    `setElems`): reversed ranges are `empty`, spans up to 64 are a packed
    bitset over the window, and wider spans are the interval with no
    holes.  No wide interval is materialized; `ofIntRange_eq_ofList`
    shows the result is exactly the `ofList` normal form of
    `setElems (.interval lo hi)`. -/
def ofIntRange (lo hi : Int) : Dom :=
  if hi < lo then empty
  else if (hi - lo + 1).toNat ≤ 64 then
    ⟨.small false lo (UInt64.ofNat (intsToBits lo (rangeInts lo (hi - lo + 1).toNat)))⟩
  else ⟨.holes lo hi []⟩

theorem enum_ofIntRange (lo hi : Int) :
    enum (ofIntRange lo hi) = (Evaluation.setElems (.interval lo hi)).map Value.int := by
  by_cases hlt : hi < lo
  · rw [ofIntRange, if_pos hlt, Evaluation.setElems, if_pos hlt]
    rfl
  · rw [ofIntRange, if_neg hlt, Evaluation.setElems, if_neg hlt]
    by_cases h64 : (hi - lo + 1).toNat ≤ 64
    · rw [if_pos h64]
      exact enum_small_intsToBits (rangeInts_pairwise lo (hi - lo + 1).toNat)
        rangeInts_lo_le (rangeInts_all_lt h64)
    · rw [if_neg h64]
      have hholes : holesInts lo hi [] = rangeInts lo (hi - lo + 1).toNat :=
        holesInts_nil_eq_rangeInts lo hi
      show (holesInts lo hi []).map Value.int = (rangeInts lo (hi - lo + 1).toNat).map Value.int
      rw [hholes]

theorem WF_ofIntRange (lo hi : Int) : WF (ofIntRange lo hi) := by
  by_cases hlt : hi < lo
  · rw [ofIntRange, if_pos hlt]
    exact WF_ofList []
  · rw [ofIntRange, if_neg hlt]
    by_cases h64 : (hi - lo + 1).toNat ≤ 64
    · rw [if_pos h64]
      refine wf_small_intsToBits rangeInts_lo_le (rangeInts_all_lt h64) ?_
      refine rangeInts_mem.mpr ⟨0, by omega, ?_⟩
      rw [show lo + ((0 : Nat) : Int) = lo by omega]
    · rw [if_neg h64]
      refine ⟨by simp, ?_, by omega, by simp⟩
      intro h hmem
      simp at hmem

/-- The direct interval construction is exactly the `ofList`
    canonicalization of the materialized `setElems` interval. -/
theorem ofIntRange_eq_ofList (lo hi : Int) :
    ofIntRange lo hi = ofList ((Evaluation.setElems (.interval lo hi)).map Value.int) :=
  enum_injective_of_WF (WF_ofIntRange lo hi) (WF_ofList _) (by
    rw [enum_ofIntRange, enum_ofList])

/-! ### Linear contiguous constructor (S0 completion)

`ofList`'s hole path scans the span against the full value list, so it is
quadratic on a wide contiguous domain.  The constructors below recognize a
contiguous ascending integer run in one allocation-free pass and emit the
`ofIntRange` shape directly; `ofRange?` returns `none` for every other
list, which keeps `ofList` as the total fallback.  All three laws
(`enum`, `WF`, and the range bridge) are proved, so callers may use the
fast shape without unfolding the constructor. -/

/-- The upper endpoint of a contiguous ascending integer run, if the whole
    value list is one.  Linear in the list length and allocation-free. -/
def rangeEndV? (lo : Int) : List Value → Option Int
  | [] => some lo
  | .int x :: rest => if x = lo + 1 then rangeEndV? x rest else none
  | _ => none

/-- A successful fast check decodes to an integer chain with the same
    endpoint, so the existing `rangeEnd?` laws apply. -/
theorem rangeEndV?_decode {lo hi : Int} {vs : List Value}
    (h : rangeEndV? lo vs = some hi) :
    ∃ xs : List Int, decodeInts vs = some xs ∧ rangeEnd? lo xs = some hi := by
  induction vs generalizing lo hi with
  | nil =>
      simp only [rangeEndV?, Option.some.injEq] at h
      subst h
      exact ⟨[], rfl, rfl⟩
  | cons v vs ih =>
      cases v with
      | int x =>
          simp only [rangeEndV?] at h
          split at h
          · next hx =>
              subst hx
              obtain ⟨xs, hdec, hre⟩ := ih h
              refine ⟨(lo + 1) :: xs, ?_, ?_⟩
              · simp only [decodeInts, hdec, Option.map_some]
              · simpa only [rangeEnd?, if_true] using hre
          · simp at h
      | bool b => simp [rangeEndV?] at h
      | setOfInt s => simp [rangeEndV?] at h
      | array a => simp [rangeEndV?] at h

/-- The linear contiguous constructor: a nonempty ascending integer run
    `lo, lo+1, ..., hi` becomes `ofIntRange lo hi` (a bitset window for
    spans at most 64 and the hole shape otherwise). -/
def ofRange? (vs : List Value) : Option Dom :=
  match vs with
  | .int lo :: rest =>
      match rangeEndV? lo rest with
      | some hi => some (ofIntRange lo hi)
      | none => none
  | _ => none

/-- Every successful `ofRange?` is the canonical range shape of its
    (decoded) input. -/
theorem ofRange?_spec {vs : List Value} {d : Dom} (h : ofRange? vs = some d) :
    ∃ lo hi : Int, ∃ xs : List Int,
      vs = (lo :: xs).map Value.int ∧
      rangeEnd? lo xs = some hi ∧ d = ofIntRange lo hi := by
  cases vs with
  | nil => simp [ofRange?] at h
  | cons v rest =>
      cases v with
      | bool b => simp [ofRange?] at h
      | int lo =>
          simp only [ofRange?] at h
          cases hre : rangeEndV? lo rest with
          | none => rw [hre] at h; simp at h
          | some hi =>
              rw [hre] at h
              dsimp only at h
              obtain ⟨xs, hdec, hrend⟩ := rangeEndV?_decode hre
              exact ⟨lo, hi, xs, by rw [decodeInts_spec hdec]; rfl, hrend,
                (Option.some.inj h).symm⟩
      | setOfInt s => simp [ofRange?] at h
      | array a => simp [ofRange?] at h

/-- `ofRange?` preserves the enumeration exactly. -/
theorem enum_ofRange? {vs : List Value} {d : Dom} (h : ofRange? vs = some d) :
    enum d = vs := by
  obtain ⟨lo, hi, xs, hvs, hre, rfl⟩ := ofRange?_spec h
  obtain ⟨hhi, -⟩ := rangeEnd?_spec hre
  have hchain := rangeEnd?_range hre
  have hset : Evaluation.setElems (.interval lo hi) =
      rangeInts lo (hi - lo + 1).toNat := by
    dsimp only [Evaluation.setElems, rangeInts]
    rw [if_neg (by omega : ¬ hi < lo)]
  rw [enum_ofIntRange, hvs, hchain, hset]

/-- `ofRange?` produces canonical domains. -/
theorem WF_ofRange? {vs : List Value} {d : Dom} (h : ofRange? vs = some d) :
    WF d := by
  obtain ⟨lo, hi, xs, -, -, rfl⟩ := ofRange?_spec h
  exact WF_ofIntRange lo hi

/-- Canonicalize a `setElems`/`intSet` integer list (the compiler's
    `var {...}` shape).  Total: admissible inputs (ascending,
    duplicate-free, satisfying the span/density conditions of
    `ofSetElemsShape_small`/`ofSetElemsShape_holes`) enter the compact
    cases, everything else falls back to `general`; in all cases the
    enumeration is the input list with order and multiplicity and the
    result is canonical (`enum_ofSetElemsShape`, `WF_ofSetElemsShape`). -/
def ofSetElemsShape (l : List Int) : Dom := ofList (l.map Value.int)

theorem enum_ofSetElemsShape (l : List Int) :
    enum (ofSetElemsShape l) = l.map Value.int := enum_ofList _

theorem WF_ofSetElemsShape (l : List Int) : WF (ofSetElemsShape l) := WF_ofList _

/-- **Admissibility, compact case**: an ascending list inside a 64-wide
    window becomes the packed bitset (the same bits `ofSmallInts?`
    computes). -/
theorem ofSetElemsShape_small {l : List Int} {lo : Int} {xs : List Int}
    (hl : l = lo :: xs) (hsorted : l.Pairwise fun a b => a < b)
    (hwin : ∀ x ∈ l, x - lo < 64) :
    ofSetElemsShape l = ⟨.small false lo (UInt64.ofNat (intsToBits lo l))⟩ := by
  have hb : ofBoolValues? (l.map Value.int) = none := by
    rw [hl, List.map_cons]
    dsimp [ofBoolValues?]
  have hcond : (sortedIntsB (lo :: xs) &&
      (lo :: xs).all (fun x => decide (x - lo < 64))) = true := by
    rw [Bool.and_eq_true]
    refine ⟨?_, List.all_eq_true.mpr ?_⟩
    · exact sortedIntsB_iff.mpr (by rw [hl] at hsorted; exact hsorted)
    · intro x hx
      have hx' : x ∈ l := by rwa [← hl] at hx
      exact decide_eq_true (hwin x hx')
  have hsmall : ofSmallInts? (l.map Value.int) =
      some ⟨.small false lo (UInt64.ofNat (intsToBits lo l))⟩ := by
    have hdec : decodeInts (xs.map Value.int) = some xs := decodeInts_map xs
    rw [hl, List.map_cons]
    unfold ofSmallInts?
    dsimp only
    rw [hdec]
    dsimp only
    rw [if_pos hcond]
  rw [ofSetElemsShape, ofList_eq_small hb hsmall]

/-- **Admissibility, hole case**: an ascending list with span above 64
    and at most a quarter of the span missing becomes the
    interval-with-holes form whose holes are the complement of the list
    inside `[lo, hi]` (the `ofHoles?` normal form). -/
theorem ofSetElemsShape_holes {l : List Int} {lo hi : Int} {xs : List Int}
    (hl : l = lo :: xs) (hlast : l.getLast? = some hi)
    (hsorted : l.Pairwise fun a b => a < b)
    (hspan : 64 < (hi - lo + 1).toNat)
    (hdens : (holesInts lo hi l).length * 4 ≤ (hi - lo + 1).toNat) :
    ofSetElemsShape l = ⟨.holes lo hi (holesInts lo hi l)⟩ := by
  have hb : ofBoolValues? (l.map Value.int) = none := by
    rw [hl, List.map_cons]
    dsimp [ofBoolValues?]
  have h64 : 64 ≤ hi - lo := by
    have h := (Int.lt_toNat (m := 64) (n := hi - lo + 1)).mp hspan
    omega
  have hmemhi : hi ∈ lo :: xs := by
    rw [← hl]
    exact (getLast?_spec hsorted hlast).1
  have hall : (lo :: xs).all (fun x => decide (x - lo < 64)) = false := by
    cases ha : (lo :: xs).all (fun x => decide (x - lo < 64)) with
    | false => rfl
    | true =>
        have := List.all_eq_true.mp ha hi hmemhi
        have hlt := of_decide_eq_true this
        omega
  have hsmall : ofSmallInts? (l.map Value.int) = none := by
    have hdec : decodeInts (xs.map Value.int) = some xs := decodeInts_map xs
    rw [hl, List.map_cons]
    unfold ofSmallInts?
    dsimp only
    rw [hdec]
    dsimp only
    by_cases hcond : (sortedIntsB (lo :: xs) &&
        (lo :: xs).all (fun x => decide (x - lo < 64))) = true
    · rw [if_pos hcond]
      rw [Bool.and_eq_true] at hcond
      rw [hcond.2] at hall
      exact absurd hall (by simp)
    · rw [if_neg hcond]
  have hpair : (lo :: xs).Pairwise fun a b => a < b := by rwa [← hl]
  have hlast' : (lo :: xs).getLast? = some hi := by rw [← hl]; exact hlast
  have hcheap : (hi - lo + 1).toNat ≤ 4 * (lo :: xs).length := by
    have hdens' : (holesInts lo hi (lo :: xs)).length * 4 ≤
        (hi - lo + 1).toNat := by
      rw [hl] at hdens
      exact hdens
    clear hdens
    have hhsorted : (holesInts lo hi (lo :: xs)).Pairwise fun a b => a < b :=
      pairwise_holesInts ..
    have hhin : ∀ h ∈ holesInts lo hi (lo :: xs), lo ≤ h ∧ h ≤ hi := by
      intro h hh
      obtain ⟨h1, h2, -⟩ := mem_holesInts.mp hh
      exact ⟨h1, h2⟩
    have hadd := length_holesInts_add hhsorted hhin
    have hpres : holesInts lo hi (holesInts lo hi (lo :: xs)) = lo :: xs := by
      apply holesInts_holesInts hpair
      · intro x hx
        rcases List.mem_cons.mp hx with h | hx'
        · rw [h]; exact Int.le_refl lo
        · exact Int.le_of_lt ((List.pairwise_cons.mp hpair).1 x hx')
      · exact (getLast?_spec hpair hlast').2
    rw [hpres] at hadd
    omega
  have hg : gaps lo xs = holesInts lo hi (lo :: xs) :=
    gaps_eq_holesInts hpair hlast'
  have hholes : ofHoles? (l.map Value.int) =
      some ⟨.holes lo hi (holesInts lo hi l)⟩ := by
    have hdec : decodeInts (xs.map Value.int) = some xs := decodeInts_map xs
    rw [hl, List.map_cons]
    unfold ofHoles?
    dsimp only
    rw [hdec]
    dsimp only
    rw [hlast']
    dsimp only
    have hcond : (sortedIntsB (lo :: xs) &&
        decide (64 < (hi - lo + 1).toNat)) = true := by
      rw [Bool.and_eq_true]
      exact ⟨sortedIntsB_iff.mpr hpair, decide_eq_true hspan⟩
    rw [if_pos hcond]
    exact mkHoles?_eq_some hcheap hg (by rw [hl] at hdens; exact hdens)
  rw [ofSetElemsShape, ofList_eq_holes hb hsmall hholes]

/-! ### Membership, cardinality, bounds -/

/-- Membership test on the compact representation (D0 (D1)). -/
def memBool (d : Dom) (v : Value) : Bool :=
  match d.rep, v with
  | .small true _ bits, .bool b => bits.toNat.testBit (if b then 1 else 0)
  | .small false off bits, .int i =>
      decide (off ≤ i) && decide (i - off < (64 : Int)) &&
        bits.toNat.testBit (i - off).toNat
  | .holes lo hi hs, .int i =>
      decide (lo ≤ i) && decide (i ≤ hi) && !(memHoles hs i)
  | .general vs, v => vs.any fun x => x.eqB v
  | _, _ => false

theorem memBool_iff (d : Dom) (v : Value) : memBool d v = true ↔ v ∈ enum d := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true =>
              cases v with
              | bool b =>
                  change bits.toNat.testBit (if b then 1 else 0) = true ↔
                    (.bool b : Value) ∈ smallBools bits
                  exact (mem_smallBools_bool bits b).symm
              | int i =>
                  change false = true ↔ (Value.int i) ∈ smallBools bits
                  exact ⟨fun h => absurd h (by simp), fun h => by
                    obtain ⟨b, hb, -⟩ := mem_smallBools.mp h
                    cases hb⟩
              | setOfInt s =>
                  change false = true ↔ (Value.setOfInt s) ∈ smallBools bits
                  exact ⟨fun h => absurd h (by simp), fun h => by
                    obtain ⟨b, hb, -⟩ := mem_smallBools.mp h
                    cases hb⟩
              | array a =>
                  change false = true ↔ (Value.array a) ∈ smallBools bits
                  exact ⟨fun h => absurd h (by simp), fun h => by
                    obtain ⟨b, hb, -⟩ := mem_smallBools.mp h
                    cases hb⟩
          | false =>
              cases v with
              | int i =>
                  change (decide (off ≤ i) && decide (i - off < (64 : Int)) &&
                      bits.toNat.testBit (i - off).toNat) = true ↔
                        (Value.int i) ∈ (smallInts off bits).map Value.int
                  rw [mem_smallInts_map_int, mem_smallInts_int, Bool.and_eq_true,
                    Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq, and_assoc]
              | bool b =>
                  change false = true ↔ (Value.bool b) ∈ (smallInts off bits).map Value.int
                  exact ⟨fun h => absurd h (by simp), fun h => by
                    obtain ⟨i, -, hi⟩ := List.mem_map.mp h
                    cases hi⟩
              | setOfInt s =>
                  change false = true ↔ (Value.setOfInt s) ∈ (smallInts off bits).map Value.int
                  exact ⟨fun h => absurd h (by simp), fun h => by
                    obtain ⟨i, -, hi⟩ := List.mem_map.mp h
                    cases hi⟩
              | array a =>
                  change false = true ↔ (Value.array a) ∈ (smallInts off bits).map Value.int
                  exact ⟨fun h => absurd h (by simp), fun h => by
                    obtain ⟨i, -, hi⟩ := List.mem_map.mp h
                    cases hi⟩
      | holes lo hi hs =>
          cases v with
          | int i =>
              change (decide (lo ≤ i) && decide (i ≤ hi) && !(memHoles hs i)) = true ↔
                (Value.int i) ∈ enum ⟨.holes lo hi hs⟩
              rw [mem_holes_enum_int, Bool.and_eq_true, Bool.and_eq_true,
                decide_eq_true_eq, decide_eq_true_eq, Bool.not_eq_true', memHoles_eq_false,
                and_assoc]
          | bool b =>
              change false = true ↔ (Value.bool b) ∈ enum ⟨.holes lo hi hs⟩
              exact ⟨fun h => absurd h (by simp), fun h => by
                obtain ⟨i, heq⟩ := eq_int_of_mem_holes_enum h
                cases heq⟩
          | setOfInt s =>
              change false = true ↔ (Value.setOfInt s) ∈ enum ⟨.holes lo hi hs⟩
              exact ⟨fun h => absurd h (by simp), fun h => by
                obtain ⟨i, heq⟩ := eq_int_of_mem_holes_enum h
                cases heq⟩
          | array a =>
              change false = true ↔ (Value.array a) ∈ enum ⟨.holes lo hi hs⟩
              exact ⟨fun h => absurd h (by simp), fun h => by
                obtain ⟨i, heq⟩ := eq_int_of_mem_holes_enum h
                cases heq⟩
      | general vs =>
          change vs.any (fun x => x.eqB v) = true ↔ v ∈ vs
          rw [List.any_eq_true]
          constructor
          · rintro ⟨x, hx, heq⟩
            rw [Evaluation.value_eqB_iff] at heq
            exact heq ▸ hx
          · intro h
            exact ⟨v, h, Evaluation.value_eqB_refl v⟩

/-- The interval-with-holes cardinality by the D0 arithmetic form
    `span - #holes`, O(#holes) (defined here so the compiled `cardFast`
    can use it; exactness is `holesCard_eq_card_of_WF` below). -/
def holesCard (lo hi : Int) (hs : List Int) : Nat :=
  (hi - lo + 1).toNat -
    (hs.filter fun h => decide (lo ≤ h) && decide (h ≤ hi)).length

/-- Computable form of the `WF` conditions of a `.holes` domain (sorted,
    strictly inside the span, wide, and at most a quarter holes). -/
def holesWFBool (lo hi : Int) (hs : List Int) : Bool :=
  sortedIntsB hs &&
    hs.all (fun h => decide (lo < h) && decide (h < hi)) &&
    decide (64 < (hi - lo + 1).toNat) &&
    decide (hs.length * 4 ≤ (hi - lo + 1).toNat)

theorem holesWFBool_iff {lo hi : Int} {hs : List Int} :
    holesWFBool lo hi hs = true ↔ WF ⟨.holes lo hi hs⟩ := by
  unfold holesWFBool WF
  rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    sortedIntsB_iff]
  constructor
  · rintro ⟨⟨⟨hsorted, hall⟩, hspan⟩, hdens⟩
    refine ⟨hsorted, ?_, ?_, ?_⟩
    · intro h hh
      have hb := List.all_eq_true.mp hall h hh
      rw [Bool.and_eq_true] at hb
      exact ⟨of_decide_eq_true hb.1, of_decide_eq_true hb.2⟩
    · exact of_decide_eq_true hspan
    · exact of_decide_eq_true hdens
  · rintro ⟨hsorted, hin, hspan, hdens⟩
    refine ⟨⟨⟨hsorted, ?_⟩, decide_eq_true hspan⟩,
      decide_eq_true hdens⟩
    apply List.all_eq_true.mpr
    intro h hh
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true (hin h hh).1, decide_eq_true (hin h hh).2⟩

/-- The proof-facing cardinality scan, exact on every constructor. -/
def cardScan (d : Dom) : Nat :=
  match d.rep with
  | .small true _ bits => (List.range 2).countP fun k => bits.toNat.testBit k
  | .small false _ bits => (List.range 64).countP fun k => bits.toNat.testBit k
  | .holes lo hi hs =>
      (List.range (hi - lo + 1).toNat).countP fun (k : Nat) =>
        !(memHoles hs (lo + (k : Int)))
  | .general vs => vs.length

/-! ### Popcount fast path

`cardScan` counts the 64 bits of a `small false` domain by walking
`List.range 64`; the compiled `cardFast` twin sums the eight bytes of the
bitset through a 256-entry table instead.  The logical definition stays
`cardScan` (and hence every existing proof is unchanged); only the
compiled body is swapped by the `@[implemented_by]` seam below. -/

/-- Popcount of the low eight bits. -/
private def pop8 (x : Nat) : Nat := (List.range 8).countP fun k => x.testBit k

/-- Byte popcount table. -/
private def byteTable : Array Nat := #[
  0, 1, 1, 2, 1, 2, 2, 3, 1, 2, 2, 3, 2, 3, 3, 4,
  1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
  1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
  2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
  1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
  2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
  2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
  3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
  1, 2, 2, 3, 2, 3, 3, 4, 2, 3, 3, 4, 3, 4, 4, 5,
  2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
  2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
  3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
  2, 3, 3, 4, 3, 4, 4, 5, 3, 4, 4, 5, 4, 5, 5, 6,
  3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
  3, 4, 4, 5, 4, 5, 5, 6, 4, 5, 5, 6, 5, 6, 6, 7,
  4, 5, 5, 6, 5, 6, 6, 7, 5, 6, 6, 7, 6, 7, 7, 8,
]

set_option maxRecDepth 100000 in
private theorem byteTable_spec (i : Nat) (hi : i < 256) :
    byteTable.getD i 0 = pop8 i := by
  have h : (List.range 256).all (fun i => byteTable.getD i 0 == pop8 i) = true := by
    decide
  have h' := (List.all_eq_true.mp h) i (List.mem_range.mpr hi)
  simpa [pop8] using h'

/-- Byte-chunked popcount of the low `8 * n` bits. -/
private def popBytes (x : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => byteTable.getD (x % 256) 0 + popBytes (x / 256) n

private theorem popBytes_eq (x n : Nat) :
    popBytes x n = (List.range (8 * n)).countP (fun k => x.testBit k) := by
  induction n generalizing x with
  | zero => simp [popBytes]
  | succ n ih =>
      rw [popBytes]
      rw [ih (x / 256)]
      have hmod : byteTable.getD (x % 256) 0 =
          (List.range 8).countP (fun k => x.testBit k) := by
        rw [byteTable_spec (x % 256) (Nat.mod_lt x (by decide : 0 < 256))]
        unfold pop8
        apply List.countP_congr
        intro k hk
        rw [List.mem_range] at hk
        rw [show x % 256 = x % 2 ^ 8 by rfl, Nat.testBit_mod_two_pow]
        simp [hk]
      rw [hmod]
      have hdiv : ∀ k, (x / 256).testBit k = x.testBit (8 + k) := by
        intro k
        have := Nat.testBit_div_two_pow (n := 8) x k
        simpa [Nat.add_comm] using this
      rw [show (List.range (8 * (n + 1))) = List.range (8 + 8 * n) by
        rw [Nat.mul_succ, Nat.add_comm]]
      rw [List.range_add, List.countP_append, List.countP_map]
      have hcongr : (fun k => x.testBit (8 + k)) = fun k => (x / 256).testBit k := by
        funext k
        exact (hdiv k).symm
      rw [show ((fun k => x.testBit k) ∘ fun x => 8 + x) =
          fun k => x.testBit (8 + k) by rfl]
      rw [hcongr]

/-- The two-bit Boolean window count, in direct form. -/
private theorem countP_range_two (f : Nat → Bool) :
    (List.range 2).countP f =
      (if f 0 then 1 else 0) + (if f 1 then 1 else 0) := by
  simp [List.range_succ]
  by_cases h0 : f 0 <;> by_cases h1 : f 1 <;> simp [h0, h1]

/-- Cardinality, exact on every constructor (the proof-facing scan).  The
    compiled twin `cardFast` is attached by `@[implemented_by]`; the
    logical body stays the direct scan so concrete `decide` proofs keep
    reducing through the old, shallow term. -/
def card (d : Dom) : Nat :=
  match d.rep with
  | .small true _ bits => (List.range 2).countP fun k => bits.toNat.testBit k
  | .small false _ bits => (List.range 64).countP fun k => bits.toNat.testBit k
  | .holes lo hi hs =>
      (List.range (hi - lo + 1).toNat).countP fun (k : Nat) =>
        !(memHoles hs (lo + (k : Int)))
  | .general vs => vs.length

/-- Compiled fast twin of `card`: direct Boolean bits, byte-table popcount
    for the 64-bit integer window, and the scan for hole intervals. -/
def cardFast (d : Dom) : Nat :=
  match d.rep with
  | .small true _ bits =>
      (if bits.toNat.testBit 0 then 1 else 0) +
        (if bits.toNat.testBit 1 then 1 else 0)
  | .small false _ bits => popBytes bits.toNat 8
  | .holes lo hi hs =>
      if holesWFBool lo hi hs then holesCard lo hi hs
      else cardScan ⟨.holes lo hi hs⟩
  | .general vs => vs.length

attribute [implemented_by cardFast] card

/-- The logical cardinality is the reference scan. -/
theorem card_eq_cardScan (d : Dom) : card d = cardScan d := rfl

theorem card_eq_length_enum (d : Dom) : card d = (enum d).length := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true =>
              dsimp only [card, enum]
              rw [List.countP_eq_length_filter, smallBools, length_filterMap_if]
          | false =>
              dsimp only [card, enum]
              rw [List.length_map, List.countP_eq_length_filter, smallInts, length_filterMap_if]
      | holes lo hi hs =>
          dsimp only [card, enum]
          rw [List.length_map, List.countP_eq_length_filter, holesInts, length_filterMap_if]
      | general vs => rfl

/-- The legacy `List.length` read on the enumeration, as a dot-notation
    accessor on the compact type (D2 S1 migration surface). -/
def length (d : Dom) : Nat := d.card

theorem length_eq_card (d : Dom) : d.length = d.card := rfl

theorem length_eq_enum (d : Dom) : d.length = (enum d).length :=
  card_eq_length_enum d

/-- The legacy `List.isEmpty` read in cardinality form.  O(1) on the
    compact constructors; the enumerating fallback is avoided. -/
def isEmpty (d : Dom) : Bool := d.card == 0

theorem isEmpty_eq_true_iff (d : Dom) : d.isEmpty = true ↔ enum d = [] := by
  unfold isEmpty
  rw [beq_iff_eq, card_eq_length_enum, List.length_eq_zero_iff]

/-- Exact emptiness: the cardinality vanishes exactly on the empty
    enumeration (D0 obligation 11). -/
theorem card_eq_zero_iff (d : Dom) : card d = 0 ↔ enum d = [] := by
  rw [card_eq_length_enum, List.length_eq_zero_iff]

/-- The `gateOk` nonemptiness test in cardinality form. -/
theorem card_pos_iff (d : Dom) : 0 < card d ↔ enum d ≠ [] := by
  rw [Nat.pos_iff_ne_zero]
  constructor
  · intro h he
    exact h ((card_eq_zero_iff d).mpr he)
  · intro h hc
    exact h ((card_eq_zero_iff d).mp hc)

theorem holesCard_eq_of_WF {lo hi : Int} {hs : List Int}
    (hsorted : hs.Pairwise fun a b => a < b)
    (hin : ∀ h ∈ hs, lo < h ∧ h < hi)
    (hspan : 64 < (hi - lo + 1).toNat) :
    holesCard lo hi hs = card ⟨.holes lo hi hs⟩ := by
  have h64 : 64 ≤ hi - lo := by
    have h := (Int.lt_toNat (m := 64) (n := hi - lo + 1)).mp hspan
    omega
  have hinRange : ∀ h ∈ hs, (decide (lo ≤ h) && decide (h ≤ hi)) = true := by
    intro h hh
    rw [Bool.and_eq_true]
    exact ⟨decide_eq_true (Int.le_of_lt (hin h hh).1), decide_eq_true (Int.le_of_lt (hin h hh).2)⟩
  have hfilter : (hs.filter fun h => decide (lo ≤ h) && decide (h ≤ hi)) = hs :=
    List.filter_eq_self.mpr hinRange
  -- the in-range holes are exactly the ascending `hs`
  have hY : ((List.range (hi - lo + 1).toNat).filterMap fun (k : Nat) =>
        if memHoles hs (lo + (k : Int)) then some (lo + (k : Int)) else none) = hs := by
    apply eq_of_pairwise_lt_of_mem_iff
    · exact pairwise_filterMap_range _ _ _
    · exact hsorted
    · intro x
      rw [List.mem_filterMap]
      constructor
      · rintro ⟨k, hk, hkf⟩
        rw [List.mem_range] at hk
        by_cases h : memHoles hs (lo + (k : Int)) = true
        · rw [if_pos h] at hkf
          rw [← Option.some.inj hkf]
          exact memHoles_iff.mp h
        · rw [if_neg h] at hkf
          exact absurd hkf (by simp)
      · intro hx
        have hxlo : lo < x := (hin x hx).1
        have hxhi : x < hi := (hin x hx).2
        have hxk : ((x - lo).toNat) < (hi - lo + 1).toNat := by
          rw [Int.toNat_lt' (by omega : 0 < (hi - lo + 1).toNat)]
          rw [Int.toNat_of_nonneg (by omega : 0 ≤ hi - lo + 1)]
          omega
        refine ⟨(x - lo).toNat, List.mem_range.mpr hxk, ?_⟩
        have hkval : lo + ((x - lo).toNat : Int) = x := by
          rw [Int.toNat_of_nonneg (by omega : 0 ≤ x - lo)]
          omega
        rw [if_pos (by rw [hkval]; exact memHoles_iff.mpr hx), hkval]
  have hholesLen : ((List.range (hi - lo + 1).toNat).filter
        (fun (k : Nat) => memHoles hs (lo + (k : Int)))).length = hs.length := by
    rw [← length_filterMap_if (l := List.range (hi - lo + 1).toNat)
      (p := fun (k : Nat) => memHoles hs (lo + (k : Int))) (f := fun k => lo + (k : Int))]
    rw [hY]
  have hcard : card ⟨.holes lo hi hs⟩ =
      (List.range (hi - lo + 1).toNat).countP
        fun (k : Nat) => !(memHoles hs (lo + (k : Int))) := rfl
  have hnon : ((List.range (hi - lo + 1).toNat).filter
        (fun (k : Nat) => !(memHoles hs (lo + (k : Int))))).length =
      (hi - lo + 1).toNat - hs.length := by
    have hp := length_filter_add_length_filter_not (List.range (hi - lo + 1).toNat)
      (fun (k : Nat) => memHoles hs (lo + (k : Int)))
    rw [List.length_range] at hp
    omega
  rw [holesCard, hfilter, hcard, List.countP_eq_length_filter, hnon]

/-- The D0 arithmetic cardinality `span - #holes` on `WF` hole domains. -/
theorem holesCard_eq_card_of_WF {lo hi : Int} {hs : List Int}
    (h : WF ⟨.holes lo hi hs⟩) : holesCard lo hi hs = card ⟨.holes lo hi hs⟩ :=
  holesCard_eq_of_WF h.1 h.2.1 h.2.2.1

/-- The compiled twin computes exactly the reference scan. -/
theorem cardFast_eq (d : Dom) : cardFast d = cardScan d := by
  cases d with
  | mk rep =>
      cases rep with
      | small isBool off bits =>
          cases isBool with
          | true =>
              simp only [cardFast, cardScan]
              rw [countP_range_two]
          | false =>
              simp only [cardFast, cardScan]
              rw [popBytes_eq]
      | holes lo hi hs =>
          simp only [cardFast]
          by_cases hwf : holesWFBool lo hi hs = true
          · rw [if_pos hwf, holesCard_eq_card_of_WF (holesWFBool_iff.mp hwf),
              card_eq_cardScan]
          · rw [if_neg hwf]
      | general vs => rfl

/-- The compiled twin read through the public cardinality. -/
theorem cardFast_eq_card (d : Dom) : cardFast d = card d :=
  (cardFast_eq d).trans (card_eq_cardScan d).symm

/-! ### Bounds with fast paths on the hole intervals -/

/-- The integer views of the enumerated values, in enumeration order. -/
def domInts (d : Dom) : List Int := (enum d).filterMap valueIntView

theorem domInts_min?_eq_some_iff {d : Dom} {i : Int} :
    (domInts d).min? = some i ↔
      (∃ v ∈ enum d, valueIntView v = some i) ∧
        ∀ v ∈ enum d, ∀ j : Int, valueIntView v = some j → i ≤ j := by
  unfold domInts
  rw [List.min?_eq_some_iff]
  constructor
  · rintro ⟨hmem, hle⟩
    refine ⟨?_, ?_⟩
    · rw [List.mem_filterMap] at hmem
      obtain ⟨v, hv, hvf⟩ := hmem
      exact ⟨v, hv, hvf⟩
    · intro v hv j hvj
      exact hle j (List.mem_filterMap.mpr ⟨v, hv, hvj⟩)
  · rintro ⟨⟨v, hv, hvf⟩, hle⟩
    refine ⟨?_, ?_⟩
    · exact List.mem_filterMap.mpr ⟨v, hv, hvf⟩
    · intro j hj
      rw [List.mem_filterMap] at hj
      obtain ⟨v', hv', hv'f⟩ := hj
      exact hle v' hv' j hv'f

theorem domInts_max?_eq_some_iff {d : Dom} {i : Int} :
    (domInts d).max? = some i ↔
      (∃ v ∈ enum d, valueIntView v = some i) ∧
        ∀ v ∈ enum d, ∀ j : Int, valueIntView v = some j → j ≤ i := by
  unfold domInts
  rw [List.max?_eq_some_iff]
  constructor
  · rintro ⟨hmem, hle⟩
    refine ⟨?_, ?_⟩
    · rw [List.mem_filterMap] at hmem
      obtain ⟨v, hv, hvf⟩ := hmem
      exact ⟨v, hv, hvf⟩
    · intro v hv j hvj
      exact hle j (List.mem_filterMap.mpr ⟨v, hv, hvj⟩)
  · rintro ⟨⟨v, hv, hvf⟩, hle⟩
    refine ⟨?_, ?_⟩
    · exact List.mem_filterMap.mpr ⟨v, hv, hvf⟩
    · intro j hj
      rw [List.mem_filterMap] at hj
      obtain ⟨v', hv', hv'f⟩ := hj
      exact hle v' hv' j hv'f

theorem domInts_min?_eq_none_iff (d : Dom) :
    (domInts d).min? = none ↔ ∀ v ∈ enum d, valueIntView v = none := by
  unfold domInts
  rw [List.min?_eq_none_iff, List.filterMap_eq_nil_iff]

theorem domInts_max?_eq_none_iff (d : Dom) :
    (domInts d).max? = none ↔ ∀ v ∈ enum d, valueIntView v = none := by
  unfold domInts
  rw [List.max?_eq_none_iff, List.filterMap_eq_nil_iff]

/-- Minimum integer of the domain.  On a hole interval the lower bound
    is read from the endpoint in O(#holes) (`memHoles hs lo`); the
    enumeration scan is the fallback for non-canonical hole data. -/
def minInt? (d : Dom) : Option Int :=
  match d.rep with
  | .holes lo hi hs =>
      if decide (lo ≤ hi) && !(memHoles hs lo) then some lo else (domInts d).min?
  | _ => (domInts d).min?

/-- Maximum integer of the domain.  On a hole interval the upper bound
    is read from the endpoint in O(#holes) (`memHoles hs hi`). -/
def maxInt? (d : Dom) : Option Int :=
  match d.rep with
  | .holes lo hi hs =>
      if decide (lo ≤ hi) && !(memHoles hs hi) then some hi else (domInts d).max?
  | _ => (domInts d).max?

theorem holes_min_mem {lo hi : Int} {hs : List Int}
    (hle : lo ≤ hi) (hnot : lo ∉ hs) :
    ∃ v ∈ enum ⟨.holes lo hi hs⟩, valueIntView v = some lo :=
  ⟨.int lo, mem_map_int.mpr (mem_holesInts.mpr ⟨Int.le_refl lo, hle, hnot⟩), rfl⟩

theorem holes_min_le {lo hi : Int} {hs : List Int} (v : Value)
    (hv : v ∈ enum ⟨.holes lo hi hs⟩) (j : Int) (hvj : valueIntView v = some j) :
    lo ≤ j := by
  obtain ⟨i, rfl⟩ := eq_int_of_mem_holes_enum hv
  have hji : i = j := Option.some.inj hvj
  rw [← hji]
  exact (mem_holes_enum_int.mp hv).1

theorem holes_max_mem {lo hi : Int} {hs : List Int}
    (hle : lo ≤ hi) (hnot : hi ∉ hs) :
    ∃ v ∈ enum ⟨.holes lo hi hs⟩, valueIntView v = some hi :=
  ⟨.int hi, mem_map_int.mpr (mem_holesInts.mpr ⟨hle, Int.le_refl hi, hnot⟩), rfl⟩

theorem holes_max_ge {lo hi : Int} {hs : List Int} (v : Value)
    (hv : v ∈ enum ⟨.holes lo hi hs⟩) (j : Int) (hvj : valueIntView v = some j) :
    j ≤ hi := by
  obtain ⟨i, rfl⟩ := eq_int_of_mem_holes_enum hv
  have hji : i = j := Option.some.inj hvj
  rw [← hji]
  exact (mem_holes_enum_int.mp hv).2.1

/-- Destructuring of the lower fast-path condition. -/
theorem fastCond_lo {lo hi : Int} {hs : List Int}
    (h : (decide (lo ≤ hi) && !(memHoles hs lo)) = true) :
    lo ≤ hi ∧ lo ∉ hs := by
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, memHoles_eq_false.mp (eq_false_of_not_eq_true h.2)⟩

/-- Destructuring of the upper fast-path condition. -/
theorem fastCond_hi {lo hi : Int} {hs : List Int}
    (h : (decide (lo ≤ hi) && !(memHoles hs hi)) = true) :
    lo ≤ hi ∧ hi ∉ hs := by
  rw [Bool.and_eq_true] at h
  exact ⟨of_decide_eq_true h.1, memHoles_eq_false.mp (eq_false_of_not_eq_true h.2)⟩

theorem minInt?_eq_some_iff {d : Dom} {i : Int} :
    minInt? d = some i ↔
      (∃ v ∈ enum d, valueIntView v = some i) ∧
        ∀ v ∈ enum d, ∀ j : Int, valueIntView v = some j → i ≤ j := by
  cases d with
  | mk rep =>
      cases rep with
      | holes lo hi hs =>
          dsimp only [minInt?]
          by_cases hcond : (decide (lo ≤ hi) && !(memHoles hs lo)) = true
          · rw [if_pos hcond]
            obtain ⟨hle, hnot⟩ := fastCond_lo hcond
            have hmem := holes_min_mem hle hnot
            have hmin : ∀ v ∈ enum ⟨.holes lo hi hs⟩, ∀ j : Int,
                valueIntView v = some j → lo ≤ j :=
              fun v hv j hvj => holes_min_le v hv j hvj
            constructor
            · intro h
              have hilo : i = lo := (Option.some.inj h).symm
              subst hilo
              exact ⟨hmem, hmin⟩
            · rintro ⟨hview, hleast⟩
              have h1 : lo ≤ i := by
                obtain ⟨v, hv, hvj⟩ := hview
                exact hmin v hv i hvj
              have h2 : i ≤ lo := by
                obtain ⟨v0, hv0, hv0j⟩ := hmem
                exact hleast v0 hv0 lo hv0j
              have hilo : i = lo := by omega
              subst hilo
              rfl
          · rw [if_neg hcond]
            exact domInts_min?_eq_some_iff
      | small isBool off bits => dsimp only [minInt?]; exact domInts_min?_eq_some_iff
      | general vs => dsimp only [minInt?]; exact domInts_min?_eq_some_iff

theorem maxInt?_eq_some_iff {d : Dom} {i : Int} :
    maxInt? d = some i ↔
      (∃ v ∈ enum d, valueIntView v = some i) ∧
        ∀ v ∈ enum d, ∀ j : Int, valueIntView v = some j → j ≤ i := by
  cases d with
  | mk rep =>
      cases rep with
      | holes lo hi hs =>
          dsimp only [maxInt?]
          by_cases hcond : (decide (lo ≤ hi) && !(memHoles hs hi)) = true
          · rw [if_pos hcond]
            obtain ⟨hle, hnot⟩ := fastCond_hi hcond
            have hmem := holes_max_mem hle hnot
            have hmax : ∀ v ∈ enum ⟨.holes lo hi hs⟩, ∀ j : Int,
                valueIntView v = some j → j ≤ hi :=
              fun v hv j hvj => holes_max_ge v hv j hvj
            constructor
            · intro h
              have hihi : i = hi := (Option.some.inj h).symm
              subst hihi
              exact ⟨hmem, hmax⟩
            · rintro ⟨hview, hgreatest⟩
              have h1 : hi ≤ i := by
                obtain ⟨v0, hv0, hv0j⟩ := hmem
                exact hgreatest v0 hv0 hi hv0j
              have h2 : i ≤ hi := by
                obtain ⟨v, hv, hvj⟩ := hview
                exact hmax v hv i hvj
              have hihi : i = hi := by omega
              subst hihi
              rfl
          · rw [if_neg hcond]
            exact domInts_max?_eq_some_iff
      | small isBool off bits => dsimp only [maxInt?]; exact domInts_max?_eq_some_iff
      | general vs => dsimp only [maxInt?]; exact domInts_max?_eq_some_iff

theorem minInt?_eq_none_iff (d : Dom) :
    minInt? d = none ↔ ∀ v ∈ enum d, valueIntView v = none := by
  cases d with
  | mk rep =>
      cases rep with
      | holes lo hi hs =>
          dsimp only [minInt?]
          by_cases hcond : (decide (lo ≤ hi) && !(memHoles hs lo)) = true
          · rw [if_pos hcond]
            obtain ⟨hle, hnot⟩ := fastCond_lo hcond
            refine ⟨fun h => absurd h (by simp), fun h => ?_⟩
            exact absurd (h (.int lo)
              (mem_map_int.mpr (mem_holesInts.mpr ⟨Int.le_refl lo, hle, hnot⟩)))
              (by simp [valueIntView])
          · rw [if_neg hcond]
            exact domInts_min?_eq_none_iff _
      | small isBool off bits => dsimp only [minInt?]; exact domInts_min?_eq_none_iff _
      | general vs => dsimp only [minInt?]; exact domInts_min?_eq_none_iff _

theorem maxInt?_eq_none_iff (d : Dom) :
    maxInt? d = none ↔ ∀ v ∈ enum d, valueIntView v = none := by
  cases d with
  | mk rep =>
      cases rep with
      | holes lo hi hs =>
          dsimp only [maxInt?]
          by_cases hcond : (decide (lo ≤ hi) && !(memHoles hs hi)) = true
          · rw [if_pos hcond]
            obtain ⟨hle, hnot⟩ := fastCond_hi hcond
            refine ⟨fun h => absurd h (by simp), fun h => ?_⟩
            exact absurd (h (.int hi)
              (mem_map_int.mpr (mem_holesInts.mpr ⟨hle, Int.le_refl hi, hnot⟩)))
              (by simp [valueIntView])
          · rw [if_neg hcond]
            exact domInts_max?_eq_none_iff _
      | small isBool off bits => dsimp only [maxInt?]; exact domInts_max?_eq_none_iff _
      | general vs => dsimp only [maxInt?]; exact domInts_max?_eq_none_iff _

/-- **Conservation (`SlotSum` min field)**: the fast query equals the
    minimum of `Value.intView` over the enumeration. -/
theorem minInt?_eq_domInts_min (d : Dom) : minInt? d = (domInts d).min? := by
  cases d with
  | mk rep =>
      cases rep with
      | holes lo hi hs =>
          dsimp only [minInt?]
          by_cases hcond : (decide (lo ≤ hi) && !(memHoles hs lo)) = true
          · rw [if_pos hcond]
            obtain ⟨hle, hnot⟩ := fastCond_lo hcond
            exact (List.min?_eq_some_iff.mpr
              ⟨List.mem_filterMap.mpr (holes_min_mem hle hnot),
                fun b hb => by
                  obtain ⟨v, hv, hvj⟩ := List.mem_filterMap.mp hb
                  exact holes_min_le v hv b hvj⟩).symm
          · rw [if_neg hcond]
      | small isBool off bits => dsimp only [minInt?]
      | general vs => dsimp only [minInt?]

/-- **Conservation (`SlotSum` max field)**: the fast query equals the
    maximum of `Value.intView` over the enumeration. -/
theorem maxInt?_eq_domInts_max (d : Dom) : maxInt? d = (domInts d).max? := by
  cases d with
  | mk rep =>
      cases rep with
      | holes lo hi hs =>
          dsimp only [maxInt?]
          by_cases hcond : (decide (lo ≤ hi) && !(memHoles hs hi)) = true
          · rw [if_pos hcond]
            obtain ⟨hle, hnot⟩ := fastCond_hi hcond
            exact (List.max?_eq_some_iff.mpr
              ⟨List.mem_filterMap.mpr (holes_max_mem hle hnot),
                fun b hb => by
                  obtain ⟨v, hv, hvj⟩ := List.mem_filterMap.mp hb
                  exact holes_max_ge v hv b hvj⟩).symm
          · rw [if_neg hcond]
      | small isBool off bits => dsimp only [maxInt?]
      | general vs => dsimp only [maxInt?]

/-! ### Structural fast twins for the compact bounds

The logical bounds scan `domInts`.  The compiled twins read the small bitset
directly (an `O(64)` scan over `smallInts`, without materialising the
`Value.int` wrappers), keeping the hole endpoint fast path.  The equality
theorems are checked here; the `@[implemented_by]` attributes live below. -/

private theorem filterMap_valueIntView_map_int (xs : List Int) :
    (xs.map Value.int).filterMap valueIntView = xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.filterMap_cons, valueIntView, ih]

private theorem domInts_small_false (off : Int) (bits : UInt64) :
    domInts ⟨.small false off bits⟩ = smallInts off bits := by
  unfold domInts enum
  rw [filterMap_valueIntView_map_int]

/-- The minimum of a packed integer list whose bit 0 is set is its offset. -/
theorem smallInts_min?_eq_head {off : Int} {bits : UInt64}
    (h0 : bits.toNat.testBit 0 = true) :
    (smallInts off bits).min? = some off := by
  rw [List.min?_eq_some_iff]
  refine ⟨?_, ?_⟩
  · have h := (mem_smallInts_iff (off := off) (bits := bits) (k := 0)
      (by decide)).mpr h0
    simpa using h
  · intro y hy
    obtain ⟨k, hk, hbit, heq⟩ := mem_smallInts.mp hy
    rw [← heq]
    omega

/-- The maximum of a nonempty packed integer list is the offset plus the
    index of its highest set bit. -/
theorem smallInts_max?_eq_log2 {off : Int} {bits : UInt64}
    (hne : bits.toNat ≠ 0) :
    (smallInts off bits).max? = some (off + (bits.toNat.log2 : Int)) := by
  rw [List.max?_eq_some_iff]
  refine ⟨?_, ?_⟩
  · have hlt : bits.toNat.log2 < 64 := by
      rw [Nat.log2_lt hne]
      exact UInt64.toNat_lt bits
    have hmem := (mem_smallInts_iff (off := off) (bits := bits)
      (k := bits.toNat.log2) hlt).mpr (Nat.testBit_log2 hne)
    simpa using hmem
  · intro y hy
    obtain ⟨k, hk, hbit, heq⟩ := mem_smallInts.mp hy
    rw [← heq]
    have hkle : k ≤ bits.toNat.log2 := by
      rw [Nat.le_log2 hne]
      exact Nat.ge_two_pow_of_testBit hbit
    omega

/-- Compiled twin of `minInt?` for small integer bitsets: the minimum of a
    canonical bitset is its offset (bit 0 set), read without materialising
    `smallInts`; the non-canonical fallback enumerates. -/
def minInt?Fast (d : Dom) : Option Int :=
  match d.rep with
  | .holes lo hi hs =>
      if decide (lo ≤ hi) && !(memHoles hs lo) then some lo else (domInts d).min?
  | .small false off bits =>
      if bits.toNat.testBit 0 then some off else (smallInts off bits).min?
  | _ => (domInts d).min?

theorem minInt?Fast_eq (d : Dom) : minInt?Fast d = minInt? d := by
  cases d with
  | mk rep =>
    cases rep with
    | holes lo hi hs => dsimp only [minInt?Fast, minInt?]
    | small isBool off bits =>
      cases isBool with
      | true => dsimp only [minInt?Fast, minInt?]
      | false =>
        dsimp only [minInt?Fast, minInt?]
        rw [domInts_small_false]
        by_cases h0 : bits.toNat.testBit 0 = true
        · rw [if_pos h0, smallInts_min?_eq_head h0]
        · rw [if_neg h0]
    | general vs => dsimp only [minInt?Fast, minInt?]

/-- Compiled twin of `maxInt?` for small integer bitsets: the maximum is the
    offset plus the highest set-bit index, read without materialising
    `smallInts`. -/
def maxInt?Fast (d : Dom) : Option Int :=
  match d.rep with
  | .holes lo hi hs =>
      if decide (lo ≤ hi) && !(memHoles hs hi) then some hi else (domInts d).max?
  | .small false off bits =>
      if h : bits.toNat = 0 then none
      else some (off + (bits.toNat.log2 : Int))
  | _ => (domInts d).max?

theorem maxInt?Fast_eq (d : Dom) : maxInt?Fast d = maxInt? d := by
  cases d with
  | mk rep =>
    cases rep with
    | holes lo hi hs => dsimp only [maxInt?Fast, maxInt?]
    | small isBool off bits =>
      cases isBool with
      | true => dsimp only [maxInt?Fast, maxInt?]
      | false =>
        dsimp only [maxInt?Fast, maxInt?]
        rw [domInts_small_false]
        by_cases h0 : bits.toNat = 0
        · rw [dif_pos h0]
          have hnil : smallInts off bits = [] := by
            unfold smallInts
            rw [h0]
            simp [Nat.zero_testBit]
          rw [hnil]
          rfl
        · rw [dif_neg h0, smallInts_max?_eq_log2 h0]
    | general vs => dsimp only [maxInt?Fast, maxInt?]

attribute [implemented_by minInt?Fast] minInt?
attribute [implemented_by maxInt?Fast] maxInt?

/-- The integer `v` when the domain denotes exactly `[.int v]`.  Structural
    on the compact representation: `.general` matches the stored list,
    `.small true` cannot be an integer singleton, and the integer cases use
    `card` plus the stored extrema instead of materialising `enum`. -/
def intSingleton? (d : Dom) : Option Int :=
  match d.rep with
  | .general vs =>
      match vs with
      | [.int v] => some v
      | _ => none
  | .small true _ _ => none
  | .small false off bits =>
      if d.card == 1 then some (off + (bits.toNat.log2 : Int)) else none
  | .holes _ _ _ =>
      if d.card == 1 then
        match d.minInt?, d.maxInt? with
        | some lo, some hi => if lo == hi then some lo else none
        | _, _ => none
      else none

/-- A small integer bitset with exactly one value is the singleton list holding
    the value at the highest set bit (`Nat.log2`). -/
theorem smallInts_singleton_log2 {off : Int} {bits : UInt64}
    (hlen : (smallInts off bits).length = 1) :
    smallInts off bits = [off + (bits.toNat.log2 : Int)] := by
  obtain ⟨x, hx⟩ := List.length_eq_one_iff.mp hlen
  have hmemx : x ∈ smallInts off bits := by rw [hx]; simp
  obtain ⟨k, hk64, hbit, hoffk⟩ := mem_smallInts.mp hmemx
  have hne : bits.toNat ≠ 0 := by
    intro h0
    rw [h0] at hbit
    simp at hbit
  have hlog : bits.toNat.log2 < 64 := by
    rw [Nat.log2_lt hne]
    exact UInt64.toNat_lt bits
  have hmemlog : off + (bits.toNat.log2 : Int) ∈ smallInts off bits :=
    (mem_smallInts_iff hlog).mpr (Nat.testBit_log2 hne)
  rw [hx] at hmemlog
  rw [hx, List.mem_singleton.mp hmemlog]

theorem intSingleton?_eq (d : Dom) :
    intSingleton? d = (match enum d with | [.int v] => some v | _ => none) := by
  cases d with
  | mk rep =>
      cases rep with
      | general vs => rfl
      | small isBool off bits =>
          cases isBool with
          | true =>
              cases h0 : bits.toNat.testBit 0 <;> cases h1 : bits.toNat.testBit 1 <;>
                simp [intSingleton?, enum, smallBools, List.range_succ_eq_map, h0, h1]
          | false =>
              by_cases hc : (⟨.small false off bits⟩ : Dom).card = 1
              · have hlen : (smallInts off bits).length = 1 := by
                  have h := hc
                  rw [card_eq_length_enum] at h
                  simpa [enum, List.length_map] using h
                have hlist := smallInts_singleton_log2 hlen
                have hen : enum ⟨.small false off bits⟩ =
                    [.int (off + (bits.toNat.log2 : Int))] := by
                  change (smallInts off bits).map Value.int =
                    [.int (off + (bits.toNat.log2 : Int))]
                  rw [hlist]
                  rfl
                have hc1 : ((⟨.small false off bits⟩ : Dom).card == 1) = true := by
                  rw [hc]; rfl
                have hl : (⟨.small false off bits⟩ : Dom).intSingleton? =
                    some (off + (bits.toNat.log2 : Int)) := by
                  simp [intSingleton?, hc1]
                rw [hl, hen]
              · have hne1 : (enum ⟨.small false off bits⟩).length ≠ 1 := by
                  intro h
                  apply hc
                  rw [card_eq_length_enum]
                  exact h
                have hb : ((⟨.small false off bits⟩ : Dom).card == 1) = false := by
                  rw [beq_eq_false_iff_ne]; exact hc
                have hl : (⟨.small false off bits⟩ : Dom).intSingleton? = none := by
                  simp [intSingleton?, hb]
                rw [hl]
                cases hen : enum ⟨.small false off bits⟩ with
                | nil => rfl
                | cons x xs =>
                    cases xs with
                    | nil =>
                        exact absurd (by rw [hen]; rfl : (enum ⟨.small false off bits⟩).length = 1) hne1
                    | cons y ys => simp
      | holes lo hi hs =>
          cases hx : enum ⟨.holes lo hi hs⟩ with
          | nil =>
              have hc : (⟨.holes lo hi hs⟩ : Dom).card = 0 := by
                rw [card_eq_length_enum, hx]; rfl
              have hb : ((⟨.holes lo hi hs⟩ : Dom).card == 1) = false := by
                rw [hc]; rfl
              have hl : (⟨.holes lo hi hs⟩ : Dom).intSingleton? = none := by
                simp [intSingleton?, hb]
              rw [hl]
          | cons x xs =>
              cases xs with
              | nil =>
                  obtain ⟨i, hi⟩ := eq_int_of_mem_holes_enum (v := x) (by rw [hx]; simp)
                  subst hi
                  have hcard : (⟨.holes lo hi hs⟩ : Dom).card = 1 := by
                    rw [card_eq_length_enum, hx]; rfl
                  have hmin : (⟨.holes lo hi hs⟩ : Dom).minInt? = some i := by
                    rw [minInt?_eq_some_iff]
                    refine ⟨⟨.int i, by rw [hx]; simp, rfl⟩, ?_⟩
                    intro w hw j hj
                    rw [hx] at hw
                    simp only [List.mem_singleton] at hw
                    subst hw
                    exact Option.some.inj hj ▸ Int.le_refl j
                  have hmax : (⟨.holes lo hi hs⟩ : Dom).maxInt? = some i := by
                    rw [maxInt?_eq_some_iff]
                    refine ⟨⟨.int i, by rw [hx]; simp, rfl⟩, ?_⟩
                    intro w hw j hj
                    rw [hx] at hw
                    simp only [List.mem_singleton] at hw
                    subst hw
                    exact Option.some.inj hj ▸ Int.le_refl j
                  have hl : (⟨.holes lo hi hs⟩ : Dom).intSingleton? = some i := by
                    unfold intSingleton?
                    rw [if_pos (by rw [hcard]; rfl), hmin, hmax]
                    simp
                  rw [hl]
              | cons y ys =>
                  have hc : (⟨.holes lo hi hs⟩ : Dom).card ≠ 1 := by
                    rw [card_eq_length_enum, hx]; simp
                  have hb : ((⟨.holes lo hi hs⟩ : Dom).card == 1) = false := by
                    rw [beq_eq_false_iff_ne]; exact hc
                  have hl : (⟨.holes lo hi hs⟩ : Dom).intSingleton? = none := by
                    simp [intSingleton?, hb]
                  rw [hl]; simp

/-- Structural Boolean-singleton test: `.general` matches the stored list,
    `.small true` reads the two bits, and the integer-only representations
    are never Boolean-valued. -/
def boolSingleton? (d : Dom) : Option Bool :=
  match d.rep with
  | .general vs =>
      match vs with
      | [.bool b] => some b
      | _ => none
  | .small true _ bits =>
      if bits.toNat.testBit 0 then
        (if bits.toNat.testBit 1 then none else some false)
      else
        (if bits.toNat.testBit 1 then some true else none)
  | .small false _ _ => none
  | .holes _ _ _ => none

theorem boolSingleton?_eq (d : Dom) :
    boolSingleton? d = (match enum d with | [.bool b] => some b | _ => none) := by
  cases d with
  | mk rep =>
    cases rep with
    | general vs =>
        cases vs with
        | nil => rfl
        | cons v vs =>
            cases vs with
            | nil =>
                cases v with
                | bool b => rfl
                | int i => rfl
                | setOfInt s => rfl
                | array a => rfl
            | cons w ws => rfl
    | small isBool off bits =>
        cases isBool with
        | true =>
            cases h0 : bits.toNat.testBit 0 <;> cases h1 : bits.toNat.testBit 1 <;>
              simp [boolSingleton?, enum, smallBools, List.range_succ_eq_map, h0, h1]
        | false =>
            simp only [boolSingleton?]
            cases h : smallInts off bits <;> simp [enum, h]
    | holes lo hi hs =>
        simp only [boolSingleton?]
        cases h : holesInts lo hi hs <;> simp [enum, h]

/-- A value is a Boolean constructor. -/
def isBoolV (v : Value) : Bool :=
  match v with | .bool _ => true | _ => false

theorem allBool_map_int (l : List Int) :
    (l.map Value.int).all isBoolV = l.isEmpty := by
  cases l <;> simp [isBoolV]

/-- Structural "every value is Boolean": `.general` scans the stored list,
    `.small true` is at most two Boolean values, and the integer-only
    representations are Boolean-valued only when empty. -/
def allBoolBStruct (d : Dom) : Bool :=
  match d.rep with
  | .general vs => vs.all isBoolV
  | .small true _ bits => (smallBools bits).all isBoolV
  | .small false _ _ => d.card == 0
  | .holes _ _ _ => d.card == 0

theorem allBoolBStruct_eq (d : Dom) : allBoolBStruct d = d.enum.all isBoolV := by
  cases d with
  | mk rep =>
    cases rep with
    | general vs => rfl
    | small b off bits =>
        cases b with
        | true => rfl
        | false =>
            unfold allBoolBStruct
            simp only
            rw [card_eq_length_enum]
            rw [enum]
            rw [allBool_map_int]
            cases h : smallInts off bits <;> simp [h]
    | holes lo hi hs =>
        unfold allBoolBStruct
        simp only
        rw [card_eq_length_enum]
        rw [enum]
        rw [allBool_map_int]
        cases h : holesInts lo hi hs <;> simp [h]

/-- A value is an integer constructor. -/
def isIntV (v : Value) : Bool :=
  match v with | .int _ => true | _ => false

/-- Structural "every value is an integer": the compact integer
    representations are integer-valued (or empty), `.small true` is
    integer-valued only when empty, and `.general` scans its stored list. -/
def allIntBStruct (d : Dom) : Bool :=
  match d.rep with
  | .general vs => vs.all isIntV
  | .small true _ bits => d.card == 0
  | .small false _ _ => true
  | .holes _ _ _ => true

theorem allIntBStruct_eq (d : Dom) : allIntBStruct d = d.enum.all isIntV := by
  cases d with
  | mk rep =>
    cases rep with
    | general vs => rfl
    | small b off bits =>
        cases b with
        | true =>
            unfold allIntBStruct
            simp only
            rw [card_eq_length_enum]
            rw [enum]
            cases h : smallBools bits with
            | nil => simp [h]
            | cons v vs =>
                have hv : v ∈ smallBools bits := by rw [h]; exact List.mem_cons_self ..
                obtain ⟨b, rfl, -⟩ := mem_smallBools.mp hv
                simp [h, isIntV]
        | false =>
            unfold allIntBStruct
            rw [enum]
            simp [isIntV]
    | holes lo hi hs =>
        unfold allIntBStruct
        rw [enum]
        simp [isIntV]

/-- Structural Boolean membership: `.general` scans the stored list and
    `.small true` scans its at-most-two Boolean values; the integer-only
    representations contain no Boolean. -/
def hasBoolBStruct (d : Dom) (c : Bool) : Bool :=
  match d.rep with
  | .general vs => vs.any fun v => match v with | .bool b => b == c | _ => false
  | .small true _ bits =>
      (smallBools bits).any fun v => match v with | .bool b => b == c | _ => false
  | .small false _ _ => false
  | .holes _ _ _ => false

theorem hasBoolBStruct_eq (d : Dom) (c : Bool) :
    hasBoolBStruct d c =
      d.enum.any (fun v => match v with | .bool b => b == c | _ => false) := by
  cases d with
  | mk rep =>
    cases rep with
    | general vs => rfl
    | small b off bits =>
        cases b with
        | true => rfl
        | false => simp [hasBoolBStruct, enum, List.any_map]
    | holes lo hi hs => simp [hasBoolBStruct, enum, List.any_map]

/-! ### Filtering -/

/-- Filter by a value predicate.  A filter that removes nothing returns the
    original domain definitionally, so no-op filters are invisible to
    proofs that later read the same slot (and reuse the same compact
    representation). -/
def filter (p : Value → Bool) (d : Dom) : Dom :=
  let vs := enum d
  let kept := vs.filter p
  if kept.length = vs.length then d else ofList kept

theorem enum_filter (p : Value → Bool) (d : Dom) :
    enum (filter p d) = (enum d).filter p := by
  unfold filter
  dsimp only
  split
  · rename_i h
    have hkept : (enum d).filter p = enum d :=
      List.Sublist.eq_of_length List.filter_sublist h
    rw [hkept]
  · rename_i h
    rw [enum_ofList]

theorem filter_eq_self {p : Value → Bool} {d : Dom}
    (h : ∀ v ∈ enum d, p v = true) :
    filter p d = d := by
  unfold filter
  dsimp only
  have hkept : (enum d).filter p = enum d := by
    rw [List.filter_eq_self]
    exact h
  rw [hkept, if_pos rfl]

theorem wf_filter (p : Value → Bool) (d : Dom) (hd : WF d) : WF (filter p d) := by
  unfold filter
  dsimp only
  split
  · exact hd
  · exact WF_ofList _

theorem memBool_filter {p : Value → Bool} {d : Dom} {v : Value} :
    memBool (filter p d) v = true ↔ memBool d v = true ∧ p v = true := by
  rw [memBool_iff, enum_filter, memBool_iff, List.mem_filter]

theorem card_filter_le (p : Value → Bool) (d : Dom) : card (filter p d) ≤ card d := by
  rw [card_eq_length_enum, card_eq_length_enum, enum_filter]
  exact List.length_filter_le _ _

theorem length_filter_le (p : Value → Bool) (d : Dom) :
    (filter p d).length ≤ d.length := by
  rw [length_eq_card, length_eq_card]
  exact card_filter_le p d

end Dom

/-- The empty compact domain, so the legacy `[]` literal keeps working. -/
instance : EmptyCollection Dom := ⟨Dom.empty⟩

/-- The compact domain carrier enumerates through its denotation and
    carries the exact compact membership test; `Dom.memBool_iff` relates
    it to `List.Mem` on `Dom.enum`.  The `Membership` instance is the
    parent projection of this class instance. -/
instance : LeanFzn.Solver.Core.DomainLike Dom where
  mem := fun d v => Dom.memBool d v = true
  elems := Dom.enum
  empty := Dom.empty
  mem_iff := fun d v => Dom.memBool_iff d v

/-- Unfolding the compact carrier's enumeration for `simp`. -/
@[simp] theorem domElems_eq_enum (d : Dom) :
    LeanFzn.Solver.Core.DomainElems.elems d = Dom.enum d := rfl

/-- Unfolding the compact carrier's empty slot for `simp`. -/
@[simp] theorem domEmpty_eq : LeanFzn.Solver.Core.DomainLike.empty (α := Dom) = Dom.empty := rfl

/-- Membership in a canonicalized list domain is list membership. -/
@[simp] theorem mem_ofList_iff (v : Value) (vs : List Value) :
    v ∈ Dom.ofList vs ↔ v ∈ vs := by
  rw [LeanFzn.Solver.Core.DomainLike.mem_iff, domElems_eq_enum, Dom.enum_ofList]

/-- No value is a member of the empty compact domain. -/
@[simp] theorem mem_empty_iff (v : Value) : v ∈ (Dom.empty : Dom) ↔ False := by
  rw [LeanFzn.Solver.Core.DomainLike.mem_iff, domElems_eq_enum, Dom.enum_empty]
  simp

/-- The cardinality of a canonicalized list is the list length. -/
@[simp] theorem length_ofList (vs : List Value) : (Dom.ofList vs).length = vs.length := by
  rw [Dom.length_eq_enum, Dom.enum_ofList]

/-- The cardinality of the empty compact domain is zero. -/
@[simp] theorem length_empty : (Dom.empty : Dom).length = 0 := by
  rw [Dom.length_eq_enum, Dom.enum_empty]
  rfl

/-- Permutation of compact domains, read through the value enumeration.
    Presentations that only reorder a domain's trial order use this
    relation; it is the compact analogue of `List.Perm` on the legacy list
    carrier. -/
def Dom.Perm (d e : Dom) : Prop := (Dom.enum d).Perm (Dom.enum e)

namespace Dom

theorem Perm.refl (d : Dom) : d.Perm d := List.Perm.refl _

theorem Perm.symm {d e : Dom} (h : d.Perm e) : e.Perm d := List.Perm.symm h

theorem Perm.trans {d e f : Dom} (h₁ : d.Perm e) (h₂ : e.Perm f) : d.Perm f :=
  List.Perm.trans h₁ h₂

/-- Permutation-equivalent domains have the same cardinality. -/
theorem Perm.length_eq {d e : Dom} (h : d.Perm e) : d.length = e.length := by
  rw [length_eq_enum, length_eq_enum]
  exact List.Perm.length_eq h

/-- Permutation-equivalent domains have the same enumerated members. -/
theorem Perm.mem_iff {d e : Dom} (h : d.Perm e) {v : Value} :
    v ∈ Dom.enum d ↔ v ∈ Dom.enum e := List.Perm.mem_iff h

/-- Permutation-equivalent domains have the same class-level members. -/
theorem Perm.dom_mem_iff {d e : Dom} (h : d.Perm e) {v : Value} :
    v ∈ d ↔ v ∈ e := by
  rw [LeanFzn.Solver.Core.DomainLike.mem_iff d v,
    LeanFzn.Solver.Core.DomainLike.mem_iff e v, domElems_eq_enum, domElems_eq_enum]
  exact h.mem_iff

/-- Permutation is contained in the enumeration subset relation. -/
theorem Perm.subset {d e : Dom} (h : d.Perm e) : (Dom.enum d) ⊆ (Dom.enum e) :=
  List.Perm.subset h

/-- A permutation maps to a permutation of the mapped enumerations. -/
theorem Perm.map {d e : Dom} (h : d.Perm e) (f : Value → α) :
    List.Perm ((Dom.enum d).map f) ((Dom.enum e).map f) := List.Perm.map f h

end Dom

/-- Membership commutes with the compact filter. -/
@[simp] theorem mem_filter_iff {p : Value → Bool} {d : Dom} {v : Value} :
    v ∈ Dom.filter p d ↔ v ∈ d ∧ p v = true := by
  change Dom.memBool (Dom.filter p d) v = true ↔
    Dom.memBool d v = true ∧ p v = true
  exact Dom.memBool_filter

/-- The compact filter is empty exactly when it drops every member. -/
@[simp] theorem enum_filter_eq_nil_iff {p : Value → Bool} {d : Dom} :
    (Dom.filter p d).enum = [] ↔ ∀ v ∈ d, ¬ p v = true := by
  rw [Dom.enum_filter]
  constructor
  · intro h v hv
    exact List.filter_eq_nil_iff.mp h v ((Dom.memBool_iff d v).mp hv)
  · intro h
    exact List.filter_eq_nil_iff.mpr (fun v hv => h v ((Dom.memBool_iff d v).mpr hv))

namespace Dom

/-- Membership in a filtered domain is membership plus the predicate. -/
theorem mem_filter {p : Value → Bool} {d : Dom} {v : Value} :
    v ∈ Dom.filter p d ↔ v ∈ d ∧ p v = true := by
  have hiff : v ∈ Dom.filter p d ↔ Dom.memBool (Dom.filter p d) v = true := by
    rw [LeanFzn.Solver.Core.DomainLike.mem_iff, domElems_eq_enum]
    exact (Dom.memBool_iff (Dom.filter p d) v).symm
  rw [hiff, Dom.memBool_filter]
  constructor
  · rintro ⟨hm, hp⟩
    refine ⟨?_, hp⟩
    rw [LeanFzn.Solver.Core.DomainLike.mem_iff, domElems_eq_enum,
      ← Dom.memBool_iff]
    exact hm
  · rintro ⟨hv, hp⟩
    refine ⟨?_, hp⟩
    rw [LeanFzn.Solver.Core.DomainLike.mem_iff, domElems_eq_enum,
      ← Dom.memBool_iff] at hv
    exact hv

end Dom

end LeanFzn.Solver.Propagation
