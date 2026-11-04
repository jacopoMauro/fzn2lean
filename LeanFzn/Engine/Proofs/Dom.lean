/-
File: LeanFzn/Engine/Proofs/Dom.lean

N3b: the compact-domain operation-law layer for Core.

`LeanFzn/Engine/Dom.lean` (N3) defines the compact representation, the
membership test `DomC.mem`, the operations `setLe`/`setGe`/`remove`/`fix`,
`evalLit`/`applyLit`, and the entry conversion, but proves no operation
laws.  This module supplies them:

* well-formedness preservation for every restriction operation;
* endpoint laws (`lo?_le`, `le_hi?`) and the fixed-value characterisation
  (`fixedValue_sound`);
* exact membership laws for `setLe`, `setGe`, `remove`, `removeIntView`,
  `fix`, `fixIntView`, plus emptiness;
* literal soundness (`evalLit_true_sound`, `evalLit_false_sound`) and the
  key N8 law `mem_applyLit`.

Everything here is proof-only: no new runtime definition is exported for
the engine (the scan helpers below are private mirrors of the existing
`lowestBit`/`highestBit` loops, used to state their specifications).

Dependencies:
  - LeanFzn.Engine.Dom: the representation and the operations.
  - LeanFzn.Solver.Propagation.BoolImplication / CompactDomain: the pointwise
    `Literal.valueHolds_*` facts (not their `Dom`-representation `WF`).

DAG: LeanFzn.Engine.Dom -> LeanFzn.Engine.Proofs.Dom
-/
import LeanFzn.Engine.Dom
import LeanFzn.Solver.Propagation.BoolImplication
import LeanFzn.Solver.Propagation.CompactDomain

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## The integer view as an `Int` -/

/-- The integer view with a default for non-integer values.  Membership in a
    compact domain is only ever true for values with an integer view, so the
    default is never observed on a member. -/
abbrev iv (v : Value) : Int := (Value.intView v).getD 0

theorem iv_of_intView {v : Value} {i : Int} (h : Value.intView v = some i) :
    iv v = i := by
  simp [iv, h]

theorem intView_iv {v : Value} :
    Value.intView v = some (iv v) ∨ Value.intView v = none := by
  unfold iv
  cases h : Value.intView v with
  | none => exact Or.inr rfl
  | some i => exact Or.inl (by simp [h])

theorem iv_eq_of_mem_intView {d : DomC} {v : Value} {i : Int}
    (hm : d.mem v = true) (hv : Value.intView v = some i) : iv v = i :=
  iv_of_intView hv

/-! ## Specifications for `lowestBit` and `highestBit`

The public scans are fuelled local recursions.  We restate them as plain
structural recursions and prove the restart equation, then show the
specification on the structural version. -/

private def lowestBitAux (w : UInt64) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, k =>
      if k < 64 then
        if w &&& u64bit k != 0 then k else lowestBitAux w fuel (k + 1)
      else 0

private def highestBitAux (w : UInt64) : Nat → Nat → Nat
  | 0, _ => 0
  | fuel + 1, k =>
      if k < 64 then
        if w &&& u64bit (63 - k) != 0 then 63 - k else highestBitAux w fuel (k + 1)
      else 0

private theorem lowestBit_go_eq_aux (w : UInt64) :
    ∀ (fuel k : Nat), 64 - k ≤ fuel → lowestBit.go w k = lowestBitAux w fuel k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk
      have hk64 : ¬ k < 64 := by omega
      rw [lowestBit.go.eq_1, if_neg hk64]
      rfl
  | succ fuel ih =>
      intro k hk
      rw [lowestBit.go.eq_1]
      by_cases h64 : k < 64
      · rw [if_pos h64]
        by_cases hbit : w &&& u64bit k != 0
        · rw [if_pos hbit]
          simp only [lowestBitAux]
          rw [if_pos h64, if_pos hbit]
        · rw [if_neg hbit]
          simp only [lowestBitAux]
          rw [if_pos h64, if_neg hbit]
          exact ih (k + 1) (by omega)
      · rw [if_neg h64]
        simp only [lowestBitAux]
        rw [if_neg h64]

private theorem highestBit_go_eq_aux (w : UInt64) :
    ∀ (fuel k : Nat), 64 - k ≤ fuel → highestBit.go w k = highestBitAux w fuel k := by
  intro fuel
  induction fuel with
  | zero =>
      intro k hk
      have hk64 : ¬ k < 64 := by omega
      rw [highestBit.go.eq_1, if_neg hk64]
      rfl
  | succ fuel ih =>
      intro k hk
      rw [highestBit.go.eq_1]
      by_cases h64 : k < 64
      · rw [if_pos h64]
        by_cases hbit : w &&& u64bit (63 - k) != 0
        · rw [if_pos hbit]
          simp only [highestBitAux]
          rw [if_pos h64, if_pos hbit]
        · rw [if_neg hbit]
          simp only [highestBitAux]
          rw [if_pos h64, if_neg hbit]
          exact ih (k + 1) (by omega)
      · rw [if_neg h64]
        simp only [highestBitAux]
        rw [if_neg h64]

private theorem lowestBitAux_spec (w : UInt64) :
    ∀ (n k : Nat), 64 ≤ k + n → k ≤ 64 →
      (lowestBitAux w n k < 64 ∧ k ≤ lowestBitAux w n k ∧
        w.toNat.testBit (lowestBitAux w n k) = true ∧
        ∀ j, k ≤ j → j < lowestBitAux w n k → w.toNat.testBit j = false) ∨
      (lowestBitAux w n k = 0 ∧
        ∀ j, k ≤ j → j < 64 → w.toNat.testBit j = false) := by
  intro n
  induction n with
  | zero =>
      intro k hfull hk
      right
      refine ⟨rfl, ?_⟩
      intro j hj hj64
      omega
  | succ n ih =>
      intro k hfull hk
      by_cases h64 : k < 64
      · simp only [lowestBitAux]
        rw [if_pos h64]
        by_cases hbit : w &&& u64bit k != 0
        · left
          rw [if_pos hbit]
          have hset : w.toNat.testBit k = true :=
            (uint64_and_u64bit_ne_zero_iff w h64).mp hbit
          exact ⟨h64, Nat.le_refl k, hset, by intro j _ hjk; omega⟩
        · rw [if_neg hbit]
          have ih' := ih (k + 1) (by omega) (by omega)
          rcases ih' with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
          · left
            refine ⟨h1, by omega, h3, ?_⟩
            intro j hj hjr
            by_cases hjk : j = k
            · rw [hjk]
              have hb : ¬ (w &&& u64bit k != 0) := by simpa using hbit
              have hiff := uint64_and_u64bit_ne_zero_iff w h64
              by_cases ht : w.toNat.testBit k = true
              · exact absurd (hiff.mpr ht) hb
              · simpa using ht
            · exact h4 j (by omega) hjr
          · right
            refine ⟨h1, ?_⟩
            intro j hj hj64
            by_cases hjk : j = k
            · rw [hjk]
              have hb : ¬ (w &&& u64bit k != 0) := by simpa using hbit
              have hiff := uint64_and_u64bit_ne_zero_iff w h64
              by_cases ht : w.toNat.testBit k = true
              · exact absurd (hiff.mpr ht) hb
              · simpa using ht
            · exact h2 j (by omega) hj64
      · right
        have hk64 : k = 64 := by omega
        subst hk64
        have hz : lowestBitAux w (n + 1) 64 = 0 := by simp [lowestBitAux]
        refine ⟨hz, ?_⟩
        intro j hj hj64
        omega

private theorem highestBitAux_spec (w : UInt64) :
    ∀ (n k : Nat), 64 ≤ k + n → k ≤ 64 →
      (highestBitAux w n k < 64 ∧ highestBitAux w n k < 64 - k ∧
        w.toNat.testBit (highestBitAux w n k) = true ∧
        ∀ j, highestBitAux w n k < j → j < 64 - k →
          w.toNat.testBit j = false) ∨
      (highestBitAux w n k = 0 ∧
        ∀ j, j < 64 - k → w.toNat.testBit j = false) := by
  intro n
  induction n with
  | zero =>
      intro k hfull hk
      right
      refine ⟨rfl, ?_⟩
      intro j hj
      omega
  | succ n ih =>
      intro k hfull hk
      by_cases h64 : k < 64
      · simp only [highestBitAux]
        rw [if_pos h64]
        by_cases hbit : w &&& u64bit (63 - k) != 0
        · left
          rw [if_pos hbit]
          have hset : w.toNat.testBit (63 - k) = true :=
            (uint64_and_u64bit_ne_zero_iff w (by omega)).mp hbit
          exact ⟨by omega, by omega, hset, by intro j hj hju; omega⟩
        · rw [if_neg hbit]
          have ih' := ih (k + 1) (by omega) (by omega)
          rcases ih' with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
          · left
            refine ⟨h1, by omega, h3, ?_⟩
            intro j hj hju
            by_cases hje : j = 63 - k
            · rw [hje]
              have hb : ¬ (w &&& u64bit (63 - k) != 0) := by simpa using hbit
              have hiff := uint64_and_u64bit_ne_zero_iff w (by omega : 63 - k < 64)
              by_cases ht : w.toNat.testBit (63 - k) = true
              · exact absurd (hiff.mpr ht) hb
              · simpa using ht
            · exact h4 j (by omega) (by omega)
          · right
            refine ⟨h1, ?_⟩
            intro j hju
            by_cases hje : j = 63 - k
            · rw [hje]
              have hb : ¬ (w &&& u64bit (63 - k) != 0) := by simpa using hbit
              have hiff := uint64_and_u64bit_ne_zero_iff w (by omega : 63 - k < 64)
              by_cases ht : w.toNat.testBit (63 - k) = true
              · exact absurd (hiff.mpr ht) hb
              · simpa using ht
            · exact h2 j (by omega)
      · right
        have hk64 : k = 64 := by omega
        subst hk64
        have hz : highestBitAux w (n + 1) 64 = 0 := by simp [highestBitAux]
        refine ⟨hz, ?_⟩
        intro j hj
        omega

/-- For a nonzero word, `lowestBit` is the least set bit: it is below 64, its
    bit is set, and every set bit is at least as large. -/
theorem lowestBit_spec {w : UInt64} (hw : w ≠ 0) :
    lowestBit w < 64 ∧ w.toNat.testBit (lowestBit w) = true ∧
      ∀ j, j < 64 → w.toNat.testBit j = true → lowestBit w ≤ j := by
  have hgo := lowestBit_go_eq_aux w 64 0 (by omega)
  have hval : lowestBit w = lowestBitAux w 64 0 := by
    have hw0 : (w == 0) = false := by simpa using hw
    unfold lowestBit
    rw [if_neg (by simp [hw0])]
    exact hgo
  have hspec := lowestBitAux_spec w 64 0 (by omega) (by omega)
  have hnonzero : w.toNat ≠ 0 := (uint64_ne_zero_iff_toNat_ne_zero w).mp hw
  rcases hspec with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · rw [hval]
    refine ⟨h1, h3, ?_⟩
    intro j hj64 hj
    by_cases hjr : j < lowestBitAux w 64 0
    · exact absurd (h4 j (by omega) hjr) (by rw [hj]; simp)
    · omega
  · exfalso
    obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hnonzero
    have hj64 : j < 64 := by
      by_cases h : j < 64
      · exact h
      · have hlt : w.toNat < 2 ^ j :=
          Nat.lt_of_lt_of_le (UInt64.toNat_lt w) (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.testBit_lt_two_pow hlt] at hj
        cases hj
    have hfalse := h2 j (by omega) hj64
    rw [hj] at hfalse
    cases hfalse

/-- For a nonzero word, `highestBit` is the greatest set bit: it is below 64,
    its bit is set, and every set bit is at most as large. -/
theorem highestBit_spec {w : UInt64} (hw : w ≠ 0) :
    highestBit w < 64 ∧ w.toNat.testBit (highestBit w) = true ∧
      ∀ j, j < 64 → w.toNat.testBit j = true → j ≤ highestBit w := by
  have hgo := highestBit_go_eq_aux w 64 0 (by omega)
  have hval : highestBit w = highestBitAux w 64 0 := by
    have hw0 : (w == 0) = false := by simpa using hw
    unfold highestBit
    rw [if_neg (by simp [hw0])]
    exact hgo
  have hspec := highestBitAux_spec w 64 0 (by omega) (by omega)
  have hnonzero : w.toNat ≠ 0 := (uint64_ne_zero_iff_toNat_ne_zero w).mp hw
  rcases hspec with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩
  · rw [hval]
    refine ⟨h1, h3, ?_⟩
    intro j hj64 hj
    by_cases hjr : highestBitAux w 64 0 < j
    · exact absurd (h4 j hjr (by omega)) (by rw [hj]; simp)
    · omega
  · exfalso
    obtain ⟨j, hj⟩ := Nat.exists_testBit_of_ne_zero hnonzero
    have hj64 : j < 64 := by
      by_cases h : j < 64
      · exact h
      · have hlt : w.toNat < 2 ^ j :=
          Nat.lt_of_lt_of_le (UInt64.toNat_lt w) (Nat.pow_le_pow_right (by decide) (by omega))
        rw [Nat.testBit_lt_two_pow hlt] at hj
        cases hj
    have hfalse := h2 j (by omega)
    rw [hj] at hfalse
    cases hfalse

/-! ## The `u64maskLe` specification -/

theorem u64maskLe_toNat {k : Nat} (hk : k < 63) :
    (u64maskLe k).toNat = 2 ^ (k + 1) - 1 := by
  unfold u64maskLe
  rw [if_neg (by omega)]
  rw [UInt64.toNat_sub, UInt64.toNat_shiftLeft, UInt64.toNat_one]
  have hshift : (UInt64.ofNat (k + 1)).toNat % 64 = k + 1 := by
    rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : k + 1 < 2 ^ 64),
      Nat.mod_eq_of_lt (by omega : k + 1 < 64)]
  rw [hshift, Nat.one_shiftLeft]
  have hsmall : 2 ^ (k + 1) < 2 ^ 64 := by
    have hle : 2 ^ (k + 1) ≤ 2 ^ 63 := Nat.pow_le_pow_right (by decide) (by omega)
    have hlt : 2 ^ 63 < 2 ^ 64 := Nat.pow_lt_pow_right (by decide) (by decide)
    omega
  rw [Nat.mod_eq_of_lt hsmall]
  have hpos : 0 < 2 ^ (k + 1) := Nat.two_pow_pos (k + 1)
  rw [show 2 ^ 64 - 1 + 2 ^ (k + 1) = 2 ^ 64 + (2 ^ (k + 1) - 1) by omega]
  rw [Nat.add_mod_left]
  rw [Nat.mod_eq_of_lt (by omega : 2 ^ (k + 1) - 1 < 2 ^ 64)]

theorem u64maskLe_testBit {k j : Nat} (hk : k < 64) (hj : j < 64) :
    (u64maskLe k).toNat.testBit j = decide (j ≤ k) := by
  by_cases hlast : k = 63
  · subst hlast
    unfold u64maskLe
    rw [if_pos (by omega)]
    have hall : (0xFFFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 64 - 1 := by decide
    rw [hall, Nat.testBit_two_pow_sub_one, decide_eq_decide]
    omega
  · have hlt : k < 63 := by omega
    rw [u64maskLe_toNat hlt, Nat.testBit_two_pow_sub_one, decide_eq_decide]
    omega

/-! ## `insertHole` as list insertion -/

/-- The scan of `insertHole` produces exactly the list insertion of its
    argument into the remaining suffix. -/
theorem insertHole_go_toList (holes : Array Int) (v : Int) :
    ∀ (i : Nat) (acc : Array Int),
      (insertHole.go holes v i acc).toList =
        acc.toList ++ insertSortedInt v (holes.toList.drop i) := by
  have key : ∀ n : Nat, ∀ i : Nat, holes.size - i = n → ∀ acc : Array Int,
      (insertHole.go holes v i acc).toList =
        acc.toList ++ insertSortedInt v (holes.toList.drop i) := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n ih =>
      intro i hni acc
      rw [insertHole.go.eq_1]
      by_cases hi : i < holes.size
      · rw [dif_pos hi]
        cases hget : holes[i]? with
        | none =>
            rw [Array.getElem?_eq_none_iff] at hget
            omega
        | some hval =>
            simp only []
            obtain ⟨_, hval_eq⟩ := Array.getElem?_eq_some_iff.mp hget
            have hdrop : holes.toList.drop i = hval :: holes.toList.drop (i + 1) := by
              rw [List.drop_eq_getElem_cons (by simpa using hi),
                Array.getElem_toList (by simpa using hi), hval_eq]
            by_cases heq : hval == v
            · rw [if_pos heq]
              have hvbeq : (v == hval) = true := by
                rw [beq_iff_eq]
                exact (beq_iff_eq.mp heq).symm
              rw [Array.toList_append, Array.toList_extract, List.extract_eq_take_drop, hdrop]
              rw [insertSortedInt.eq_2, if_pos hvbeq]
              rw [List.take_of_length_le (by simp [List.length_drop]; omega)]
            · rw [if_neg heq]
              have hvbeq : (v == hval) = false := by
                rw [beq_eq_false_iff_ne]
                intro hv
                exact heq (beq_iff_eq.mpr hv.symm)
              by_cases hlt : v < hval
              · rw [if_pos hlt]
                rw [Array.toList_append, Array.toList_append, Array.toList_extract,
                  List.extract_eq_take_drop, hdrop]
                rw [insertSortedInt.eq_2, if_neg (by rw [hvbeq]; decide), if_pos hlt]
                rw [List.take_of_length_le (by simp [List.length_drop]; omega)]
                simp [List.append_assoc]
              · rw [if_neg hlt]
                have hm : holes.size - (i + 1) < n := by omega
                have hrec := ih (holes.size - (i + 1)) hm (i + 1) rfl (acc.push hval)
                rw [hrec, Array.toList_push, hdrop]
                rw [insertSortedInt.eq_2, if_neg (by rw [hvbeq]; decide), if_neg hlt]
                simp [List.append_assoc]
      · rw [dif_neg hi]
        have hnil : holes.toList.drop i = [] :=
          List.drop_eq_nil_of_le (by simpa using Nat.le_of_not_lt hi)
        simp [Array.toList_push, hnil, insertSortedInt]
  intro i acc
  exact key (holes.size - i) i rfl acc

theorem insertHole_toList (holes : Array Int) (v : Int) :
    (insertHole holes v).toList = insertSortedInt v holes.toList := by
  unfold insertHole
  simpa using insertHole_go_toList holes v 0 #[]

theorem mem_insertHole {holes : Array Int} {v x : Int} :
    x ∈ (insertHole holes v).toList ↔ x = v ∨ x ∈ holes.toList := by
  rw [insertHole_toList, mem_insertSortedInt]

theorem pairwise_insertHole {holes : Array Int} {v : Int}
    (h : holes.toList.Pairwise (fun a b => a < b)) :
    (insertHole holes v).toList.Pairwise (fun a b => a < b) := by
  rw [insertHole_toList]
  exact pairwise_insertSortedInt h

/-! ## Well-formedness preservation -/

theorem uint8_and_three_of_and_three {x m : UInt8} (hx : x &&& 3 = x) :
    (x &&& m) &&& 3 = x &&& m := by
  apply UInt8.toNat_inj.mp
  have hx' : x.toNat &&& 3 = x.toNat := by simpa using congrArg UInt8.toNat hx
  rw [UInt8.toNat_and, UInt8.toNat_and]
  show (x.toNat &&& m.toNat) &&& 3 = x.toNat &&& m.toNat
  calc
    (x.toNat &&& m.toNat) &&& 3 = x.toNat &&& (m.toNat &&& 3) := Nat.and_assoc _ _ _
    _ = x.toNat &&& (3 &&& m.toNat) := by rw [Nat.and_comm m.toNat 3]
    _ = (x.toNat &&& 3) &&& m.toNat := (Nat.and_assoc _ _ _).symm
    _ = x.toNat &&& m.toNat := by rw [hx']


theorem DomC.setLe_WF (d : DomC) (k : Int) (h : d.WF) : (d.setLe k).WF := by
  cases d with
  | bool bits =>
      simp only [DomC.WF] at h
      rw [DomC.setLe.eq_1]
      split
      · simp only [DomC.WF]
        decide
      · split
        · simp only [DomC.WF]
          exact uint8_and_three_of_and_three h
        · simp only [DomC.WF]
          exact uint8_and_three_of_and_three h
  | bounds lo hi => rw [DomC.setLe.eq_2]; simp [DomC.WF]
  | bitset lo words =>
      rw [DomC.setLe.eq_3]
      repeat' first | split | dsimp only
      all_goals simp [DomC.WF]
  | boundsHoles lo hi holes =>
      simp only [DomC.WF] at h
      rw [DomC.setLe.eq_4]
      by_cases hk : k < hi
      · rw [if_pos hk]
        by_cases hlo : k < lo
        · rw [if_pos hlo]; simp [DomC.WF]
        · rw [if_neg hlo]
          simp only [DomC.WF]
          constructor
          · rw [Array.toList_filter]
            exact List.Pairwise.filter _ h.1
          · intro x hx
            rw [Array.toList_filter, List.mem_filter] at hx
            exact ⟨(h.2 x hx.1).1, of_decide_eq_true hx.2⟩
      · rw [if_neg hk]
        by_cases hlo : hi < lo
        · rw [if_pos hlo]; simp [DomC.WF]
        · rw [if_neg hlo]
          simp only [DomC.WF]
          constructor
          · rw [Array.toList_filter]
            exact List.Pairwise.filter _ h.1
          · intro x hx
            rw [Array.toList_filter, List.mem_filter] at hx
            exact ⟨(h.2 x hx.1).1, of_decide_eq_true hx.2⟩


theorem DomC.setGe_WF (d : DomC) (k : Int) (h : d.WF) : (d.setGe k).WF := by
  cases d with
  | bool bits =>
      simp only [DomC.WF] at h
      rw [DomC.setGe.eq_1]
      split
      · simp only [DomC.WF]
        decide
      · split
        · simp only [DomC.WF]
          exact uint8_and_three_of_and_three h
        · simp only [DomC.WF]
          exact uint8_and_three_of_and_three h
  | bounds lo hi => rw [DomC.setGe.eq_2]; simp [DomC.WF]
  | bitset lo words =>
      rw [DomC.setGe.eq_3]
      repeat' first | split | dsimp only
      all_goals simp [DomC.WF]
  | boundsHoles lo hi holes =>
      simp only [DomC.WF] at h
      rw [DomC.setGe.eq_4]
      by_cases hk : lo < k
      · rw [if_pos hk]
        by_cases hhi : hi < k
        · rw [if_pos hhi]; simp [DomC.WF]
        · rw [if_neg hhi]
          simp only [DomC.WF]
          constructor
          · rw [Array.toList_filter]
            exact List.Pairwise.filter _ h.1
          · intro x hx
            rw [Array.toList_filter, List.mem_filter] at hx
            exact ⟨of_decide_eq_true hx.2, (h.2 x hx.1).2⟩
      · rw [if_neg hk]
        by_cases hhi : hi < lo
        · rw [if_pos hhi]; simp [DomC.WF]
        · rw [if_neg hhi]
          simp only [DomC.WF]
          constructor
          · rw [Array.toList_filter]
            exact List.Pairwise.filter _ h.1
          · intro x hx
            rw [Array.toList_filter, List.mem_filter] at hx
            exact ⟨of_decide_eq_true hx.2, (h.2 x hx.1).2⟩

theorem DomC.remove_WF (d : DomC) (w : Value) (h : d.WF) : (d.remove w).WF := by
  cases d with
  | bool bits =>
      cases w with
      | bool b =>
          simp only [DomC.WF] at h ⊢
          rw [DomC.remove.eq_1]
          exact uint8_and_three_of_and_three h
      | int i => exact h
      | setOfInt s => exact h
      | array a => exact h
  | bounds lo hi =>
      cases w with
      | int v =>
          rw [DomC.remove.eq_2]
          split
          · simp [DomC.WF]
          · split
            · simp [DomC.WF]
            · split
              · simp [DomC.WF]
              · simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at *
                simp [DomC.WF]
                omega
      | bool b => exact h
      | setOfInt s => exact h
      | array a => exact h
  | bitset lo words =>
      cases w with
      | int v =>
          rw [DomC.remove.eq_3]
          repeat' first | split | dsimp only
          all_goals simp [DomC.WF]
      | bool b => exact h
      | setOfInt s => exact h
      | array a => exact h
  | boundsHoles lo hi holes =>
      simp only [DomC.WF] at h
      cases w with
      | int v =>
          rw [DomC.remove.eq_4]
          by_cases hout : (decide (v < lo) || decide (hi < v)) = true
          · rw [if_pos hout]; exact h
          · rw [if_neg hout]
            by_cases hmem : memHoleRange holes v = true
            · rw [if_pos hmem]; exact h
            · rw [if_neg hmem]
              have hnotmem : v ∉ holes.toList := by
                have hf : memHoleRange holes v = false := by
                  cases hm : memHoleRange holes v
                  · rfl
                  · exact absurd hm hmem
                exact (memHoleRange_eq_false_iff h.1).mp hf
              by_cases hlo : (v == lo) = true
              · rw [if_pos hlo]
                simp only [DomC.WF]
                constructor
                · exact h.1
                · intro x hx
                  have hxr := h.2 x hx
                  have hvlo : v = lo := beq_iff_eq.mp hlo
                  have hxne : x ≠ lo := by
                    intro hxl
                    exact hnotmem (by simpa [hvlo, hxl] using hx)
                  omega
              · rw [if_neg hlo]
                by_cases hhi : (v == hi) = true
                · rw [if_pos hhi]
                  simp only [DomC.WF]
                  constructor
                  · exact h.1
                  · intro x hx
                    have hxr := h.2 x hx
                    have hvhi : v = hi := beq_iff_eq.mp hhi
                    have hxne : x ≠ hi := by
                      intro hxh
                      exact hnotmem (by simpa [hvhi, hxh] using hx)
                    omega
                · rw [if_neg hhi]
                  simp only [DomC.WF]
                  constructor
                  · rw [insertHole_toList]
                    exact pairwise_insertSortedInt h.1
                  · intro x hx
                    rw [mem_insertHole] at hx
                    rcases hx with hxv | hx
                    · rw [hxv]
                      simp only [Bool.or_eq_true, decide_eq_true_eq, not_or, Int.not_lt] at hout
                      exact hout
                    · exact h.2 x hx
      | bool b => exact h
      | setOfInt s => exact h
      | array a => exact h


theorem DomC.removeIntView_WF (d : DomC) (v : Int) (h : d.WF) :
    (d.removeIntView v).WF := by
  cases d with
  | bool bits =>
      simp only [DomC.removeIntView]
      split
      · exact DomC.remove_WF _ _ h
      · split
        · exact DomC.remove_WF _ _ h
        · exact h
  | bounds lo hi => simp only [DomC.removeIntView]; exact DomC.remove_WF _ _ h
  | bitset lo words => simp only [DomC.removeIntView]; exact DomC.remove_WF _ _ h
  | boundsHoles lo hi holes => simp only [DomC.removeIntView]; exact DomC.remove_WF _ _ h

theorem DomC.fix_WF (d : DomC) (w : Value) (h : d.WF) : (d.fix w).WF := by
  cases w with
  | bool b =>
      rw [DomC.fix.eq_1]
      by_cases hm : d.mem (Value.bool b) = true
      · rw [if_pos hm]
        simp only [DomC.WF]
        cases b <;> decide
      · rw [if_neg hm]
        simp [DomC.WF]
  | int i =>
      rw [DomC.fix.eq_2]
      by_cases hm : d.mem (Value.int i) = true
      · rw [if_pos hm]
        simp [DomC.WF]
      · rw [if_neg hm]
        simp [DomC.WF]
  | setOfInt s =>
      simp [DomC.fix, DomC.WF]
  | array a =>
      simp [DomC.fix, DomC.WF]

theorem DomC.fixIntView_WF (d : DomC) (v : Int) (h : d.WF) :
    (d.fixIntView v).WF := by
  cases d with
  | bool bits =>
      simp only [DomC.fixIntView]
      split
      · exact DomC.fix_WF _ _ h
      · split
        · exact DomC.fix_WF _ _ h
        · simp [DomC.WF]
  | bounds lo hi => simp only [DomC.fixIntView]; exact DomC.fix_WF _ _ h
  | bitset lo words => simp only [DomC.fixIntView]; exact DomC.fix_WF _ _ h
  | boundsHoles lo hi holes => simp only [DomC.fixIntView]; exact DomC.fix_WF _ _ h

theorem DomC.applyLit_WF (d : DomC) (l : Literal) (h : d.WF) :
    (d.applyLit l).WF := by
  cases l with
  | mk atom positive =>
      cases atom with
      | intNe s v =>
          simp only [DomC.applyLit]
          split
          · exact DomC.removeIntView_WF _ _ h
          · exact DomC.fixIntView_WF _ _ h
      | intLe s k =>
          simp only [DomC.applyLit]
          split
          · exact DomC.setLe_WF _ _ h
          · exact DomC.setGe_WF _ _ h
      | boolEq s b =>
          simp only [DomC.applyLit]
          exact DomC.fix_WF _ _ h

theorem bitsetMem_eq_true_iff (words : Array UInt64) (n : Nat) :
    bitsetMem words n = true ↔
      ∃ w, words[n / 64]? = some w ∧ w.toNat.testBit (n % 64) = true := by
  unfold bitsetMem
  cases h : words[n / 64]? with
  | none =>
      simp only [Bool.false_eq_true, false_iff]
      rintro ⟨w, hw, -⟩
      cases hw
  | some w =>
      constructor
      · intro hbit
        exact ⟨w, rfl, (uint64_and_u64bit_ne_zero_iff w (Nat.mod_lt n (by decide))).mp hbit⟩
      · rintro ⟨w', hw', hbit⟩
        obtain rfl := Option.some.inj hw'
        exact (uint64_and_u64bit_ne_zero_iff w (Nat.mod_lt n (by decide))).mpr hbit

theorem bitsetMem_eq_false_iff (words : Array UInt64) (n : Nat) :
    bitsetMem words n = false ↔
      ∀ w, words[n / 64]? = some w → w.toNat.testBit (n % 64) = false := by
  constructor
  · intro h w hw
    cases hb : w.toNat.testBit (n % 64)
    · rfl
    · exact absurd ((bitsetMem_eq_true_iff words n).mpr ⟨w, hw, hb⟩) (by rw [h]; simp)
  · intro h
    cases hb : bitsetMem words n with
    | false => rfl
    | true =>
        obtain ⟨w, hw, ht⟩ := (bitsetMem_eq_true_iff words n).mp hb
        rw [h w hw] at ht
        cases ht

/-! ### `lowestBit` scan for `lo?` -/

theorem goLo_some_spec (lo : Int) (words : Array UInt64) :
    ∀ (m i : Nat), words.size - i = m → ∀ l,
      DomC.lo?.goLo lo words i = some l →
      ∀ n, i ≤ n / 64 → bitsetMem words n = true → l ≤ lo + (n : Int) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro i hm l hgo n hni hmem
    rw [DomC.lo?.goLo.eq_1] at hgo
    by_cases hi : i < words.size
    · rw [dif_pos hi] at hgo
      cases hget : words[i]? with
      | none =>
          rw [Array.getElem?_eq_none_iff] at hget
          omega
      | some w =>
          rw [hget] at hgo
          change (if (w == 0) = true then DomC.lo?.goLo lo words (i + 1)
            else some (lo + ((i * 64 + lowestBit w : Nat) : Int))) = some l at hgo
          by_cases hw : (w == 0) = true
          · rw [if_pos hw] at hgo
            by_cases hni' : n / 64 = i
            · exfalso
              have := (bitsetMem_eq_true_iff words n).mp hmem
              obtain ⟨w', hw', hbit⟩ := this
              rw [hni', hget] at hw'
              obtain rfl := Option.some.inj hw'
              rw [beq_iff_eq] at hw
              subst hw
              simp at hbit
            · have hge : i + 1 ≤ n / 64 := by omega
              exact ih (words.size - (i + 1)) (by omega) (i + 1) (by omega) l hgo n hge hmem
          · rw [if_neg hw] at hgo
            obtain rfl := Option.some.inj hgo
            have hwne : w ≠ 0 := by
              intro h; exact hw (by rw [h]; rfl)
            have hspec := lowestBit_spec hwne
            by_cases hni' : n / 64 = i
            · have hn : n = i * 64 + n % 64 := by omega
              have hbitle : lowestBit w ≤ n % 64 := by
                apply hspec.2.2
                · exact Nat.mod_lt n (by decide)
                · exact ((bitsetMem_eq_true_iff words n).mp hmem).choose_spec.1 |> fun _ => by
                    obtain ⟨w', hw', hbit⟩ := (bitsetMem_eq_true_iff words n).mp hmem
                    rw [hni', hget] at hw'
                    obtain rfl := Option.some.inj hw'
                    exact hbit
              rw [hn]
              have : (i * 64 + n % 64 : Nat) = i * 64 + n % 64 := rfl
              omega
            · have hn64 : (i + 1) * 64 ≤ n := by omega
              have hlt : lowestBit w < 64 := hspec.1
              have : i * 64 + lowestBit w ≤ n := by omega
              omega
    · rw [dif_neg hi] at hgo
      cases hgo

/-! ### `highestBit` scan for `hi?` -/

private def hiInv (lo : Int) (words : Array UInt64) (i : Nat) (acc : Option Int) : Prop :=
  match acc with
  | none => ∀ n, n / 64 < i → bitsetMem words n = false
  | some a => ∀ n, n / 64 < i → bitsetMem words n = true → lo + (n : Int) ≤ a

private theorem hiInv_step_zero {lo : Int} {words : Array UInt64} {i : Nat}
    {acc : Option Int} (hinv : hiInv lo words i acc) {w : UInt64}
    (hget : words[i]? = some w) (hw : w = 0) :
    hiInv lo words (i + 1) acc := by
  unfold hiInv at hinv ⊢
  cases acc with
  | none =>
      intro n hn
      by_cases hlt : n / 64 < i
      · exact hinv n hlt
      · have hni : n / 64 = i := by omega
        rw [bitsetMem_eq_false_iff]
        intro w' hw'
        rw [hni, hget] at hw'
        obtain rfl := Option.some.inj hw'
        rw [hw]
        simp
  | some a =>
      intro n hn hmem
      by_cases hlt : n / 64 < i
      · exact hinv n hlt hmem
      · have hni : n / 64 = i := by omega
        have hfalse : bitsetMem words n = false := by
          rw [bitsetMem_eq_false_iff]
          intro w' hw'
          rw [hni, hget] at hw'
          obtain rfl := Option.some.inj hw'
          rw [hw]
          simp
        rw [hfalse] at hmem
        cases hmem

private theorem hiInv_step_nonzero {lo : Int} {words : Array UInt64} {i : Nat}
    {acc : Option Int} (hinv : hiInv lo words i acc) {w : UInt64}
    (hget : words[i]? = some w) (hw : w ≠ 0) :
    hiInv lo words (i + 1) (some (lo + ((i * 64 + highestBit w : Nat) : Int))) := by
  unfold hiInv at hinv ⊢
  intro n hn hmem
  by_cases hlt : n / 64 < i
  · rcases acc with _ | a
    · exact absurd (hinv n hlt) (by rw [hmem]; simp)
    · have hb := hinv n hlt hmem
      have hltn : n < i * 64 + 64 := by omega
      have hle : (n : Int) ≤ (i * 64 : Nat) := by omega
      omega
  · have hni : n / 64 = i := by omega
    obtain ⟨w', hw', hbit⟩ := (bitsetMem_eq_true_iff words n).mp hmem
    rw [hni, hget] at hw'
    obtain rfl := Option.some.inj hw'
    have hspec := highestBit_spec hw
    have hbitle : n % 64 ≤ highestBit w := by
      apply hspec.2.2
      · exact Nat.mod_lt n (by decide)
      · exact hbit
    have hn : n = i * 64 + n % 64 := by omega
    rw [hn]
    omega

private theorem goHi_spec (lo : Int) (words : Array UInt64) :
    ∀ (m i : Nat), words.size - i = m → ∀ acc, hiInv lo words i acc →
      (∀ l, DomC.hi?.goHi lo words i acc = some l →
        ∀ n, bitsetMem words n = true → lo + (n : Int) ≤ l) ∧
      (DomC.hi?.goHi lo words i acc = none →
        ∀ n, bitsetMem words n = false) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro i hm acc hinv
    unfold hiInv at hinv
    rw [DomC.hi?.goHi.eq_1]
    by_cases hi : i < words.size
    · rw [dif_pos hi]
      cases hget : words[i]? with
      | none =>
          rw [Array.getElem?_eq_none_iff] at hget
          omega
      | some w =>
          dsimp only
          by_cases hw : (w == 0) = true
          · rw [if_pos hw]
            have hw0 : w = 0 := beq_iff_eq.mp hw
            exact ih (words.size - (i + 1)) (by omega) (i + 1) (by omega) acc
              (hiInv_step_zero hinv hget hw0)
          · rw [if_neg hw]
            have hwne : w ≠ 0 := by
              intro h; exact hw (by rw [h]; rfl)
            exact ih (words.size - (i + 1)) (by omega) (i + 1) (by omega) _
              (hiInv_step_nonzero hinv hget hwne)
    · rw [dif_neg hi]
      constructor
      · intro l hl n hmem
        rcases acc with _ | a
        · simp at hl
        · obtain rfl := Option.some.inj hl
          obtain ⟨w, hw, -⟩ := (bitsetMem_eq_true_iff words n).mp hmem
          have hlt : n / 64 < words.size := by
            obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hw
            exact hlt
          apply hinv n
          · have hle : words.size ≤ i := Nat.le_of_not_lt hi
            omega
          · exact hmem
      · intro hnone n
        subst hnone
        by_cases hlt : n / 64 < words.size
        · have hle : words.size ≤ i := Nat.le_of_not_lt hi
          exact hinv n (by omega)
        · rw [bitsetMem_eq_false_iff]
          intro w hw
          obtain ⟨hsize, -⟩ := Array.getElem?_eq_some_iff.mp hw
          omega

/-- If the `hi?` scan of a bitset finds no member, then the bitset is empty. -/
theorem bitsetMem_eq_false_of_hi?_none {lo : Int} {words : Array UInt64}
    (h : DomC.hi? (.bitset lo words) = none) (n : Nat) : bitsetMem words n = false := by
  rw [DomC.hi?.eq_3] at h
  exact (goHi_spec lo words words.size 0 (by omega) none (by
    unfold hiInv; intro k hk; omega)).2 h n

/-! ### Hole scans for `boundsHoles` endpoints -/

theorem goHoleLo_some_spec (hi : Int) (holes : Array Int) :
    ∀ (m k : Nat) (v : Int) (l : Int), holes.size - k = m →
      DomC.lo?.goHoleLo hi holes v k = some l →
      v ≤ l ∧ ∀ y, v ≤ y → y < l → y ∈ holes.toList := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k v l hm hgo
    rw [DomC.lo?.goHoleLo.eq_1] at hgo
    by_cases hk : k < holes.size
    · rw [dif_pos hk] at hgo
      cases hget : holes[k]? with
      | none =>
          rw [Array.getElem?_eq_none_iff] at hget
          omega
      | some h =>
          rw [hget] at hgo
          change (if (h == v) = true then DomC.lo?.goHoleLo hi holes (v + 1) (k + 1)
            else some v) = some l at hgo
          by_cases heq : (h == v) = true
          · rw [if_pos heq] at hgo
            obtain ⟨hvl, hmem⟩ := ih (holes.size - (k + 1)) (by omega) (k + 1) (v + 1) l (by omega) hgo
            refine ⟨by omega, ?_⟩
            intro y hyv hyl
            by_cases hyv' : y = v
            · subst hyv'
              rw [Array.mem_toList_iff]
              exact Array.mem_of_getElem? (by simpa [beq_iff_eq.mp heq] using hget)
            · exact hmem y (by omega) hyl
          · rw [if_neg heq] at hgo
            obtain rfl := Option.some.inj hgo
            exact ⟨Int.le_refl v, by intro y hyv hyl; omega⟩
    · rw [dif_neg hk] at hgo
      by_cases hvhi : v ≤ hi
      · rw [if_pos hvhi] at hgo
        obtain rfl := Option.some.inj hgo
        exact ⟨Int.le_refl v, by intro y hyv hyl; omega⟩
      · rw [if_neg hvhi] at hgo
        cases hgo

theorem goHoleHi_some_spec (lo : Int) (holes : Array Int) :
    ∀ (m k : Nat) (v : Int) (l : Int), holes.size - k = m →
      DomC.hi?.goHoleHi lo holes v k = some l →
      l ≤ v ∧ ∀ y, l < y → y ≤ v → y ∈ holes.toList := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro k v l hm hgo
    rw [DomC.hi?.goHoleHi.eq_1] at hgo
    by_cases hk : k < holes.size
    · rw [dif_pos hk] at hgo
      cases hget : holes[holes.size - 1 - k]? with
      | none =>
          rw [Array.getElem?_eq_none_iff] at hget
          omega
      | some h =>
          rw [hget] at hgo
          change (if (h == v) = true then DomC.hi?.goHoleHi lo holes (v - 1) (k + 1)
            else some v) = some l at hgo
          by_cases heq : (h == v) = true
          · rw [if_pos heq] at hgo
            obtain ⟨hlv, hmem⟩ := ih (holes.size - (k + 1)) (by omega) (k + 1) (v - 1) l (by omega) hgo
            refine ⟨by omega, ?_⟩
            intro y hly hyv
            by_cases hyv' : y = v
            · subst hyv'
              rw [Array.mem_toList_iff]
              exact Array.mem_of_getElem? (by simpa [beq_iff_eq.mp heq] using hget)
            · exact hmem y hly (by omega)
          · rw [if_neg heq] at hgo
            obtain rfl := Option.some.inj hgo
            exact ⟨Int.le_refl v, by intro y hly hyv; omega⟩
    · rw [dif_neg hk] at hgo
      by_cases hlov : lo ≤ v
      · rw [if_pos hlov] at hgo
        obtain rfl := Option.some.inj hgo
        exact ⟨Int.le_refl v, by intro y hly hyv; omega⟩
      · rw [if_neg hlov] at hgo
        cases hgo


/-! ### Endpoint laws -/

theorem DomC.lo?_le (d : DomC) (hWF : d.WF) {lo : Int} (h : d.lo? = some lo)
    {v : Value} (hm : d.mem v = true) : lo ≤ iv v := by
  cases d with
  | bool bits =>
      rw [DomC.lo?.eq_1] at h
      by_cases h1 : (bits &&& 1 != 0) = true
      · rw [if_pos h1] at h
        obtain rfl := Option.some.inj h
        cases v with
        | bool b => cases b <;> simp [iv, Value.intView]
        | int i => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
      · rw [if_neg h1] at h
        by_cases h2 : (bits &&& 2 != 0) = true
        · rw [if_pos h2] at h
          obtain rfl := Option.some.inj h
          have h1z : bits &&& 1 = 0 := by
            simpa using h1
          cases v with
          | bool b =>
              cases b
              · simp [DomC.mem, h1z] at hm
              · simp [iv, Value.intView]
          | int i => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
        · rw [if_neg h2] at h
          cases h
  | bounds blo bhi =>
      rw [DomC.lo?.eq_2] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        obtain rfl := Option.some.inj h
        cases v with
        | int w =>
            simp only [DomC.mem.eq_2, Bool.and_eq_true, decide_eq_true_eq] at hm
            simpa [iv, Value.intView] using hm.1
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
  | bitset blo words =>
      rw [DomC.lo?.eq_3] at h
      have hspec := goLo_some_spec blo words words.size 0 (by omega) lo h
      cases v with
      | int w =>
            change lo ≤ w
            simp only [DomC.mem.eq_3] at hm
            by_cases hneg : w - blo < 0
            · rw [if_pos hneg] at hm; cases hm
            · rw [if_neg hneg] at hm
              have hn : ((w - blo).toNat : Int) = w - blo := by omega
              have := hspec (w - blo).toNat (by omega) hm
              omega
      | bool b => simp [DomC.mem] at hm
      | setOfInt s => simp [DomC.mem] at hm
      | array a => simp [DomC.mem] at hm
  | boundsHoles blo bhi holes =>
      rw [DomC.lo?.eq_4] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        have hspec := goHoleLo_some_spec bhi holes holes.size 0 blo lo (by omega) h
        cases v with
        | int w =>
              change lo ≤ w
              have hm' : (decide (blo ≤ w) = true ∧ decide (w ≤ bhi) = true) ∧
                  (memHoleRange holes w = false) := by
                simpa only [DomC.mem.eq_4, Bool.and_eq_true, Bool.not_eq_true'] using hm
              have hbw : blo ≤ w := of_decide_eq_true hm'.1.1
              have hnotmem : w ∉ holes.toList :=
                (memHoleRange_eq_false_iff hWF.1).mp hm'.2
              by_cases hwl : w < lo
              · exact absurd (hspec.2 w hbw hwl) hnotmem
              · omega
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm

theorem DomC.le_hi? (d : DomC) (hWF : d.WF) {hi : Int} (h : d.hi? = some hi)
    {v : Value} (hm : d.mem v = true) : iv v ≤ hi := by
  cases d with
  | bool bits =>
      rw [DomC.hi?.eq_1] at h
      by_cases h1 : (bits &&& 2 != 0) = true
      · rw [if_pos h1] at h
        obtain rfl := Option.some.inj h
        cases v with
        | bool b => cases b <;> simp [iv, Value.intView]
        | int i => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
      · rw [if_neg h1] at h
        by_cases h2 : (bits &&& 1 != 0) = true
        · rw [if_pos h2] at h
          obtain rfl := Option.some.inj h
          have h1z : bits &&& 2 = 0 := by
            simpa using h1
          cases v with
          | bool b =>
              cases b
              · simp [iv, Value.intView]
              · simp [DomC.mem, h1z] at hm
          | int i => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
        · rw [if_neg h2] at h
          cases h
  | bounds blo bhi =>
      rw [DomC.hi?.eq_2] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        obtain rfl := Option.some.inj h
        cases v with
        | int w =>
            simp only [DomC.mem.eq_2, Bool.and_eq_true, decide_eq_true_eq] at hm
            simpa [iv, Value.intView] using hm.2
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
  | bitset blo words =>
      rw [DomC.hi?.eq_3] at h
      have hgo := (goHi_spec blo words words.size 0 (by omega) none (by
        unfold hiInv; intro n hn; omega)).1 hi h
      cases v with
      | int w =>
          change w ≤ hi
          simp only [DomC.mem.eq_3] at hm
          by_cases hneg : w - blo < 0
          · rw [if_pos hneg] at hm; cases hm
          · rw [if_neg hneg] at hm
            have hn : ((w - blo).toNat : Int) = w - blo := by omega
            have := hgo (w - blo).toNat hm
            omega
      | bool b => simp [DomC.mem] at hm
      | setOfInt s => simp [DomC.mem] at hm
      | array a => simp [DomC.mem] at hm
  | boundsHoles blo bhi holes =>
      rw [DomC.hi?.eq_4] at h
      by_cases hlt : decide (bhi < blo) = true
      · rw [if_pos hlt] at h; cases h
      · rw [if_neg hlt] at h
        have hspec := goHoleHi_some_spec blo holes holes.size 0 bhi hi (by omega) h
        cases v with
        | int w =>
              change w ≤ hi
              have hm' : (decide (blo ≤ w) = true ∧ decide (w ≤ bhi) = true) ∧
                  (memHoleRange holes w = false) := by
                simpa only [DomC.mem.eq_4, Bool.and_eq_true, Bool.not_eq_true'] using hm
              have hwb : w ≤ bhi := of_decide_eq_true hm'.1.2
              have hnotmem : w ∉ holes.toList :=
                (memHoleRange_eq_false_iff hWF.1).mp hm'.2
              by_cases hwh : hi < w
              · exact absurd (hspec.2 w hwh hwb) hnotmem
              · omega
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm


/-! ### Existence from the `lo?` scans -/

theorem goLo_mem_spec (lo : Int) (words : Array UInt64) :
    ∀ (m i : Nat) (l : Int), words.size - i = m →
      DomC.lo?.goLo lo words i = some l →
      ∃ n, i ≤ n / 64 ∧ bitsetMem words n = true ∧ l = lo + (n : Int) := by
  intro m
  induction m using Nat.strongRecOn with
  | ind m ih =>
    intro i l hm hgo
    rw [DomC.lo?.goLo.eq_1] at hgo
    by_cases hi : i < words.size
    · rw [dif_pos hi] at hgo
      cases hget : words[i]? with
      | none =>
          rw [Array.getElem?_eq_none_iff] at hget
          omega
      | some w =>
          rw [hget] at hgo
          change (if (w == 0) = true then DomC.lo?.goLo lo words (i + 1)
            else some (lo + ((i * 64 + lowestBit w : Nat) : Int))) = some l at hgo
          by_cases hw : (w == 0) = true
          · rw [if_pos hw] at hgo
            obtain ⟨n, hn, hmem, hl⟩ := ih (words.size - (i + 1)) (by omega) (i + 1) l (by omega) hgo
            exact ⟨n, by omega, hmem, hl⟩
          · rw [if_neg hw] at hgo
            obtain rfl := Option.some.inj hgo
            have hwne : w ≠ 0 := by intro h; exact hw (by rw [h]; rfl)
            have hspec := lowestBit_spec hwne
            have hdiv : (i * 64 + lowestBit w) / 64 = i := by omega
            have hmod : (i * 64 + lowestBit w) % 64 = lowestBit w := by omega
            refine ⟨i * 64 + lowestBit w, by omega, ?_, rfl⟩
            rw [bitsetMem_eq_true_iff]
            refine ⟨w, ?_, ?_⟩
            · rw [hdiv]
              exact hget
            · rw [hmod]
              exact hspec.2.1
    · rw [dif_neg hi] at hgo
      cases hgo

/-- If the lower scan of a sorted in-range hole array returns `a`, then `a` is
    not one of the holes (so it is present in the represented domain). -/
theorem goHoleLo_some_not_mem {lo hi : Int} {holes : Array Int} {a : Int}
    (hpair : holes.toList.Pairwise (fun x y => x < y))
    (hrange : ∀ h ∈ holes.toList, lo ≤ h)
    (hgo : DomC.lo?.goHoleLo hi holes lo 0 = some a) :
    lo ≤ a ∧ a ∉ holes.toList := by
  have key : ∀ (m k : Nat) (v a : Int), holes.size - k = m → v = lo + (k : Int) →
      (∀ j, j < k → holes[j]? = some (lo + (j : Int))) →
      DomC.lo?.goHoleLo hi holes v k = some a →
      v ≤ a ∧ a ∉ holes.toList := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro k v a hm hv hpre hgo
      rw [DomC.lo?.goHoleLo.eq_1] at hgo
      by_cases hk : k < holes.size
      · rw [dif_pos hk] at hgo
        cases hget : holes[k]? with
        | none =>
            rw [Array.getElem?_eq_none_iff] at hget
            omega
        | some h =>
            rw [hget] at hgo
            change (if (h == v) = true then DomC.lo?.goHoleLo hi holes (v + 1) (k + 1)
              else some v) = some a at hgo
            by_cases heq : (h == v) = true
            · rw [if_pos heq] at hgo
              have hpre' : ∀ j, j < k + 1 → holes[j]? = some (lo + (j : Int)) := by
                intro j hj
                by_cases hjk : j < k
                · exact hpre j hjk
                · have hjkeq : j = k := by omega
                  subst hjkeq
                  rw [hget]
                  have : h = v := beq_iff_eq.mp heq
                  rw [this, hv]
              obtain ⟨h1, h2⟩ := ih (holes.size - (k + 1)) (by omega) (k + 1) (v + 1) a (by omega)
                (by omega) hpre' hgo
              exact ⟨by omega, h2⟩
            · rw [if_neg heq] at hgo
              have hva : v = a := Option.some.inj hgo
              constructor
              · exact Int.le_of_eq hva
              · intro hmem
                obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hmem
                have hjsize : j < holes.size := by simpa using hj
                have hgetj : holes[j] = a := by simpa using hjv
                by_cases hjk : j < k
                · have hp := hpre j hjk
                  rw [Array.getElem?_eq_getElem hjsize] at hp
                  have hp' : holes[j] = lo + (j : Int) := Option.some.inj hp
                  rw [hgetj] at hp'
                  omega
                · by_cases hjeq : j = k
                  · have hqj : holes[j]? = some a := by
                      rw [Array.getElem?_eq_getElem hjsize]; exact congrArg some hgetj
                    have hqk : holes[k]? = some a := by rwa [hjeq] at hqj
                    have : h = a := by
                      rw [hget] at hqk
                      exact Option.some.inj hqk
                    have : h = v := by omega
                    exact heq (by rw [beq_iff_eq]; exact this)
                  · have hkj : k < j := by omega
                    by_cases hk0 : k = 0
                    · have hq0 : holes[0]? = some h := by rwa [hk0] at hget
                      have hget0 : holes[0] = h := by
                        rw [Array.getElem?_eq_getElem (by omega)] at hq0
                        exact Option.some.inj hq0
                      have hlt : holes[0] < holes[j] :=
                        array_lt_of_pairwise hpair (by omega) hjsize (by omega)
                      rw [hget0, hgetj] at hlt
                      have hmemh : h ∈ holes.toList :=
                        Array.mem_toList_iff.mpr (Array.mem_of_getElem? hget)
                      have hhlo : lo ≤ h := hrange h hmemh
                      have hv0 : v = lo := by rw [hv, hk0]; simp
                      omega
                    · have hpos : 0 < k := by omega
                      have hprev : holes[k - 1]? = some (lo + ((k - 1 : Nat) : Int)) :=
                        hpre (k - 1) (by omega)
                      have hprevget : holes[k - 1] = lo + ((k - 1 : Nat) : Int) := by
                        rw [Array.getElem?_eq_getElem (by omega)] at hprev
                        exact Option.some.inj hprev
                      have hlt1 : holes[k - 1] < holes[k] :=
                        array_lt_of_pairwise hpair (by omega) hk (by omega)
                      have hkget : holes[k] = h := by
                        rw [Array.getElem?_eq_getElem hk] at hget
                        exact Option.some.inj hget
                      have hlt2 : holes[k] < holes[j] :=
                        array_lt_of_pairwise hpair hk hjsize hkj
                      rw [hgetj] at hlt2
                      rw [hkget, hprevget] at hlt1
                      omega
      · rw [dif_neg hk] at hgo
        by_cases hvhi : v ≤ hi
        · rw [if_pos hvhi] at hgo
          have hva : v = a := Option.some.inj hgo
          constructor
          · exact Int.le_of_eq hva
          · intro hmem
            obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp hmem
            have hjsize : j < holes.size := by simpa using hj
            have hjk : j < k := by omega
            have := hpre j hjk
            rw [Array.getElem?_eq_getElem hjsize] at this
            have heqj : holes[j] = lo + (j : Int) := Option.some.inj this
            have hjv' : holes[j] = a := by simpa using hjv
            rw [heqj] at hjv'
            have : (j : Int) < (k : Int) := by exact_mod_cast hjk
            omega
        · rw [if_neg hvhi] at hgo
          cases hgo
  exact key holes.size 0 lo a (by omega) (by omega) (by intro j hj; omega) hgo


theorem bitset_mem_int_of_lo?_eq {lo : Int} {words : Array UInt64} {a : Int}
    (h : (DomC.bitset lo words).lo? = some a) :
    (DomC.bitset lo words).mem (.int a) = true := by
  rw [DomC.lo?.eq_3] at h
  obtain ⟨n, -, hmem, hl⟩ := goLo_mem_spec lo words words.size 0 a (by omega) h
  have hnonneg : ¬ a - lo < 0 := by omega
  simp only [DomC.mem.eq_3]
  rw [if_neg hnonneg]
  have hn : (a - lo).toNat = n := by omega
  rw [hn]
  exact hmem

theorem boundsHoles_mem_int_of_lo?_hi?_eq {lo hi : Int} {holes : Array Int} {a : Int}
    (hWF : (DomC.boundsHoles lo hi holes).WF)
    (hlo : (DomC.boundsHoles lo hi holes).lo? = some a)
    (hhi : (DomC.boundsHoles lo hi holes).hi? = some a) :
    (DomC.boundsHoles lo hi holes).mem (.int a) = true := by
  rw [DomC.lo?.eq_4] at hlo
  rw [DomC.hi?.eq_4] at hhi
  by_cases hlt : decide (hi < lo) = true
  · rw [if_pos hlt] at hlo; cases hlo
  · rw [if_neg hlt] at hlo
    rw [if_neg hlt] at hhi
    have hpair := hWF.1
    have hrange : ∀ h ∈ holes.toList, lo ≤ h := fun h hh => (hWF.2 h hh).1
    obtain ⟨hloa, hnotmem⟩ := goHoleLo_some_not_mem hpair hrange hlo
    have hhia : a ≤ hi :=
      (goHoleHi_some_spec lo holes holes.size 0 hi a (by omega) hhi).1
    have h1 : decide (lo ≤ a) = true := by simp [hloa]
    have h2 : decide (a ≤ hi) = true := by simp [hhia]
    have hnot : memHoleRange holes a = false :=
      (memHoleRange_eq_false_iff hpair).mpr hnotmem
    simp only [DomC.mem.eq_4]
    rw [h1, h2, hnot]
    rfl

theorem DomC.fixedValue_isSome_iff_exists (d : DomC) :
    d.fixedValue.isSome = true ↔ ∃ v, d.fixedValue = some v :=
  Option.isSome_iff_exists

theorem DomC.fixedValue_sound (d : DomC) (hWF : d.WF) {v : Value}
    (h : d.fixedValue = some v) :
    d.mem v = true ∧ ∀ w, d.mem w = true → w = v := by
  cases d with
  | bool bits =>
      rw [DomC.fixedValue.eq_1] at h
      split at h
      · rename_i hbits
        obtain rfl := Option.some.inj h
        have hbits' : bits = 1 := by rw [← hWF]; exact hbits
        constructor
        · simp [DomC.mem, hbits']
        · intro w hw
          cases w with
          | bool b =>
              cases b
              · rfl
              · have hzero : (1 &&& 2 : UInt8) = 0 := by decide
                simp [DomC.mem, hbits', hzero] at hw
          | int i => simp [DomC.mem] at hw
          | setOfInt s => simp [DomC.mem] at hw
          | array a => simp [DomC.mem] at hw
      · rename_i hbits
        obtain rfl := Option.some.inj h
        have hbits' : bits = 2 := by rw [← hWF]; exact hbits
        constructor
        · simp [DomC.mem, hbits']
        · intro w hw
          cases w with
          | bool b =>
              cases b
              · have hzero : (2 &&& 1 : UInt8) = 0 := by decide
                simp [DomC.mem, hbits', hzero] at hw
              · rfl
          | int i => simp [DomC.mem] at hw
          | setOfInt s => simp [DomC.mem] at hw
          | array a => simp [DomC.mem] at hw
      · cases h
  | bounds lo hi =>
      rw [DomC.fixedValue.eq_2] at h
      by_cases heq : (lo == hi) = true
      · rw [if_pos heq] at h
        obtain rfl := Option.some.inj h
        have hloeq : lo = hi := beq_iff_eq.mp heq
        constructor
        · simp [DomC.mem, hloeq]
        · intro w hw
          cases w with
          | int i =>
              simp only [DomC.mem.eq_2, Bool.and_eq_true, decide_eq_true_eq] at hw
              have : i = lo := by omega
              subst this
              rfl
          | bool b => simp [DomC.mem] at hw
          | setOfInt s => simp [DomC.mem] at hw
          | array a => simp [DomC.mem] at hw
      · rw [if_neg heq] at h
        cases h
  | bitset lo words =>
      rw [DomC.fixedValue.eq_3] at h
      split at h
      · rename_i a b hlo hhi
        by_cases hab : (a == b) = true
        · rw [if_pos hab] at h
          obtain rfl := Option.some.inj h
          have hba : b = a := (beq_iff_eq.mp hab).symm
          rw [hba] at hhi
          constructor
          · exact bitset_mem_int_of_lo?_eq hlo
          · intro w hw
            cases w with
            | int i =>
                have h1 : a ≤ i := by
                  have := DomC.lo?_le (.bitset lo words) hWF hlo hw
                  simpa [iv, Value.intView] using this
                have h2 : i ≤ a := by
                  have := DomC.le_hi? (.bitset lo words) hWF hhi hw
                  simpa [iv, Value.intView] using this
                have : i = a := by omega
                subst this
                rfl
            | bool b => simp [DomC.mem] at hw
            | setOfInt s => simp [DomC.mem] at hw
            | array a => simp [DomC.mem] at hw
        · rw [if_neg hab] at h
          cases h
      · cases h
  | boundsHoles lo hi holes =>
      rw [DomC.fixedValue.eq_4] at h
      split at h
      · rename_i a b hlo hhi
        by_cases hab : (a == b) = true
        · rw [if_pos hab] at h
          obtain rfl := Option.some.inj h
          have hba : b = a := (beq_iff_eq.mp hab).symm
          rw [hba] at hhi
          constructor
          · exact boundsHoles_mem_int_of_lo?_hi?_eq hWF hlo hhi
          · intro w hw
            cases w with
            | int i =>
                have h1 : a ≤ i := by
                  have := DomC.lo?_le (.boundsHoles lo hi holes) hWF hlo hw
                  simpa [iv, Value.intView] using this
                have h2 : i ≤ a := by
                  have := DomC.le_hi? (.boundsHoles lo hi holes) hWF hhi hw
                  simpa [iv, Value.intView] using this
                have : i = a := by omega
                subst this
                rfl
            | bool b => simp [DomC.mem] at hw
            | setOfInt s => simp [DomC.mem] at hw
            | array a => simp [DomC.mem] at hw
        · rw [if_neg hab] at h
          cases h
      · cases h


theorem bitsetMem_extract_zero {words : Array UInt64} {stop n : Nat}
    (hstop : n / 64 < stop) :
    bitsetMem (words.extract 0 stop) n = bitsetMem words n := by
  apply Bool.eq_iff_iff.mpr
  rw [bitsetMem_eq_true_iff, bitsetMem_eq_true_iff]
  constructor
  · rintro ⟨w, hw, hbit⟩
    rw [Array.getElem?_extract] at hw
    by_cases h : n / 64 < min stop words.size - 0
    · rw [if_pos h] at hw
      exact ⟨w, by simpa using hw, hbit⟩
    · rw [if_neg h] at hw
      cases hw
  · rintro ⟨w, hw, hbit⟩
    obtain ⟨hsize, -⟩ := Array.getElem?_eq_some_iff.mp hw
    refine ⟨w, ?_, hbit⟩
    rw [Array.getElem?_extract]
    rw [if_pos]
    · simpa using hw
    · omega

theorem bitsetMem_extract_offset {words : Array UInt64} {start stop n : Nat}
    (hstart : start ≤ n / 64) (hstop : n / 64 < stop) (hsize : n / 64 < words.size) :
    bitsetMem (words.extract start stop) (n - start * 64) = bitsetMem words n := by
  apply Bool.eq_iff_iff.mpr
  rw [bitsetMem_eq_true_iff, bitsetMem_eq_true_iff]
  have hn : start * 64 ≤ n := by
    have := Nat.mul_le_mul_right 64 hstart
    omega
  have hdiv : (n - start * 64) / 64 = n / 64 - start := by omega
  have hmod : (n - start * 64) % 64 = n % 64 := by omega
  constructor
  · rintro ⟨w, hw, hbit⟩
    rw [Array.getElem?_extract] at hw
    by_cases h : (n - start * 64) / 64 < min stop words.size - start
    · rw [if_pos h] at hw
      rw [hdiv] at h
      rw [hmod] at hbit
      refine ⟨w, ?_, hbit⟩
      have hsum : start + (n / 64 - start) = n / 64 := by omega
      rwa [hdiv, hsum] at hw
    · rw [if_neg h] at hw
      cases hw
  · rintro ⟨w, hw, hbit⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Array.getElem?_extract, if_pos]
      · have hsum : start + (n / 64 - start) = n / 64 := by omega
        rwa [hdiv, hsum]
      · rw [hdiv]; omega
    · rw [hmod]; exact hbit

theorem bitsetMem_set! {words : Array UInt64} {wi : Nat} (hwi : wi < words.size)
    (w : UInt64) (n : Nat) :
    bitsetMem (words.set! wi w) n =
      if n / 64 = wi then (w &&& u64bit (n % 64)) != 0 else bitsetMem words n := by
  unfold bitsetMem
  rw [Array.set!_eq_setIfInBounds]
  rw [Array.getElem?_setIfInBounds]
  by_cases h : wi = n / 64
  · rw [if_pos h, if_pos hwi, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hn => h hn.symm)]

theorem bitsetMem_extract_last_zero {a : Array UInt64} (hh : 0 < a.size)
    (hlast : (a[a.size - 1]! == 0) = true) (n : Nat) :
    bitsetMem (a.extract 0 (a.size - 1)) n = bitsetMem a n := by
  apply Bool.eq_iff_iff.mpr
  rw [bitsetMem_eq_true_iff, bitsetMem_eq_true_iff]
  constructor
  · rintro ⟨w, hw, hbit⟩
    rw [Array.getElem?_extract] at hw
    by_cases h : n / 64 < min (a.size - 1) a.size - 0
    · rw [if_pos h] at hw
      exact ⟨w, by simpa using hw, hbit⟩
    · rw [if_neg h] at hw
      cases hw
  · rintro ⟨w, hw, hbit⟩
    obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hw
    by_cases hlastidx : n / 64 = a.size - 1
    · have hz : w = 0 := by
        have h1 : a[n / 64]! = w := by
          rw [Array.getElem!_eq_getD]
          unfold Array.getD
          rw [dif_pos hlt]
          exact heq
        rw [← h1, hlastidx]
        exact beq_iff_eq.mp hlast
      have : w.toNat.testBit (n % 64) = false := by rw [hz]; simp
      rw [this] at hbit
      cases hbit
    · refine ⟨w, ?_, hbit⟩
      rw [Array.getElem?_extract, if_pos]
      · simpa using hw
      · omega

theorem bitsetMem_trim (a : Array UInt64) (n : Nat) :
    bitsetMem (DomC.setLe.trim a) n = bitsetMem a n := by
  have key : ∀ m : Nat, ∀ a : Array UInt64, a.size = m → ∀ n : Nat,
      bitsetMem (DomC.setLe.trim a) n = bitsetMem a n := by
    intro m
    induction m using Nat.strongRecOn with
    | ind m ih =>
      intro a ha n
      rw [DomC.setLe.trim.eq_1]
      split
      · rename_i hh
        split
        · rename_i hlast
          have hm : (a.extract 0 (a.size - 1)).size < m := by
            rw [Array.size_extract]
            omega
          rw [ih (a.extract 0 (a.size - 1)).size hm (a.extract 0 (a.size - 1)) rfl n]
          exact bitsetMem_extract_last_zero hh hlast n
        · rfl
      · rfl
  exact key a.size a rfl n

/-- Extracting from word `start` to the end shifts membership by `start * 64`,
    with no side conditions. -/
theorem bitsetMem_extract_from (words : Array UInt64) (start n : Nat) :
    bitsetMem (words.extract start words.size) n = bitsetMem words (start * 64 + n) := by
  apply Bool.eq_iff_iff.mpr
  rw [bitsetMem_eq_true_iff, bitsetMem_eq_true_iff]
  constructor
  · rintro ⟨w, hw, hbit⟩
    rw [Array.getElem?_extract] at hw
    by_cases h : n / 64 < min words.size words.size - start
    · rw [if_pos h] at hw
      refine ⟨w, ?_, ?_⟩
      · have hsum : start + n / 64 = (start * 64 + n) / 64 := by omega
        rwa [hsum] at hw
      · have hmod : (start * 64 + n) % 64 = n % 64 := by omega
        rw [hmod]; exact hbit
    · rw [if_neg h] at hw
      cases hw
  · rintro ⟨w, hw, hbit⟩
    refine ⟨w, ?_, ?_⟩
    · rw [Array.getElem?_extract, if_pos]
      · have hdiv : (start * 64 + n) / 64 = start + n / 64 := by omega
        rw [hdiv] at hw
        exact hw
      · have hdiv : (start * 64 + n) / 64 = start + n / 64 := by omega
        obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hw
        rw [hdiv] at hlt; omega
    · have hmod : (start * 64 + n) % 64 = n % 64 := by omega
      rw [← hmod]; exact hbit

/-- The high mask used by `setGe`: all bits at positions `≥ b` are set. -/
theorem u64maskGe_testBit (b j : Nat) (hb : b < 64) (hj : j < 64) :
    ((if b == 0 then (0xFFFFFFFFFFFFFFFF : UInt64)
      else (0xFFFFFFFFFFFFFFFF : UInt64) <<< (UInt64.ofNat b)) &&& u64bit j) != 0 ↔
      b ≤ j := by
  rw [bne_iff_ne, uint64_ne_zero_iff_toNat_ne_zero, UInt64.toNat_and, u64bit_toNat hj,
    nat_and_two_pow_ne_zero]
  have hall : (0xFFFFFFFFFFFFFFFF : UInt64).toNat = 2 ^ 64 - 1 := by decide
  by_cases hb0 : b = 0
  · subst hb0
    simp only [beq_self_eq_true, if_true, hall, Nat.testBit_two_pow_sub_one]
    simp [hj]
  · have hbf : (b == 0) = false := by
      rw [beq_eq_false_iff_ne]; exact hb0
    rw [hbf]
    simp only [Bool.false_eq_true, if_false]
    rw [UInt64.toNat_shiftLeft]
    have hof : (UInt64.ofNat b).toNat % 64 = b := by
      rw [UInt64.toNat_ofNat', Nat.mod_eq_of_lt (by omega : b < 2 ^ 64),
        Nat.mod_eq_of_lt hb]
    rw [hof, hall, Nat.testBit_mod_two_pow,
      show decide (j < 64) = true from by simp [hj], Bool.true_and,
      Nat.testBit_shiftLeft]
    have hdec : decide (j ≥ b) = decide (b ≤ j) := by
      rw [decide_eq_decide]
    rw [hdec, Nat.testBit_two_pow_sub_one]
    have hsub : j - b < 64 := by omega
    simp [hsub]

/-- Clearing the bit at position `b` does not change any other bit. -/
theorem u64_and_not_u64bit_ne_zero_iff (w : UInt64) {b j : Nat}
    (hb : b < 64) (hj : j < 64) :
    ((w &&& ~~~(u64bit b)) &&& u64bit j) != 0 ↔
      (w &&& u64bit j) != 0 ∧ j ≠ b := by
  rw [uint64_and_u64bit_ne_zero_iff w hj]
  rw [bne_iff_ne, uint64_ne_zero_iff_toNat_ne_zero, UInt64.toNat_and, UInt64.toNat_and,
    UInt64.toNat_not, u64bit_toNat hb, u64bit_toNat hj, nat_and_two_pow_ne_zero]
  have hsize : UInt64.size = 2 ^ 64 := rfl
  have hblt : 2 ^ b < 2 ^ 64 := by
    rw [← hsize]; exact Nat.pow_lt_pow_right (by decide) hb
  have hsub : UInt64.size - 1 - 2 ^ b = 2 ^ 64 - (2 ^ b + 1) := by
    rw [hsize]; omega
  rw [hsub, Nat.testBit_and, Nat.testBit_two_pow_sub_succ hblt]
  have hbitb : (2 ^ b).testBit j = decide (b = j) := by
    rw [Nat.testBit_two_pow, decide_eq_decide]
  rw [hbitb, show decide (j < 64) = true from by simp [hj], Bool.true_and]
  by_cases hjb : j = b
  · subst hjb
    simp
  · have hbj : b ≠ j := by omega
    simp [hbj]
    intro _ h
    exact hbj h.symm


/-! ### Word-level membership helpers -/

theorem bitsetMem_eq_false_of_size_le (a : Array UInt64) (n : Nat)
    (h : a.size ≤ n / 64) : bitsetMem a n = false := by
  unfold bitsetMem
  cases hh : a[n / 64]? with
  | none => rfl
  | some w =>
      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hh
      omega

theorem bitsetMem_extract_full (words : Array UInt64) (n : Nat) :
    bitsetMem (words.extract 0 words.size) n = bitsetMem words n := by
  by_cases h : n / 64 < words.size
  · exact bitsetMem_extract_zero h
  · have hl : bitsetMem (words.extract 0 words.size) n = false := by
      apply bitsetMem_eq_false_of_size_le
      rw [Array.size_extract]
      omega
    have hr : bitsetMem words n = false := bitsetMem_eq_false_of_size_le words n (by omega)
    rw [hl, hr]

theorem bitsetMem_all_zero (a : Array UInt64) (n : Nat)
    (hall : a.all (fun w => w == 0) = true) : bitsetMem a n = false := by
  unfold bitsetMem
  cases hh : a[n / 64]? with
  | none => rfl
  | some w =>
      obtain ⟨hlt, heq⟩ := Array.getElem?_eq_some_iff.mp hh
      have hw := (Array.all_eq_true.mp hall) (n / 64) hlt
      have hzero : a[n / 64] = 0 := beq_iff_eq.mp hw
      have hwzero : w = 0 := by rw [← heq, hzero]
      rw [hwzero]
      simp

theorem getElem_extract_succ (words : Array UInt64) {wi : Nat} (hwi : wi < words.size) :
    (words.extract 0 (wi + 1))[wi]! = words[wi] := by
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos (by rw [Array.size_extract]; omega)]
  rw [Array.getInternal_eq_getElem, Array.getElem_extract]
  simp

theorem getElem_extract_zero (words : Array UInt64) {wi : Nat} (hwi : wi < words.size) :
    (words.extract wi words.size)[0]! = words[wi] := by
  rw [Array.getElem!_eq_getD]
  unfold Array.getD
  rw [dif_pos (by rw [Array.size_extract]; omega)]
  rw [Array.getInternal_eq_getElem, Array.getElem_extract]
  simp

theorem u64maskLe_and_u64bit_ne_zero_iff (w : UInt64) {bi j : Nat}
    (hbi : bi < 64) (hj : j < 64) :
    ((w &&& u64maskLe bi) &&& u64bit j) != 0 ↔
      (w &&& u64bit j) != 0 ∧ j ≤ bi := by
  rw [uint64_and_u64bit_ne_zero_iff _ hj, UInt64.toNat_and, Nat.testBit_and,
    u64maskLe_testBit hbi hj, Bool.and_eq_true, ← uint64_and_u64bit_ne_zero_iff w hj,
    decide_eq_true_eq]

theorem u64maskGe_and_u64bit_ne_zero_iff (w : UInt64) {b j : Nat}
    (hb : b < 64) (hj : j < 64) :
    ((w &&& (if b == 0 then (0xFFFFFFFFFFFFFFFF : UInt64)
      else (0xFFFFFFFFFFFFFFFF : UInt64) <<< (UInt64.ofNat b))) &&& u64bit j) != 0 ↔
      (w &&& u64bit j) != 0 ∧ b ≤ j := by
  have hmask : (if b == 0 then (0xFFFFFFFFFFFFFFFF : UInt64)
      else (0xFFFFFFFFFFFFFFFF : UInt64) <<< (UInt64.ofNat b)).toNat.testBit j = true ↔ b ≤ j := by
    rw [← uint64_and_u64bit_ne_zero_iff _ hj]
    exact u64maskGe_testBit b j hb hj
  rw [uint64_and_u64bit_ne_zero_iff _ hj, UInt64.toNat_and, Nat.testBit_and,
    Bool.and_eq_true, hmask, ← uint64_and_u64bit_ne_zero_iff w hj]

theorem bitsetMem_setLe_word (words : Array UInt64) {wi bi n : Nat}
    (hwi : wi < words.size) (hbi : bi < 64) :
    bitsetMem ((words.extract 0 (wi + 1)).set! wi
        ((words.extract 0 (wi + 1))[wi]! &&& u64maskLe bi)) n = true ↔
      bitsetMem words n = true ∧ n ≤ wi * 64 + bi := by
  have hsize : (words.extract 0 (wi + 1)).size = wi + 1 := by
    rw [Array.size_extract]; omega
  have hwi' : wi < (words.extract 0 (wi + 1)).size := by omega
  rw [bitsetMem_set! hwi']
  by_cases hlt : n / 64 < wi
  · have hne : n / 64 ≠ wi := by omega
    rw [if_neg hne]
    rw [bitsetMem_extract_zero (by omega : n / 64 < wi + 1)]
    constructor
    · intro h
      exact ⟨h, by omega⟩
    · intro h
      exact h.1
  · by_cases heq : n / 64 = wi
    · rw [if_pos heq]
      rw [getElem_extract_succ words hwi]
      rw [u64maskLe_and_u64bit_ne_zero_iff _ hbi (Nat.mod_lt n (by decide))]
      constructor
      · rintro ⟨hbit, hle⟩
        have hbit' : words[wi].toNat.testBit (n % 64) = true :=
          (uint64_and_u64bit_ne_zero_iff words[wi] (Nat.mod_lt n (by decide))).mp hbit
        have hm : bitsetMem words n = true := by
          rw [bitsetMem_eq_true_iff]
          refine ⟨words[wi], ?_, hbit'⟩
          rw [heq, Array.getElem?_eq_getElem hwi]
        have hn : n = wi * 64 + n % 64 := by omega
        exact ⟨hm, by omega⟩
      · rintro ⟨hm, hle⟩
        obtain ⟨w, hw, hbit⟩ := (bitsetMem_eq_true_iff words n).mp hm
        rw [heq, Array.getElem?_eq_getElem hwi] at hw
        obtain rfl := Option.some.inj hw
        have hbit' : (words[wi] &&& u64bit (n % 64)) != 0 :=
          (uint64_and_u64bit_ne_zero_iff words[wi] (Nat.mod_lt n (by decide))).mpr hbit
        have hle' : n % 64 ≤ bi := by omega
        exact ⟨hbit', hle'⟩
    · have hgt : wi < n / 64 := by omega
      rw [if_neg (by omega : ¬ n / 64 = wi)]
      have hfalse : bitsetMem (words.extract 0 (wi + 1)) n = false := by
        apply bitsetMem_eq_false_of_size_le
        rw [hsize]
        omega
      rw [hfalse]
      constructor
      · intro h; cases h
      · rintro ⟨-, hle⟩
        omega

theorem bitsetMem_setLe_word_ge (words : Array UInt64) {wi bi n : Nat}
    (hwi : words.size ≤ wi) (hbi : bi < 64) :
    bitsetMem (words.extract 0 words.size) n = true ↔
      bitsetMem words n = true ∧ n ≤ wi * 64 + bi := by
  rw [bitsetMem_extract_full]
  constructor
  · intro h
    refine ⟨h, ?_⟩
    obtain ⟨w, hw, -⟩ := (bitsetMem_eq_true_iff words n).mp h
    obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hw
    omega
  · intro h
    exact h.1

theorem bitsetMem_setGe_word (words : Array UInt64) {wi bi n : Nat}
    (hwi : wi < words.size) (hbi : bi < 64) :
    bitsetMem ((words.extract wi words.size).set! 0
        ((words.extract wi words.size)[0]! &&&
          (if bi == 0 then (0xFFFFFFFFFFFFFFFF : UInt64)
           else (0xFFFFFFFFFFFFFFFF : UInt64) <<< (UInt64.ofNat bi)))) n = true ↔
      bitsetMem words (wi * 64 + n) = true ∧ bi ≤ n := by
  have hsize : (words.extract wi words.size).size = words.size - wi := by
    rw [Array.size_extract]
    simp
  have hzero : 0 < (words.extract wi words.size).size := by omega
  by_cases hn : n < 64
  · have hdiv : n / 64 = 0 := by omega
    have hmod : n % 64 = n := Nat.mod_eq_of_lt hn
    rw [bitsetMem_set! hzero]
    rw [if_pos hdiv]
    rw [getElem_extract_zero words hwi, hmod]
    rw [u64maskGe_and_u64bit_ne_zero_iff _ hbi hn]
    have htarget : bitsetMem words (wi * 64 + n) = true ↔
        (words[wi] &&& u64bit n) != 0 := by
      rw [bitsetMem_eq_true_iff]
      constructor
      · rintro ⟨w, hw, hbit⟩
        have hdiv' : (wi * 64 + n) / 64 = wi := by omega
        have hmod' : (wi * 64 + n) % 64 = n := by omega
        rw [hdiv', Array.getElem?_eq_getElem hwi] at hw
        obtain rfl := Option.some.inj hw
        have hbitn : words[wi].toNat.testBit n = true := by
          rwa [hmod'] at hbit
        exact (uint64_and_u64bit_ne_zero_iff words[wi] hn).mpr hbitn
      · intro hbit
        refine ⟨words[wi], ?_, ?_⟩
        · rw [show (wi * 64 + n) / 64 = wi by omega, Array.getElem?_eq_getElem hwi]
        · have hbitn := (uint64_and_u64bit_ne_zero_iff words[wi] hn).mp hbit
          rwa [show (wi * 64 + n) % 64 = n by omega]
    rw [htarget]
  · have hne : n / 64 ≠ 0 := by omega
    rw [bitsetMem_set! hzero]
    rw [if_neg hne]
    rw [bitsetMem_extract_from]
    constructor
    · intro h
      exact ⟨h, by omega⟩
    · intro h
      exact h.1


/-! ## Membership laws for restriction operations -/

/-! ## `UInt8` mask identities -/

theorem uint8_and_one_and_one (x : UInt8) : (x &&& 1) &&& 1 = x &&& 1 := by
  rw [UInt8.and_assoc]
  have h : ((1 : UInt8) &&& 1) = 1 := by decide
  rw [h]

theorem uint8_and_one_and_two (x : UInt8) : (x &&& 1) &&& 2 = 0 := by
  rw [UInt8.and_assoc]
  have h : ((1 : UInt8) &&& 2) = 0 := by decide
  rw [h, UInt8.and_zero]

theorem uint8_and_two_and_one (x : UInt8) : (x &&& 2) &&& 1 = 0 := by
  rw [UInt8.and_assoc]
  have h : ((2 : UInt8) &&& 1) = 0 := by decide
  rw [h, UInt8.and_zero]

theorem uint8_and_two_and_two (x : UInt8) : (x &&& 2) &&& 2 = x &&& 2 := by
  rw [UInt8.and_assoc]
  have h : ((2 : UInt8) &&& 2) = 2 := by decide
  rw [h]

theorem uint8_and_three_and_one (x : UInt8) : (x &&& 3) &&& 1 = x &&& 1 := by
  rw [UInt8.and_assoc]
  have h : ((3 : UInt8) &&& 1) = 1 := by decide
  rw [h]

theorem uint8_and_three_and_two (x : UInt8) : (x &&& 3) &&& 2 = x &&& 2 := by
  rw [UInt8.and_assoc]
  have h : ((3 : UInt8) &&& 2) = 2 := by decide
  rw [h]

/-! ## Basic membership helpers -/

theorem DomC.mem_empty (v : Value) : DomC.empty.mem v = false := by
  cases v with
  | int i =>
      simp only [DomC.empty, DomC.mem]
      by_cases h : 1 ≤ i
      · have h2 : ¬ i ≤ 0 := by omega
        simp [h, h2]
      · simp [h]
  | bool b => simp [DomC.empty, DomC.mem]
  | setOfInt s => simp [DomC.empty, DomC.mem]
  | array a => simp [DomC.empty, DomC.mem]

theorem DomC.mem_intView_exists {d : DomC} {u : Value} (hm : d.mem u = true) :
    ∃ i, Value.intView u = some i := by
  cases d with
  | bool bits =>
      cases u with
      | bool b => exact ⟨if b then 1 else 0, by simp [Value.intView]⟩
      | int i => simp [DomC.mem] at hm
      | setOfInt s => simp [DomC.mem] at hm
      | array a => simp [DomC.mem] at hm
  | bounds lo hi =>
      cases u with
      | int i => exact ⟨i, rfl⟩
      | bool b => simp [DomC.mem] at hm
      | setOfInt s => simp [DomC.mem] at hm
      | array a => simp [DomC.mem] at hm
  | bitset lo words =>
      cases u with
      | int i => exact ⟨i, rfl⟩
      | bool b => simp [DomC.mem] at hm
      | setOfInt s => simp [DomC.mem] at hm
      | array a => simp [DomC.mem] at hm
  | boundsHoles lo hi holes =>
      cases u with
      | int i => exact ⟨i, rfl⟩
      | bool b => simp [DomC.mem] at hm
      | setOfInt s => simp [DomC.mem] at hm
      | array a => simp [DomC.mem] at hm

theorem DomC.memIntView_eq_true_iff (d : DomC) (v : Int) :
    d.memIntView v = true ↔
      ∃ u, d.mem u = true ∧ Value.intView u = some v := by
  cases d with
  | bool bits =>
      simp only [DomC.memIntView]
      by_cases hv0 : v = 0
      · subst hv0
        simp only [beq_self_eq_true, if_true]
        constructor
        · intro h
          exact ⟨.bool false, h, rfl⟩
        · rintro ⟨u, hm, huv⟩
          cases u with
          | bool b =>
              cases b
              · exact hm
              · simp [Value.intView] at huv
          | int i => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · by_cases hv1 : v = 1
        · subst hv1
          rw [if_neg (by simp [hv0])]
          simp only [beq_self_eq_true, if_true]
          constructor
          · intro h
            exact ⟨.bool true, h, rfl⟩
          · rintro ⟨u, hm, huv⟩
            cases u with
            | bool b =>
                cases b
                · simp [Value.intView] at huv
                · exact hm
            | int i => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
        · rw [if_neg (by simp [hv0]), if_neg (by simp [hv1])]
          constructor
          · intro h; cases h
          · rintro ⟨u, hm, huv⟩
            cases u with
            | bool b =>
                cases b
                · simp [Value.intView] at huv; omega
                · simp [Value.intView] at huv; omega
            | int i => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
  | bounds lo hi =>
      simp only [DomC.memIntView, DomC.mem]
      constructor
      · intro h
        exact ⟨.int v, h, rfl⟩
      · rintro ⟨u, hm, huv⟩
        cases u with
        | int i =>
            simp only [Value.intView, Option.some.injEq] at huv
            subst huv
            exact hm
        | bool b => simp at hm
        | setOfInt s => simp at hm
        | array a => simp at hm
  | bitset lo words =>
      simp only [DomC.memIntView, DomC.mem]
      constructor
      · intro h
        exact ⟨.int v, h, rfl⟩
      · rintro ⟨u, hm, huv⟩
        cases u with
        | int i =>
            simp only [Value.intView, Option.some.injEq] at huv
            subst huv
            exact hm
        | bool b => simp at hm
        | setOfInt s => simp at hm
        | array a => simp at hm
  | boundsHoles lo hi holes =>
      simp only [DomC.memIntView, DomC.mem]
      constructor
      · intro h
        exact ⟨.int v, h, rfl⟩
      · rintro ⟨u, hm, huv⟩
        cases u with
        | int i =>
            simp only [Value.intView, Option.some.injEq] at huv
            subst huv
            exact hm
        | bool b => simp at hm
        | setOfInt s => simp at hm
        | array a => simp at hm

theorem DomC.memIntView_eq_false_iff (d : DomC) (v : Int) :
    d.memIntView v = false ↔
      ∀ u, d.mem u = true → Value.intView u ≠ some v := by
  constructor
  · intro h u hm huv
    have ht : d.memIntView v = true :=
      (DomC.memIntView_eq_true_iff d v).mpr ⟨u, hm, huv⟩
    rw [h] at ht
    cases ht
  · intro h
    cases hb : d.memIntView v with
    | false => rfl
    | true =>
        obtain ⟨u, hm, huv⟩ := (DomC.memIntView_eq_true_iff d v).mp hb
        exact absurd huv (h u hm)

theorem DomC.memIntView_false_of_mem {d : DomC} {u : Value} {v : Int}
    (h : d.memIntView v = false) (hm : d.mem u = true) :
    Value.intView u ≠ some v :=
  (DomC.memIntView_eq_false_iff d v).mp h u hm

theorem DomC.memIntView_true_of_mem {d : DomC} {u : Value} {v : Int}
    (hm : d.mem u = true) (huv : Value.intView u = some v) :
    d.memIntView v = true :=
  (DomC.memIntView_eq_true_iff d v).mpr ⟨u, hm, huv⟩

theorem boundsHoles_mem_int_iff (lo hi : Int) (holes : Array Int) (x : Int) :
    (DomC.boundsHoles lo hi holes).mem (.int x) = true ↔
      lo ≤ x ∧ x ≤ hi ∧ memHoleRange holes x = false := by
  simp [DomC.mem, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

theorem memHoleRange_filter_le_iff {holes : Array Int} (hpair : holes.toList.Pairwise (fun a b => a < b))
    (hi' v : Int) :
    memHoleRange (holes.filter (fun h => decide (h ≤ hi'))) v = true ↔
      memHoleRange holes v = true ∧ v ≤ hi' := by
  have hpair' : (holes.filter (fun h => decide (h ≤ hi'))).toList.Pairwise (fun a b => a < b) := by
    rw [Array.toList_filter]
    exact List.Pairwise.filter _ hpair
  rw [memHoleRange_eq_true_iff (holes := holes.filter (fun h => decide (h ≤ hi'))) hpair']
  rw [Array.toList_filter, List.mem_filter]
  rw [memHoleRange_eq_true_iff (holes := holes) hpair]
  constructor
  · rintro ⟨hm, hd⟩
    exact ⟨hm, of_decide_eq_true hd⟩
  · rintro ⟨hm, hv⟩
    exact ⟨hm, decide_eq_true hv⟩

theorem memHoleRange_filter_ge_iff {holes : Array Int} (hpair : holes.toList.Pairwise (fun a b => a < b))
    (lo' v : Int) :
    memHoleRange (holes.filter (fun h => decide (lo' ≤ h))) v = true ↔
      memHoleRange holes v = true ∧ lo' ≤ v := by
  have hpair' : (holes.filter (fun h => decide (lo' ≤ h))).toList.Pairwise (fun a b => a < b) := by
    rw [Array.toList_filter]
    exact List.Pairwise.filter _ hpair
  rw [memHoleRange_eq_true_iff (holes := holes.filter (fun h => decide (lo' ≤ h))) hpair']
  rw [Array.toList_filter, List.mem_filter]
  rw [memHoleRange_eq_true_iff (holes := holes) hpair]
  constructor
  · rintro ⟨hm, hd⟩
    exact ⟨hm, of_decide_eq_true hd⟩
  · rintro ⟨hm, hv⟩
    exact ⟨hm, decide_eq_true hv⟩

theorem boundsHoles_filter_le_mem_int_iff (lo hi' : Int) (holes : Array Int) (x : Int)
    (hpair : holes.toList.Pairwise (fun a b => a < b)) :
    (DomC.boundsHoles lo hi' (holes.filter (fun h => decide (h ≤ hi')))).mem (.int x) = true ↔
      lo ≤ x ∧ x ≤ hi' ∧ memHoleRange holes x = false := by
  rw [boundsHoles_mem_int_iff]
  constructor
  · rintro ⟨hlo, hhi, hf⟩
    refine ⟨hlo, hhi, ?_⟩
    cases hb : memHoleRange holes x
    · rfl
    · exfalso
      have ht := (memHoleRange_filter_le_iff hpair hi' x).mpr ⟨hb, hhi⟩
      rw [hf] at ht
      cases ht
  · rintro ⟨hlo, hhi, hh⟩
    refine ⟨hlo, hhi, ?_⟩
    cases hb : memHoleRange (holes.filter (fun h => decide (h ≤ hi'))) x
    · rfl
    · exfalso
      have ht := (memHoleRange_filter_le_iff hpair hi' x).mp hb
      rw [hh] at ht
      cases ht.1

theorem boundsHoles_filter_ge_mem_int_iff (lo' hi : Int) (holes : Array Int) (x : Int)
    (hpair : holes.toList.Pairwise (fun a b => a < b)) :
    (DomC.boundsHoles lo' hi (holes.filter (fun h => decide (lo' ≤ h)))).mem (.int x) = true ↔
      lo' ≤ x ∧ x ≤ hi ∧ memHoleRange holes x = false := by
  rw [boundsHoles_mem_int_iff]
  constructor
  · rintro ⟨hlo, hhi, hf⟩
    refine ⟨hlo, hhi, ?_⟩
    cases hb : memHoleRange holes x
    · rfl
    · exfalso
      have ht := (memHoleRange_filter_ge_iff hpair lo' x).mpr ⟨hb, hlo⟩
      rw [hf] at ht
      cases ht
  · rintro ⟨hlo, hhi, hh⟩
    refine ⟨hlo, hhi, ?_⟩
    cases hb : memHoleRange (holes.filter (fun h => decide (lo' ≤ h))) x
    · rfl
    · exfalso
      have ht := (memHoleRange_filter_ge_iff hpair lo' x).mp hb
      rw [hh] at ht
      cases ht.1



theorem mem_if_empty_bitset (lo : Int) (words : Array UInt64) (x : Int) :
    (if words.isEmpty then (DomC.bounds 1 0 : DomC) else .bitset lo words).mem (.int x)
      = (if x - lo < 0 then false else bitsetMem words (x - lo).toNat) := by
  by_cases h : words.isEmpty = true
  · rw [if_pos h]
    have hsz : words.size = 0 := Array.isEmpty_iff_size_eq_zero.mp h
    by_cases hx : x - lo < 0
    · rw [if_pos hx]
      show DomC.empty.mem (.int x) = false
      rw [DomC.mem_empty]
    · rw [if_neg hx]
      have hfalse : bitsetMem words (x - lo).toNat = false := by
        apply bitsetMem_eq_false_of_size_le
        omega
      rw [hfalse]
      show DomC.empty.mem (.int x) = false
      rw [DomC.mem_empty]
  · rw [if_neg h]
    simp only [DomC.mem]

theorem mem_bool_bounds_bitset_ite (c : Bool) (lo : Int) (kept : Array UInt64) (b : Bool) :
    (if c then (DomC.bounds 1 0 : DomC) else .bitset lo kept).mem (.bool b) = false := by
  by_cases h : c = true
  · rw [if_pos h]; simp [DomC.mem]
  · rw [if_neg h]; simp [DomC.mem]

theorem mem_if_allzero_bitset (base : Int) (kept : Array UInt64) (x : Int) :
    (if kept.all (fun w => w == 0) then (DomC.bounds 1 0 : DomC) else .bitset base kept).mem (.int x)
      = (if x - base < 0 then false else bitsetMem kept (x - base).toNat) := by
  by_cases h : kept.all (fun w => w == 0) = true
  · rw [if_pos h]
    by_cases hx : x - base < 0
    · rw [if_pos hx]
      show DomC.empty.mem (.int x) = false
      rw [DomC.mem_empty]
    · rw [if_neg hx]
      have hfalse : bitsetMem kept (x - base).toNat = false := bitsetMem_all_zero kept _ h
      rw [hfalse]
      show DomC.empty.mem (.int x) = false
      rw [DomC.mem_empty]
  · rw [if_neg h]
    simp only [DomC.mem]

/-! ## `setLe` membership -/

theorem DomC.mem_setLe (d : DomC) (k : Int) (hWF : d.WF) (v : Value) :
    (d.setLe k).mem v = true ↔
      d.mem v = true ∧ ∃ i, Value.intView v = some i ∧ i ≤ k := by
  cases d with
  | bool bits =>
      simp only [DomC.WF] at hWF
      rw [DomC.setLe.eq_1]
      by_cases hk0 : k < 0
      · rw [if_pos hk0]
        constructor
        · intro h
          cases v <;> simp [DomC.mem] at h <;> omega
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | bool b =>
              cases b <;> simp [Value.intView] at hiv <;> omega
          | int i' => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · by_cases hk : k == 0
        · rw [if_neg hk0, if_pos hk]
          have hkz : k = 0 := beq_iff_eq.mp hk
          subst hkz
          constructor
          · intro hmv
            cases v with
            | bool b =>
                cases b
                · simp [DomC.mem, uint8_and_one_and_one] at hmv ⊢
                  exact ⟨hmv, 0, rfl, by omega⟩
                · simp [DomC.mem, uint8_and_one_and_two] at hmv
            | int i' => simp [DomC.mem] at hmv
            | setOfInt s => simp [DomC.mem] at hmv
            | array a => simp [DomC.mem] at hmv
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | bool b =>
                cases b
                · simp [DomC.mem, uint8_and_one_and_one] at hm ⊢
                  exact hm
                · simp [Value.intView] at hiv
                  omega
            | int i' => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
        · rw [if_neg hk0, if_neg hk]
          have hkpos : 1 ≤ k := by
            have hkge : 0 ≤ k := by omega
            have hkne : k ≠ 0 := by
              intro h; exact hk (by simpa [h])
            omega
          constructor
          · intro hmv
            cases v with
            | bool b =>
                cases b
                · simp [DomC.mem, hWF] at hmv ⊢
                  exact ⟨hmv, 0, rfl, by omega⟩
                · simp [DomC.mem, hWF] at hmv ⊢
                  exact ⟨hmv, 1, rfl, by omega⟩
            | int i' => simp [DomC.mem] at hmv
            | setOfInt s => simp [DomC.mem] at hmv
            | array a => simp [DomC.mem] at hmv
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | bool b =>
                cases b
                · simp [DomC.mem, hWF] at hm ⊢
                  exact hm
                · simp [DomC.mem, hWF] at hm ⊢
                  exact hm
            | int i' => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
  | bounds lo hi =>
      simp only [DomC.WF] at hWF
      rw [DomC.setLe.eq_2]
      by_cases hk : k < hi
      · rw [if_pos hk]
        constructor
        · intro hm
          cases v with
          | int i =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              exact ⟨⟨hm.1, by omega⟩, i, rfl, by omega⟩
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | int i' =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              simp only [Value.intView, Option.some.injEq] at hiv
              subst hiv
              exact ⟨hm.1, by omega⟩
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · rw [if_neg hk]
        constructor
        · intro hm
          cases v with
          | int i =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              exact ⟨hm, i, rfl, by omega⟩
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | int i' =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              exact hm
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
  | bitset lo words =>
      simp only [DomC.WF] at hWF
      rw [DomC.setLe.eq_3]
      cases v with
      | int x =>
          simp only [Value.intView, Option.some.injEq, exists_eq_left']
          by_cases hk : k < lo
          · rw [if_pos hk]
            constructor
            · intro h
              have hb : (DomC.bounds 1 0).mem (.int x) = false := by
                show DomC.empty.mem (.int x) = false
                rw [DomC.mem_empty]
              rw [hb] at h; cases h
            · rintro ⟨hm, hik⟩
              simp only [DomC.mem, if_pos (show x - lo < 0 by omega)] at hm
              cases hm
          · rw [if_neg hk]
            by_cases hsz : words.size = 0
            · rw [if_neg (show ¬ ((k - lo).toNat / 64 < words.size) by omega), hsz]
              have hempty : (words.extract 0 0).isEmpty = true := by
                rw [Array.isEmpty]; simp
              rw [if_pos hempty]
              constructor
              · intro h
                have hb : (DomC.bounds 1 0).mem (.int x) = false := by
                  show DomC.empty.mem (.int x) = false
                  rw [DomC.mem_empty]
                rw [hb] at h; cases h
              · rintro ⟨hm, -⟩
                simp only [DomC.mem] at hm
                by_cases hx : x - lo < 0
                · rw [if_pos hx] at hm; cases hm
                · rw [if_neg hx] at hm
                  have hfalse : bitsetMem words (x - lo).toNat = false := by
                    apply bitsetMem_eq_false_of_size_le
                    omega
                  rw [hfalse] at hm; cases hm
            · by_cases hwi : (k - lo).toNat / 64 < words.size
              · rw [if_pos hwi]
                have hsize : (words.extract 0 ((k - lo).toNat / 64 + 1)).size
                    = (k - lo).toNat / 64 + 1 := by
                  rw [Array.size_extract]; omega
                have hempty : (words.extract 0 ((k - lo).toNat / 64 + 1)).isEmpty = false := by
                  rw [Array.isEmpty]
                  simp [hsize]
                rw [if_neg (by rw [hempty]; decide)]
                rw [hsize]
                rw [if_pos (show (k - lo).toNat / 64 < (k - lo).toNat / 64 + 1 by omega)]
                rw [if_pos (show (k - lo).toNat / 64 < (k - lo).toNat / 64 + 1 by omega)]
                rw [mem_if_empty_bitset]
                rw [bitsetMem_trim]
                by_cases hx : x - lo < 0
                · rw [if_pos hx]
                  simp only [DomC.mem, if_pos hx]
                  simp
                · rw [if_neg hx]
                  rw [bitsetMem_setLe_word (words := words) (wi := (k - lo).toNat / 64)
                    (bi := (k - lo).toNat % 64) (n := (x - lo).toNat) hwi
                    (Nat.mod_lt _ (by decide))]
                  simp only [DomC.mem, if_neg hx]
                  have hw : (k - lo).toNat / 64 * 64 + (k - lo).toNat % 64
                      = (k - lo).toNat := by
                    have := Nat.div_add_mod (k - lo).toNat 64
                    omega
                  have hle : (x - lo).toNat ≤ (k - lo).toNat ↔ x ≤ k := by
                    rw [← Int.ofNat_le, Int.toNat_of_nonneg (by omega),
                      Int.toNat_of_nonneg (by omega)]
                    constructor <;> intro h <;> omega
                  constructor
                  · rintro ⟨hm, hn⟩
                    exact ⟨hm, hle.mp (by rwa [hw] at hn)⟩
                  · rintro ⟨hm, hik⟩
                    refine ⟨hm, ?_⟩
                    rw [hw]
                    exact hle.mpr hik
              · rw [if_neg hwi]
                have hsize : (words.extract 0 words.size).size = words.size := by
                  rw [Array.size_extract]; omega
                have hempty : (words.extract 0 words.size).isEmpty = false := by
                  rw [Array.isEmpty]
                  simp [hsize, hsz]
                rw [if_neg (by rw [hempty]; decide)]
                rw [hsize]
                rw [if_neg hwi]
                rw [mem_if_empty_bitset]
                rw [bitsetMem_trim]
                by_cases hx : x - lo < 0
                · rw [if_pos hx]
                  simp only [DomC.mem, if_pos hx]
                  simp
                · rw [if_neg hx]
                  rw [bitsetMem_setLe_word_ge (words := words) (wi := (k - lo).toNat / 64)
                    (bi := (k - lo).toNat % 64) (n := (x - lo).toNat) (by omega)
                    (Nat.mod_lt _ (by decide))]
                  simp only [DomC.mem, if_neg hx]
                  have hw : (k - lo).toNat / 64 * 64 + (k - lo).toNat % 64
                      = (k - lo).toNat := by
                    have := Nat.div_add_mod (k - lo).toNat 64
                    omega
                  have hle : (x - lo).toNat ≤ (k - lo).toNat ↔ x ≤ k := by
                    rw [← Int.ofNat_le, Int.toNat_of_nonneg (by omega),
                      Int.toNat_of_nonneg (by omega)]
                    constructor <;> intro h <;> omega
                  constructor
                  · rintro ⟨hm, hn⟩
                    exact ⟨hm, hle.mp (by rwa [hw] at hn)⟩
                  · rintro ⟨hm, hik⟩
                    refine ⟨hm, ?_⟩
                    rw [hw]
                    exact hle.mpr hik
      | bool b =>
          by_cases hk : k < lo
          · rw [if_pos hk]; simp [DomC.mem]
          · rw [if_neg hk]; dsimp only
            by_cases h1 : (words.extract 0 (if (k - lo).toNat / 64 < words.size
                then (k - lo).toNat / 64 + 1 else words.size)).isEmpty
            · rw [if_pos h1]; simp [DomC.mem]
            · rw [if_neg h1]
              rw [mem_bool_bounds_bitset_ite]
              simp [DomC.mem]
      | setOfInt s =>
          constructor
          · intro h
            obtain ⟨i, hi⟩ := DomC.mem_intView_exists h
            simp [Value.intView] at hi
          · rintro ⟨hm, i, hi, -⟩
            simp [Value.intView] at hi
      | array a =>
          constructor
          · intro h
            obtain ⟨i, hi⟩ := DomC.mem_intView_exists h
            simp [Value.intView] at hi
          · rintro ⟨hm, i, hi, -⟩
            simp [Value.intView] at hi
  | boundsHoles lo hi holes =>
      simp only [DomC.WF] at hWF
      rw [DomC.setLe.eq_4]
      by_cases hlt : (if k < hi then k else hi) < lo
      · rw [if_pos hlt]
        constructor
        · intro h
          cases v <;> simp [DomC.mem] at h <;> omega
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | int x =>
              simp only [DomC.mem, Bool.and_eq_true, Bool.not_eq_true',
                decide_eq_true_eq] at hm
              simp only [Value.intView, Option.some.injEq] at hiv
              subst hiv
              by_cases hk : k < hi
              · rw [if_pos hk] at hlt
                omega
              · rw [if_neg hk] at hlt
                omega
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · rw [if_neg hlt]
        by_cases hk : k < hi
        · have hhi' : (if k < hi then k else hi) = k := if_pos hk
          rw [hhi']
          constructor
          · intro hm
            cases v with
            | int x =>
                rw [boundsHoles_filter_le_mem_int_iff lo k holes x hWF.1] at hm
                rw [boundsHoles_mem_int_iff]
                exact ⟨⟨hm.1, by omega, hm.2.2⟩, x, rfl, hm.2.1⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | int x =>
                simp only [Value.intView, Option.some.injEq] at hiv
                subst hiv
                rw [boundsHoles_mem_int_iff] at hm
                rw [boundsHoles_filter_le_mem_int_iff lo k holes x hWF.1]
                exact ⟨hm.1, hik, hm.2.2⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
        · have hhi' : (if k < hi then k else hi) = hi := if_neg hk
          rw [hhi']
          constructor
          · intro hm
            cases v with
            | int x =>
                rw [boundsHoles_filter_le_mem_int_iff lo hi holes x hWF.1] at hm
                rw [boundsHoles_mem_int_iff]
                exact ⟨hm, x, rfl, by omega⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | int x =>
                simp only [Value.intView, Option.some.injEq] at hiv
                subst hiv
                rw [boundsHoles_mem_int_iff] at hm
                rw [boundsHoles_filter_le_mem_int_iff lo hi holes x hWF.1]
                exact ⟨hm.1, hm.2.1, hm.2.2⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm


/-! ## `setGe` membership -/

theorem DomC.mem_setGe (d : DomC) (k : Int) (hWF : d.WF) (v : Value) :
    (d.setGe k).mem v = true ↔
      d.mem v = true ∧ ∃ i, Value.intView v = some i ∧ k ≤ i := by
  cases d with
  | bool bits =>
      simp only [DomC.WF] at hWF
      rw [DomC.setGe.eq_1]
      by_cases hk1 : 1 < k
      · rw [if_pos hk1]
        constructor
        · intro h
          cases v <;> simp [DomC.mem] at h
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | bool b =>
              cases b <;> simp [Value.intView] at hiv <;> omega
          | int i' => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · by_cases hk : k == 1
        · rw [if_neg hk1, if_pos hk]
          have hkz : k = 1 := beq_iff_eq.mp hk
          subst hkz
          constructor
          · intro hmv
            cases v with
            | bool b =>
                cases b
                · simp [DomC.mem, uint8_and_two_and_one] at hmv
                · simp [DomC.mem, uint8_and_two_and_two] at hmv ⊢
                  exact ⟨hmv, 1, rfl, by omega⟩
            | int i' => simp [DomC.mem] at hmv
            | setOfInt s => simp [DomC.mem] at hmv
            | array a => simp [DomC.mem] at hmv
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | bool b =>
                cases b
                · simp [Value.intView] at hiv
                  omega
                · simp [DomC.mem, uint8_and_two_and_two] at hm ⊢
                  exact hm
            | int i' => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
        · rw [if_neg hk1, if_neg hk]
          have hkle : k ≤ 0 := by
            have : k ≤ 1 := by omega
            have : k ≠ 1 := by
              intro h; exact hk (by simpa [h])
            omega
          constructor
          · intro hmv
            cases v with
            | bool b =>
                cases b
                · simp [DomC.mem, hWF] at hmv ⊢
                  exact ⟨hmv, 0, rfl, by omega⟩
                · simp [DomC.mem, hWF] at hmv ⊢
                  exact ⟨hmv, 1, rfl, by omega⟩
            | int i' => simp [DomC.mem] at hmv
            | setOfInt s => simp [DomC.mem] at hmv
            | array a => simp [DomC.mem] at hmv
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | bool b =>
                cases b
                · simp [DomC.mem, hWF] at hm ⊢
                  exact hm
                · simp [DomC.mem, hWF] at hm ⊢
                  exact hm
            | int i' => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
  | bounds lo hi =>
      simp only [DomC.WF] at hWF
      rw [DomC.setGe.eq_2]
      by_cases hk : lo < k
      · rw [if_pos hk]
        constructor
        · intro hm
          cases v with
          | int i =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              exact ⟨⟨by omega, hm.2⟩, i, rfl, by omega⟩
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | int i' =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              simp only [Value.intView, Option.some.injEq] at hiv
              subst hiv
              exact ⟨by omega, hm.2⟩
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · rw [if_neg hk]
        constructor
        · intro hm
          cases v with
          | int i =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              exact ⟨hm, i, rfl, by omega⟩
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | int i' =>
              simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq] at hm ⊢
              exact hm
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
  | bitset lo words =>
      simp only [DomC.WF] at hWF
      rw [DomC.setGe.eq_3]
      cases v with
      | int x =>
          simp only [Value.intView, Option.some.injEq, exists_eq_left']
          cases hhi : DomC.hi? (.bitset lo words) with
          | none =>
              rw [if_pos (by rfl)]
              constructor
              · intro h
                have hb : (DomC.bounds 1 0).mem (.int x) = false := by
                  show DomC.empty.mem (.int x) = false
                  rw [DomC.mem_empty]
                rw [hb] at h; cases h
              · rintro ⟨hm, -⟩
                simp only [DomC.mem] at hm
                by_cases hx : x - lo < 0
                · rw [if_pos hx] at hm; cases hm
                · rw [if_neg hx] at hm
                  have hfalse := bitsetMem_eq_false_of_hi?_none hhi (x - lo).toNat
                  rw [hfalse] at hm; cases hm
          | some a =>
              rw [if_neg (show ¬((some a).isNone = true) by simp)]
              by_cases hge : (((if lo < k then k else lo) - lo).toNat / 64 ≥ words.size)
              · rw [if_pos hge]
                rw [if_pos (by rfl)]
                constructor
                · intro h
                  have hb : (DomC.bounds 1 0).mem (.int x) = false := by
                    show DomC.empty.mem (.int x) = false
                    rw [DomC.mem_empty]
                  rw [hb] at h; cases h
                · rintro ⟨hm, hkx⟩
                  simp only [DomC.mem] at hm
                  by_cases hx : x - lo < 0
                  · rw [if_pos hx] at hm; cases hm
                  · rw [if_neg hx] at hm
                    have hlo'_le : (if lo < k then k else lo) ≤ x := by
                      by_cases hk : lo < k
                      · rw [if_pos hk]; exact hkx
                      · rw [if_neg hk]; omega
                    have hdiff_le : ((if lo < k then k else lo) - lo).toNat ≤ (x - lo).toNat := by
                      apply Int.toNat_le_toNat; omega
                    have hdiv : words.size ≤ (x - lo).toNat / 64 := by
                      omega
                    have hfalse : bitsetMem words (x - lo).toNat = false := by
                      apply bitsetMem_eq_false_of_size_le
                      omega
                    rw [hfalse] at hm; cases hm
              · rw [if_neg hge]
                have hlt : ((if lo < k then k else lo) - lo).toNat / 64 < words.size := by omega
                have hsize : (words.extract (((if lo < k then k else lo) - lo).toNat / 64) words.size).size
                    = words.size - ((if lo < k then k else lo) - lo).toNat / 64 := by
                  rw [Array.size_extract]; simp
                have hempty : (words.extract (((if lo < k then k else lo) - lo).toNat / 64) words.size).isEmpty = false := by
                  rw [Array.isEmpty]; simp [hsize]; omega
                rw [if_neg (by rw [hempty]; decide)]
                rw [mem_if_allzero_bitset]
                by_cases hx : x - (lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64)) < 0
                · rw [if_pos hx]
                  simp only [DomC.mem]
                  constructor
                  · intro h; cases h
                  · rintro ⟨hm, hkx⟩
                    by_cases hxlo : x - lo < 0
                    · rw [if_pos hxlo] at hm; cases hm
                    · rw [if_neg hxlo] at hm
                      by_cases hk : lo < k
                      · have hbase_le : lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64) ≤ k := by
                          rw [if_pos hk]
                          have hWint : (((((if lo < k then k else lo) - lo).toNat) : Nat) : Int)
                              = (if lo < k then k else lo) - lo := by
                            exact Int.toNat_of_nonneg (by omega)
                          have hWsplit : ((if lo < k then k else lo) - lo).toNat
                              = ((if lo < k then k else lo) - lo).toNat / 64 * 64
                                + ((if lo < k then k else lo) - lo).toNat % 64 := by
                            have := Nat.div_add_mod ((if lo < k then k else lo) - lo).toNat 64
                            omega
                          omega
                        omega
                      · have hbase : lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64) = lo := by
                          rw [if_neg hk]
                          simp
                        omega
                · rw [if_neg hx]
                  rw [bitsetMem_setGe_word (words := words)
                    (wi := ((if lo < k then k else lo) - lo).toNat / 64)
                    (bi := ((if lo < k then k else lo) - lo).toNat % 64)
                    (n := (x - (lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64))).toNat)
                    hlt (Nat.mod_lt _ (by decide))]
                  simp only [DomC.mem, if_neg (show ¬ x - lo < 0 by omega)]
                  have hWint : (((((if lo < k then k else lo) - lo).toNat) : Nat) : Int)
                      = (if lo < k then k else lo) - lo := by
                    exact Int.toNat_of_nonneg (by omega)
                  have hWsplit : ((if lo < k then k else lo) - lo).toNat
                      = ((if lo < k then k else lo) - lo).toNat / 64 * 64
                        + ((if lo < k then k else lo) - lo).toNat % 64 := by
                    have := Nat.div_add_mod ((if lo < k then k else lo) - lo).toNat 64
                    omega
                  have hmint : (((x - (lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64))).toNat : Nat) : Int)
                      = x - (lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64)) := by
                    exact Int.toNat_of_nonneg (by omega)
                  have hm_eq : ((if lo < k then k else lo) - lo).toNat / 64 * 64
                        + (x - (lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64))).toNat
                      = (x - lo).toNat := by
                    have h2 : ((((if lo < k then k else lo) - lo).toNat / 64 * 64
                        + (x - (lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64))).toNat : Nat) : Int)
                        = ((x - lo).toNat : Int) := by
                      rw [Int.natCast_add, hmint, Int.toNat_of_nonneg (by omega)]
                      omega
                    exact Int.ofNat.inj h2
                  have hbase_eq : lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64)
                        + ↑(((if lo < k then k else lo) - lo).toNat % 64)
                      = (if lo < k then k else lo) := by
                    omega
                  have hbi_iff : ((if lo < k then k else lo) - lo).toNat % 64
                        ≤ (x - (lo + ↑(((if lo < k then k else lo) - lo).toNat / 64 * 64))).toNat
                      ↔ k ≤ x := by
                    have hmcast := hmint
                    by_cases hk : lo < k
                    · rw [if_pos hk] at hbase_eq
                      omega
                    · rw [if_neg hk] at hbase_eq
                      omega
                  rw [hm_eq]
                  constructor
                  · rintro ⟨hm, hbi⟩
                    exact ⟨hm, hbi_iff.mp hbi⟩
                  · rintro ⟨hm, hkx⟩
                    exact ⟨hm, hbi_iff.mpr hkx⟩
      | bool b =>
          simp only [Value.intView]
          cases hhi : DomC.hi? (.bitset lo words) with
          | none =>
              rw [if_pos (by rfl)]
              simp [DomC.mem]
          | some a =>
              rw [if_neg (show ¬((some a).isNone = true) by simp)]
              by_cases hge : (((if lo < k then k else lo) - lo).toNat / 64 ≥ words.size)
              · rw [if_pos hge]
                rw [if_pos (by rfl)]
                simp [DomC.mem]
              · rw [if_neg hge]
                have hlt : ((if lo < k then k else lo) - lo).toNat / 64 < words.size := by omega
                have hsize : (words.extract (((if lo < k then k else lo) - lo).toNat / 64) words.size).size
                    = words.size - ((if lo < k then k else lo) - lo).toNat / 64 := by
                  rw [Array.size_extract]; simp
                have hempty : (words.extract (((if lo < k then k else lo) - lo).toNat / 64) words.size).isEmpty = false := by
                  rw [Array.isEmpty]; simp [hsize]; omega
                rw [if_neg (by rw [hempty]; decide)]
                rw [mem_bool_bounds_bitset_ite]
                simp [DomC.mem]
      | setOfInt s =>
          constructor
          · intro h
            obtain ⟨i, hi⟩ := DomC.mem_intView_exists h
            simp [Value.intView] at hi
          · rintro ⟨hm, i, hi, -⟩
            simp [Value.intView] at hi
      | array a =>
          constructor
          · intro h
            obtain ⟨i, hi⟩ := DomC.mem_intView_exists h
            simp [Value.intView] at hi
          · rintro ⟨hm, i, hi, -⟩
            simp [Value.intView] at hi
  | boundsHoles lo hi holes =>
      simp only [DomC.WF] at hWF
      rw [DomC.setGe.eq_4]
      by_cases hlt : hi < (if lo < k then k else lo)
      · rw [if_pos hlt]
        constructor
        · intro h
          cases v <;> simp [DomC.mem] at h <;> omega
        · rintro ⟨hm, i, hiv, hik⟩
          cases v with
          | int x =>
              simp only [DomC.mem, Bool.and_eq_true, Bool.not_eq_true',
                decide_eq_true_eq] at hm
              simp only [Value.intView, Option.some.injEq] at hiv
              subst hiv
              by_cases hk : lo < k
              · rw [if_pos hk] at hlt
                omega
              · rw [if_neg hk] at hlt
                omega
          | bool b => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · rw [if_neg hlt]
        by_cases hk : lo < k
        · have hlo' : (if lo < k then k else lo) = k := if_pos hk
          rw [hlo']
          constructor
          · intro hm
            cases v with
            | int x =>
                rw [boundsHoles_filter_ge_mem_int_iff k hi holes x hWF.1] at hm
                rw [boundsHoles_mem_int_iff]
                exact ⟨⟨by omega, hm.2.1, hm.2.2⟩, x, rfl, hm.1⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | int x =>
                simp only [Value.intView, Option.some.injEq] at hiv
                subst hiv
                rw [boundsHoles_mem_int_iff] at hm
                rw [boundsHoles_filter_ge_mem_int_iff k hi holes x hWF.1]
                exact ⟨hik, hm.2.1, hm.2.2⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
        · have hlo' : (if lo < k then k else lo) = lo := if_neg hk
          rw [hlo']
          constructor
          · intro hm
            cases v with
            | int x =>
                rw [boundsHoles_filter_ge_mem_int_iff lo hi holes x hWF.1] at hm
                rw [boundsHoles_mem_int_iff]
                exact ⟨hm, x, rfl, by omega⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
          · rintro ⟨hm, i, hiv, hik⟩
            cases v with
            | int x =>
                simp only [Value.intView, Option.some.injEq] at hiv
                subst hiv
                rw [boundsHoles_mem_int_iff] at hm
                rw [boundsHoles_filter_ge_mem_int_iff lo hi holes x hWF.1]
                exact ⟨hm.1, hm.2.1, hm.2.2⟩
            | bool b => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm


theorem DomC.mem_fix (d : DomC) (w v : Value) (hWF : d.WF) :
    (d.fix w).mem v = true ↔ d.mem v = true ∧ v = w := by
  cases w with
  | bool b =>
      rw [DomC.fix.eq_1]
      by_cases hm : d.mem (.bool b) = true
      · rw [if_pos hm]
        cases d with
        | bool bits =>
            cases b
            · cases v with
              | bool b' =>
                  cases b'
                  · simpa [DomC.mem] using hm
                  · simp [DomC.mem] <;> decide
              | int i => simp [DomC.mem]
              | setOfInt s => simp [DomC.mem]
              | array a => simp [DomC.mem]
            · cases v with
              | bool b' =>
                  cases b'
                  · simp [DomC.mem] <;> decide
                  · simpa [DomC.mem] using hm
              | int i => simp [DomC.mem]
              | setOfInt s => simp [DomC.mem]
              | array a => simp [DomC.mem]
        | bounds lo hi => simp [DomC.mem] at hm
        | bitset lo words => simp [DomC.mem] at hm
        | boundsHoles lo hi holes => simp [DomC.mem] at hm
      · rw [if_neg hm]
        constructor
        · intro h
          have hb : (DomC.bounds 1 0).mem v = false := by
            show DomC.empty.mem v = false
            rw [DomC.mem_empty]
          rw [hb] at h; cases h
        · rintro ⟨hmv, rfl⟩
          exact absurd hmv hm
  | int i =>
      rw [DomC.fix.eq_2]
      by_cases hm : d.mem (.int i) = true
      · rw [if_pos hm]
        cases v with
        | int x =>
            simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨h1, h2⟩
              have hxi : x = i := by omega
              subst hxi
              exact ⟨hm, rfl⟩
            · rintro ⟨hmv, hiv⟩
              cases hiv
              omega
        | bool b => simp [DomC.mem]
        | setOfInt s => simp [DomC.mem]
        | array a => simp [DomC.mem]
      · rw [if_neg hm]
        constructor
        · intro h
          have hb : (DomC.bounds 1 0).mem v = false := by
            show DomC.empty.mem v = false
            rw [DomC.mem_empty]
          rw [hb] at h; cases h
        · rintro ⟨hmv, rfl⟩
          exact absurd hmv hm
  | setOfInt s =>
      cases v <;> simp [DomC.fix, DomC.mem, DomC.mem_empty] <;> omega
  | array a =>
      cases v <;> simp [DomC.fix, DomC.mem, DomC.mem_empty] <;> omega

theorem DomC.mem_fixIntView (d : DomC) (k : Int) (v : Value) (hWF : d.WF) :
    (d.fixIntView k).mem v = true ↔ d.mem v = true ∧ Value.intView v = some k := by
  cases d with
  | bool bits =>
      simp only [DomC.fixIntView]
      by_cases h0 : k == 0
      · rw [if_pos h0]
        have hk0 : k = 0 := beq_iff_eq.mp h0
        subst hk0
        rw [DomC.mem_fix (.bool bits) (.bool false) v hWF]
        constructor
        · rintro ⟨hm, hv⟩
          exact ⟨hm, by rw [hv]; rfl⟩
        · rintro ⟨hm, hiv⟩
          refine ⟨hm, ?_⟩
          cases v with
          | bool b =>
              cases b
              · rfl
              · simp [Value.intView] at hiv
          | int i => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · rw [if_neg h0]
        by_cases h1 : k == 1
        · rw [if_pos h1]
          have hk1 : k = 1 := beq_iff_eq.mp h1
          subst hk1
          rw [DomC.mem_fix (.bool bits) (.bool true) v hWF]
          constructor
          · rintro ⟨hm, hv⟩
            exact ⟨hm, by rw [hv]; rfl⟩
          · rintro ⟨hm, hiv⟩
            refine ⟨hm, ?_⟩
            cases v with
            | bool b =>
                cases b
                · simp [Value.intView] at hiv
                · rfl
            | int i => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
        · rw [if_neg h1]
          have hk0 : k ≠ 0 := by
            intro h; exact h0 (by rw [h]; rfl)
          have hk1 : k ≠ 1 := by
            intro h; exact h1 (by rw [h]; rfl)
          constructor
          · intro h
            have hb : (DomC.bounds 1 0).mem v = false := by
              show DomC.empty.mem v = false
              rw [DomC.mem_empty]
            rw [hb] at h; cases h
          · rintro ⟨hm, hiv⟩
            cases v with
            | bool b =>
                cases b
                · simp [Value.intView] at hiv
                  omega
                · simp [Value.intView] at hiv
                  omega
            | int i => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
  | bounds lo hi =>
      simp only [DomC.fixIntView]
      rw [DomC.mem_fix (DomC.bounds lo hi) (.int k) v hWF]
      constructor
      · rintro ⟨hm, hv⟩
        exact ⟨hm, by rw [hv]; rfl⟩
      · rintro ⟨hm, hiv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            simp only [Value.intView, Option.some.injEq] at hiv
            subst hiv; rfl
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
  | bitset lo words =>
      simp only [DomC.fixIntView]
      rw [DomC.mem_fix (DomC.bitset lo words) (.int k) v hWF]
      constructor
      · rintro ⟨hm, hv⟩
        exact ⟨hm, by rw [hv]; rfl⟩
      · rintro ⟨hm, hiv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            simp only [Value.intView, Option.some.injEq] at hiv
            subst hiv; rfl
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
  | boundsHoles lo hi holes =>
      simp only [DomC.fixIntView]
      rw [DomC.mem_fix (DomC.boundsHoles lo hi holes) (.int k) v hWF]
      constructor
      · rintro ⟨hm, hv⟩
        exact ⟨hm, by rw [hv]; rfl⟩
      · rintro ⟨hm, hiv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            simp only [Value.intView, Option.some.injEq] at hiv
            subst hiv; rfl
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm

theorem uint8_and_254_and_1 (x : UInt8) : (x &&& 254) &&& 1 = 0 := by
  rw [UInt8.and_assoc, show (254:UInt8) &&& 1 = 0 by decide, UInt8.and_zero]

theorem uint8_and_254_and_2 (x : UInt8) : (x &&& 254) &&& 2 = x &&& 2 := by
  rw [UInt8.and_assoc, show (254:UInt8) &&& 2 = 2 by decide]

theorem uint8_and_253_and_1 (x : UInt8) : (x &&& 253) &&& 1 = x &&& 1 := by
  rw [UInt8.and_assoc, show (253:UInt8) &&& 1 = 1 by decide]

theorem uint8_and_253_and_2 (x : UInt8) : (x &&& 253) &&& 2 = 0 := by
  rw [UInt8.and_assoc, show (253:UInt8) &&& 2 = 0 by decide, UInt8.and_zero]


theorem memHoleRange_singleton (v x : Int) :
    memHoleRange #[v] x = decide (x = v) := by
  by_cases h : x = v
  · cases h
    have htrue : memHoleRange #[v] v = true :=
      (memHoleRange_eq_true_iff (by simp)).mpr (by simp)
    rw [htrue]
    simp
  · have hfalse : memHoleRange #[v] x = false :=
      (memHoleRange_eq_false_iff (by simp)).mpr (by simp [h])
    rw [hfalse]
    simp [h]

theorem boundsHoles_singleton_mem_int (lo hi r x : Int) :
    (DomC.boundsHoles lo hi #[r]).mem (.int x) = true ↔
      lo ≤ x ∧ x ≤ hi ∧ x ≠ r := by
  simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq]
  rw [memHoleRange_singleton]
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, and_assoc]


theorem bitsetMem_eq_word_and (words : Array UInt64) {wi m : Nat} {w : UInt64}
    (hw : words[wi]? = some w) (hm : m / 64 = wi) :
    bitsetMem words m = ((w &&& u64bit (m % 64)) != 0) := by
  unfold bitsetMem
  rw [hm, hw]

theorem bitsetMem_eq_word_and_true (words : Array UInt64) {wi m : Nat} {w : UInt64}
    (hw : words[wi]? = some w) (hm : m / 64 = wi) :
    bitsetMem words m = true ↔ (w &&& u64bit (m % 64)) != 0 := by
  rw [bitsetMem_eq_word_and words hw hm]

theorem bitsetMem_eq_false_of_getElem?_none {words : Array UInt64} {n : Nat}
    (h : words[n / 64]? = none) : bitsetMem words n = false := by
  unfold bitsetMem
  rw [h]

theorem mod_ne_iff_ne_of_div_eq {m n wi : Nat} (hm : m / 64 = wi) (hn : n / 64 = wi) :
    m % 64 ≠ n % 64 ↔ m ≠ n := by
  constructor
  · intro h hmn
    exact h (by rw [hmn])
  · intro h hmod
    apply h
    have h1 := Nat.div_add_mod m 64
    have h2 := Nat.div_add_mod n 64
    rw [hm] at h1
    rw [hn, ← hmod] at h2
    omega

theorem bitset_set!_mem_iff (words : Array UInt64) {n : Nat}
    (hwi : n / 64 < words.size) {w : UInt64} (hw : words[n / 64]? = some w)
    {m : Nat} (hm : m / 64 = n / 64) :
    bitsetMem (words.set! (n / 64) (w &&& ~~~u64bit (n % 64))) m = true ↔
      bitsetMem words m = true ∧ m % 64 ≠ n % 64 := by
  rw [bitsetMem_set! hwi]
  rw [if_pos hm]
  rw [u64_and_not_u64bit_ne_zero_iff w (Nat.mod_lt n (by decide)) (Nat.mod_lt m (by decide))]
  rw [bitsetMem_eq_word_and_true words hw hm]

theorem DomC.mem_eq_false_of_value_not_int {d : DomC} {v : Value}
    (hd : ∀ bits, d ≠ .bool bits) (hv : ∀ i, v ≠ .int i) : d.mem v = false := by
  cases d with
  | bool bits => exact absurd rfl (hd bits)
  | bounds lo hi => cases v <;> simp [DomC.mem] at *
  | bitset lo words => cases v <;> simp [DomC.mem] at *
  | boundsHoles lo hi holes => cases v <;> simp [DomC.mem] at *

theorem DomC.mem_remove (d : DomC) (w v : Value) (hWF : d.WF) :
    (d.remove w).mem v = true ↔ d.mem v = true ∧ v ≠ w := by
  cases d with
  | bool bits =>
      cases w with
      | bool b =>
          rw [DomC.remove.eq_1]
          cases b
          · cases v with
            | bool b' =>
                cases b'
                · simp [DomC.mem, uint8_and_254_and_1]
                · simp [DomC.mem, uint8_and_254_and_2]
            | int i => simp [DomC.remove, DomC.mem]
            | setOfInt s => simp [DomC.remove, DomC.mem]
            | array a => simp [DomC.remove, DomC.mem]
          · cases v with
            | bool b' =>
                cases b'
                · simp [DomC.mem, uint8_and_253_and_1]
                · simp [DomC.mem, uint8_and_253_and_2]
            | int i => simp [DomC.remove, DomC.mem]
            | setOfInt s => simp [DomC.remove, DomC.mem]
            | array a => simp [DomC.remove, DomC.mem]
      | int i =>
          cases v with
          | bool b => simp [DomC.remove, DomC.mem]
          | int j => simp [DomC.remove, DomC.mem]
          | setOfInt s => simp [DomC.remove, DomC.mem]
          | array a => simp [DomC.remove, DomC.mem]
      | setOfInt s =>
          cases v with
          | bool b => simp [DomC.remove, DomC.mem]
          | int j => simp [DomC.remove, DomC.mem]
          | setOfInt s' => simp [DomC.remove, DomC.mem]
          | array a => simp [DomC.remove, DomC.mem]
      | array a =>
          cases v with
          | bool b => simp [DomC.remove, DomC.mem]
          | int j => simp [DomC.remove, DomC.mem]
          | setOfInt s => simp [DomC.remove, DomC.mem]
          | array a' => simp [DomC.remove, DomC.mem]
  | bounds lo hi =>
      cases w with
      | int r =>
          rw [DomC.remove.eq_2]
          cases v with
          | int x =>
              by_cases hout : r < lo ∨ hi < r
              · rw [if_pos (by simp [hout])]
                simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq, Value.int.injEq]
                constructor
                · rintro ⟨h1, h2⟩
                  exact ⟨⟨h1, h2⟩, by grind⟩
                · rintro ⟨⟨h1, h2⟩, -⟩
                  exact ⟨h1, h2⟩
              · rw [if_neg (by simp [hout])]
                by_cases hlo : r = lo
                · subst hlo
                  rw [if_pos (by simp)]
                  simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq, Value.int.injEq]
                  constructor
                  · rintro ⟨h1, h2⟩
                    exact ⟨⟨by grind, h2⟩, by grind⟩
                  · rintro ⟨⟨h1, h2⟩, hne⟩
                    exact ⟨by grind, h2⟩
                · rw [if_neg (by simp [hlo])]
                  by_cases hhi : r = hi
                  · subst hhi
                    rw [if_pos (by simp)]
                    simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq, Value.int.injEq]
                    constructor
                    · rintro ⟨h1, h2⟩
                      exact ⟨⟨h1, by grind⟩, by grind⟩
                    · rintro ⟨⟨h1, h2⟩, hne⟩
                      exact ⟨h1, by grind⟩
                  · rw [if_neg (by simp [hhi])]
                    rw [boundsHoles_singleton_mem_int]
                    simp only [DomC.mem, Bool.and_eq_true, decide_eq_true_eq,
                      Value.int.injEq, ne_eq, and_assoc]
          | bool b =>
              have hd : ∀ bits, (if (decide (r < lo) || decide (hi < r)) = true then
                  DomC.bounds lo hi
                else if (r == lo) = true then DomC.bounds (lo + 1) hi
                else if (r == hi) = true then DomC.bounds lo (hi - 1)
                else DomC.boundsHoles lo hi #[r]) ≠ DomC.bool bits := by
                intro bits
                grind
              rw [DomC.mem_eq_false_of_value_not_int hd (by intro i h; cases h)]
              simp [DomC.mem]
          | setOfInt s =>
              have hd : ∀ bits, (if (decide (r < lo) || decide (hi < r)) = true then
                  DomC.bounds lo hi
                else if (r == lo) = true then DomC.bounds (lo + 1) hi
                else if (r == hi) = true then DomC.bounds lo (hi - 1)
                else DomC.boundsHoles lo hi #[r]) ≠ DomC.bool bits := by
                intro bits
                grind
              rw [DomC.mem_eq_false_of_value_not_int hd (by intro i h; cases h)]
              simp [DomC.mem]
          | array a =>
              have hd : ∀ bits, (if (decide (r < lo) || decide (hi < r)) = true then
                  DomC.bounds lo hi
                else if (r == lo) = true then DomC.bounds (lo + 1) hi
                else if (r == hi) = true then DomC.bounds lo (hi - 1)
                else DomC.boundsHoles lo hi #[r]) ≠ DomC.bool bits := by
                intro bits
                grind
              rw [DomC.mem_eq_false_of_value_not_int hd (by intro i h; cases h)]
              simp [DomC.mem]
      | bool b =>
          cases v <;> simp [DomC.remove, DomC.mem]
      | setOfInt s =>
          cases v <;> simp [DomC.remove, DomC.mem]
      | array a =>
          cases v <;> simp [DomC.remove, DomC.mem]
  | bitset lo words =>
      cases w with
      | int r =>
          rw [DomC.remove.eq_3]
          cases v with
          | int x =>
              by_cases hr : r - lo < 0
              · rw [if_pos hr]
                simp only [DomC.mem, Value.int.injEq, ne_eq]
                constructor
                · intro hm
                  refine ⟨hm, ?_⟩
                  have hxlo : lo ≤ x := by
                    by_cases h : lo ≤ x
                    · exact h
                    · have hlt : x - lo < 0 := by omega
                      rw [if_pos hlt] at hm
                      cases hm
                  omega
                · rintro ⟨hm, -⟩
                  simpa using hm
              · rw [if_neg hr]
                dsimp only
                cases hw : words[(r - lo).toNat / 64]? with
                | none =>
                    dsimp only
                    simp only [DomC.mem, Value.int.injEq, ne_eq]
                    constructor
                    · intro hm
                      refine ⟨hm, ?_⟩
                      intro hxr
                      rw [hxr] at hm
                      rw [if_neg hr, bitsetMem_eq_false_of_getElem?_none hw] at hm
                      cases hm
                    · rintro ⟨hm, -⟩
                      exact hm
                | some word =>
                    dsimp only
                    have hwi : (r - lo).toNat / 64 < words.size := by
                      obtain ⟨hlt, -⟩ := Array.getElem?_eq_some_iff.mp hw
                      exact hlt
                    by_cases hx : x - lo < 0
                    · simp only [DomC.mem, if_pos hx]
                      constructor
                      · intro h; cases h
                      · rintro ⟨h, -⟩; cases h
                    · simp only [DomC.mem, if_neg hx]
                      have hxr : ((x - lo).toNat = (r - lo).toNat) ↔ x = r := by
                        constructor
                        · intro h
                          have h' := congrArg (fun k : Nat => (k : Int)) h
                          rw [Int.toNat_of_nonneg (by omega : (0:Int) ≤ x - lo),
                            Int.toNat_of_nonneg (by omega : (0:Int) ≤ r - lo)] at h'
                          omega
                        · intro h
                          rw [h]
                      by_cases hm : (x - lo).toNat / 64 = (r - lo).toNat / 64
                      · rw [bitset_set!_mem_iff words hwi hw hm]
                        have hmod : (x - lo).toNat % 64 ≠ (r - lo).toNat % 64 ↔ x ≠ r := by
                          rw [mod_ne_iff_ne_of_div_eq hm rfl]
                          exact not_congr hxr
                        simp only [Value.int.injEq, ne_eq, hmod]
                      · rw [bitsetMem_set! hwi, if_neg hm]
                        simp only [Value.int.injEq, ne_eq]
                        constructor
                        · intro hb
                          exact ⟨hb, by intro hxr; apply hm; rw [hxr]⟩
                        · rintro ⟨hb, -⟩
                          exact hb
          | bool b =>
              by_cases hr : r - lo < 0
              · rw [if_pos hr]; simp [DomC.mem]
              · rw [if_neg hr]
                dsimp only
                cases hw : words[(r - lo).toNat / 64]? with
                | none => simp [hw, DomC.mem]
                | some word => simp [hw, DomC.mem]
          | setOfInt s =>
              by_cases hr : r - lo < 0
              · rw [if_pos hr]; simp [DomC.mem]
              · rw [if_neg hr]
                dsimp only
                cases hw : words[(r - lo).toNat / 64]? with
                | none => simp [hw, DomC.mem]
                | some word => simp [hw, DomC.mem]
          | array a =>
              by_cases hr : r - lo < 0
              · rw [if_pos hr]; simp [DomC.mem]
              · rw [if_neg hr]
                dsimp only
                cases hw : words[(r - lo).toNat / 64]? with
                | none => simp [hw, DomC.mem]
                | some word => simp [hw, DomC.mem]
      | bool b =>
          cases v <;> simp [DomC.remove, DomC.mem]
      | setOfInt s =>
          cases v <;> simp [DomC.remove, DomC.mem]
      | array a =>
          cases v <;> simp [DomC.remove, DomC.mem]
  | boundsHoles lo hi holes =>
      simp only [DomC.WF] at hWF
      obtain ⟨hpair, hrange⟩ := hWF
      cases w with
      | int r =>
          have hd : ∀ bits, (DomC.boundsHoles lo hi holes).remove (.int r) ≠ DomC.bool bits := by
            intro bits
            rw [DomC.remove.eq_4]
            grind
          cases v with
          | int x =>
              rw [DomC.remove.eq_4]
              by_cases hout : r < lo ∨ hi < r
              · rw [if_pos (by simp [hout])]
                rw [boundsHoles_mem_int_iff]
                simp only [Value.int.injEq, ne_eq]
                constructor
                · rintro ⟨h1, h2, hnot⟩
                  exact ⟨⟨h1, h2, hnot⟩, by rintro rfl; rcases hout with h | h <;> omega⟩
                · rintro ⟨⟨h1, h2, hnot⟩, -⟩
                  exact ⟨h1, h2, hnot⟩
              · rw [if_neg (by simp [hout])]
                by_cases hmem : memHoleRange holes r = true
                · rw [if_pos hmem]
                  rw [boundsHoles_mem_int_iff]
                  simp only [Value.int.injEq, ne_eq]
                  constructor
                  · rintro ⟨h1, h2, hnot⟩
                    refine ⟨⟨h1, h2, hnot⟩, ?_⟩
                    rintro rfl
                    rw [hmem] at hnot
                    cases hnot
                  · rintro ⟨⟨h1, h2, hnot⟩, -⟩
                    exact ⟨h1, h2, hnot⟩
                · rw [if_neg hmem]
                  by_cases hlo : r = lo
                  · rw [if_pos (by simp [hlo])]
                    rw [boundsHoles_mem_int_iff, boundsHoles_mem_int_iff]
                    simp only [Value.int.injEq, ne_eq]
                    subst hlo
                    constructor
                    · rintro ⟨h1, h2, hnot⟩
                      exact ⟨⟨by omega, h2, hnot⟩, by omega⟩
                    · rintro ⟨⟨h1, h2, hnot⟩, hne⟩
                      exact ⟨by omega, h2, hnot⟩
                  · rw [if_neg (by simp [hlo])]
                    by_cases hhi : r = hi
                    · rw [if_pos (by simp [hhi])]
                      rw [boundsHoles_mem_int_iff, boundsHoles_mem_int_iff]
                      simp only [Value.int.injEq, ne_eq]
                      subst hhi
                      constructor
                      · rintro ⟨h1, h2, hnot⟩
                        exact ⟨⟨h1, by omega, hnot⟩, by omega⟩
                      · rintro ⟨⟨h1, h2, hnot⟩, hne⟩
                        exact ⟨h1, by omega, hnot⟩
                    · rw [if_neg (by simp [hhi])]
                      rw [boundsHoles_mem_int_iff, boundsHoles_mem_int_iff]
                      have hins : memHoleRange (insertHole holes r) x = false ↔
                          memHoleRange holes x = false ∧ x ≠ r := by
                        have hpair' := pairwise_insertHole (holes := holes) (v := r) hpair
                        rw [memHoleRange_eq_false_iff hpair', memHoleRange_eq_false_iff hpair]
                        rw [mem_insertHole]
                        constructor
                        · intro h
                          exact ⟨by intro hx; exact h (Or.inr hx),
                            by intro hxr; exact h (Or.inl hxr)⟩
                        · rintro ⟨hh, hne⟩ hmem
                          rcases hmem with hxr | hx
                          · exact hne hxr
                          · exact hh hx
                      rw [hins]
                      simp only [Value.int.injEq, ne_eq]
                      constructor
                      · rintro ⟨h1, h2, hnot, hne⟩
                        exact ⟨⟨h1, h2, hnot⟩, hne⟩
                      · rintro ⟨⟨h1, h2, hnot⟩, hne⟩
                        exact ⟨h1, h2, hnot, hne⟩
          | bool b =>
              rw [DomC.mem_eq_false_of_value_not_int hd (by intro i h; cases h)]
              simp [DomC.mem]
          | setOfInt s =>
              rw [DomC.mem_eq_false_of_value_not_int hd (by intro i h; cases h)]
              simp [DomC.mem]
          | array a =>
              rw [DomC.mem_eq_false_of_value_not_int hd (by intro i h; cases h)]
              simp [DomC.mem]
      | bool b =>
          cases v <;> simp [DomC.remove, DomC.mem]
      | setOfInt s =>
          cases v <;> simp [DomC.remove, DomC.mem]
      | array a =>
          cases v <;> simp [DomC.remove, DomC.mem]

theorem DomC.mem_removeIntView (d : DomC) (k : Int) (v : Value) (hWF : d.WF) :
    (d.removeIntView k).mem v = true ↔ d.mem v = true ∧ Value.intView v ≠ some k := by
  cases d with
  | bool bits =>
      simp only [DomC.removeIntView]
      by_cases h0 : (k == 0) = true
      · rw [if_pos h0]
        have hk0 : k = 0 := beq_iff_eq.mp h0
        subst hk0
        rw [DomC.mem_remove (.bool bits) (.bool false) v hWF]
        constructor
        · rintro ⟨hm, hv⟩
          refine ⟨hm, ?_⟩
          cases v with
          | bool b =>
              cases b
              · exact absurd rfl hv
              · simp [Value.intView]
          | int i => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
        · rintro ⟨hm, hiv⟩
          refine ⟨hm, ?_⟩
          cases v with
          | bool b =>
              cases b
              · simp [Value.intView] at hiv
              · simp
          | int i => simp [DomC.mem] at hm
          | setOfInt s => simp [DomC.mem] at hm
          | array a => simp [DomC.mem] at hm
      · rw [if_neg h0]
        by_cases h1 : (k == 1) = true
        · rw [if_pos h1]
          have hk1 : k = 1 := beq_iff_eq.mp h1
          subst hk1
          rw [DomC.mem_remove (.bool bits) (.bool true) v hWF]
          constructor
          · rintro ⟨hm, hv⟩
            refine ⟨hm, ?_⟩
            cases v with
            | bool b =>
              cases b
              · simp [Value.intView]
              · exact absurd rfl hv
            | int i => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
          · rintro ⟨hm, hiv⟩
            refine ⟨hm, ?_⟩
            cases v with
            | bool b =>
                cases b
                · simp
                · simp [Value.intView] at hiv
            | int i => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
        · rw [if_neg h1]
          have hk0 : k ≠ 0 := by
            intro h; exact h0 (by rw [h]; rfl)
          have hk1 : k ≠ 1 := by
            intro h; exact h1 (by rw [h]; rfl)
          constructor
          · intro hm
            refine ⟨hm, ?_⟩
            cases v with
            | bool b =>
                cases b <;> simp [Value.intView] <;> omega
            | int i => simp [DomC.mem] at hm
            | setOfInt s => simp [DomC.mem] at hm
            | array a => simp [DomC.mem] at hm
          · rintro ⟨hm, hiv⟩
            exact hm
  | bounds lo hi =>
      simp only [DomC.removeIntView]
      rw [DomC.mem_remove (DomC.bounds lo hi) (.int k) v hWF]
      constructor
      · rintro ⟨hm, hv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            intro hik
            have hik' : i = k := by simpa [Value.intView] using hik
            exact hv (by rw [hik'])
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
      · rintro ⟨hm, hiv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            intro hik
            exact hiv (by simpa [Value.intView] using congrArg Value.intView hik)
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
  | bitset lo words =>
      simp only [DomC.removeIntView]
      rw [DomC.mem_remove (DomC.bitset lo words) (.int k) v hWF]
      constructor
      · rintro ⟨hm, hv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            intro hik
            have hik' : i = k := by simpa [Value.intView] using hik
            exact hv (by rw [hik'])
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
      · rintro ⟨hm, hiv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            intro hik
            exact hiv (by simpa [Value.intView] using congrArg Value.intView hik)
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
  | boundsHoles lo hi holes =>
      simp only [DomC.removeIntView]
      rw [DomC.mem_remove (DomC.boundsHoles lo hi holes) (.int k) v hWF]
      constructor
      · rintro ⟨hm, hv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            intro hik
            have hik' : i = k := by simpa [Value.intView] using hik
            exact hv (by rw [hik'])
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm
      · rintro ⟨hm, hiv⟩
        refine ⟨hm, ?_⟩
        cases v with
        | int i =>
            intro hik
            exact hiv (by simpa [Value.intView] using congrArg Value.intView hik)
        | bool b => simp [DomC.mem] at hm
        | setOfInt s => simp [DomC.mem] at hm
        | array a => simp [DomC.mem] at hm

/-! ### Emptiness -/

theorem DomC.isEmpty_sound (d : DomC) (h : d.isEmpty = true) (v : Value) :
    d.mem v = false := by
  cases d with
  | bool bits =>
      rw [DomC.isEmpty.eq_1] at h
      have h3 : bits &&& 3 = 0 := beq_iff_eq.mp h
      cases v with
      | bool b =>
          cases b
          · have h1 : bits &&& 1 = 0 := by
              rw [← uint8_and_three_and_one bits, h3, UInt8.zero_and]
            simp [DomC.mem, h1]
          · have h2 : bits &&& 2 = 0 := by
              rw [← uint8_and_three_and_two bits, h3, UInt8.zero_and]
            simp [DomC.mem, h2]
      | int i => simp [DomC.mem]
      | setOfInt s => simp [DomC.mem]
      | array a => simp [DomC.mem]
  | bounds lo hi =>
      rw [DomC.isEmpty.eq_2] at h
      have hlt : hi < lo := of_decide_eq_true h
      cases v with
      | int i =>
          simp only [DomC.mem]
          by_cases h1 : lo ≤ i
          · have h2 : ¬ i ≤ hi := by omega
            simp [h1, h2]
          · simp [h1]
      | bool b => simp [DomC.mem]
      | setOfInt s => simp [DomC.mem]
      | array a => simp [DomC.mem]
  | bitset lo words =>
      rw [DomC.isEmpty.eq_3] at h
      cases v with
      | int i =>
          simp only [DomC.mem]
          by_cases hx : i - lo < 0
          · simp [hx]
          · simp [hx, bitsetMem_all_zero words (i - lo).toNat h]
      | bool b => simp [DomC.mem]
      | setOfInt s => simp [DomC.mem]
      | array a => simp [DomC.mem]
  | boundsHoles lo hi holes =>
      rw [DomC.isEmpty.eq_4] at h
      have hlt : hi < lo := of_decide_eq_true h
      cases v with
      | int i =>
          simp only [DomC.mem]
          by_cases h1 : lo ≤ i
          · have h2 : ¬ i ≤ hi := by omega
            simp [h1, h2]
          · simp [h1]
      | bool b => simp [DomC.mem]
      | setOfInt s => simp [DomC.mem]
      | array a => simp [DomC.mem]

/-! ### Pointwise `valueHolds` characterisations -/

theorem valueHolds_intNe_pos_iff (s : Nat) (x : Int) (v : Value) :
    Literal.valueHolds ⟨.intNe s x, true⟩ v = true ↔
      ∃ i, Value.intView v = some i ∧ i ≠ x := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_intNe_pos_false_iff (s : Nat) (x : Int) (v : Value) :
    Literal.valueHolds ⟨.intNe s x, true⟩ v = false ↔
      ∀ i, Value.intView v = some i → i = x := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_intNe_neg_iff (s : Nat) (x : Int) (v : Value) :
    Literal.valueHolds ⟨.intNe s x, false⟩ v = true ↔
      Value.intView v = some x := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_intNe_neg_false_iff (s : Nat) (x : Int) (v : Value) :
    Literal.valueHolds ⟨.intNe s x, false⟩ v = false ↔
      Value.intView v ≠ some x := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_intLe_pos_iff (s : Nat) (k : Int) (v : Value) :
    Literal.valueHolds ⟨.intLe s k, true⟩ v = true ↔
      ∃ i, Value.intView v = some i ∧ i ≤ k := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_intLe_pos_false_iff (s : Nat) (k : Int) (v : Value) :
    Literal.valueHolds ⟨.intLe s k, true⟩ v = false ↔
      ∀ i, Value.intView v = some i → ¬ i ≤ k := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_intLe_neg_iff (s : Nat) (k : Int) (v : Value) :
    Literal.valueHolds ⟨.intLe s k, false⟩ v = true ↔
      ∃ i, Value.intView v = some i ∧ k < i := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_intLe_neg_false_iff (s : Nat) (k : Int) (v : Value) :
    Literal.valueHolds ⟨.intLe s k, false⟩ v = false ↔
      ∀ i, Value.intView v = some i → ¬ k < i := by
  cases v <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_boolEq_iff (s : Nat) (b : Bool) (pos : Bool) (v : Value) :
    Literal.valueHolds ⟨.boolEq s b, pos⟩ v = true ↔
      v = Value.bool (if pos then b else !b) := by
  cases v with
  | bool actual =>
      cases actual <;> cases pos <;> cases b <;> simp [Literal.valueHolds]
  | int i => cases pos <;> cases b <;> simp [Literal.valueHolds, Value.intView]
  | setOfInt s => cases pos <;> cases b <;> simp [Literal.valueHolds, Value.intView]
  | array a => cases pos <;> cases b <;> simp [Literal.valueHolds, Value.intView]

theorem valueHolds_boolEq_false_iff (s : Nat) (b : Bool) (pos : Bool) (v : Value) :
    Literal.valueHolds ⟨.boolEq s b, pos⟩ v = false ↔
      v ≠ Value.bool (if pos then b else !b) := by
  cases v with
  | bool actual =>
      cases actual <;> cases pos <;> cases b <;> simp [Literal.valueHolds]
  | int i => cases pos <;> cases b <;> simp [Literal.valueHolds, Value.intView]
  | setOfInt s => cases pos <;> cases b <;> simp [Literal.valueHolds, Value.intView]
  | array a => cases pos <;> cases b <;> simp [Literal.valueHolds, Value.intView]

theorem intView_eq_some_iv_of_mem {d : DomC} {v : Value} (hm : d.mem v = true) :
    Value.intView v = some (iv v) := by
  obtain ⟨i, hi⟩ := DomC.mem_intView_exists hm
  rw [hi, iv_of_intView hi]

theorem DomC.evalLit_true_sound (d : DomC) (l : Literal) (hWF : d.WF)
    (h : d.evalLit l = some true) :
    ∀ v, d.mem v = true → Literal.valueHolds l v = true := by
  intro v hm
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | intNe s x =>
      by_cases hfix : d.fixedValue.isSome = true
      · simp only [DomC.evalLit, if_pos hfix] at h
        have hval : (if pos = true then !(d.memIntView x) else d.memIntView x) = true :=
          Option.some.inj h
        cases pos
        · simp only [Bool.false_eq_true, if_false] at hval
          obtain ⟨w, hw⟩ := (DomC.fixedValue_isSome_iff_exists d).mp hfix
          obtain ⟨hmw, hall⟩ := DomC.fixedValue_sound d hWF hw
          obtain ⟨u, hu, hiv⟩ := (DomC.memIntView_eq_true_iff d x).mp hval
          rw [hall u hu] at hiv
          rw [hall v hm]
          rw [valueHolds_intNe_neg_iff]
          exact hiv
        · simp only [if_true] at hval
          have hx : d.memIntView x = false := by simpa using hval
          have hne := DomC.memIntView_false_of_mem hx hm
          rw [valueHolds_intNe_pos_iff]
          have hi : Value.intView v = some (iv v) := intView_eq_some_iv_of_mem hm
          exact ⟨iv v, hi, by intro hix; exact hne (by rw [hi, hix])⟩
      · simp only [DomC.evalLit, if_neg hfix] at h
        cases hmv : d.memIntView x
        · cases pos
          · simp [hmv] at h
          · have hx : d.memIntView x = false := hmv
            have hne := DomC.memIntView_false_of_mem hx hm
            rw [valueHolds_intNe_pos_iff]
            have hi : Value.intView v = some (iv v) := intView_eq_some_iv_of_mem hm
            exact ⟨iv v, hi, by intro hix; exact hne (by rw [hi, hix])⟩
        · cases pos <;> simp [hmv] at h
  | intLe s k =>
      cases hlo : d.lo? with
      | none => simp [DomC.evalLit, hlo] at h
      | some lo =>
          cases hhi : d.hi? with
          | none => simp [DomC.evalLit, hlo, hhi] at h
          | some hi =>
              simp only [DomC.evalLit, hlo, hhi] at h
              cases pos
              · simp only [Bool.false_eq_true, if_false] at h
                by_cases hk : lo > k
                · have hiv := intView_eq_some_iv_of_mem hm
                  rw [valueHolds_intLe_neg_iff]
                  refine ⟨iv v, hiv, ?_⟩
                  have := DomC.lo?_le d hWF hlo hm
                  omega
                · simp [hk] at h
              · simp only [if_true] at h
                by_cases hk : hi ≤ k
                · have hiv := intView_eq_some_iv_of_mem hm
                  rw [valueHolds_intLe_pos_iff]
                  refine ⟨iv v, hiv, ?_⟩
                  have := DomC.le_hi? d hWF hhi hm
                  omega
                · simp [hk] at h
  | boolEq s b =>
      cases hfv : d.fixedValue with
      | none => simp [DomC.evalLit, hfv] at h
      | some w =>
          cases w with
          | bool actual =>
              simp only [DomC.evalLit, hfv] at h
              have hval : (if pos = true then actual == b else actual != b) = true :=
                Option.some.inj h
              obtain ⟨hmw, hall⟩ := DomC.fixedValue_sound d hWF hfv
              have hvw : v = Value.bool actual := hall v hm
              rw [hvw]
              rw [valueHolds_boolEq_iff]
              cases pos
              · simp only [Bool.false_eq_true, if_false] at hval
                cases actual <;> cases b <;> simp_all
              · simp only [if_true] at hval
                cases actual <;> cases b <;> simp_all
          | int i => simp [DomC.evalLit, hfv] at h
          | setOfInt s => simp [DomC.evalLit, hfv] at h
          | array a => simp [DomC.evalLit, hfv] at h

theorem DomC.evalLit_false_sound (d : DomC) (l : Literal) (hWF : d.WF)
    (h : d.evalLit l = some false) :
    ∀ v, d.mem v = true → Literal.valueHolds l v = false := by
  intro v hm
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | intNe s x =>
      by_cases hfix : d.fixedValue.isSome = true
      · simp only [DomC.evalLit, if_pos hfix] at h
        have hval : (if pos = true then !(d.memIntView x) else d.memIntView x) = false :=
          Option.some.inj h
        cases pos
        · simp only [Bool.false_eq_true, if_false] at hval
          have hne := DomC.memIntView_false_of_mem hval hm
          rw [valueHolds_intNe_neg_false_iff]
          exact hne
        · simp only [if_true] at hval
          have hx : d.memIntView x = true := by simpa using hval
          obtain ⟨w, hw⟩ := (DomC.fixedValue_isSome_iff_exists d).mp hfix
          obtain ⟨hmw, hall⟩ := DomC.fixedValue_sound d hWF hw
          obtain ⟨u, hu, hiv⟩ := (DomC.memIntView_eq_true_iff d x).mp hx
          rw [hall u hu] at hiv
          rw [hall v hm]
          rw [valueHolds_intNe_pos_false_iff]
          intro i hi
          rw [hiv] at hi
          exact (Option.some.inj hi).symm
      · simp only [DomC.evalLit, if_neg hfix] at h
        cases hmv : d.memIntView x
        · cases pos
          · have hne := DomC.memIntView_false_of_mem hmv hm
            rw [valueHolds_intNe_neg_false_iff]
            exact hne
          · simp [hmv] at h
        · cases pos <;> simp [hmv] at h
  | intLe s k =>
      cases hlo : d.lo? with
      | none => simp [DomC.evalLit, hlo] at h
      | some lo =>
          cases hhi : d.hi? with
          | none => simp [DomC.evalLit, hlo, hhi] at h
          | some hi =>
              simp only [DomC.evalLit, hlo, hhi] at h
              cases pos
              · simp only [Bool.false_eq_true, if_false] at h
                by_cases hk : lo > k
                · simp [hk] at h
                · by_cases hk2 : hi ≤ k
                  · have hiv := intView_eq_some_iv_of_mem hm
                    rw [valueHolds_intLe_neg_false_iff]
                    intro i hi'
                    have hii : i = iv v := (iv_of_intView hi').symm
                    rw [hii]
                    have := DomC.le_hi? d hWF hhi hm
                    omega
                  · simp [hk, hk2] at h
              · simp only [if_true] at h
                by_cases hk : hi ≤ k
                · simp [hk] at h
                · by_cases hk2 : lo > k
                  · have hiv := intView_eq_some_iv_of_mem hm
                    rw [valueHolds_intLe_pos_false_iff]
                    intro i hi'
                    have hii : i = iv v := (iv_of_intView hi').symm
                    rw [hii]
                    have := DomC.lo?_le d hWF hlo hm
                    omega
                  · simp [hk, hk2] at h
  | boolEq s b =>
      cases hfv : d.fixedValue with
      | none => simp [DomC.evalLit, hfv] at h
      | some w =>
          cases w with
          | bool actual =>
              simp only [DomC.evalLit, hfv] at h
              have hval : (if pos = true then actual == b else actual != b) = false :=
                Option.some.inj h
              obtain ⟨hmw, hall⟩ := DomC.fixedValue_sound d hWF hfv
              have hvw : v = Value.bool actual := hall v hm
              rw [hvw, valueHolds_boolEq_false_iff]
              cases pos
              · simp only [Bool.false_eq_true, if_false] at hval
                cases actual <;> cases b <;> simp_all
              · simp only [if_true] at hval
                cases actual <;> cases b <;> simp_all
          | int i => simp [DomC.evalLit, hfv] at h
          | setOfInt s => simp [DomC.evalLit, hfv] at h
          | array a => simp [DomC.evalLit, hfv] at h

theorem DomC.mem_applyLit (d : DomC) (l : Literal) (hWF : d.WF) (v : Value) :
    (d.applyLit l).mem v = true ↔ d.mem v = true ∧ Literal.valueHolds l v = true := by
  obtain ⟨atom, pos⟩ := l
  cases atom with
  | intNe s x =>
      cases pos
      · simp only [DomC.applyLit, Bool.false_eq_true, if_true, if_false]
        rw [DomC.mem_fixIntView d x v hWF, valueHolds_intNe_neg_iff]
      · simp only [DomC.applyLit, Bool.false_eq_true, if_true, if_false]
        rw [DomC.mem_removeIntView d x v hWF, valueHolds_intNe_pos_iff]
        constructor
        · rintro ⟨hm, hne⟩
          refine ⟨hm, ?_⟩
          have hi : Value.intView v = some (iv v) := intView_eq_some_iv_of_mem hm
          exact ⟨iv v, hi, by intro hix; exact hne (by rw [hi, hix])⟩
        · rintro ⟨hm, hix⟩
          refine ⟨hm, ?_⟩
          obtain ⟨i, hi', hne⟩ := hix
          intro hsome
          rw [hsome] at hi'
          exact hne (Option.some.inj hi').symm
  | intLe s k =>
      cases pos
      · simp only [DomC.applyLit, Bool.false_eq_true, if_true, if_false]
        rw [DomC.mem_setGe d (k + 1) hWF v, valueHolds_intLe_neg_iff]
        constructor
        · rintro ⟨hm, i, hi, hik⟩
          exact ⟨hm, i, hi, by omega⟩
        · rintro ⟨hm, i, hi, hik⟩
          exact ⟨hm, i, hi, by omega⟩
      · simp only [DomC.applyLit, Bool.false_eq_true, if_true, if_false]
        rw [DomC.mem_setLe d k hWF v, valueHolds_intLe_pos_iff]
  | boolEq s b =>
      cases pos
      · simp only [DomC.applyLit, Bool.false_eq_true, if_true, if_false]
        rw [DomC.mem_fix d (.bool (!b)) v hWF, valueHolds_boolEq_iff]
        simp
      · simp only [DomC.applyLit, Bool.false_eq_true, if_true, if_false]
        rw [DomC.mem_fix d (.bool b) v hWF, valueHolds_boolEq_iff]
        simp

theorem valueHolds_eq_map_beq (atom : Atom) (pos : Bool) (v : Value) :
    Literal.valueHolds ⟨atom, pos⟩ v =
      ((Atom.evalAtValue atom v).map (fun x => if pos then x else !x) == some true) := by
  cases atom <;> cases v <;> cases pos <;>
    simp [Atom.evalAtValue, Literal.valueHolds, Value.intView]

theorem Literal.eval_eq_valueHolds (l : Literal) (a : LeanFzn.Solver.Core.Assignment) {v : Value}
    (hslot : a[l.atom.slot]? = some v) :
    l.eval a = some true ↔ l.valueHolds v = true := by
  obtain ⟨atom, pos⟩ := l
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hslot
  rw [Literal.eval, Atom.eval_eq_evalAtValue atom a hlt, hget, valueHolds_eq_map_beq]
  simp

theorem Literal.eval_eq_valueHolds_false (l : Literal) (a : LeanFzn.Solver.Core.Assignment) {v : Value}
    (hslot : a[l.atom.slot]? = some v)
    (hdef : l.atom.evalAtValue v ≠ none) :
    l.eval a = some false ↔ l.valueHolds v = false := by
  obtain ⟨atom, pos⟩ := l
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp hslot
  rw [Literal.eval, Atom.eval_eq_evalAtValue atom a hlt, hget, valueHolds_eq_map_beq]
  have hdef' : Atom.evalAtValue atom v ≠ none := hdef
  cases h : Atom.evalAtValue atom v with
  | none => exact absurd h hdef'
  | some x => cases x <;> simp [h]


/-! ### `applyLit` after a definite evaluation -/

/-- If `evalLit` already decided the literal as true, applying it does not
change membership: the literal holds on every value of the domain. -/
theorem DomC.mem_applyLit_of_evalLit_true (d : DomC) (l : Literal) (hWF : d.WF)
    (h : d.evalLit l = some true) (v : Value) :
    (d.applyLit l).mem v = true ↔ d.mem v = true := by
  rw [DomC.mem_applyLit d l hWF v]
  constructor
  · rintro ⟨hm, _⟩
    exact hm
  · intro hm
    exact ⟨hm, DomC.evalLit_true_sound d l hWF h v hm⟩

/-- Applying the same literal twice does not change membership. -/
theorem DomC.mem_applyLit_applyLit (d : DomC) (l : Literal) (hWF : d.WF) (v : Value) :
    ((d.applyLit l).applyLit l).mem v = true ↔ (d.applyLit l).mem v = true := by
  rw [DomC.mem_applyLit (d.applyLit l) l (DomC.applyLit_WF d l hWF) v,
    DomC.mem_applyLit d l hWF v]
  constructor
  · rintro ⟨⟨hm, hv⟩, _⟩
    exact ⟨hm, hv⟩
  · rintro ⟨hm, hv⟩
    exact ⟨⟨hm, hv⟩, hv⟩

end LeanFzn.Engine
