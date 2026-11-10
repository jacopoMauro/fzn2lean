/-
File: LeanFzn/Engine/Bits.lean

Machine-word bit helpers for the Core engine: the low/high set-bit scans and
their native fast twins.

The scans `lowestBit`/`highestBit` are the logical models used in proofs.
They walk at most 64 single-bit masks.  `lowestBitFast`/`highestBitFast`
compute the same results with `UInt64.log2` (a native count-leading-zeros)
and the two's-complement low-bit mask `w &&& -w`; the `@[csimp]` theorems at
the bottom of this file install them as the compiled implementations.

The specifications `lowestBit_spec`/`highestBit_spec` are stated against the
logical scans, so every downstream proof keeps using the simple 64-step
characterisation.

Dependencies: core Lean only (`UInt64.log2`, `Nat.testBit`).
-/
import Init.Data.UInt.Log2
import Init.Data.Nat.Bitwise.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Div.Basic

namespace LeanFzn.Engine

/-! ## Set-bit scans -/

/-- The one-bit mask at position `k % 64`. -/
def u64bit (k : Nat) : UInt64 := (1 : UInt64) <<< (UInt64.ofNat (k % 64))

/-- Lowest set bit of a nonzero word.  Uses a 64-bit mask rather than a
    `Nat.testBit` conversion so the bitset endpoints stay on machine words. -/
def lowestBit (w : UInt64) : Nat :=
  let rec go (k : Nat) : Nat :=
    if k < 64 then
      if w &&& u64bit k != 0 then k else go (k + 1)
    else 0
  termination_by 64 - k
  if w == 0 then 0 else go 0

/-- Highest set bit of a nonzero word (64-bit masks, no `Nat.testBit`). -/
def highestBit (w : UInt64) : Nat :=
  let rec go (k : Nat) : Nat :=
    if k < 64 then
      if w &&& u64bit (63 - k) != 0 then 63 - k else go (k + 1)
    else 0
  termination_by 64 - k
  if w == 0 then 0 else go 0


/-! ## Bit lemmas -/

theorem nat_and_two_pow_ne_zero {n k : Nat} :
    n &&& 2 ^ k ≠ 0 ↔ n.testBit k = true := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := Nat.exists_testBit_of_ne_zero h
    rw [Nat.testBit_and, Nat.testBit_two_pow] at hi
    by_cases hik : k = i
    · subst hik
      simpa using hi
    · simp [hik] at hi
  · intro h hz
    have hfalse : Nat.testBit (n &&& 2 ^ k) k = false := by rw [hz, Nat.zero_testBit]
    rw [Nat.testBit_and, Nat.testBit_two_pow] at hfalse
    simp [h] at hfalse

theorem uint64_ne_zero_iff_toNat_ne_zero (x : UInt64) : x ≠ 0 ↔ x.toNat ≠ 0 := by
  constructor
  · intro h hz
    exact h (UInt64.toNat_inj.mp (by simpa using hz))
  · intro h hz
    exact h (by rw [hz]; rfl)

/-- The one-bit mask `u64bit k` has Nat value `2^k` for a position `k < 64`. -/
theorem u64bit_toNat {k : Nat} (hk : k < 64) : (u64bit k).toNat = 2 ^ k := by
  unfold u64bit
  rw [UInt64.toNat_shiftLeft, UInt64.toNat_one]
  have hkmod : k % 64 = k := Nat.mod_eq_of_lt hk
  have hof : (UInt64.ofNat (k % 64)).toNat = k := by
    rw [UInt64.toNat_ofNat', hkmod, Nat.mod_eq_of_lt]
    omega
  rw [hof, hkmod, Nat.one_shiftLeft]
  rw [Nat.mod_eq_of_lt]
  exact Nat.pow_lt_pow_right (by decide : 1 < 2) hk

theorem uint64_and_u64bit_ne_zero_iff (x : UInt64) {k : Nat} (hk : k < 64) :
    (x &&& u64bit k) != 0 ↔ x.toNat.testBit k = true := by
  rw [bne_iff_ne, uint64_ne_zero_iff_toNat_ne_zero, UInt64.toNat_and,
    u64bit_toNat hk]
  exact nat_and_two_pow_ne_zero


/-! ## Specifications of the logical scans -/

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


/-! ## Native fast twins -/

@[inline] def highestBitFast (w : UInt64) : Nat :=
  (UInt64.log2 w).toNat

@[inline] def lowestBitFast (w : UInt64) : Nat :=
  if w == 0 then 0 else (UInt64.log2 (w &&& (-w))).toNat

private theorem testBit_two_pow_lt (k j : Nat) (h : j < k) :
    (2 ^ k).testBit j = false := by
  rw [Nat.testBit_two_pow]
  simp [show k ≠ j by omega]

theorem highestBitFast_eq (w : UInt64) : highestBit w = highestBitFast w := by
  by_cases hw : w = 0
  · subst hw
    have hlog : (UInt64.log2 0).toNat = 0 := by decide
    simp [highestBit, highestBitFast, hlog]
  · unfold highestBitFast
    have hspec := highestBit_spec (w := w) hw
    obtain ⟨hlt, hbit, hmax⟩ := hspec
    rw [show (UInt64.log2 w).toNat = Nat.log2 w.toNat from rfl]
    refine ((Nat.log2_eq_iff (n := w.toNat) (k := highestBit w) (by
      exact (uint64_ne_zero_iff_toNat_ne_zero w).mp hw)).mpr ?_).symm
    constructor
    · exact Nat.ge_two_pow_of_testBit hbit
    · refine Nat.lt_pow_two_of_testBit w.toNat (n := highestBit w + 1) ?_
      intro i hi
      by_cases hi64 : i < 64
      · cases h : w.toNat.testBit i with
        | false => rfl
        | true =>
            have := hmax i hi64 h
            omega
      · have hnlt : w.toNat < 2 ^ i := by
          have hle : 64 ≤ i := by omega
          exact Nat.lt_of_lt_of_le (UInt64.toNat_lt_size w)
            (Nat.pow_le_pow_right (n := 2) (by decide) hle)
        exact Nat.testBit_lt_two_pow hnlt

/-- The low-bit mask `w &&& -w` is `2 ^ lowestBit w` in `Nat`. -/
theorem lowestBitFast_eq (w : UInt64) : lowestBit w = lowestBitFast w := by
  by_cases hw : w = 0
  · subst hw
    simp [lowestBit, lowestBitFast]
  · unfold lowestBitFast
    rw [if_neg (by simp [hw])]
    rw [show (UInt64.log2 (w &&& -w)).toNat = Nat.log2 (w &&& -w).toNat from rfl]
    have hspec := lowestBit_spec (w := w) hw
    obtain ⟨hlt, hbit, hmin⟩ := hspec
    let n := w.toNat
    let lb := lowestBit w
    have hbit' : n.testBit lb = true := hbit
    have hmin' : ∀ j, j < 64 → n.testBit j = true → lb ≤ j := hmin
    have hn0 : 0 < n := Nat.pos_of_ne_zero ((uint64_ne_zero_iff_toNat_ne_zero w).mp hw)
    have hnlt : n < 2 ^ 64 := by simpa [n] using UInt64.toNat_lt_size w
    have hneg : (-w).toNat = 2 ^ 64 - n := by
      rw [UInt64.toNat_neg]
      have hsize : UInt64.size = 2 ^ 64 := rfl
      rw [hsize, Nat.mod_eq_of_lt]
      omega
    have hmtoNat : (w &&& (-w)).toNat = n &&& (2 ^ 64 - n) := by
      rw [UInt64.toNat_and, hneg]
    -- The low `lb+1` bits of `n` are `2 ^ lb`.
    have hmask : n &&& (2 ^ (lb + 1) - 1) = 2 ^ lb := by
      apply Nat.eq_of_testBit_eq
      intro j
      rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_two_pow]
      by_cases hj : j < lb
      · have hnj : n.testBit j = false := by
          cases h : n.testBit j with
          | false => rfl
          | true =>
              have := hmin' j (by omega) h
              omega
        simp [hj, hnj, show ¬ lb = j by omega]
      · by_cases hje : j = lb
        · subst hje
          simp [hbit']
        · have hjlb : ¬ j < lb + 1 := by omega
          have hjl : ¬ lb = j := by omega
          simp [hjlb, hjl]
    have hmod : n % 2 ^ (lb + 1) = 2 ^ lb := by
      rw [← Nat.and_two_pow_sub_one_eq_mod]
      exact hmask
    let A := 2 ^ (lb + 1) * (n / 2 ^ (lb + 1))
    have hn_eq : n = A + 2 ^ lb := by
      have h := Nat.div_add_mod n (2 ^ (lb + 1))
      rw [hmod] at h
      exact h.symm
    have hn1_eq : n - 1 = A + (2 ^ lb - 1) := by
      have ht : 1 ≤ 2 ^ lb := Nat.one_le_two_pow
      omega
    -- Bits of `n` and `n - 1` above `lb`.
    have hbits_n : ∀ j, n.testBit j =
        if j < lb + 1 then (2 ^ lb).testBit j
        else (n / 2 ^ (lb + 1)).testBit (j - (lb + 1)) := by
      intro j
      have h := Nat.testBit_two_pow_mul_add (n / 2 ^ (lb + 1))
        (b := 2 ^ lb) (i := lb + 1) (by rw [Nat.pow_succ]; omega) j
      calc n.testBit j = (A + 2 ^ lb).testBit j := by rw [hn_eq]
        _ = _ := h
    have hbits_n1 : ∀ j, (n - 1).testBit j =
        if j < lb + 1 then (2 ^ lb - 1).testBit j
        else (n / 2 ^ (lb + 1)).testBit (j - (lb + 1)) := by
      intro j
      have h := Nat.testBit_two_pow_mul_add (n / 2 ^ (lb + 1))
        (b := 2 ^ lb - 1) (i := lb + 1) (by rw [Nat.pow_succ]; omega) j
      calc (n - 1).testBit j = (A + (2 ^ lb - 1)).testBit j := by rw [hn1_eq]
        _ = _ := h
    -- Pointwise description of the low-bit mask below the 64-bit cut.
    have hbit_m : ∀ j, j < 64 → (w &&& -w).toNat.testBit j =
        (n.testBit j && !(n - 1).testBit j) := by
      intro j hj
      rw [hmtoNat, Nat.testBit_and]
      have hsub : (2 ^ 64 - n).testBit j = !(n - 1).testBit j := by
        have hpred : n - 1 < 2 ^ 64 := by omega
        have h := Nat.testBit_two_pow_sub_succ (n := 64) (x := n - 1) hpred j
        have hsucc : n - 1 + 1 = n := Nat.sub_one_add_one_eq_of_pos hn0
        rw [hsucc] at h
        rw [h]
        simp [hj]
      rw [hsub]
    have hbit_lb : (w &&& -w).toNat.testBit lb = true := by
      rw [hbit_m lb hlt]
      rw [hbits_n lb, hbits_n1 lb]
      simp [hbit']
    have hbit_high : ∀ j, lb + 1 ≤ j → (w &&& -w).toNat.testBit j = false := by
      intro j hj
      by_cases hj64 : j < 64
      · rw [hbit_m j hj64, hbits_n j, hbits_n1 j]
        have hnot : ¬ j < lb + 1 := by omega
        rw [if_neg hnot, if_neg hnot]
        cases h : (n / 2 ^ (lb + 1)).testBit (j - (lb + 1)) <;> simp
      · rw [hmtoNat]
        apply Nat.testBit_lt_two_pow
        have hlt64 : n &&& (2 ^ 64 - n) < 2 ^ 64 :=
          Nat.and_lt_two_pow n (by omega)
        exact Nat.lt_of_lt_of_le hlt64 (Nat.pow_le_pow_right (n := 2) (by decide) (by omega))
    have hm0 : (w &&& -w).toNat ≠ 0 := by
      intro hz
      rw [hz] at hbit_lb
      simp at hbit_lb
    refine ((Nat.log2_eq_iff (n := (w &&& -w).toNat) (k := lb) hm0).mpr ?_).symm
    exact ⟨Nat.ge_two_pow_of_testBit hbit_lb,
      Nat.lt_pow_two_of_testBit (w &&& -w).toNat (n := lb + 1)
        (fun j hj => hbit_high j hj)⟩

@[csimp] theorem lowestBit_eq_fast : @lowestBit = @lowestBitFast := by
  funext w
  exact lowestBitFast_eq w

@[csimp] theorem highestBit_eq_fast : @highestBit = @highestBitFast := by
  funext w
  exact highestBitFast_eq w


end LeanFzn.Engine
