/-
File: solver/LCG/Proofs/Fam/Times.lean

Purpose:
  The `timesSlot i j k` (`int_times` style) bound propagator with its
  complete proof package, mirroring the arithmetic-family packages of
  Fam/Arith.lean (itself a mirror of Proofs/Propagators.lean and the
  nogood-true helpers of Proofs/Reason.lean). Nothing here edits the
  shared registration: the standalone packaging
  (`propagatorOfProvedBT` etc.) keeps this module self-contained.

Propagator (bounds `x ∈ [xi',xi]`, `y ∈ [yj',yj]`, `z ∈ [zk',zk]`;
`z = x·y` over slots `i j k`):

  * `propTimes` implements the two z-side corner deductions plus
    the eight operand-side SIGN deductions:
      - `z ≥ cornerMin xi' xi yj' yj`  (causes `x ≥ xi'`, `x ≤ xi`,
        `y ≥ yj'`, `y ≤ yj`);
      - `z ≤ cornerMax xi' xi yj' yj`  (same four causes);
      - `x ≥ 0` when `0 < yj'` and `0 ≤ zk'`;
      - `x ≤ 0` when `0 < yj'` and `zk ≤ 0`;
      - `x ≤ 0` when `yj < 0` and `0 ≤ zk'`;
      - `x ≥ 0` when `yj < 0` and `zk ≤ 0`;
      - the four y-side duals (reading `x`'s extrema for the guard).
    The product of the intervals `[xi',xi] × [yj',yj]` has its
    minimum at `cornerMin` and maximum at `cornerMax`, the four
    corner products (the domain-level reference is
    `propTimesBounded`'s corner arithmetic, solver/Propagators.lean;
    the definitions here match that reference's shape). Because the
    product is not monotone, the whole interval pin is needed: each
    nogood is a FIVE-literal clause with FOUR causes.

  Nogoods (each integer-valid under `x·y = z`):
      - `[z > m−1, x < xi', x > xi, y < yj', y > yj]`
        = `[negLe k (m−1), posLe i (xi'−1), negLe i xi,
           posLe j (yj'−1), negLe j yj]` with `m = cornerMin`;
      - `[z ≤ M, x < xi', x > xi, y < yj', y > yj]`
        = `[posLe k M, posLe i (xi'−1), negLe i xi,
           posLe j (yj'−1), negLe j yj]` with `M = cornerMax`.
    Validity: any `x ∈ [xi',xi]`, `y ∈ [yj',yj]` has
    `m ≤ x·y ≤ M` (the interval product's extremes are at corners);
    `z < m` or `z > M` while `x`, `y` in range contradicts `z = x·y`.

  There is deliberately no conflict arm: `narrowLo`/`narrowHi` report
  their own conflicts when the z-domain is disjoint from `[m, M]`
  (exactly `propPlus`'s shape — a conflict fires when the z-domain
  lies entirely on the wrong side of a deduced bound).

Verification: `timeout 700 env LEAN_NUM_THREADS=4 lake env lean
solver/LCG/Proofs/Fam/Times.lean` — zero errors.

Dependencies:
  - solver.LCG.Proofs.ConstFamilies: the shared narrow inversions,
    coherence bridges, normalization facts.
  - solver.LCG.Proofs.Theory: the narrow conflict inversions.
  - solver.LCG.Propagate: State, narrowLo/narrowHi, firstEvent,
    domMinI/domMaxI.
  - solver.LCG.Encoding: literal evaluation bridges.
  - solver.Domain: not needed beyond what the above re-export.

DAG:
  LCG.Proofs.Theory + LCG.Proofs.ConstFamilies + LCG.Propagate
    -> LCG.Proofs.Fam.Times (this module)
-/


import solver.LCG.Proofs.ConstFamilies
import solver.LCG.Proofs.Theory
import solver.LCG.Propagate
import solver.LCG.Encoding

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (DomConstraint)

/-! ## Shared corner helpers

The four-corner product bounds of two intervals — local twins of the
domain-level `cornerMin`/`cornerMax` of `propTimesBounded`
(solver/Propagators.lean), in the same shape. -/

/-- The four-corner lower product bound of the intervals `[a, b]` and
    `[c, d]`. -/
def cornerMin (a b c d : Int) : Int :=
  min (min (a * c) (a * d)) (min (b * c) (b * d))

/-- The four-corner upper product bound of the intervals `[a, b]` and
    `[c, d]`. -/
def cornerMax (a b c d : Int) : Int :=
  max (max (a * c) (a * d)) (max (b * c) (b * d))

/-- Two values in `[a, b] × [c, d]` have a product at least the
    smallest corner product (the interval product's minimum is at a
    corner). -/
theorem times_cornerMin_le {a b c d x y : Int}
    (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    cornerMin a b c d ≤ x * y := by
  unfold cornerMin
  have Ha : min (a * c) (a * d) ≤ a * y := by
    by_cases ha : 0 ≤ a
    · have e : a * c ≤ a * y := Int.mul_le_mul_of_nonneg_left hy1 ha
      omega
    · have e : a * d ≤ a * y :=
        Int.mul_le_mul_of_nonpos_left (by omega : a ≤ 0) hy2
      omega
  have Hb : min (b * c) (b * d) ≤ b * y := by
    by_cases hb : 0 ≤ b
    · have e : b * c ≤ b * y := Int.mul_le_mul_of_nonneg_left hy1 hb
      omega
    · have e : b * d ≤ b * y :=
        Int.mul_le_mul_of_nonpos_left (by omega : b ≤ 0) hy2
      omega
  have H1 : min (a * y) (b * y) ≤ x * y := by
    by_cases hy : 0 ≤ y
    · have e : a * y ≤ x * y := Int.mul_le_mul_of_nonneg_right hx1 hy
      omega
    · have e : b * y ≤ x * y :=
        Int.mul_le_mul_of_nonpos_right hx2 (by omega : y ≤ 0)
      omega
  omega

/-- Two values in `[a, b] × [c, d]` have a product at most the
    largest corner product. -/
theorem times_le_cornerMax {a b c d x y : Int}
    (hx1 : a ≤ x) (hx2 : x ≤ b) (hy1 : c ≤ y) (hy2 : y ≤ d) :
    x * y ≤ cornerMax a b c d := by
  unfold cornerMax
  have Ha : a * y ≤ max (a * c) (a * d) := by
    by_cases ha : 0 ≤ a
    · have e : a * y ≤ a * d := Int.mul_le_mul_of_nonneg_left hy2 ha
      omega
    · have e : a * y ≤ a * c :=
        Int.mul_le_mul_of_nonpos_left (by omega : a ≤ 0) hy1
      omega
  have Hb : b * y ≤ max (b * c) (b * d) := by
    by_cases hb : 0 ≤ b
    · have e : b * y ≤ b * d := Int.mul_le_mul_of_nonneg_left hy2 hb
      omega
    · have e : b * y ≤ b * c :=
        Int.mul_le_mul_of_nonpos_left (by omega : b ≤ 0) hy1
      omega
  have H1 : x * y ≤ max (a * y) (b * y) := by
    by_cases hy : 0 ≤ y
    · have e : x * y ≤ b * y := Int.mul_le_mul_of_nonneg_right hx2 hy
      omega
    · have e : x * y ≤ a * y :=
        Int.mul_le_mul_of_nonpos_right hx1 (by omega : y ≤ 0)
      omega
  omega

/-! ## Sign helpers

The four sign products the operand-side deductions need (with the
unit thresholds the integer order literals provide), the sign
derivations from `x·y = z`, and the guard-membership inversion of
the eight operand-side arms. -/

/-- A nonpositive-times-positive product is at most `-1`. -/
theorem times_mul_nonpos_pos {w v : Int} (hw : w ≤ -1) (hv : 1 ≤ v) :
    w * v ≤ -1 := by
  have e : w * v ≤ w * 1 :=
    Int.mul_le_mul_of_nonpos_left (by omega : w ≤ 0)
      (by omega : (1:Int) ≤ v)
  rw [Int.mul_one] at e
  omega

/-- A positive-times-positive product is at least `1`. -/
theorem times_mul_pos_pos {w v : Int} (hw : 1 ≤ w) (hv : 1 ≤ v) :
    1 ≤ w * v := by
  have e : w * 1 ≤ w * v :=
    Int.mul_le_mul_of_nonneg_left (by omega : (1:Int) ≤ v)
      (by omega : 0 ≤ w)
  rw [Int.mul_one] at e
  omega

/-- A positive-times-nonpositive product is at most `-1`. -/
theorem times_mul_pos_nonpos {w v : Int} (hw : 1 ≤ w) (hv : v ≤ -1) :
    w * v ≤ -1 := by
  have e : w * v ≤ w * (-1) :=
    Int.mul_le_mul_of_nonneg_left (by omega : v ≤ (-1:Int))
      (by omega : 0 ≤ w)
  have e2 : w * (-1) = -w := by rw [Int.mul_neg, Int.mul_one]
  omega

/-- A nonpositive-times-nonpositive product is at least `1`. -/
theorem times_mul_neg_neg {w v : Int} (hw : w ≤ -1) (hv : v ≤ -1) :
    1 ≤ w * v := by
  have e : -w * -v = w * v := Int.neg_mul_neg w v
  have h1 : 1 ≤ (-w) * (-v) :=
    times_mul_pos_pos (by omega) (by omega)
  omega

/-- With `y ≥ 1` and `z = x·y ≥ 0`, the factor `x` is nonnegative. -/
theorem times_sign_x_nonneg {x y z : Int} (hmul : x * y = z)
    (hy : 1 ≤ y) (hz : 0 ≤ z) : 0 ≤ x := by
  by_cases hx : x ≤ -1
  · have h := times_mul_nonpos_pos hx hy
    omega
  · omega

/-- With `y ≥ 1` and `z = x·y ≤ 0`, the factor `x` is nonpositive. -/
theorem times_sign_x_nonpos {x y z : Int} (hmul : x * y = z)
    (hy : 1 ≤ y) (hz : z ≤ 0) : x ≤ 0 := by
  by_cases hx : 1 ≤ x
  · have h := times_mul_pos_pos hx hy
    omega
  · omega

/-- With `y ≤ −1` and `z = x·y ≥ 0`, the factor `x` is nonpositive. -/
theorem times_sign_x_nonpos_of_neg {x y z : Int} (hmul : x * y = z)
    (hy : y ≤ -1) (hz : 0 ≤ z) : x ≤ 0 := by
  by_cases hx : 1 ≤ x
  · have h := times_mul_pos_nonpos hx hy
    omega
  · omega

/-- With `y ≤ −1` and `z = x·y ≤ 0`, the factor `x` is nonnegative. -/
theorem times_sign_x_nonneg_of_neg {x y z : Int} (hmul : x * y = z)
    (hy : y ≤ -1) (hz : z ≤ 0) : 0 ≤ x := by
  by_cases hx : x ≤ -1
  · have h := times_mul_neg_neg hx hy
    omega
  · omega

/-- With `x ≥ 1` and `z = x·y ≥ 0`, the factor `y` is nonnegative. -/
theorem times_sign_y_nonneg {x y z : Int} (hmul : x * y = z)
    (hx : 1 ≤ x) (hz : 0 ≤ z) : 0 ≤ y := by
  by_cases hy : y ≤ -1
  · have h := times_mul_nonpos_pos hy hx
    have hcomm : x * y = y * x := Int.mul_comm x y
    omega
  · omega

/-- With `x ≥ 1` and `z = x·y ≤ 0`, the factor `y` is nonpositive. -/
theorem times_sign_y_nonpos {x y z : Int} (hmul : x * y = z)
    (hx : 1 ≤ x) (hz : z ≤ 0) : y ≤ 0 := by
  by_cases hy : 1 ≤ y
  · have h := times_mul_pos_pos hx hy
    omega
  · omega

/-- With `x ≤ −1` and `z = x·y ≥ 0`, the factor `y` is nonpositive. -/
theorem times_sign_y_nonpos_of_neg {x y z : Int} (hmul : x * y = z)
    (hx : x ≤ -1) (hz : 0 ≤ z) : y ≤ 0 := by
  by_cases hy : 1 ≤ y
  · have h := times_mul_pos_nonpos hy hx
    have hcomm : x * y = y * x := Int.mul_comm x y
    omega
  · omega

/-- With `x ≤ −1` and `z = x·y ≤ 0`, the factor `y` is nonnegative. -/
theorem times_sign_y_nonneg_of_neg {x y z : Int} (hmul : x * y = z)
    (hx : x ≤ -1) (hz : z ≤ 0) : 0 ≤ y := by
  by_cases hy : y ≤ -1
  · have h := times_mul_neg_neg hx hy
    omega
  · omega

/-- Membership in `propTimes`'s sweep list: either one of the two
    corner arms (returned verbatim) or one of the eight guarded
    sign arms with the guards of the arm the result belongs to and
    the result itself (the guard is checked before the arm enters
    the list, so an arm member always carries its side
    conditions). -/
theorem times_sign_arm {st : State} {i j k : Nat}
    {yj' yj xi' xi zk' zk : Int} {r : PropagationResult}
    (h : r ∈ [narrowLo st k (cornerMin xi' xi yj' yj)
        [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
          negLe i xi, posLe j (yj' - 1), negLe j yj],
        narrowHi st k (cornerMax xi' xi yj' yj)
        [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
          negLe i xi, posLe j (yj' - 1), negLe j yj]]
      ++ (if 0 < yj' ∧ 0 ≤ zk' then
        [narrowLo st i 0
          [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
      ++ (if 0 < yj' ∧ zk ≤ 0 then
        [narrowHi st i 0 [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
      ++ (if yj < 0 ∧ 0 ≤ zk' then
        [narrowHi st i 0 [posLe i 0, negLe j yj, posLe k (-1)]] else [])
      ++ (if yj < 0 ∧ zk ≤ 0 then
        [narrowLo st i 0 [negLe i (-1), negLe j yj, negLe k 0]] else [])
      ++ (if 0 < xi' ∧ 0 ≤ zk' then
        [narrowLo st j 0
          [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
      ++ (if 0 < xi' ∧ zk ≤ 0 then
        [narrowHi st j 0 [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
      ++ (if xi < 0 ∧ 0 ≤ zk' then
        [narrowHi st j 0 [posLe j 0, negLe i xi, posLe k (-1)]] else [])
      ++ (if xi < 0 ∧ zk ≤ 0 then
        [narrowLo st j 0 [negLe j (-1), negLe i xi, negLe k 0]] else [])) :
    r = narrowLo st k (cornerMin xi' xi yj' yj)
      [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
        negLe i xi, posLe j (yj' - 1), negLe j yj] ∨
    r = narrowHi st k (cornerMax xi' xi yj' yj)
      [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
        negLe i xi, posLe j (yj' - 1), negLe j yj] ∨
    (0 < yj' ∧ 0 ≤ zk' ∧ r = narrowLo st i 0
        [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]) ∨
    (0 < yj' ∧ zk ≤ 0 ∧ r = narrowHi st i 0
        [posLe i 0, posLe j (yj' - 1), negLe k 0]) ∨
    (yj < 0 ∧ 0 ≤ zk' ∧ r = narrowHi st i 0
        [posLe i 0, negLe j yj, posLe k (-1)]) ∨
    (yj < 0 ∧ zk ≤ 0 ∧ r = narrowLo st i 0
        [negLe i (-1), negLe j yj, negLe k 0]) ∨
    (0 < xi' ∧ 0 ≤ zk' ∧ r = narrowLo st j 0
        [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]) ∨
    (0 < xi' ∧ zk ≤ 0 ∧ r = narrowHi st j 0
        [posLe j 0, posLe i (xi' - 1), negLe k 0]) ∨
    (xi < 0 ∧ 0 ≤ zk' ∧ r = narrowHi st j 0
        [posLe j 0, negLe i xi, posLe k (-1)]) ∨
    (xi < 0 ∧ zk ≤ 0 ∧ r = narrowLo st j 0
        [negLe j (-1), negLe i xi, negLe k 0]) := by
  -- the append chain is left-nested with the corner pair at its
  -- head; peel the eight sign chunks from the right until the
  -- corner pair remains
  rcases List.mem_append.mp h with hpre | hs8
  · rcases List.mem_append.mp hpre with hpre | hs7
    · rcases List.mem_append.mp hpre with hpre | hs6
      · rcases List.mem_append.mp hpre with hpre | hs5
        · rcases List.mem_append.mp hpre with hpre | hs4
          · rcases List.mem_append.mp hpre with hpre | hs3
            · rcases List.mem_append.mp hpre with hpre | hs2
              · rcases List.mem_append.mp hpre with hcorner | hs1
                · rcases List.mem_cons.mp hcorner with h1 | h1
                  · exact Or.inl h1
                  · exact Or.inr (Or.inl (List.mem_singleton.mp h1))
                · by_cases hc : 0 < yj' ∧ 0 ≤ zk'
                  · rw [if_pos hc] at hs1
                    rcases List.mem_cons.mp hs1 with h2 | h2
                    · exact Or.inr (Or.inr (Or.inl ⟨hc.1, hc.2, h2⟩))
                    · exact absurd h2 (by simp)
                  · rw [if_neg hc] at hs1
                    exact absurd hs1 (by simp)
              · by_cases hc : 0 < yj' ∧ zk ≤ 0
                · rw [if_pos hc] at hs2
                  rcases List.mem_cons.mp hs2 with h2 | h2
                  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hc.1, hc.2, h2⟩)))
                  · exact absurd h2 (by simp)
                · rw [if_neg hc] at hs2
                  exact absurd hs2 (by simp)
            · by_cases hc : yj < 0 ∧ 0 ≤ zk'
              · rw [if_pos hc] at hs3
                rcases List.mem_cons.mp hs3 with h2 | h2
                · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                    ⟨hc.1, hc.2, h2⟩))))
                · exact absurd h2 (by simp)
              · rw [if_neg hc] at hs3
                exact absurd hs3 (by simp)
          · by_cases hc : yj < 0 ∧ zk ≤ 0
            · rw [if_pos hc] at hs4
              rcases List.mem_cons.mp hs4 with h2 | h2
              · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
                  ⟨hc.1, hc.2, h2⟩)))))
              · exact absurd h2 (by simp)
            · rw [if_neg hc] at hs4
              exact absurd hs4 (by simp)
        · by_cases hc : 0 < xi' ∧ 0 ≤ zk'
          · rw [if_pos hc] at hs5
            rcases List.mem_cons.mp hs5 with h2 | h2
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (Or.inl ⟨hc.1, hc.2, h2⟩))))))
            · exact absurd h2 (by simp)
          · rw [if_neg hc] at hs5
            exact absurd hs5 (by simp)
      · by_cases hc : 0 < xi' ∧ zk ≤ 0
        · rw [if_pos hc] at hs6
          rcases List.mem_cons.mp hs6 with h2 | h2
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
              (Or.inr (Or.inl ⟨hc.1, hc.2, h2⟩)))))))
          · exact absurd h2 (by simp)
        · rw [if_neg hc] at hs6
          exact absurd hs6 (by simp)
    · by_cases hc : xi < 0 ∧ 0 ≤ zk'
      · rw [if_pos hc] at hs7
        rcases List.mem_cons.mp hs7 with h2 | h2
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
            (Or.inr (Or.inl ⟨hc.1, hc.2, h2⟩))))))))
        · exact absurd h2 (by simp)
      · rw [if_neg hc] at hs7
        exact absurd hs7 (by simp)
  · by_cases hc : xi < 0 ∧ zk ≤ 0
    · rw [if_pos hc] at hs8
      rcases List.mem_cons.mp hs8 with h2 | h2
      · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
          (Or.inr (Or.inr ⟨hc.1, hc.2, h2⟩))))))))
      · exact absurd h2 (by simp)
    · rw [if_neg hc] at hs8
      exact absurd hs8 (by simp)

/-! ## The propagator -/

/-- `int_times`-style: `x * y = z` over slots `i j k`; bounds
    `x ∈ [xi',xi]`, `y ∈ [yj',yj]`, `z ∈ [zk',zk]` (only the `x` and
    `y` extrema are read).

    Nogoods (each integer-valid under `x * y = z`, causes in
    brackets):
    * `z ≥ cornerMin xi' xi yj' yj` (causes `x ≥ xi'`, `x ≤ xi`,
      `y ≥ yj'`, `y ≤ yj`): `[z > m−1, x < xi', x > xi, y < yj',
      y > yj]` with `m = cornerMin xi' xi yj' yj` — if `x` and `y`
      are pinned inside their intervals, the product
      `z = x·y ≥ m`, so a point falsifying all five literals
      violates the constraint (the whole interval pin is a cause
      because the product is not monotone);
    * `z ≤ cornerMax xi' xi yj' yj` (same four causes):
      `[z ≤ M, x < xi', x > xi, y < yj', y > yj]` with
      `M = cornerMax xi' xi yj' yj` — dually, `z = x·y ≤ M`.

    The eight operand-side SIGN deductions (each guarded by the
    other operand's sign interval, read off the domain extrema at
    the state — the arm only enters the sweep when its side
    conditions hold, so the emitted nogood needs no further
    premises):
    * `x ≥ 0` (guards `0 < yj'`, `0 ≤ zk'`; causes `y ≥ yj'`,
      `z ≥ zk'`): `[x < 0, y < yj', z < zk']` — with `y ≥ yj' > 0`
      and `z ≥ zk' ≥ 0`, a negative `x` gives
      `z = x·y ≤ (−1)·yj' < 0 ≤ zk' ≤ z`;
    * `x ≤ 0` (guards `0 < yj'`, `zk ≤ 0`; causes `y ≥ yj'`,
      `z ≤ zk`): `[x > 0, y < yj', z > zk]` — with `x ≥ 1`,
      `y ≥ yj' ≥ 1`, `z ≤ zk ≤ 0`: `z = x·y ≥ 1 > 0 ≥ zk ≥ z`;
    * `x ≤ 0` (guards `yj < 0`, `0 ≤ zk'`; causes `y ≤ yj`,
      `z ≥ zk'`): `[x > 0, y > yj, z < zk']` — with `x ≥ 1`,
      `y ≤ yj ≤ −1`, `z ≥ zk' ≥ 0`: `z = x·y ≤ (−1)·x < 0 ≤ z`;
    * `x ≥ 0` (guards `yj < 0`, `zk ≤ 0`; causes `y ≤ yj`,
      `z ≤ zk`): `[x < 0, y > yj, z > zk]` — with `x ≤ −1`,
      `y ≤ yj ≤ −1`, `z ≤ zk ≤ 0`: `z = x·y ≥ 1 > 0 ≥ z`;
    * the four y-side duals (swap the i/j roles, reading `x`'s
      extrema for the guard).

    Deliberately incomplete: the x/y-side BOUND deductions (e.g.
    `x ≤ zk / yj` when `y ≥ yj' > 0`) need sign case splits and
    integer division; they are left to decisions and the leaf check.
    The z-corners and the operand-side sign deductions are emitted.

    No direct conflict arm: `narrowLo`/`narrowHi` report their own
    conflicts when a deduced bound is falsified by the domain
    (exactly `propPlus`'s shape). -/
def propTimes (st : State) (i j k : Nat) : PropagationResult :=
  match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []),
        domMinI (st.domains.getD j []), domMaxI (st.domains.getD j []),
        domMinI (st.domains.getD k []), domMaxI (st.domains.getD k []) with
  | some xi', some xi, some yj', some yj, some zk', some zk =>
      firstEvent
        ([ -- z ≥ cornerMin xi' xi yj' yj
           --   (causes: x ≥ xi', x ≤ xi, y ≥ yj', y ≤ yj)
           narrowLo st k (cornerMin xi' xi yj' yj)
             [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
               negLe i xi, posLe j (yj' - 1), negLe j yj]
        , -- z ≤ cornerMax xi' xi yj' yj  (same four causes)
          narrowHi st k (cornerMax xi' xi yj' yj)
            [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
              negLe i xi, posLe j (yj' - 1), negLe j yj]
        ] ++ -- x ≥ 0  (guards: 0 < yj', 0 ≤ zk')
        (if 0 < yj' ∧ 0 ≤ zk' then
          [narrowLo st i 0
            [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
        ++ -- x ≤ 0  (guards: 0 < yj', zk ≤ 0)
        (if 0 < yj' ∧ zk ≤ 0 then
          [narrowHi st i 0
            [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
        ++ -- x ≤ 0  (guards: yj < 0, 0 ≤ zk')
        (if yj < 0 ∧ 0 ≤ zk' then
          [narrowHi st i 0
            [posLe i 0, negLe j yj, posLe k (-1)]] else [])
        ++ -- x ≥ 0  (guards: yj < 0, zk ≤ 0)
        (if yj < 0 ∧ zk ≤ 0 then
          [narrowLo st i 0
            [negLe i (-1), negLe j yj, negLe k 0]] else [])
        ++ -- y ≥ 0  (guards: 0 < xi', 0 ≤ zk')
        (if 0 < xi' ∧ 0 ≤ zk' then
          [narrowLo st j 0
            [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
        ++ -- y ≤ 0  (guards: 0 < xi', zk ≤ 0)
        (if 0 < xi' ∧ zk ≤ 0 then
          [narrowHi st j 0
            [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
        ++ -- y ≤ 0  (guards: xi < 0, 0 ≤ zk')
        (if xi < 0 ∧ 0 ≤ zk' then
          [narrowHi st j 0
            [posLe j 0, negLe i xi, posLe k (-1)]] else [])
        ++ -- y ≥ 0  (guards: xi < 0, zk ≤ 0)
        (if xi < 0 ∧ zk ≤ 0 then
          [narrowLo st j 0
            [negLe j (-1), negLe i xi, negLe k 0]] else []))
  | _, _, _, _, _, _ => .stable

/-! ## Constraint semantics at integer views -/

/-- The timesSlot constraint's semantics force all three views to
    exist and carry the product. -/
theorem timesSlot_views (a : Assignment) (i j k : Nat)
    (h : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ x y z, slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z ∧ x * y = z := by
  obtain ⟨p, q, r, hpi, hqj, hrk, hmul⟩ := h
  exact ⟨p, q, r, slotInt_of_int_read hpi, slotInt_of_int_read hqj,
    slotInt_of_int_read hrk, hmul⟩

/-! ## The nogood-true helpers (corner disjunctions)

Each helper proves, from the family constraint's semantics at ONE
assignment, that an emitted nogood carries a true literal — the
single place the family arithmetic lives; the `_safe` entitlement
arm, `Reason.Valid`, and the state-free entitlement all consume
them. -/

/-- timesSlot nogood 1 (the corner-min arm): `[z > m−1, x < xi',
    x > xi, y < yj', y > yj]` with `m = cornerMin xi' xi yj' yj` — if
    `x ≤ xi'−1` the second is true; else if `xi < x` the third; else
    if `y ≤ yj'−1` the fourth; else if `yj < y` the fifth; else
    `xi' ≤ x ≤ xi` and `yj' ≤ y ≤ yj`, so `z = x·y ≥ m > m−1`, the
    head. -/
theorem times_nogood_min_true {a : Assignment} {i j k : Nat}
    {xi' xi yj' yj : Int}
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
        negLe i xi, posLe j (yj' - 1), negLe j yj],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hlo : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hhi : xi < x
    · exact ⟨negLe i xi, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
    · by_cases hlo2 : y ≤ yj' - 1
      · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)), by
          rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
      · by_cases hhi2 : yj < y
        · exact ⟨negLe j yj, List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))), by
            rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩
        · exact ⟨negLe k (cornerMin xi' xi yj' yj - 1),
            List.mem_cons_self, by
            rw [eval_negLe_iff]
            have hcm : cornerMin xi' xi yj' yj ≤ x * y :=
              times_cornerMin_le (by omega) (by omega) (by omega)
              (by omega)
            exact ⟨z, hz, by omega⟩⟩

/-- timesSlot nogood 2 (the corner-max arm): `[z ≤ M, x < xi',
    x > xi, y < yj', y > yj]` with `M = cornerMax xi' xi yj' yj` —
    the four cause literals as in nogood 1; else `xi' ≤ x ≤ xi` and
    `yj' ≤ y ≤ yj`, so `z = x·y ≤ M`, the head. -/
theorem times_nogood_max_true {a : Assignment} {i j k : Nat}
    {xi' xi yj' yj : Int}
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
        negLe i xi, posLe j (yj' - 1), negLe j yj],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hlo : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hhi : xi < x
    · exact ⟨negLe i xi, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
    · by_cases hlo2 : y ≤ yj' - 1
      · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          List.mem_cons_self)), by
          rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
      · by_cases hhi2 : yj < y
        · exact ⟨negLe j yj, List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
            (List.mem_cons_of_mem _ List.mem_cons_self))), by
            rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩
        · exact ⟨posLe k (cornerMax xi' xi yj' yj),
            List.mem_cons_self, by
            rw [eval_posLe_iff]
            have hcx : x * y ≤ cornerMax xi' xi yj' yj :=
              times_le_cornerMax (by omega) (by omega) (by omega)
              (by omega)
            exact ⟨z, hz, by omega⟩⟩

/-- timesSlot sign nogood (the `x ≥ 0` arm): `[x < 0, y < yj',
    z < 0]` — if `y ≤ yj'−1` the second is true; else `y ≥ yj' ≥ 1`,
    so a negative `x` gives `z = x·y ≤ −1`, the third literal
    (`z ≤ −1`); else `x ≥ 0`, the head. (The arm fires only when
    the guard `0 ≤ zk'` makes the cause `z ≥ 0` trail-true, but the
    clause itself needs no guard: the z-cause is stated at the sign
    threshold `z ≤ −1`.) -/
theorem times_nogood_i_nonneg_true {a : Assignment} {i j k : Nat}
    {yj' : Int} (hpos : 1 ≤ yj')
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe i (-1), posLe j (yj' - 1), posLe k (-1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : y ≤ yj' - 1
  · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨y, hy, hcase1⟩⟩
  · by_cases hcase2 : x ≤ -1
    · exact ⟨posLe k (-1), List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_posLe_iff]
        have h : x * y ≤ -1 := times_mul_nonpos_pos hcase2 (by omega)
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨negLe i (-1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- timesSlot sign nogood (the `x ≤ 0` arm): `[x > 0, y < yj',
    z > 0]` — if `y ≤ yj'−1` the second is true; else `y ≥ yj' ≥ 1`,
    so a positive `x` gives `z = x·y ≥ 1`, the third literal
    (`z > 0`); else `x ≤ 0`, the head. -/
theorem times_nogood_i_nonpos_true {a : Assignment} {i j k : Nat}
    {yj' : Int} (hpos : 1 ≤ yj')
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe i 0, posLe j (yj' - 1), negLe k 0],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : y ≤ yj' - 1
  · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨y, hy, hcase1⟩⟩
  · by_cases hcase2 : 1 ≤ x
    · exact ⟨negLe k 0, List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_negLe_iff]
        have h : 1 ≤ x * y := times_mul_pos_pos hcase2 (by omega)
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨posLe i 0, List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- timesSlot sign nogood (the `x ≤ 0` arm, negative y):
    `[x > 0, y > yj, z < 0]` — if `yj < y` the second is true; else
    `y ≤ yj ≤ −1`, so a positive `x` gives `z = x·y ≤ −1`, the
    third literal (`z ≤ −1`); else `x ≤ 0`, the head. -/
theorem times_nogood_i_nonpos_hi_true {a : Assignment} {i j k : Nat}
    {yj : Int} (hneg : yj ≤ -1)
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe i 0, negLe j yj, posLe k (-1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : yj < y
  · exact ⟨negLe j yj, List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, hcase1⟩⟩
  · by_cases hcase2 : 1 ≤ x
    · exact ⟨posLe k (-1), List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_posLe_iff]
        have h : x * y ≤ -1 := times_mul_pos_nonpos hcase2 (by omega)
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨posLe i 0, List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- timesSlot sign nogood (the `x ≥ 0` arm, negative y):
    `[x < 0, y > yj, z > 0]` — if `yj < y` the second is true; else
    `y ≤ yj ≤ −1`, so a negative `x` gives `z = x·y ≥ 1`, the third
    literal (`z > 0`); else `x ≥ 0`, the head. -/
theorem times_nogood_i_nonneg_hi_true {a : Assignment} {i j k : Nat}
    {yj : Int} (hneg : yj ≤ -1)
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe i (-1), negLe j yj, negLe k 0],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : yj < y
  · exact ⟨negLe j yj, List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, hcase1⟩⟩
  · by_cases hcase2 : x ≤ -1
    · exact ⟨negLe k 0, List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_negLe_iff]
        have h : 1 ≤ x * y := times_mul_neg_neg hcase2 (by omega)
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨negLe i (-1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- timesSlot sign nogood (the `y ≥ 0` arm): `[y < 0, x < xi',
    z < 0]` — the i/j dual of `times_nogood_i_nonneg_true`. -/
theorem times_nogood_j_nonneg_true {a : Assignment} {i j k : Nat}
    {xi' : Int} (hpos : 1 ≤ xi')
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe j (-1), posLe i (xi' - 1), posLe k (-1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, hcase1⟩⟩
  · by_cases hcase2 : y ≤ -1
    · exact ⟨posLe k (-1), List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_posLe_iff]
        have h : y * x ≤ -1 := times_mul_nonpos_pos hcase2 (by omega)
        have hcomm : x * y = y * x := Int.mul_comm x y
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨negLe j (-1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- timesSlot sign nogood (the `y ≤ 0` arm): `[y > 0, x < xi',
    z > 0]` — the i/j dual of `times_nogood_i_nonpos_true`. -/
theorem times_nogood_j_nonpos_true {a : Assignment} {i j k : Nat}
    {xi' : Int} (hpos : 1 ≤ xi')
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe j 0, posLe i (xi' - 1), negLe k 0],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, hcase1⟩⟩
  · by_cases hcase2 : 1 ≤ y
    · exact ⟨negLe k 0, List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_negLe_iff]
        have h : 1 ≤ x * y := times_mul_pos_pos (by omega) hcase2
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨posLe j 0, List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- timesSlot sign nogood (the `y ≤ 0` arm, negative x):
    `[y > 0, x > xi, z < 0]` — the i/j dual of
    `times_nogood_i_nonpos_hi_true`. -/
theorem times_nogood_j_nonpos_hi_true {a : Assignment} {i j k : Nat}
    {xi : Int} (hneg : xi ≤ -1)
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe j 0, negLe i xi, posLe k (-1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : xi < x
  · exact ⟨negLe i xi, List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, hcase1⟩⟩
  · by_cases hcase2 : 1 ≤ y
    · exact ⟨posLe k (-1), List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_posLe_iff]
        have h : y * x ≤ -1 := times_mul_pos_nonpos hcase2 (by omega)
        have hcomm : x * y = y * x := Int.mul_comm x y
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨posLe j 0, List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- timesSlot sign nogood (the `y ≥ 0` arm, negative x):
    `[y < 0, x > xi, z > 0]` — the i/j dual of
    `times_nogood_i_nonneg_hi_true`. -/
theorem times_nogood_j_nonneg_hi_true {a : Assignment} {i j k : Nat}
    {xi : Int} (hneg : xi ≤ -1)
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe j (-1), negLe i xi, negLe k 0],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  by_cases hcase1 : xi < x
  · exact ⟨negLe i xi, List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, hcase1⟩⟩
  · by_cases hcase2 : y ≤ -1
    · exact ⟨negLe k 0, List.mem_cons_of_mem _
        (List.mem_cons_of_mem _ List.mem_cons_self), by
        rw [eval_negLe_iff]
        have h : 1 ≤ x * y := times_mul_neg_neg (by omega) hcase2
        exact ⟨z, hz, by omega⟩⟩
    · exact ⟨negLe j (-1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩


/-! ## Reason-validity shared kernels

Local copies of Reason.lean's shared kernels (the standalone
packaging below keeps this module self-contained). -/

/-- Reason validity from clause truth (Reason.lean's
    `reason_valid_of_clause_true`). -/
theorem times_reason_valid_of_clause_true
    {problem : Problem DomConstraint Unit}
    {l : Literal} {r : Reason}
    (hmem : l ∈ r.clause)
    (htrue : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      ∃ l' ∈ r.clause, l'.eval a = some true) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l :=
  ⟨fun a ha => htrue a ha, decide_eq_true hmem⟩

/-- Normalization transfer from the raw emitted clause. -/
theorem times_reason_clause_norm_sf {r : Reason} {ng : Clause}
    (hcl : r = { clause := ng })
    (hnorm : ∀ q ∈ ng, q = q.norm) :
    ∀ q ∈ r.clause, q = q.norm := by
  intro q hq
  rw [hcl] at hq
  exact hnorm q hq

/-- A five-literal order clause is normalized. -/
theorem times_order5_norm {l1 l2 l3 l4 l5 : Literal}
    (h1 : l1 = l1.norm) (h2 : l2 = l2.norm) (h3 : l3 = l3.norm)
    (h4 : l4 = l4.norm) (h5 : l5 = l5.norm) :
    ∀ q ∈ [l1, l2, l3, l4, l5], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h1
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact h2
    · rcases List.mem_cons.mp hq with rfl | hq
      · exact h3
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact h4
        · rw [List.mem_singleton.mp hq]
          exact h5

/-- A three-literal order clause is normalized. -/
theorem times_order3_norm {l1 l2 l3 : Literal}
    (h1 : l1 = l1.norm) (h2 : l2 = l2.norm) (h3 : l3 = l3.norm) :
    ∀ q ∈ [l1, l2, l3], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h1
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact h2
    · rw [List.mem_singleton.mp hq]
      exact h3

/-! ## The per-arm pack at a fitting solution -/

/-- The per-arm arithmetic pack for propTimes at a fitting solution:
    the product equation and the six domain bounds. -/
theorem timesSlot_pack {st : State} {a : Assignment} {i j k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.timesSlot i j k).SatisfiedBy a)
    {xi' xi yj' yj zk' zk : Int}
    (hxi' : domMinI (st.domains.getD i []) = some xi')
    (hxi : domMaxI (st.domains.getD i []) = some xi)
    (hyj' : domMinI (st.domains.getD j []) = some yj')
    (hyj : domMaxI (st.domains.getD j []) = some yj)
    (hzk' : domMinI (st.domains.getD k []) = some zk')
    (hzk : domMaxI (st.domains.getD k []) = some zk) :
    ∃ x y z,
      slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z ∧ x * y = z ∧
      xi' ≤ x ∧ x ≤ xi ∧ yj' ≤ y ∧ y ≤ yj ∧ zk' ≤ z ∧ z ≤ zk := by
  obtain ⟨x, y, z, hx, hy, hz, hmul⟩ := timesSlot_views a i j k hcons
  exact ⟨x, y, z, hx, hy, hz, hmul,
    fits_min_bound hfit hxi' hx, fits_max_bound hfit hxi hx,
    fits_min_bound hfit hyj' hy, fits_max_bound hfit hyj hy,
    fits_min_bound hfit hzk' hz, fits_max_bound hfit hzk hz⟩

/-! ## propTimes soundness: `x * y = z` over slots i j k -/

/-- The propagator of a `timesSlot i j k` constraint: implied-literal
    soundness, conflict soundness, and entitlement, at every state. -/
theorem propTimes_safe (st : State) (i j k : Nat) :
    (∀ l r, propTimes st i j k = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.timesSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propTimes st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.timesSlot i j k).SatisfiedBy a → False) ∧
    (∀ c, propTimes st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.timesSlot i j k).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · -- implied-literal soundness
    intro l r hrun a hfit hcons
    unfold propTimes at hrun
    split at hrun
    next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
      obtain ⟨x, y, z, hx, hy, hz, hmul, b1, b2, b3, b4, b5, b6⟩ :=
        timesSlot_pack hfit hcons hxi' hxi hyj' hyj hzk' hzk
      rcases firstEvent_mem
                      ([narrowLo st k (cornerMin xi' xi yj' yj)
                [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj],
             narrowHi st k (cornerMax xi' xi yj' yj)
                [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj]]
              ++ (if 0 < yj' ∧ 0 ≤ zk' then
                [narrowLo st i 0
                  [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
              ++ (if 0 < yj' ∧ zk ≤ 0 then
                [narrowHi st i 0
                  [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
              ++ (if yj < 0 ∧ 0 ≤ zk' then
                [narrowHi st i 0
                  [posLe i 0, negLe j yj, posLe k (-1)]] else [])
              ++ (if yj < 0 ∧ zk ≤ 0 then
                [narrowLo st i 0
                  [negLe i (-1), negLe j yj, negLe k 0]] else [])
              ++ (if 0 < xi' ∧ 0 ≤ zk' then
                [narrowLo st j 0
                  [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
              ++ (if 0 < xi' ∧ zk ≤ 0 then
                [narrowHi st j 0
                  [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
              ++ (if xi < 0 ∧ 0 ≤ zk' then
                [narrowHi st j 0
                  [posLe j 0, negLe i xi, posLe k (-1)]] else [])
              ++ (if xi < 0 ∧ zk ≤ 0 then
                [narrowLo st j 0
                  [negLe j (-1), negLe i xi, negLe k 0]] else []))
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · rcases times_sign_arm hmem with hcorner | hcorner |
        ⟨hyj', hzk', hnarrow⟩ | ⟨hyj', hzk, hnarrow⟩ |
        ⟨hyj, hzk', hnarrow⟩ | ⟨hyj, hzk, hnarrow⟩ |
        ⟨hxi', hzk', hnarrow⟩ | ⟨hxi', hzk, hnarrow⟩ |
        ⟨hxi, hzk', hnarrow⟩ | ⟨hxi, hzk, hnarrow⟩
        · -- arm 1: implied negLe k (cornerMin − 1); z = x·y ≥ cornerMin
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hcorner)
          subst hl; rw [eval_negLe_iff]
          have hcm : cornerMin xi' xi yj' yj ≤ x * y :=
            times_cornerMin_le b1 b2 b3 b4
          exact ⟨z, hz, by omega⟩
        · -- arm 2: implied posLe k cornerMax; z = x·y ≤ cornerMax
          obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hcorner)
          subst hl; rw [eval_posLe_iff]
          have hcx : x * y ≤ cornerMax xi' xi yj' yj :=
            times_le_cornerMax b1 b2 b3 b4
          exact ⟨z, hz, by omega⟩
        · -- sign arm: implied negLe i (−1); y ≥ 1 ∧ z ≥ 0 → x ≥ 0
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_negLe_iff]
          exact ⟨x, hx, times_sign_x_nonneg hmul (by omega) (by omega)⟩
        · -- sign arm: implied posLe i 0; y ≥ 1 ∧ z ≤ 0 → x ≤ 0
          obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_posLe_iff]
          exact ⟨x, hx, times_sign_x_nonpos hmul (by omega) (by omega)⟩
        · -- sign arm: implied posLe i 0; y ≤ −1 ∧ z ≥ 0 → x ≤ 0
          obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_posLe_iff]
          exact ⟨x, hx,
            times_sign_x_nonpos_of_neg hmul (by omega) (by omega)⟩
        · -- sign arm: implied negLe i (−1); y ≤ −1 ∧ z ≤ 0 → x ≥ 0
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_negLe_iff]
          exact ⟨x, hx,
            times_sign_x_nonneg_of_neg hmul (by omega) (by omega)⟩
        · -- sign arm: implied negLe j (−1); x ≥ 1 ∧ z ≥ 0 → y ≥ 0
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_negLe_iff]
          exact ⟨y, hy, times_sign_y_nonneg hmul (by omega) (by omega)⟩
        · -- sign arm: implied posLe j 0; x ≥ 1 ∧ z ≤ 0 → y ≤ 0
          obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_posLe_iff]
          exact ⟨y, hy, times_sign_y_nonpos hmul (by omega) (by omega)⟩
        · -- sign arm: implied posLe j 0; x ≤ −1 ∧ z ≥ 0 → y ≤ 0
          obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_posLe_iff]
          exact ⟨y, hy,
            times_sign_y_nonpos_of_neg hmul (by omega) (by omega)⟩
        · -- sign arm: implied negLe j (−1); x ≤ −1 ∧ z ≤ 0 → y ≥ 0
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
          subst hl; rw [eval_negLe_iff]
          exact ⟨y, hy,
            times_sign_y_nonneg_of_neg hmul (by omega) (by omega)⟩
    next => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · -- conflict soundness: the bounds contradict x * y = z at
      -- every fitting solution
      intro c hrun a hfit hcons
      unfold propTimes at hrun
      split at hrun
      next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
        obtain ⟨x, y, z, hx, hy, hz, hmul, b1, b2, b3, b4, b5, b6⟩ :=
          timesSlot_pack hfit hcons hxi' hxi hyj' hyj hzk' hzk
        have hcm : cornerMin xi' xi yj' yj ≤ x * y :=
          times_cornerMin_le b1 b2 b3 b4
        have hcx : x * y ≤ cornerMax xi' xi yj' yj :=
          times_le_cornerMax b1 b2 b3 b4
        rcases firstEvent_mem
                        ([narrowLo st k (cornerMin xi' xi yj' yj)
                [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj],
             narrowHi st k (cornerMax xi' xi yj' yj)
                [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj]]
              ++ (if 0 < yj' ∧ 0 ≤ zk' then
                [narrowLo st i 0
                  [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
              ++ (if 0 < yj' ∧ zk ≤ 0 then
                [narrowHi st i 0
                  [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
              ++ (if yj < 0 ∧ 0 ≤ zk' then
                [narrowHi st i 0
                  [posLe i 0, negLe j yj, posLe k (-1)]] else [])
              ++ (if yj < 0 ∧ zk ≤ 0 then
                [narrowLo st i 0
                  [negLe i (-1), negLe j yj, negLe k 0]] else [])
              ++ (if 0 < xi' ∧ 0 ≤ zk' then
                [narrowLo st j 0
                  [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
              ++ (if 0 < xi' ∧ zk ≤ 0 then
                [narrowHi st j 0
                  [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
              ++ (if xi < 0 ∧ 0 ≤ zk' then
                [narrowHi st j 0
                  [posLe j 0, negLe i xi, posLe k (-1)]] else [])
              ++ (if xi < 0 ∧ zk ≤ 0 then
                [narrowLo st j 0
                  [negLe j (-1), negLe i xi, negLe k 0]] else []))
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases times_sign_arm hmem with hcorner | hcorner |
          ⟨hyj', hzk', hnarrow⟩ | ⟨hyj', hzk, hnarrow⟩ |
          ⟨hyj, hzk', hnarrow⟩ | ⟨hyj, hzk, hnarrow⟩ |
          ⟨hxi', hzk', hnarrow⟩ | ⟨hxi', hzk, hnarrow⟩ |
          ⟨hxi, hzk', hnarrow⟩ | ⟨hxi, hzk, hnarrow⟩
          · -- arm 1 conflict: mx_k < cornerMin; but z = x·y ≥ cornerMin
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm hcorner)
            have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
            have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
            omega
          · -- arm 2 conflict: mn_k > cornerMax; but z = x·y ≤ cornerMax
            obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
              narrowHi_conflict_inv (Eq.symm hcorner)
            have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
            have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
            omega
          · -- sign arms: the guards give the sign of y (resp. x)
            -- and the sign of z, so the deduced sign of x (resp. y)
            -- holds at every fitting solution — the domain cannot
            -- lie entirely on the other side, so a conflict is
            -- impossible
            have hsign : 0 ≤ x :=
              times_sign_x_nonneg hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
            have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
            omega
          · have hsign : x ≤ 0 :=
              times_sign_x_nonpos hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
            have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
            omega
          · have hsign : x ≤ 0 :=
              times_sign_x_nonpos_of_neg hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
            have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
            omega
          · have hsign : 0 ≤ x :=
              times_sign_x_nonneg_of_neg hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
            have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
            omega
          · have hsign : 0 ≤ y :=
              times_sign_y_nonneg hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            have hmny : mn ≤ y := fits_min_bound hfit hmn hy
            have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
            omega
          · have hsign : y ≤ 0 :=
              times_sign_y_nonpos hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            have hmny : mn ≤ y := fits_min_bound hfit hmn hy
            have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
            omega
          · have hsign : y ≤ 0 :=
              times_sign_y_nonpos_of_neg hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            have hmny : mn ≤ y := fits_min_bound hfit hmn hy
            have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
            omega
          · have hsign : 0 ≤ y :=
              times_sign_y_nonneg_of_neg hmul (by omega) (by omega)
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            have hmny : mn ≤ y := fits_min_bound hfit hmn hy
            have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
            omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · -- entitlement: each nogood is integer-valid under x * y = z
      -- at a fitting solution
      intro c hrun a hfit hcons
      unfold propTimes at hrun
      split at hrun
      next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
        rcases firstEvent_mem
                        ([narrowLo st k (cornerMin xi' xi yj' yj)
                [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj],
             narrowHi st k (cornerMax xi' xi yj' yj)
                [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj]]
              ++ (if 0 < yj' ∧ 0 ≤ zk' then
                [narrowLo st i 0
                  [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
              ++ (if 0 < yj' ∧ zk ≤ 0 then
                [narrowHi st i 0
                  [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
              ++ (if yj < 0 ∧ 0 ≤ zk' then
                [narrowHi st i 0
                  [posLe i 0, negLe j yj, posLe k (-1)]] else [])
              ++ (if yj < 0 ∧ zk ≤ 0 then
                [narrowLo st i 0
                  [negLe i (-1), negLe j yj, negLe k 0]] else [])
              ++ (if 0 < xi' ∧ 0 ≤ zk' then
                [narrowLo st j 0
                  [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
              ++ (if 0 < xi' ∧ zk ≤ 0 then
                [narrowHi st j 0
                  [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
              ++ (if xi < 0 ∧ 0 ≤ zk' then
                [narrowHi st j 0
                  [posLe j 0, negLe i xi, posLe k (-1)]] else [])
              ++ (if xi < 0 ∧ zk ≤ 0 then
                [narrowLo st j 0
                  [negLe j (-1), negLe i xi, negLe k 0]] else []))
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases times_sign_arm hmem with hcorner | hcorner |
          ⟨hyj', hzk', hnarrow⟩ | ⟨hyj', hzk, hnarrow⟩ |
          ⟨hyj, hzk', hnarrow⟩ | ⟨hyj, hzk, hnarrow⟩ |
          ⟨hxi', hzk', hnarrow⟩ | ⟨hxi', hzk, hnarrow⟩ |
          ⟨hxi, hzk', hnarrow⟩ | ⟨hxi, hzk, hnarrow⟩
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm hcorner)
            rw [hcc]
            exact times_nogood_min_true hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm hcorner)
            rw [hcc]
            exact times_nogood_max_true hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_i_nonneg_true (by omega) hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_i_nonpos_true (by omega) hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_i_nonpos_hi_true (by omega) hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_i_nonneg_hi_true (by omega) hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_j_nonneg_true (by omega) hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_j_nonpos_true (by omega) hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_j_nonpos_hi_true (by omega) hcons
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm hnarrow)
            rw [hcc]
            exact times_nogood_j_nonneg_hi_true (by omega) hcons
      next => exact absurd hrun (by intro hc; simp at hc)
 /-! ## State-free reason validity (Reason.Valid + normalization) -/

/-- The state-free reason-validity lemma for the `timesSlot`
    family: all ten nogoods are integer-valid under the constraint
    alone (the sign nogoods carry their interval sign premise). -/
theorem propTimes_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.timesSlot i j k ∈ problem.constraints)
    (hrun : propTimes st i j k = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propTimes at hrun
  split at hrun
  next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
    rcases firstEvent_mem
                    ([narrowLo st k (cornerMin xi' xi yj' yj)
                [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj],
             narrowHi st k (cornerMax xi' xi yj' yj)
                [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj]]
              ++ (if 0 < yj' ∧ 0 ≤ zk' then
                [narrowLo st i 0
                  [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
              ++ (if 0 < yj' ∧ zk ≤ 0 then
                [narrowHi st i 0
                  [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
              ++ (if yj < 0 ∧ 0 ≤ zk' then
                [narrowHi st i 0
                  [posLe i 0, negLe j yj, posLe k (-1)]] else [])
              ++ (if yj < 0 ∧ zk ≤ 0 then
                [narrowLo st i 0
                  [negLe i (-1), negLe j yj, negLe k 0]] else [])
              ++ (if 0 < xi' ∧ 0 ≤ zk' then
                [narrowLo st j 0
                  [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
              ++ (if 0 < xi' ∧ zk ≤ 0 then
                [narrowHi st j 0
                  [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
              ++ (if xi < 0 ∧ 0 ≤ zk' then
                [narrowHi st j 0
                  [posLe j 0, negLe i xi, posLe k (-1)]] else [])
              ++ (if xi < 0 ∧ zk ≤ 0 then
                [narrowLo st j 0
                  [negLe j (-1), negLe i xi, negLe k 0]] else []))
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases times_sign_arm hmem with hcorner | hcorner |
      ⟨hyj', hzk', hnarrow⟩ | ⟨hyj', hzk, hnarrow⟩ |
      ⟨hyj, hzk', hnarrow⟩ | ⟨hyj, hzk, hnarrow⟩ |
      ⟨hxi', hzk', hnarrow⟩ | ⟨hxi', hzk, hnarrow⟩ |
      ⟨hxi, hzk', hnarrow⟩ | ⟨hxi, hzk, hnarrow⟩
      · -- emission 1: implied negLe k (cornerMin − 1), five-literal
        -- corner-min nogood
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm hcorner)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order5_norm rfl rfl rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
              negLe i xi, posLe j (yj' - 1), negLe j yj] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_min_true (ha.2 _ hprob)
      · -- emission 2: implied posLe k cornerMax, five-literal
        -- corner-max nogood
        obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm hcorner)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order5_norm rfl rfl rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
              negLe i xi, posLe j (yj' - 1), negLe j yj] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_max_true (ha.2 _ hprob)
      · -- emission 3: implied negLe i (−1), the x ≥ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe i (-1), posLe j (yj' - 1), posLe k (-1)] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_i_nonneg_true (by omega) (ha.2 _ hprob)
      · -- emission 4: implied posLe i 0, the x ≤ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [posLe i 0, posLe j (yj' - 1), negLe k 0] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_i_nonpos_true (by omega) (ha.2 _ hprob)
      · -- emission 5: implied posLe i 0, the x ≤ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [posLe i 0, negLe j yj, posLe k (-1)] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_i_nonpos_hi_true (by omega) (ha.2 _ hprob)
      · -- emission 6: implied negLe i (−1), the x ≥ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe i (-1), negLe j yj, negLe k 0] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_i_nonneg_hi_true (by omega) (ha.2 _ hprob)
      · -- emission 7: implied negLe j (−1), the y ≥ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe j (-1), posLe i (xi' - 1), posLe k (-1)] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_j_nonneg_true (by omega) (ha.2 _ hprob)
      · -- emission 8: implied posLe j 0, the y ≤ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [posLe j 0, posLe i (xi' - 1), negLe k 0] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_j_nonpos_true (by omega) (ha.2 _ hprob)
      · -- emission 9: implied posLe j 0, the y ≤ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [posLe j 0, negLe i xi, posLe k (-1)] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_j_nonpos_hi_true (by omega) (ha.2 _ hprob)
      · -- emission 10: implied negLe j (−1), the y ≥ 0 sign nogood
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨times_reason_valid_of_clause_true hpivmem ?_,
          times_reason_clause_norm_sf hcl
            (times_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe j (-1), negLe i xi, negLe k 0] := by
          rw [hcl]
        rw [hcl2]
        exact times_nogood_j_nonneg_hi_true (by omega) (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

 /-! ## State-free conflict entitlement -/

/-- The state-free conflict entitlement for the `timesSlot` family:
    every conflict clause is one of the ten nogoods, so it carries
    a true literal at every internal problem solution. -/
theorem propTimes_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i j k : Nat}
    {c : Clause}
    (hprob : DomConstraint.timesSlot i j k ∈ problem.constraints)
    (hrun : propTimes st i j k = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propTimes at hrun
  split at hrun
  next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
    rcases firstEvent_mem
                    ([narrowLo st k (cornerMin xi' xi yj' yj)
                [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj],
             narrowHi st k (cornerMax xi' xi yj' yj)
                [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
                  negLe i xi, posLe j (yj' - 1), negLe j yj]]
              ++ (if 0 < yj' ∧ 0 ≤ zk' then
                [narrowLo st i 0
                  [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
              ++ (if 0 < yj' ∧ zk ≤ 0 then
                [narrowHi st i 0
                  [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
              ++ (if yj < 0 ∧ 0 ≤ zk' then
                [narrowHi st i 0
                  [posLe i 0, negLe j yj, posLe k (-1)]] else [])
              ++ (if yj < 0 ∧ zk ≤ 0 then
                [narrowLo st i 0
                  [negLe i (-1), negLe j yj, negLe k 0]] else [])
              ++ (if 0 < xi' ∧ 0 ≤ zk' then
                [narrowLo st j 0
                  [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
              ++ (if 0 < xi' ∧ zk ≤ 0 then
                [narrowHi st j 0
                  [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
              ++ (if xi < 0 ∧ 0 ≤ zk' then
                [narrowHi st j 0
                  [posLe j 0, negLe i xi, posLe k (-1)]] else [])
              ++ (if xi < 0 ∧ zk ≤ 0 then
                [narrowLo st j 0
                  [negLe j (-1), negLe i xi, negLe k 0]] else []))
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases times_sign_arm hmem with hcorner | hcorner |
      ⟨hyj', hzk', hnarrow⟩ | ⟨hyj', hzk, hnarrow⟩ |
      ⟨hyj, hzk', hnarrow⟩ | ⟨hyj, hzk, hnarrow⟩ |
      ⟨hxi', hzk', hnarrow⟩ | ⟨hxi', hzk, hnarrow⟩ |
      ⟨hxi, hzk', hnarrow⟩ | ⟨hxi, hzk, hnarrow⟩
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm hcorner)
        rw [hcc]
        exact times_nogood_min_true (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowHi_conflict_inv (Eq.symm hcorner)
        rw [hcc]
        exact times_nogood_max_true (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_i_nonneg_true (by omega) (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowHi_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_i_nonpos_true (by omega) (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowHi_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_i_nonpos_hi_true (by omega) (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_i_nonneg_hi_true (by omega) (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_j_nonneg_true (by omega) (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowHi_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_j_nonpos_true (by omega) (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowHi_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_j_nonpos_hi_true (by omega) (ha.2 _ hprob)
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm hnarrow)
        rw [hcc]
        exact times_nogood_j_nonneg_hi_true (by omega) (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-! ## The emission-slot inversion

Every implied literal of `propTimes` is an order literal on one of
the three slots — the decidedness dispatch of Reason.lean consumes
this without re-mirroring the sweep. -/

/-- An implied literal of `propTimes` is a `negLe`/`posLe` on one of
    the slots `i`, `j`, `k`. -/
theorem propTimes_implied_slot {st : State} {i j k : Nat}
    {l : Literal} {r : Reason}
    (hrun : propTimes st i j k = .implied l r) :
    (∃ c, l = negLe i c) ∨ (∃ c, l = posLe i c) ∨
    (∃ c, l = negLe j c) ∨ (∃ c, l = posLe j c) ∨
    (∃ c, l = negLe k c) ∨ (∃ c, l = posLe k c) := by
  unfold propTimes at hrun
  split at hrun
  next _ _ _ _ _ _ xi' xi yj' yj zk' zk hxi' hxi hyj' hyj hzk' hzk =>
    rcases firstEvent_mem
        ([narrowLo st k (cornerMin xi' xi yj' yj)
            [negLe k (cornerMin xi' xi yj' yj - 1), posLe i (xi' - 1),
              negLe i xi, posLe j (yj' - 1), negLe j yj],
         narrowHi st k (cornerMax xi' xi yj' yj)
            [posLe k (cornerMax xi' xi yj' yj), posLe i (xi' - 1),
              negLe i xi, posLe j (yj' - 1), negLe j yj]]
          ++ (if 0 < yj' ∧ 0 ≤ zk' then
            [narrowLo st i 0
              [negLe i (-1), posLe j (yj' - 1), posLe k (-1)]] else [])
          ++ (if 0 < yj' ∧ zk ≤ 0 then
            [narrowHi st i 0
              [posLe i 0, posLe j (yj' - 1), negLe k 0]] else [])
          ++ (if yj < 0 ∧ 0 ≤ zk' then
            [narrowHi st i 0
              [posLe i 0, negLe j yj, posLe k (-1)]] else [])
          ++ (if yj < 0 ∧ zk ≤ 0 then
            [narrowLo st i 0
              [negLe i (-1), negLe j yj, negLe k 0]] else [])
          ++ (if 0 < xi' ∧ 0 ≤ zk' then
            [narrowLo st j 0
              [negLe j (-1), posLe i (xi' - 1), posLe k (-1)]] else [])
          ++ (if 0 < xi' ∧ zk ≤ 0 then
            [narrowHi st j 0
              [posLe j 0, posLe i (xi' - 1), negLe k 0]] else [])
          ++ (if xi < 0 ∧ 0 ≤ zk' then
            [narrowHi st j 0
              [posLe j 0, negLe i xi, posLe k (-1)]] else [])
          ++ (if xi < 0 ∧ zk ≤ 0 then
            [narrowLo st j 0
              [negLe j (-1), negLe i xi, negLe k 0]] else []))
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases times_sign_arm hmem with hcorner | hcorner |
        ⟨_, _, hnarrow⟩ | ⟨_, _, hnarrow⟩ |
        ⟨_, _, hnarrow⟩ | ⟨_, _, hnarrow⟩ |
        ⟨_, _, hnarrow⟩ | ⟨_, _, hnarrow⟩ |
        ⟨_, _, hnarrow⟩ | ⟨_, _, hnarrow⟩
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hcorner)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hl⟩))))
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hcorner)
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨_, hl⟩))))
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        exact Or.inl ⟨_, hl⟩
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        exact Or.inr (Or.inl ⟨_, hl⟩)
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        exact Or.inr (Or.inl ⟨_, hl⟩)
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        exact Or.inl ⟨_, hl⟩
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        exact Or.inr (Or.inr (Or.inl ⟨_, hl⟩))
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hl⟩)))
      · obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm hnarrow)
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, hl⟩)))
      · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm hnarrow)
        exact Or.inr (Or.inr (Or.inl ⟨_, hl⟩))
  next => exact absurd hrun (by intro hc; simp at hc)

/-! ## The standalone packaging

A self-contained registration of exactly the `timesSlot` family, in
the shape of Arith.lean's `propagatorOfProvedB6` packaging. -/

/-- The propagator of this module's family: `timesSlot`. -/
def propagatorOfProvedBT : DomConstraint → Option Propagator
  | .timesSlot i j k =>
      some { watches := [], run := fun st => propTimes st i j k }
  | _ => none

/-- Membership inversion for the registration. -/
theorem propagatorOfProvedBT_mem {dcs : List DomConstraint}
    {p : Propagator}
    (hp : p ∈ dcs.filterMap propagatorOfProvedBT) :
    ∃ dc ∈ dcs, propagatorOfProvedBT dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProvedBT dc with
      | none =>
          simp only [List.filterMap_cons, hpdc] at hp
          obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp
          exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩
      | some p0 =>
          simp only [List.filterMap_cons, hpdc] at hp
          rcases List.mem_cons.mp hp with hp2 | hp2
          · rw [hp2]
            exact ⟨dc, List.mem_cons_self, hpdc⟩
          · obtain ⟨dc2, hdc2mem, hdc2⟩ := ih hp2
            exact ⟨dc2, List.mem_cons_of_mem _ hdc2mem, hdc2⟩

/-- Emission inversion for the registration: a propagator's run is
    the family's propagator. -/
theorem propagatorOfProvedBT_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProvedBT dc = some p)
    (hrun : p.run st = res) :
    ∃ i j k, dc = .timesSlot i j k ∧ propTimes st i j k = res := by
  match hdc : dc with
  | .timesSlot i j k =>
      simp only [propagatorOfProvedBT] at hprop
      refine ⟨i, j, k, rfl, ?_⟩
      have hp2 : p = { watches := [], run := fun st => propTimes st i j k } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .eqSlot i j
  | .neSlot i j | .leSlot i j | .constEq i v
  | .plusSlot i j k | .allDiff is
  | .minSlot i j k | .maxSlot i j k | .absSlot i k2
  | .linEq coeffs is b | .linLe coeffs is b
  | .ltSlot i j | .ltConstHi i c | .ltConstLo i c
  | .leConstHi i c | .leConstLo i c
  | .boolNotSlot i j | .boolAndSlot i j k | .boolOrSlot i j k =>
      exfalso
      simp only [propagatorOfProvedBT] at hprop
      exact absurd hprop (by intro hc; cases hc)

/-! ## Axiom checks

Every theorem above uses only the standard axioms. -/

#print axioms propTimes_safe
#print axioms propTimes_entitled
#print axioms propTimes_reason_valid
#print axioms propagatorOfProvedBT_mem
#print axioms propagatorOfProvedBT_run
#print axioms timesSlot_pack
#print axioms timesSlot_views
#print axioms times_nogood_min_true
#print axioms times_nogood_max_true
#print axioms times_nogood_i_nonneg_true
#print axioms times_nogood_i_nonpos_true
#print axioms times_nogood_i_nonpos_hi_true
#print axioms times_nogood_i_nonneg_hi_true
#print axioms times_nogood_j_nonneg_true
#print axioms times_nogood_j_nonpos_true
#print axioms times_nogood_j_nonpos_hi_true
#print axioms times_nogood_j_nonneg_hi_true
#print axioms times_cornerMin_le
#print axioms times_le_cornerMax
#print axioms times_sign_arm
#print axioms propTimes_implied_slot

/-! ## Smoke checks

One concrete state where the propagator fires `.implied` with the
expected literal and reason clause, one where it is `.stable`, and
two exercising the operand-side sign deductions. -/

/-- Smoke state for `propTimes`: slots `x ∈ [2,3]`, `y ∈ [2,3]`,
    `z ∈ [0,9]` — the corners of `[2,3] × [2,3]` are
    `cornerMin = 4`, `cornerMax = 9`, so the first firing arm is the
    z-lower-bound narrowing to `4` (implied literal
    `negLe 2 3`). -/
def times_smoke_implied : State where
  domains := [[.int 2, .int 3], [.int 2, .int 3], [.int 0, .int 9]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propTimes times_smoke_implied 0 1 2 = .implied (negLe 2 3)
    { clause := [negLe 2 3, posLe 0 1, negLe 0 3, posLe 1 1,
      negLe 1 3] } := by rfl

/-- Smoke state for `propTimes` (stable): slots `x ∈ [2,3]`,
    `y ∈ [2,3]`, `z ∈ [4,9]` — `z`'s bounds `[4,9]` already sit
    inside the corner interval `[4,9]`, so both arms are `.stable`. -/
def times_smoke_stable : State where
  domains := [[.int 2, .int 3], [.int 2, .int 3], [.int 4, .int 9]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propTimes times_smoke_stable 0 1 2 = .stable := by rfl

/-- Smoke state for `propTimes` (the `x ≥ 0` sign arm): slots
    `x ∈ [−3,3]`, `y ∈ [1,4]`, `z ∈ [1,12]` — the corners of
    `[−3,3] × [1,4]` are `cornerMin = −12`, `cornerMax = 12`, so
    `z`'s bounds sit inside the corner interval; the first firing
    arm is the operand-side deduction `x ≥ 0` (guards `0 < yj' = 1`
    and `0 ≤ zk' = 1`), the implied literal `negLe 0 (−1)` with the
    sign nogood `[x < 0, y < 1, z < 1]`. -/
def times_smoke_sign_pos : State where
  domains := [[.int (-3), .int 3], [.int 1, .int 4], [.int 1, .int 12]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propTimes times_smoke_sign_pos 0 1 2 = .implied (negLe 0 (-1))
    { clause := [negLe 0 (-1), posLe 1 0, posLe 2 (-1)] } := by rfl

/-- Smoke state for `propTimes` (the `x ≤ 0` sign arm): slots
    `x ∈ [−3,3]`, `y ∈ [1,4]`, `z ∈ [−12,−1]` — the corners of
    `[−3,3] × [1,4]` are `cornerMin = −12`, `cornerMax = 12`, so
    `z`'s bounds sit inside the corner interval; the first firing
    arm is the operand-side deduction `x ≤ 0` (guards `0 < yj' = 1`
    and `zk = −1 ≤ 0`), the implied literal `posLe 0 0` with the
    sign nogood `[x > 0, y < 1, z > −1]`. -/
def times_smoke_sign_neg : State where
  domains := [[.int (-3), .int 3], [.int 1, .int 4],
    [.int (-12), .int (-1)]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propTimes times_smoke_sign_neg 0 1 2 = .implied (posLe 0 0)
    { clause := [posLe 0 0, posLe 1 0, negLe 2 0] } := by rfl

end LeanFzn.Solver.LCG
