/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/Arith.lean

Purpose:
  The three arithmetic families of PLAN.md §5 item 3, LCG layer: the
  `minSlot i j k` / `maxSlot i j k` (`int_min` / `int_max` style)
  and `absSlot i k` (`int_abs` style) bound propagators with their
  complete proof packages, mirroring the plusSlot package of
  Proofs/Propagators.lean and the nogood-true helpers of
  Proofs/Reason.lean. Nothing here edits the shared registration:
  the standalone packaging (`propagatorOfProvedB6` etc.) keeps this
  module self-contained.

Propagators (bounds `x ∈ [xi',xi]`, `y ∈ [yj',yj]`, `z ∈ [zk',zk]`):

  * `propMin` (`min x y = z`, slots i j k):
      - z ≥ min(xi', yj')   (causes x ≥ xi', y ≥ yj');
      - z ≤ min(xi, yj)     (causes x ≤ xi, y ≤ yj);
      - x ≥ zk'             (cause z ≥ zk'; min x y = z ≥ zk' forces
                             x ≥ zk');
      - y ≥ zk'             (cause z ≥ zk').
    Nogoods (each integer-valid under `min x y = z`):
      - [z > min(xi',yj')−1, x < xi', y < yj']
        = [negLe k (m−1), posLe i (xi'−1), posLe j (yj'−1)];
      - [z ≤ min(xi,yj), x > xi, y > yj]
        = [posLe k m', negLe i xi, negLe j yj];
      - [x > zk'−1, z ≤ zk'−1] = [negLe i (zk'−1), posLe k (zk'−1)];
      - [y > zk'−1, z ≤ zk'−1] = [negLe j (zk'−1), posLe k (zk'−1)].
    There is deliberately no conflict arm: `narrowLo`/`narrowHi`
    report their own conflicts when a bound is falsified by the
    domain (propPlus's shape).

  * `propMax` (`max x y = z`): the dual (swap lo/hi):
      - z ≥ max(xi', yj'), z ≤ max(xi, yj), x ≤ zk, y ≤ zk.

  * `propAbs` (r = |x|, slots i k; `x ∈ [xi',xi]`, `r ∈ [rk',rk]`):
      - r ≥ 0 (the unit nogood [negLe k (−1)], valid since
        r = |x| ≥ 0);
      - r ≥ absCornerMin xi' xi, the tightest lower bound |·| attains
        over [xi',xi] (0 when the interval straddles 0, else the
        nearer endpoint's absolute value; the domain-level reference
        is `propAbsBounded`'s `atLeastVals 0` combined with the
        operand-side corner bound) — causes x ≥ xi', x ≤ xi;
      - r ≤ max(|xi'|,|xi|) (the corner max) — same causes;
      - x ≤ rk (cause r ≤ rk: x ≤ |x| = r ≤ rk);
      - x ≥ −rk (cause r ≤ rk: −|x| ≤ x).

Verification: `timeout 600 env LEAN_NUM_THREADS=4 lake env lean
LeanFzn/Solver/UIP/Proofs/Fam/Arith.lean` — zero errors.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.ConstFamilies: the shared narrow inversions,
    coherence bridges, normalization facts.
  - LeanFzn.Solver.Propagation.Proofs.Theory: the narrow conflict inversions.
  - LeanFzn.Solver.Propagation.Propagate: State, narrowLo/narrowHi, firstEvent,
    domMinI/domMaxI.
  - LeanFzn.Solver.Propagation.Encoding: literal evaluation bridges.
  - LeanFzn.Compiler.Domain: not needed beyond what the above re-export.

DAG:
  LeanFzn.Solver.UIP.Proofs.Theory + LeanFzn.Solver.UIP.Proofs.ConstFamilies + LeanFzn.Solver.UIP.Propagate
    -> LeanFzn.Solver.UIP.Proofs.Fam.Arith (this module)
-/


import LeanFzn.Solver.Propagation.Proofs.ConstFamilies
import LeanFzn.Solver.Propagation.Proofs.Theory
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Solver.Propagation.Encoding
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## Shared abs helpers

`absValue` (LeanFzn.Solver/Propagators.lean) with the corner facts the
abs family needs. -/

/-- `absValue` is nonnegative. -/
theorem arith_absValue_nonneg (p : Int) : 0 ≤ absValue p := by
  unfold absValue
  split <;> omega

/-- A value is at most its own absolute value. -/
theorem arith_le_absValue (p : Int) : p ≤ absValue p := by
  unfold absValue
  split <;> omega

/-- A value is at least the negation of its own absolute value. -/
theorem arith_neg_absValue_le (p : Int) : -absValue p ≤ p := by
  unfold absValue
  split <;> omega

/-- `absValue` at a nonnegative argument is the argument. -/
theorem arith_absValue_of_nonneg {p : Int} (hp : 0 ≤ p) :
    absValue p = p := by
  unfold absValue; rw [if_neg (by omega : ¬ p < 0)]

/-- `absValue` at a negative argument is the negation. -/
theorem arith_absValue_of_neg {p : Int} (hp : p < 0) :
    absValue p = -p := by
  unfold absValue; rw [if_pos hp]

/-- The absolute value over an interval is at most the larger
    endpoint absolute value. -/
theorem arith_absValue_le_range {lo hi x : Int}
    (h1 : lo ≤ x) (h2 : x ≤ hi) :
    absValue x ≤ max (absValue lo) (absValue hi) := by
  by_cases hx : x < 0
  · rw [arith_absValue_of_neg hx]
    have e1 : -absValue lo ≤ lo := arith_neg_absValue_le lo
    omega
  · rw [arith_absValue_of_nonneg (by omega : 0 ≤ x)]
    have e2 : hi ≤ absValue hi := arith_le_absValue hi
    omega

/-- The tight lower corner of `|·|` over `[lo, hi]`: `0` when the
    interval straddles 0, else the nearer endpoint's absolute value
    (the abs function's minimum over an interval is at an endpoint,
    or 0 when 0 is in range). -/
def absCornerMin (lo hi : Int) : Int :=
  if lo ≤ 0 ∧ 0 ≤ hi then 0 else min (absValue lo) (absValue hi)

/-- The corner lower bound: `absCornerMin lo hi ≤ |x|` for every
    `x` of `[lo, hi]`. -/
theorem arith_absCornerMin_le {lo hi x : Int}
    (h1 : lo ≤ x) (h2 : x ≤ hi) :
    absCornerMin lo hi ≤ absValue x := by
  unfold absCornerMin
  split
  · exact arith_absValue_nonneg x
  · rcases (by omega : hi < 0 ∨ 0 < lo) with hneg | hpos
    · rw [arith_absValue_of_neg (by omega : x < 0)]
      have e1 : absValue lo = -lo :=
        arith_absValue_of_neg (by omega)
      have e2 : absValue hi = -hi :=
        arith_absValue_of_neg (by omega)
      omega
    · rw [arith_absValue_of_nonneg (by omega : 0 ≤ x)]
      have e1 : absValue lo = lo :=
        arith_absValue_of_nonneg (by omega)
      have e2 : absValue hi = hi :=
        arith_absValue_of_nonneg (by omega)
      omega

/-! ## The propagators -/

/-- `int_min`-style: `min x y = z` over slots `i j k`; bounds
    `x ∈ [xi',xi]`, `y ∈ [yj',yj]`, `z ∈ [zk',zk]`.

    Nogoods (each integer-valid under `min x y = z`, causes in
    brackets):
    * `z ≥ min(xi',yj')` (causes `x ≥ xi'`, `y ≥ yj'`):
      `[z > m−1, x < xi', y < yj']` with `m = min(xi',yj')` — if
      `x ≥ xi'` and `y ≥ yj'` then `z = min x y ≥ m`, so a point
      falsifying all three literals violates the constraint;
    * `z ≤ min(xi,yj)` (causes `x ≤ xi`, `y ≤ yj`):
      `[z ≤ m', x > xi, y > yj]` with `m' = min(xi,yj)`;
    * `x ≥ zk'` (cause `z ≥ zk'`): `[x > zk'−1, z ≤ zk'−1]` —
      `x < zk'` and `z ≥ zk'` give `z = min x y ≤ x < zk' ≤ z`;
    * `y ≥ zk'` (cause `z ≥ zk'`): the dual on `y`.

    No direct conflict arm: `narrowLo`/`narrowHi` report their own
    conflicts when the deduced bound is falsified by the domain
    (exactly `propPlus`'s shape). -/
def propMin (st : State) (i j k : Nat) : PropagationResult :=
  match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []),
        domMinI (st.domains.getD j []), domMaxI (st.domains.getD j []),
        domMinI (st.domains.getD k []) with
  | some xi', some xi, some yj', some yj, some zk' =>
      firstEvent
        [ -- z ≥ min(xi', yj')  (causes: x ≥ xi', y ≥ yj')
          narrowLo st k (min xi' yj')
            [negLe k (min xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)]
        , -- z ≤ min(xi, yj)  (causes: x ≤ xi, y ≤ yj)
          narrowHi st k (min xi yj)
            [posLe k (min xi yj), negLe i xi, negLe j yj]
        , -- x ≥ zk'  (cause: z ≥ zk')
          narrowLo st i zk' [negLe i (zk' - 1), posLe k (zk' - 1)]
        , -- y ≥ zk'  (cause: z ≥ zk')
          narrowLo st j zk' [negLe j (zk' - 1), posLe k (zk' - 1)]
        ]
  | _, _, _, _, _ => .stable

/-- `int_max`-style: `max x y = z` over slots `i j k` — the dual of
    `propMin` (swap lo/hi):
    * `z ≥ max(xi',yj')` (causes `x ≥ xi'`, `y ≥ yj'`):
      `[z > M−1, x < xi', y < yj']` with `M = max(xi',yj')`;
    * `z ≤ max(xi,yj)` (causes `x ≤ xi`, `y ≤ yj`):
      `[z ≤ M', x > xi, y > yj]` with `M' = max(xi,yj)`;
    * `x ≤ zk` (cause `z ≤ zk`): `[x ≤ zk, z > zk]` — `x > zk` and
      `z ≤ zk` give `z = max x y ≥ x > zk ≥ z`;
    * `y ≤ zk` (cause `z ≤ zk`): the dual on `y`. -/
def propMax (st : State) (i j k : Nat) : PropagationResult :=
  match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []),
        domMinI (st.domains.getD j []), domMaxI (st.domains.getD j []),
        domMaxI (st.domains.getD k []) with
  | some xi', some xi, some yj', some yj, some zk =>
      firstEvent
        [ -- z ≥ max(xi', yj')  (causes: x ≥ xi', y ≥ yj')
          narrowLo st k (max xi' yj')
            [negLe k (max xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)]
        , -- z ≤ max(xi, yj)  (causes: x ≤ xi, y ≤ yj)
          narrowHi st k (max xi yj)
            [posLe k (max xi yj), negLe i xi, negLe j yj]
        , -- x ≤ zk  (cause: z ≤ zk)
          narrowHi st i zk [posLe i zk, negLe k zk]
        , -- y ≤ zk  (cause: z ≤ zk)
          narrowHi st j zk [posLe j zk, negLe k zk]
        ]
  | _, _, _, _, _ => .stable

/-- `int_abs`-style: `r = |x|` over slots `i k`; bounds
    `x ∈ [xi',xi]`, `r ∈ [rk',rk]` (only `rk` is read).

    Nogoods (each integer-valid under `r = |x|`):
    * `r ≥ 0` (no cause): `[r > −1]` — `r = |x| ≥ 0` always;
    * `r ≥ absCornerMin xi' xi` (causes `x ≥ xi'`, `x ≤ xi`):
      `[r > c−1, x < xi', x > xi]` with `c = absCornerMin xi' xi` —
      the abs function's minimum over `[xi',xi]` is at an endpoint
      (or 0 when the interval straddles 0);
    * `r ≤ max(|xi'|,|xi|)` (same causes): `[r ≤ M, x < xi', x > xi]`;
    * `x ≤ rk` (cause `r ≤ rk`): `[x ≤ rk, r > rk]` — `x ≤ |x| =
      r ≤ rk`;
    * `x ≥ −rk` (cause `r ≤ rk`): `[x > −rk−1, r > rk]` —
      `−|x| ≤ x` and `|x| = r ≤ rk`. -/
def propAbs (st : State) (i k : Nat) : PropagationResult :=
  match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []),
        domMaxI (st.domains.getD k []) with
  | some xi', some xi, some rk =>
      firstEvent
        [ -- r ≥ 0  (r = |x| ≥ 0)
          narrowLo st k 0 [negLe k (-1)]
        , -- r ≥ absCornerMin xi' xi  (causes: x ≥ xi', x ≤ xi)
          narrowLo st k (absCornerMin xi' xi)
            [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1), negLe i xi]
        , -- r ≤ max(|xi'|,|xi|)  (causes: x ≥ xi', x ≤ xi)
          narrowHi st k (max (absValue xi') (absValue xi))
            [posLe k (max (absValue xi') (absValue xi)),
              posLe i (xi' - 1), negLe i xi]
        , -- x ≤ rk  (cause: r ≤ rk)
          narrowHi st i rk [posLe i rk, negLe k rk]
        , -- x ≥ −rk  (cause: r ≤ rk)
          narrowLo st i (-rk) [negLe i (-rk - 1), negLe k rk]
        ]
  | _, _, _ => .stable

/-! ## Constraint semantics at integer views -/

/-- The minSlot constraint's semantics force all three views to
    exist and carry the minimum. -/
theorem minSlot_views (a : Assignment) (i j k : Nat)
    (h : (DomConstraint.minSlot i j k).SatisfiedBy a) :
    ∃ x y z, slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z ∧ min x y = z := by
  obtain ⟨p, q, r, hpi, hqj, hrk, hmin⟩ := h
  exact ⟨p, q, r, slotInt_of_int_read hpi, slotInt_of_int_read hqj,
    slotInt_of_int_read hrk, hmin⟩

/-- The maxSlot constraint's semantics force all three views to
    exist and carry the maximum. -/
theorem maxSlot_views (a : Assignment) (i j k : Nat)
    (h : (DomConstraint.maxSlot i j k).SatisfiedBy a) :
    ∃ x y z, slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z ∧ max x y = z := by
  obtain ⟨p, q, r, hpi, hqj, hrk, hmax⟩ := h
  exact ⟨p, q, r, slotInt_of_int_read hpi, slotInt_of_int_read hqj,
    slotInt_of_int_read hrk, hmax⟩

/-- The absSlot constraint's semantics force both views to exist
    and carry the absolute value. -/
theorem absSlot_views (a : Assignment) (i k : Nat)
    (h : (DomConstraint.absSlot i k).SatisfiedBy a) :
    ∃ x r, slotInt a i = some x ∧ slotInt a k = some r ∧
      absValue x = r := by
  obtain ⟨p, q, hpi, hrk, habs⟩ := h
  exact ⟨p, q, slotInt_of_int_read hpi, slotInt_of_int_read hrk, habs⟩

/-! ## The nogood-true helpers (two-case disjunctions)

Each helper proves, from the family constraint's semantics at ONE
assignment, that an emitted nogood carries a true literal — the
single place the family arithmetic lives; the `_safe` entitlement
arm, `Reason.Valid`, and the state-free entitlement all consume
them. -/

/-- minSlot nogood 1: `[z > m−1, x < xi', y < yj']` with
    `m = min(xi',yj')` — if `x ≤ xi'−1` the second is true; else
    if `y ≤ yj'−1` the third; else `z = min x y ≥ min xi' yj' > m−1`,
    the head. -/
theorem arith_min_nogood_lo_k_true {a : Assignment} {i j k : Nat}
    {xi' yj' : Int}
    (hcons : (DomConstraint.minSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe k (min xi' yj' - 1), posLe i (xi' - 1),
        posLe j (yj' - 1)], l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmin⟩ := minSlot_views a i j k hcons
  by_cases hxi : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hyj : y ≤ yj' - 1
    · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
    · exact ⟨negLe k (min xi' yj' - 1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩

/-- minSlot nogood 2: `[z ≤ m', x > xi, y > yj]` with
    `m' = min(xi,yj)` — if `xi < x` the second is true; else if
    `yj < y` the third; else `z = min x y ≤ min xi yj = m'`. -/
theorem arith_min_nogood_hi_k_true {a : Assignment} {i j k : Nat}
    {xi yj : Int}
    (hcons : (DomConstraint.minSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe k (min xi yj), negLe i xi, negLe j yj],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmin⟩ := minSlot_views a i j k hcons
  by_cases hxi : xi < x
  · exact ⟨negLe i xi, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hyj : yj < y
    · exact ⟨negLe j yj, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩
    · exact ⟨posLe k (min xi yj), List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩

/-- minSlot nogood 3 (the 2-literal x-arm): `[x > zk'−1, z ≤ zk'−1]`
    — if `z ≤ zk'−1` the second is true; else `z = min x y ≥ zk'`
    forces `x ≥ z ≥ zk' > zk'−1`, the head. -/
theorem arith_min_nogood_lo_i_true {a : Assignment} {i j k : Nat}
    {zk' : Int}
    (hcons : (DomConstraint.minSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe i (zk' - 1), posLe k (zk' - 1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmin⟩ := minSlot_views a i j k hcons
  by_cases hzk : z ≤ zk' - 1
  · exact ⟨posLe k (zk' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩
  · exact ⟨negLe i (zk' - 1), List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- minSlot nogood 4 (the 2-literal y-arm): `[y > zk'−1, z ≤ zk'−1]`
    — the dual on `y`. -/
theorem arith_min_nogood_lo_j_true {a : Assignment} {i j k : Nat}
    {zk' : Int}
    (hcons : (DomConstraint.minSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe j (zk' - 1), posLe k (zk' - 1)],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmin⟩ := minSlot_views a i j k hcons
  by_cases hzk : z ≤ zk' - 1
  · exact ⟨posLe k (zk' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩
  · exact ⟨negLe j (zk' - 1), List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- maxSlot nogood 1: `[z > M−1, x < xi', y < yj']` with
    `M = max(xi',yj')` — if `x ≤ xi'−1` the second is true; else
    if `y ≤ yj'−1` the third; else `z = max x y ≥ max xi' yj' > M−1`. -/
theorem arith_max_nogood_lo_k_true {a : Assignment} {i j k : Nat}
    {xi' yj' : Int}
    (hcons : (DomConstraint.maxSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [negLe k (max xi' yj' - 1), posLe i (xi' - 1),
        posLe j (yj' - 1)], l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmax⟩ := maxSlot_views a i j k hcons
  by_cases hxi : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hyj : y ≤ yj' - 1
    · exact ⟨posLe j (yj' - 1), List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩
    · exact ⟨negLe k (max xi' yj' - 1), List.mem_cons_self, by
        rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩

/-- maxSlot nogood 2: `[z ≤ M', x > xi, y > yj]` with
    `M' = max(xi,yj)` — if `xi < x` the second is true; else if
    `yj < y` the third; else `z = max x y ≤ max xi yj = M'`. -/
theorem arith_max_nogood_hi_k_true {a : Assignment} {i j k : Nat}
    {xi yj : Int}
    (hcons : (DomConstraint.maxSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe k (max xi yj), negLe i xi, negLe j yj],
      l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmax⟩ := maxSlot_views a i j k hcons
  by_cases hxi : xi < x
  · exact ⟨negLe i xi, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hyj : yj < y
    · exact ⟨negLe j yj, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_negLe_iff]; exact ⟨y, hy, by omega⟩⟩
    · exact ⟨posLe k (max xi yj), List.mem_cons_self, by
        rw [eval_posLe_iff]; exact ⟨z, hz, by omega⟩⟩

/-- maxSlot nogood 3 (the 2-literal x-arm): `[x ≤ zk, z > zk]` —
    if `zk < z` the second is true; else `z = max x y ≤ zk` forces
    `x ≤ z ≤ zk`, the head. -/
theorem arith_max_nogood_hi_i_true {a : Assignment} {i j k : Nat}
    {zk : Int}
    (hcons : (DomConstraint.maxSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe i zk, negLe k zk], l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmax⟩ := maxSlot_views a i j k hcons
  by_cases hzk : zk < z
  · exact ⟨negLe k zk, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩
  · exact ⟨posLe i zk, List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- maxSlot nogood 4 (the 2-literal y-arm): `[y ≤ zk, z > zk]` —
    the dual on `y`. -/
theorem arith_max_nogood_hi_j_true {a : Assignment} {i j k : Nat}
    {zk : Int}
    (hcons : (DomConstraint.maxSlot i j k).SatisfiedBy a) :
    ∃ l ∈ [posLe j zk, negLe k zk], l.eval a = some true := by
  obtain ⟨x, y, z, hx, hy, hz, hmax⟩ := maxSlot_views a i j k hcons
  by_cases hzk : zk < z
  · exact ⟨negLe k zk, List.mem_cons_of_mem _ List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨z, hz, by omega⟩⟩
  · exact ⟨posLe j zk, List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨y, hy, by omega⟩⟩

/-- absSlot nogood 0 (the r ≥ 0 unit): `[r > −1]` — `r = |x| ≥ 0`
    always, the head. -/
theorem arith_abs_nogood_zero_true {a : Assignment} {i k : Nat}
    (hcons : (DomConstraint.absSlot i k).SatisfiedBy a) :
    ∃ l ∈ [negLe k (-1)], l.eval a = some true := by
  obtain ⟨x, r, hx, hr, habs⟩ := absSlot_views a i k hcons
  refine ⟨negLe k (-1), List.mem_cons_self, ?_⟩
  rw [eval_negLe_iff]
  refine ⟨r, hr, ?_⟩
  rw [← habs]
  exact arith_absValue_nonneg x

/-- absSlot nogood 1 (the corner-min arm): `[r > c−1, x < xi',
    x > xi]` with `c = absCornerMin xi' xi` — if `x ≤ xi'−1` the
    second is true; else if `xi < x` the third; else `xi' ≤ x ≤ xi`
    so `r = |x| ≥ c > c−1`, the head. -/
theorem arith_abs_nogood_corner_lo_true {a : Assignment} {i k : Nat}
    {xi' xi : Int}
    (hcons : (DomConstraint.absSlot i k).SatisfiedBy a) :
    ∃ l ∈ [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1),
        negLe i xi], l.eval a = some true := by
  obtain ⟨x, r, hx, hr, habs⟩ := absSlot_views a i k hcons
  by_cases hlo : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hhi : xi < x
    · exact ⟨negLe i xi, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
    · have hcorner : absCornerMin xi' xi ≤ absValue x :=
        arith_absCornerMin_le (by omega) (by omega)
      exact ⟨negLe k (absCornerMin xi' xi - 1), List.mem_cons_self, by
        rw [eval_negLe_iff]
        exact ⟨r, hr, by rw [← habs]; omega⟩⟩

/-- absSlot nogood 2 (the corner-max arm): `[r ≤ M, x < xi',
    x > xi]` with `M = max(|xi'|,|xi|)` — if `x ≤ xi'−1` the second
    is true; else if `xi < x` the third; else `r = |x| ≤ M`, the
    head. -/
theorem arith_abs_nogood_corner_hi_true {a : Assignment} {i k : Nat}
    {xi' xi : Int}
    (hcons : (DomConstraint.absSlot i k).SatisfiedBy a) :
    ∃ l ∈ [posLe k (max (absValue xi') (absValue xi)),
        posLe i (xi' - 1), negLe i xi], l.eval a = some true := by
  obtain ⟨x, r, hx, hr, habs⟩ := absSlot_views a i k hcons
  by_cases hlo : x ≤ xi' - 1
  · exact ⟨posLe i (xi' - 1), List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩
  · by_cases hhi : xi < x
    · exact ⟨negLe i xi, List.mem_cons_of_mem _ (List.mem_cons_of_mem _
        List.mem_cons_self), by
        rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩
    · have hrange : absValue x ≤ max (absValue xi') (absValue xi) :=
        arith_absValue_le_range (by omega) (by omega)
      exact ⟨posLe k (max (absValue xi') (absValue xi)),
        List.mem_cons_self, by
        rw [eval_posLe_iff]
        exact ⟨r, hr, by rw [← habs]; omega⟩⟩

/-- absSlot nogood 3 (the x ≤ rk arm): `[x ≤ rk, r > rk]` — if
    `rk < r` the second is true; else `x ≤ |x| = r ≤ rk`, the
    head. -/
theorem arith_abs_nogood_hi_i_true {a : Assignment} {i k : Nat}
    {rk : Int}
    (hcons : (DomConstraint.absSlot i k).SatisfiedBy a) :
    ∃ l ∈ [posLe i rk, negLe k rk], l.eval a = some true := by
  obtain ⟨x, r, hx, hr, habs⟩ := absSlot_views a i k hcons
  by_cases hrk : rk < r
  · exact ⟨negLe k rk, List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨r, hr, by omega⟩⟩
  · have hlex : x ≤ absValue x := arith_le_absValue x
    exact ⟨posLe i rk, List.mem_cons_self, by
      rw [eval_posLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-- absSlot nogood 4 (the x ≥ −rk arm): `[x > −rk−1, r > rk]` —
    if `rk < r` the second is true; else `x ≥ −|x| = −r ≥ −rk >
    −rk−1`, the head. -/
theorem arith_abs_nogood_lo_i_true {a : Assignment} {i k : Nat}
    {rk : Int}
    (hcons : (DomConstraint.absSlot i k).SatisfiedBy a) :
    ∃ l ∈ [negLe i (-rk - 1), negLe k rk], l.eval a = some true := by
  obtain ⟨x, r, hx, hr, habs⟩ := absSlot_views a i k hcons
  by_cases hrk : rk < r
  · exact ⟨negLe k rk, List.mem_cons_of_mem _
      List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨r, hr, by omega⟩⟩
  · have hneg : -absValue x ≤ x := arith_neg_absValue_le x
    exact ⟨negLe i (-rk - 1), List.mem_cons_self, by
      rw [eval_negLe_iff]; exact ⟨x, hx, by omega⟩⟩

/-! ## Reason-validity shared kernels

Local copies of Reason.lean's shared kernels (the standalone
packaging below keeps this module self-contained). -/

/-- Reason validity from clause truth (Reason.lean's
    `reason_valid_of_clause_true`). -/
theorem arith_reason_valid_of_clause_true
    {problem : Problem DomConstraint Unit}
    {l : Literal} {r : Reason}
    (hmem : l ∈ r.clause)
    (htrue : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      ∃ l' ∈ r.clause, l'.eval a = some true) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l :=
  ⟨fun a ha => htrue a ha, decide_eq_true hmem⟩

/-- Normalization transfer from the raw emitted clause. -/
theorem arith_reason_clause_norm_sf {r : Reason} {ng : Clause}
    (hcl : r = { clause := ng })
    (hnorm : ∀ q ∈ ng, q = q.norm) :
    ∀ q ∈ r.clause, q = q.norm := by
  intro q hq
  rw [hcl] at hq
  exact hnorm q hq

/-- A two-literal order clause is normalized. -/
theorem arith_order2_norm {l1 l2 : Literal}
    (h1 : l1 = l1.norm) (h2 : l2 = l2.norm) :
    ∀ q ∈ [l1, l2], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h1
  · rw [List.mem_singleton.mp hq]
    exact h2

/-- A three-literal order clause is normalized. -/
theorem arith_order3_norm {l1 l2 l3 : Literal}
    (h1 : l1 = l1.norm) (h2 : l2 = l2.norm) (h3 : l3 = l3.norm) :
    ∀ q ∈ [l1, l2, l3], q = q.norm := by
  intro q hq
  rcases List.mem_cons.mp hq with rfl | hq
  · exact h1
  · rcases List.mem_cons.mp hq with rfl | hq
    · exact h2
    · rw [List.mem_singleton.mp hq]
      exact h3

/-! ## The per-arm packs at a fitting solution -/

/-- The per-arm arithmetic pack for propMin at a fitting solution:
    the min-equation and the five domain bounds. -/
theorem minSlot_pack {st : State} {a : Assignment} {i j k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.minSlot i j k).SatisfiedBy a)
    {xi' xi yj' yj zk' : Int}
    (hxi' : domMinI (st.domains.getD i []) = some xi')
    (hxi : domMaxI (st.domains.getD i []) = some xi)
    (hyj' : domMinI (st.domains.getD j []) = some yj')
    (hyj : domMaxI (st.domains.getD j []) = some yj)
    (hzk' : domMinI (st.domains.getD k []) = some zk') :
    ∃ x y z,
      slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z ∧ min x y = z ∧
      xi' ≤ x ∧ x ≤ xi ∧ yj' ≤ y ∧ y ≤ yj ∧ zk' ≤ z := by
  obtain ⟨x, y, z, hx, hy, hz, hmin⟩ := minSlot_views a i j k hcons
  exact ⟨x, y, z, hx, hy, hz, hmin,
    fits_min_bound hfit hxi' hx, fits_max_bound hfit hxi hx,
    fits_min_bound hfit hyj' hy, fits_max_bound hfit hyj hy,
    fits_min_bound hfit hzk' hz⟩

/-- The per-arm arithmetic pack for propMax at a fitting solution. -/
theorem maxSlot_pack {st : State} {a : Assignment} {i j k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.maxSlot i j k).SatisfiedBy a)
    {xi' xi yj' yj zk : Int}
    (hxi' : domMinI (st.domains.getD i []) = some xi')
    (hxi : domMaxI (st.domains.getD i []) = some xi)
    (hyj' : domMinI (st.domains.getD j []) = some yj')
    (hyj : domMaxI (st.domains.getD j []) = some yj)
    (hzk : domMaxI (st.domains.getD k []) = some zk) :
    ∃ x y z,
      slotInt a i = some x ∧ slotInt a j = some y ∧
      slotInt a k = some z ∧ max x y = z ∧
      xi' ≤ x ∧ x ≤ xi ∧ yj' ≤ y ∧ y ≤ yj ∧ z ≤ zk := by
  obtain ⟨x, y, z, hx, hy, hz, hmax⟩ := maxSlot_views a i j k hcons
  exact ⟨x, y, z, hx, hy, hz, hmax,
    fits_min_bound hfit hxi' hx, fits_max_bound hfit hxi hx,
    fits_min_bound hfit hyj' hy, fits_max_bound hfit hyj hy,
    fits_max_bound hfit hzk hz⟩

/-- The per-arm arithmetic pack for propAbs at a fitting solution. -/
theorem absSlot_pack {st : State} {a : Assignment} {i k : Nat}
    (hfit : Core.Assignment.Fits st.domains a)
    (hcons : (DomConstraint.absSlot i k).SatisfiedBy a)
    {xi' xi rk : Int}
    (hxi' : domMinI (st.domains.getD i []) = some xi')
    (hxi : domMaxI (st.domains.getD i []) = some xi)
    (hrk : domMaxI (st.domains.getD k []) = some rk) :
    ∃ x r,
      slotInt a i = some x ∧ slotInt a k = some r ∧ absValue x = r ∧
      xi' ≤ x ∧ x ≤ xi ∧ r ≤ rk := by
  obtain ⟨x, r, hx, hr, habs⟩ := absSlot_views a i k hcons
  exact ⟨x, r, hx, hr, habs,
    fits_min_bound hfit hxi' hx, fits_max_bound hfit hxi hx,
    fits_max_bound hfit hrk hr⟩

/-! ## propMin soundness: `min x y = z` over slots i j k -/

/-- The propagator of a `minSlot i j k` constraint: implied-literal
    soundness, conflict soundness, and entitlement, at every state. -/
theorem propMin_safe (st : State) (i j k : Nat) :
    (∀ l r, propMin st i j k = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.minSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propMin st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.minSlot i j k).SatisfiedBy a → False) ∧
    (∀ c, propMin st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.minSlot i j k).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · -- implied-literal soundness
    intro l r hrun a hfit hcons
    unfold propMin at hrun
    split at hrun
    next _ _ _ _ _ xi' xi yj' yj zk' hxi' hxi hyj' hyj hzk' =>
      rcases firstEvent_mem
          [narrowLo st k (min xi' yj')
              [negLe k (min xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
           narrowHi st k (min xi yj)
              [posLe k (min xi yj), negLe i xi, negLe j yj],
           narrowLo st i zk' [negLe i (zk' - 1), posLe k (zk' - 1)],
           narrowLo st j zk' [negLe j (zk' - 1), posLe k (zk' - 1)]]
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨x, y, z, hx, hy, hz, hmin, b1, b2, b3, b4, b5⟩ :=
          minSlot_pack hfit hcons hxi' hxi hyj' hyj hzk'
        rcases List.mem_cons.mp hmem with h1' | hrest1
        · -- arm 1: implied negLe k (min xi' yj' − 1)
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
          subst hl; rw [eval_negLe_iff]
          exact ⟨z, hz, by omega⟩
        · rcases List.mem_cons.mp hrest1 with h2' | hrest2
          · -- arm 2: implied posLe k (min xi yj)
            obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h2')
            subst hl; rw [eval_posLe_iff]
            exact ⟨z, hz, by omega⟩
          · rcases List.mem_cons.mp hrest2 with h3' | hrest3
            · -- arm 3: implied negLe i (zk'−1)
              obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h3')
              subst hl; rw [eval_negLe_iff]
              exact ⟨x, hx, by omega⟩
            · -- arm 4: implied negLe j (zk'−1)
              obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm
                (List.mem_singleton.mp hrest3))
              subst hl; rw [eval_negLe_iff]
              exact ⟨y, hy, by omega⟩
    next => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · -- conflict soundness: the bounds contradict min x y = z at
      -- every fitting solution
      intro c hrun a hfit hcons
      unfold propMin at hrun
      split at hrun
      next _ _ _ _ _ xi' xi yj' yj zk' hxi' hxi hyj' hyj hzk' =>
        rcases firstEvent_mem
            [narrowLo st k (min xi' yj')
                [negLe k (min xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
             narrowHi st k (min xi yj)
                [posLe k (min xi yj), negLe i xi, negLe j yj],
             narrowLo st i zk' [negLe i (zk' - 1), posLe k (zk' - 1)],
             narrowLo st j zk' [negLe j (zk' - 1), posLe k (zk' - 1)]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · obtain ⟨x, y, z, hx, hy, hz, hmin, b1, b2, b3, b4, b5⟩ :=
              minSlot_pack hfit hcons hxi' hxi hyj' hyj hzk'
          rcases List.mem_cons.mp hmem with h1' | hrest1
          · -- arm 1 conflict: mx_k < min xi' yj'; but z ≥ that
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
            have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
            omega
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · -- arm 2 conflict: mn_k > min xi yj; but z ≤ that
              obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                narrowHi_conflict_inv (Eq.symm h2')
              have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
              have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
              omega
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · -- arm 3 conflict: mx_i < zk'; but x ≥ z ≥ zk'
                obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
                  narrowLo_conflict_inv (Eq.symm h3')
                have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
                have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
                omega
              · -- arm 4 conflict: mx_j < zk'; but y ≥ z ≥ zk'
                obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
                  narrowLo_conflict_inv (Eq.symm
                    (List.mem_singleton.mp hrest3))
                have hmny : mn ≤ y := fits_min_bound hfit hmn hy
                have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
                omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · -- entitlement: each nogood is integer-valid under
      -- min x y = z at a fitting solution
      intro c hrun a hfit hcons
      unfold propMin at hrun
      split at hrun
      next _ _ _ _ _ xi' xi yj' yj zk' hxi' hxi hyj' hyj hzk' =>
        rcases firstEvent_mem
            [narrowLo st k (min xi' yj')
                [negLe k (min xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
             narrowHi st k (min xi yj)
                [posLe k (min xi yj), negLe i xi, negLe j yj],
             narrowLo st i zk' [negLe i (zk' - 1), posLe k (zk' - 1)],
             narrowLo st j zk' [negLe j (zk' - 1), posLe k (zk' - 1)]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            rw [hcc]
            exact arith_min_nogood_lo_k_true hcons
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm h2')
              rw [hcc]
              exact arith_min_nogood_hi_k_true hcons
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨_, _, _, _, _, hcc⟩ :=
                  narrowLo_conflict_inv (Eq.symm h3')
                rw [hcc]
                exact arith_min_nogood_lo_i_true hcons
              · obtain ⟨_, _, _, _, _, hcc⟩ :=
                  narrowLo_conflict_inv (Eq.symm
                    (List.mem_singleton.mp hrest3))
                rw [hcc]
                exact arith_min_nogood_lo_j_true hcons
      next => exact absurd hrun (by intro hc; simp at hc)

/-! ## propMax soundness: `max x y = z` over slots i j k -/

/-- The propagator of a `maxSlot i j k` constraint: the dual triple
    of `propMin_safe`. -/
theorem propMax_safe (st : State) (i j k : Nat) :
    (∀ l r, propMax st i j k = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.maxSlot i j k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propMax st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.maxSlot i j k).SatisfiedBy a → False) ∧
    (∀ c, propMax st i j k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.maxSlot i j k).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · -- implied-literal soundness
    intro l r hrun a hfit hcons
    unfold propMax at hrun
    split at hrun
    next _ _ _ _ _ xi' xi yj' yj zk hxi' hxi hyj' hyj hzk =>
      rcases firstEvent_mem
          [narrowLo st k (max xi' yj')
              [negLe k (max xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
           narrowHi st k (max xi yj)
              [posLe k (max xi yj), negLe i xi, negLe j yj],
           narrowHi st i zk [posLe i zk, negLe k zk],
           narrowHi st j zk [posLe j zk, negLe k zk]]
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨x, y, z, hx, hy, hz, hmax, b1, b2, b3, b4, b5⟩ :=
          maxSlot_pack hfit hcons hxi' hxi hyj' hyj hzk
        rcases List.mem_cons.mp hmem with h1' | hrest1
        · -- arm 1: implied negLe k (max xi' yj' − 1)
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
          subst hl; rw [eval_negLe_iff]
          exact ⟨z, hz, by omega⟩
        · rcases List.mem_cons.mp hrest1 with h2' | hrest2
          · -- arm 2: implied posLe k (max xi yj)
            obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h2')
            subst hl; rw [eval_posLe_iff]
            exact ⟨z, hz, by omega⟩
          · rcases List.mem_cons.mp hrest2 with h3' | hrest3
            · -- arm 3: implied posLe i zk
              obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h3')
              subst hl; rw [eval_posLe_iff]
              exact ⟨x, hx, by omega⟩
            · -- arm 4: implied posLe j zk
              obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm
                (List.mem_singleton.mp hrest3))
              subst hl; rw [eval_posLe_iff]
              exact ⟨y, hy, by omega⟩
    next => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · -- conflict soundness
      intro c hrun a hfit hcons
      unfold propMax at hrun
      split at hrun
      next _ _ _ _ _ xi' xi yj' yj zk hxi' hxi hyj' hyj hzk =>
        rcases firstEvent_mem
            [narrowLo st k (max xi' yj')
                [negLe k (max xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
             narrowHi st k (max xi yj)
                [posLe k (max xi yj), negLe i xi, negLe j yj],
             narrowHi st i zk [posLe i zk, negLe k zk],
             narrowHi st j zk [posLe j zk, negLe k zk]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · obtain ⟨x, y, z, hx, hy, hz, hmax, b1, b2, b3, b4, b5⟩ :=
              maxSlot_pack hfit hcons hxi' hxi hyj' hyj hzk
          rcases List.mem_cons.mp hmem with h1' | hrest1
          · -- arm 1 conflict: mx_k < max xi' yj'; but z ≥ that
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
            have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
            omega
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · -- arm 2 conflict: mn_k > max xi yj; but z ≤ that
              obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                narrowHi_conflict_inv (Eq.symm h2')
              have hmnz : mn ≤ z := fits_min_bound hfit hmn hz
              have hmxz : z ≤ mx := fits_max_bound hfit hmx hz
              omega
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · -- arm 3 conflict: mn_i > zk; but x ≤ z ≤ zk
                obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                  narrowHi_conflict_inv (Eq.symm h3')
                have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
                have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
                omega
              · -- arm 4 conflict: mn_j > zk; but y ≤ z ≤ zk
                obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                  narrowHi_conflict_inv (Eq.symm
                    (List.mem_singleton.mp hrest3))
                have hmny : mn ≤ y := fits_min_bound hfit hmn hy
                have hmxy : y ≤ mx := fits_max_bound hfit hmx hy
                omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · -- entitlement
      intro c hrun a hfit hcons
      unfold propMax at hrun
      split at hrun
      next _ _ _ _ _ xi' xi yj' yj zk hxi' hxi hyj' hyj hzk =>
        rcases firstEvent_mem
            [narrowLo st k (max xi' yj')
                [negLe k (max xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
             narrowHi st k (max xi yj)
                [posLe k (max xi yj), negLe i xi, negLe j yj],
             narrowHi st i zk [posLe i zk, negLe k zk],
             narrowHi st j zk [posLe j zk, negLe k zk]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            rw [hcc]
            exact arith_max_nogood_lo_k_true hcons
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm h2')
              rw [hcc]
              exact arith_max_nogood_hi_k_true hcons
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨_, _, _, _, _, hcc⟩ :=
                  narrowHi_conflict_inv (Eq.symm h3')
                rw [hcc]
                exact arith_max_nogood_hi_i_true hcons
              · obtain ⟨_, _, _, _, _, hcc⟩ :=
                  narrowHi_conflict_inv (Eq.symm
                    (List.mem_singleton.mp hrest3))
                rw [hcc]
                exact arith_max_nogood_hi_j_true hcons
      next => exact absurd hrun (by intro hc; simp at hc)

/-! ## propAbs soundness: `r = |x|` over slots i k -/

/-- The propagator of an `absSlot i k` constraint: implied-literal
    soundness, conflict soundness, and entitlement, at every state. -/
theorem propAbs_safe (st : State) (i k : Nat) :
    (∀ l r, propAbs st i k = .implied l r →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.absSlot i k).SatisfiedBy a →
        l.eval a = some true) ∧
    (∀ c, propAbs st i k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.absSlot i k).SatisfiedBy a → False) ∧
    (∀ c, propAbs st i k = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.absSlot i k).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  constructor
  · -- implied-literal soundness
    intro l r hrun a hfit hcons
    unfold propAbs at hrun
    split at hrun
    next _ _ _ xi' xi rk hxi' hxi hrk =>
      rcases firstEvent_mem
          [narrowLo st k 0 [negLe k (-1)],
           narrowLo st k (absCornerMin xi' xi)
              [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1), negLe i xi],
           narrowHi st k (max (absValue xi') (absValue xi))
              [posLe k (max (absValue xi') (absValue xi)),
                posLe i (xi' - 1), negLe i xi],
           narrowHi st i rk [posLe i rk, negLe k rk],
           narrowLo st i (-rk) [negLe i (-rk - 1), negLe k rk]]
          (.implied l r) hrun with hstable | hmem
      · exact absurd hstable (by intro hc; cases hc)
      · obtain ⟨x, r2, hx, hr, habs, b1, b2, b3⟩ :=
          absSlot_pack hfit hcons hxi' hxi hrk
        have hnonneg : 0 ≤ r2 := by
          rw [← habs]; exact arith_absValue_nonneg x
        have hcorner : absCornerMin xi' xi ≤ r2 := by
          rw [← habs]; exact arith_absCornerMin_le b1 b2
        have hrange : r2 ≤ max (absValue xi') (absValue xi) := by
          rw [← habs]; exact arith_absValue_le_range b1 b2
        have hlex : x ≤ r2 := by
          rw [← habs]; exact arith_le_absValue x
        have hneg : -r2 ≤ x := by
          rw [← habs]; exact arith_neg_absValue_le x
        rcases List.mem_cons.mp hmem with h1' | hrest1
        · -- arm 0: implied negLe k (−1); r = |x| ≥ 0
          obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1')
          subst hl; rw [eval_negLe_iff]
          exact ⟨r2, hr, by omega⟩
        · rcases List.mem_cons.mp hrest1 with h2' | hrest2
          · -- arm 1: implied negLe k (absCornerMin xi' xi − 1)
            obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h2')
            subst hl; rw [eval_negLe_iff]
            exact ⟨r2, hr, by omega⟩
          · rcases List.mem_cons.mp hrest2 with h3' | hrest3
            · -- arm 2: implied posLe k (max |xi'| |xi|)
              obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h3')
              subst hl; rw [eval_posLe_iff]
              exact ⟨r2, hr, by omega⟩
            · rcases List.mem_cons.mp hrest3 with h4' | hrest4
              · -- arm 3: implied posLe i rk
                obtain ⟨hl, _⟩ := narrowHi_implied_inv (Eq.symm h4')
                subst hl; rw [eval_posLe_iff]
                exact ⟨x, hx, by omega⟩
              · -- arm 4: implied negLe i (−rk−1)
                obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm
                  (List.mem_singleton.mp hrest4))
                subst hl; rw [eval_negLe_iff]
                exact ⟨x, hx, by omega⟩
    next => exact absurd hrun (by intro hc; simp at hc)
  · constructor
    · -- conflict soundness: the bounds contradict r = |x| at
      -- every fitting solution
      intro c hrun a hfit hcons
      unfold propAbs at hrun
      split at hrun
      next _ _ _ xi' xi rk hxi' hxi hrk =>
        rcases firstEvent_mem
            [narrowLo st k 0 [negLe k (-1)],
             narrowLo st k (absCornerMin xi' xi)
                [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1), negLe i xi],
             narrowHi st k (max (absValue xi') (absValue xi))
                [posLe k (max (absValue xi') (absValue xi)),
                  posLe i (xi' - 1), negLe i xi],
             narrowHi st i rk [posLe i rk, negLe k rk],
             narrowLo st i (-rk) [negLe i (-rk - 1), negLe k rk]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · obtain ⟨x, r2, hx, hr, habs, b1, b2, b3⟩ :=
              absSlot_pack hfit hcons hxi' hxi hrk
          have hnonneg : 0 ≤ r2 := by
            rw [← habs]; exact arith_absValue_nonneg x
          have hcorner : absCornerMin xi' xi ≤ r2 := by
            rw [← habs]; exact arith_absCornerMin_le b1 b2
          have hrange : r2 ≤ max (absValue xi') (absValue xi) := by
            rw [← habs]; exact arith_absValue_le_range b1 b2
          have hlex : x ≤ r2 := by
            rw [← habs]; exact arith_le_absValue x
          have hneg : -r2 ≤ x := by
            rw [← habs]; exact arith_neg_absValue_le x
          rcases List.mem_cons.mp hmem with h1' | hrest1
          · -- arm 0 conflict: mx_k < 0; but r = |x| ≥ 0
            obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            have hmnz : mn ≤ r2 := fits_min_bound hfit hmn hr
            have hmxz : r2 ≤ mx := fits_max_bound hfit hmx hr
            omega
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · -- arm 1 conflict: mx_k < absCornerMin xi' xi;
              -- but r = |x| ≥ that corner
              obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
                narrowLo_conflict_inv (Eq.symm h2')
              have hmnz : mn ≤ r2 := fits_min_bound hfit hmn hr
              have hmxz : r2 ≤ mx := fits_max_bound hfit hmx hr
              omega
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · -- arm 2 conflict: mn_k > max |xi'| |xi|;
                -- but r = |x| ≤ that corner
                obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                  narrowHi_conflict_inv (Eq.symm h3')
                have hmnz : mn ≤ r2 := fits_min_bound hfit hmn hr
                have hmxz : r2 ≤ mx := fits_max_bound hfit hmx hr
                omega
              · rcases List.mem_cons.mp hrest3 with h4' | hrest4
                · -- arm 3 conflict: mn_i > rk; but x ≤ |x| = r ≤ rk
                  obtain ⟨mn, mx, hmn, hmx, hgt, _⟩ :=
                    narrowHi_conflict_inv (Eq.symm h4')
                  have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
                  have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
                  omega
                · -- arm 4 conflict: mx_i < −rk; but x ≥ −|x| ≥ −rk
                  obtain ⟨mn, mx, hmn, hmx, hlt, _⟩ :=
                    narrowLo_conflict_inv (Eq.symm
                      (List.mem_singleton.mp hrest4))
                  have hmnx : mn ≤ x := fits_min_bound hfit hmn hx
                  have hmxx : x ≤ mx := fits_max_bound hfit hmx hx
                  omega
      next => exact absurd hrun (by intro hc; simp at hc)
    · -- entitlement: each nogood is integer-valid under r = |x|
      -- at a fitting solution
      intro c hrun a hfit hcons
      unfold propAbs at hrun
      split at hrun
      next _ _ _ xi' xi rk hxi' hxi hrk =>
        rcases firstEvent_mem
            [narrowLo st k 0 [negLe k (-1)],
             narrowLo st k (absCornerMin xi' xi)
                [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1), negLe i xi],
             narrowHi st k (max (absValue xi') (absValue xi))
                [posLe k (max (absValue xi') (absValue xi)),
                  posLe i (xi' - 1), negLe i xi],
             narrowHi st i rk [posLe i rk, negLe k rk],
             narrowLo st i (-rk) [negLe i (-rk - 1), negLe k rk]]
            (.conflict c) hrun with hstable | hmem
        · exact absurd hstable (by intro hc; cases hc)
        · rcases List.mem_cons.mp hmem with h1' | hrest1
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm h1')
            rw [hcc]
            exact arith_abs_nogood_zero_true hcons
          · rcases List.mem_cons.mp hrest1 with h2' | hrest2
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowLo_conflict_inv (Eq.symm h2')
              rw [hcc]
              exact arith_abs_nogood_corner_lo_true hcons
            · rcases List.mem_cons.mp hrest2 with h3' | hrest3
              · obtain ⟨_, _, _, _, _, hcc⟩ :=
                  narrowHi_conflict_inv (Eq.symm h3')
                rw [hcc]
                exact arith_abs_nogood_corner_hi_true hcons
              · rcases List.mem_cons.mp hrest3 with h4' | hrest4
                · obtain ⟨_, _, _, _, _, hcc⟩ :=
                    narrowHi_conflict_inv (Eq.symm h4')
                  rw [hcc]
                  exact arith_abs_nogood_hi_i_true hcons
                · obtain ⟨_, _, _, _, _, hcc⟩ :=
                    narrowLo_conflict_inv (Eq.symm
                      (List.mem_singleton.mp hrest4))
                  rw [hcc]
                  exact arith_abs_nogood_lo_i_true hcons
      next => exact absurd hrun (by intro hc; simp at hc)

/-! ## State-free reason validity (Reason.Valid + normalization) -/

/-- The state-free reason-validity lemma for the `minSlot` family:
    all four nogoods are integer-valid under the constraint
    alone. -/
theorem propMin_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.minSlot i j k).SatisfiedBy a)
    (hrun : propMin st i j k = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propMin at hrun
  split at hrun
  next _ _ _ _ _ xi' xi yj' yj zk' hxi' hxi hyj' hyj hzk' =>
    rcases firstEvent_mem
        [narrowLo st k (min xi' yj')
            [negLe k (min xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
         narrowHi st k (min xi yj)
            [posLe k (min xi yj), negLe i xi, negLe j yj],
         narrowLo st i zk' [negLe i (zk' - 1), posLe k (zk' - 1)],
         narrowLo st j zk' [negLe j (zk' - 1), posLe k (zk' - 1)]]
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · -- emission 1: implied negLe k (min xi' yj' − 1), nogood
        -- [negLe k (min xi' yj' − 1), posLe i (xi'−1), posLe j (yj'−1)]
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h1')
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
          arith_reason_clause_norm_sf hcl
            (arith_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe k (min xi' yj' - 1), posLe i (xi' - 1),
              posLe j (yj' - 1)] := by rw [hcl]
        rw [hcl2]
        exact arith_min_nogood_lo_k_true (hprob _ ha)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · -- emission 2: implied posLe k (min xi yj)
          obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm h2')
          have hpivmem : l ∈ r.clause := by
            subst hl; rw [hcl]; exact List.mem_cons_self
          refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
            arith_reason_clause_norm_sf hcl
              (arith_order3_norm rfl rfl rfl)⟩
          intro a ha
          have hcl2 : r.clause =
              [posLe k (min xi yj), negLe i xi, negLe j yj] := by
            rw [hcl]
          rw [hcl2]
          exact arith_min_nogood_hi_k_true (hprob _ ha)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · -- emission 3: implied negLe i (zk'−1), 2-literal nogood
            obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h3')
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
              arith_reason_clause_norm_sf hcl
                (arith_order2_norm rfl rfl)⟩
            intro a ha
            have hcl2 : r.clause =
                [negLe i (zk' - 1), posLe k (zk' - 1)] := by rw [hcl]
            rw [hcl2]
            exact arith_min_nogood_lo_i_true (hprob _ ha)
          · -- emission 4: implied negLe j (zk'−1)
            obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm
              (List.mem_singleton.mp hrest3))
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
              arith_reason_clause_norm_sf hcl
                (arith_order2_norm rfl rfl)⟩
            intro a ha
            have hcl2 : r.clause =
                [negLe j (zk' - 1), posLe k (zk' - 1)] := by rw [hcl]
            rw [hcl2]
            exact arith_min_nogood_lo_j_true (hprob _ ha)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free reason-validity lemma for the `maxSlot` family. -/
theorem propMax_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i j k : Nat} {l : Literal} {r : Reason}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.maxSlot i j k).SatisfiedBy a)
    (hrun : propMax st i j k = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propMax at hrun
  split at hrun
  next _ _ _ _ _ xi' xi yj' yj zk hxi' hxi hyj' hyj hzk =>
    rcases firstEvent_mem
        [narrowLo st k (max xi' yj')
            [negLe k (max xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
         narrowHi st k (max xi yj)
            [posLe k (max xi yj), negLe i xi, negLe j yj],
         narrowHi st i zk [posLe i zk, negLe k zk],
         narrowHi st j zk [posLe j zk, negLe k zk]]
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h1')
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
          arith_reason_clause_norm_sf hcl
            (arith_order3_norm rfl rfl rfl)⟩
        intro a ha
        have hcl2 : r.clause =
            [negLe k (max xi' yj' - 1), posLe i (xi' - 1),
              posLe j (yj' - 1)] := by rw [hcl]
        rw [hcl2]
        exact arith_max_nogood_lo_k_true (hprob _ ha)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm h2')
          have hpivmem : l ∈ r.clause := by
            subst hl; rw [hcl]; exact List.mem_cons_self
          refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
            arith_reason_clause_norm_sf hcl
              (arith_order3_norm rfl rfl rfl)⟩
          intro a ha
          have hcl2 : r.clause =
              [posLe k (max xi yj), negLe i xi, negLe j yj] := by
            rw [hcl]
          rw [hcl2]
          exact arith_max_nogood_hi_k_true (hprob _ ha)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm h3')
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
              arith_reason_clause_norm_sf hcl
                (arith_order2_norm rfl rfl)⟩
            intro a ha
            have hcl2 : r.clause =
                [posLe i zk, negLe k zk] := by rw [hcl]
            rw [hcl2]
            exact arith_max_nogood_hi_i_true (hprob _ ha)
          · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm
              (List.mem_singleton.mp hrest3))
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
              arith_reason_clause_norm_sf hcl
                (arith_order2_norm rfl rfl)⟩
            intro a ha
            have hcl2 : r.clause =
                [posLe j zk, negLe k zk] := by rw [hcl]
            rw [hcl2]
            exact arith_max_nogood_hi_j_true (hprob _ ha)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free reason-validity lemma for the `absSlot`
    family. -/
theorem propAbs_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {i k : Nat} {l : Literal} {r : Reason}
    (hprob : DomConstraint.absSlot i k ∈ problem.constraints)
    (hrun : propAbs st i k = .implied l r) :
    Reason.Valid problem DomConstraint.SatisfiedBy r l ∧
      (∀ q ∈ r.clause, q = q.norm) := by
  unfold propAbs at hrun
  split at hrun
  next _ _ _ xi' xi rk hxi' hxi hrk =>
    rcases firstEvent_mem
        [narrowLo st k 0 [negLe k (-1)],
         narrowLo st k (absCornerMin xi' xi)
            [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1), negLe i xi],
         narrowHi st k (max (absValue xi') (absValue xi))
            [posLe k (max (absValue xi') (absValue xi)),
              posLe i (xi' - 1), negLe i xi],
         narrowHi st i rk [posLe i rk, negLe k rk],
         narrowLo st i (-rk) [negLe i (-rk - 1), negLe k rk]]
        (.implied l r) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · -- emission 0: implied negLe k (−1), unit nogood
        obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h1')
        have hpivmem : l ∈ r.clause := by
          subst hl; rw [hcl]; exact List.mem_cons_self
        refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
          arith_reason_clause_norm_sf hcl
            (fun q hq => by
              rcases List.mem_cons.mp hq with rfl | hq
              · exact rfl
              · exact absurd hq (by simp))⟩
        intro a ha
        have hcl2 : r.clause = [negLe k (-1)] := by rw [hcl]
        rw [hcl2]
        exact arith_abs_nogood_zero_true (ha.2 _ hprob)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · -- emission 1: the corner-min nogood
          obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h2')
          have hpivmem : l ∈ r.clause := by
            subst hl; rw [hcl]; exact List.mem_cons_self
          refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
            arith_reason_clause_norm_sf hcl
              (arith_order3_norm rfl rfl rfl)⟩
          intro a ha
          have hcl2 : r.clause =
              [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1),
                negLe i xi] := by rw [hcl]
          rw [hcl2]
          exact arith_abs_nogood_corner_lo_true (ha.2 _ hprob)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · -- emission 2: the corner-max nogood
            obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm h3')
            have hpivmem : l ∈ r.clause := by
              subst hl; rw [hcl]; exact List.mem_cons_self
            refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
              arith_reason_clause_norm_sf hcl
                (arith_order3_norm rfl rfl rfl)⟩
            intro a ha
            have hcl2 : r.clause =
                [posLe k (max (absValue xi') (absValue xi)),
                  posLe i (xi' - 1), negLe i xi] := by rw [hcl]
            rw [hcl2]
            exact arith_abs_nogood_corner_hi_true (ha.2 _ hprob)
          · rcases List.mem_cons.mp hrest3 with h4' | hrest4
            · -- emission 3: implied posLe i rk, 2-literal nogood
              obtain ⟨hl, hcl⟩ := narrowHi_implied_inv (Eq.symm h4')
              have hpivmem : l ∈ r.clause := by
                subst hl; rw [hcl]; exact List.mem_cons_self
              refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
                arith_reason_clause_norm_sf hcl
                  (arith_order2_norm rfl rfl)⟩
              intro a ha
              have hcl2 : r.clause =
                  [posLe i rk, negLe k rk] := by rw [hcl]
              rw [hcl2]
              exact arith_abs_nogood_hi_i_true (ha.2 _ hprob)
            · -- emission 4: implied negLe i (−rk−1)
              obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm
                (List.mem_singleton.mp hrest4))
              have hpivmem : l ∈ r.clause := by
                subst hl; rw [hcl]; exact List.mem_cons_self
              refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
                arith_reason_clause_norm_sf hcl
                  (arith_order2_norm rfl rfl)⟩
              intro a ha
              have hcl2 : r.clause =
                  [negLe i (-rk - 1), negLe k rk] := by rw [hcl]
              rw [hcl2]
              exact arith_abs_nogood_lo_i_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-! ## State-free conflict entitlement -/

/-- The state-free conflict entitlement for the `minSlot` family:
    every conflict clause is one of the four nogoods, so it carries
    a true literal at every internal problem solution. -/
theorem propMin_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i j k : Nat}
    {c : Clause}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.minSlot i j k).SatisfiedBy a)
    (hrun : propMin st i j k = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propMin at hrun
  split at hrun
  next _ _ _ _ _ xi' xi yj' yj zk' hxi' hxi hyj' hyj hzk' =>
    rcases firstEvent_mem
        [narrowLo st k (min xi' yj')
            [negLe k (min xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
         narrowHi st k (min xi yj)
            [posLe k (min xi yj), negLe i xi, negLe j yj],
         narrowLo st i zk' [negLe i (zk' - 1), posLe k (zk' - 1)],
         narrowLo st j zk' [negLe j (zk' - 1), posLe k (zk' - 1)]]
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm h1')
        rw [hcc]
        exact arith_min_nogood_lo_k_true (hprob _ ha)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · obtain ⟨_, _, _, _, _, hcc⟩ :=
            narrowHi_conflict_inv (Eq.symm h2')
          rw [hcc]
          exact arith_min_nogood_hi_k_true (hprob _ ha)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm h3')
            rw [hcc]
            exact arith_min_nogood_lo_i_true (hprob _ ha)
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowLo_conflict_inv (Eq.symm
                (List.mem_singleton.mp hrest3))
            rw [hcc]
            exact arith_min_nogood_lo_j_true (hprob _ ha)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free conflict entitlement for the `maxSlot` family. -/
theorem propMax_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i j k : Nat}
    {c : Clause}
    (hprob : ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
      (DomConstraint.maxSlot i j k).SatisfiedBy a)
    (hrun : propMax st i j k = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propMax at hrun
  split at hrun
  next _ _ _ _ _ xi' xi yj' yj zk hxi' hxi hyj' hyj hzk =>
    rcases firstEvent_mem
        [narrowLo st k (max xi' yj')
            [negLe k (max xi' yj' - 1), posLe i (xi' - 1), posLe j (yj' - 1)],
         narrowHi st k (max xi yj)
            [posLe k (max xi yj), negLe i xi, negLe j yj],
         narrowHi st i zk [posLe i zk, negLe k zk],
         narrowHi st j zk [posLe j zk, negLe k zk]]
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm h1')
        rw [hcc]
        exact arith_max_nogood_lo_k_true (hprob _ ha)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · obtain ⟨_, _, _, _, _, hcc⟩ :=
            narrowHi_conflict_inv (Eq.symm h2')
          rw [hcc]
          exact arith_max_nogood_hi_k_true (hprob _ ha)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm h3')
            rw [hcc]
            exact arith_max_nogood_hi_i_true (hprob _ ha)
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm
                (List.mem_singleton.mp hrest3))
            rw [hcc]
            exact arith_max_nogood_hi_j_true (hprob _ ha)
  next => exact absurd hrun (by intro hc; simp at hc)

/-- The state-free conflict entitlement for the `absSlot` family. -/
theorem propAbs_entitled
    {problem : Problem DomConstraint Unit} {st : State} {i k : Nat}
    {c : Clause}
    (hprob : DomConstraint.absSlot i k ∈ problem.constraints)
    (hrun : propAbs st i k = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propAbs at hrun
  split at hrun
  next _ _ _ xi' xi rk hxi' hxi hrk =>
    rcases firstEvent_mem
        [narrowLo st k 0 [negLe k (-1)],
         narrowLo st k (absCornerMin xi' xi)
            [negLe k (absCornerMin xi' xi - 1), posLe i (xi' - 1), negLe i xi],
         narrowHi st k (max (absValue xi') (absValue xi))
            [posLe k (max (absValue xi') (absValue xi)),
              posLe i (xi' - 1), negLe i xi],
         narrowHi st i rk [posLe i rk, negLe k rk],
         narrowLo st i (-rk) [negLe i (-rk - 1), negLe k rk]]
        (.conflict c) hrun with hstable | hmem
    · exact absurd hstable (by intro hc; cases hc)
    · rcases List.mem_cons.mp hmem with h1' | hrest1
      · obtain ⟨_, _, _, _, _, hcc⟩ :=
          narrowLo_conflict_inv (Eq.symm h1')
        rw [hcc]
        exact arith_abs_nogood_zero_true (ha.2 _ hprob)
      · rcases List.mem_cons.mp hrest1 with h2' | hrest2
        · obtain ⟨_, _, _, _, _, hcc⟩ :=
            narrowLo_conflict_inv (Eq.symm h2')
          rw [hcc]
          exact arith_abs_nogood_corner_lo_true (ha.2 _ hprob)
        · rcases List.mem_cons.mp hrest2 with h3' | hrest3
          · obtain ⟨_, _, _, _, _, hcc⟩ :=
              narrowHi_conflict_inv (Eq.symm h3')
            rw [hcc]
            exact arith_abs_nogood_corner_hi_true (ha.2 _ hprob)
          · rcases List.mem_cons.mp hrest3 with h4' | hrest4
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm h4')
              rw [hcc]
              exact arith_abs_nogood_hi_i_true (ha.2 _ hprob)
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowLo_conflict_inv (Eq.symm
                  (List.mem_singleton.mp hrest4))
              rw [hcc]
              exact arith_abs_nogood_lo_i_true (ha.2 _ hprob)
  next => exact absurd hrun (by intro hc; simp at hc)

/-! ## L3: the pair / two-element array shapes reduce to the slot forms

`minPair`/`maxPair` over three SLOT operands imply the corresponding
`minSlot`/`maxSlot` (NOT the two-element `minGen`/`maxGen`, whose
`minValue` reading ignores a non-integer tail element) (a bang read `a[i]!` is an integer only when
the slot is in range, since the default value is Boolean). -/

theorem slotBang_int {a : List Value} {i : Nat} {p : Int}
    (h : a[i]! = .int p) : a[i]? = some (.int p) := by
  by_cases hi : i < a.length
  · rw [getElem!_pos a i hi] at h
    rw [List.getElem?_eq_getElem hi]; exact congrArg some h
  · rw [getElem!_neg a i hi] at h
    exact absurd h (by intro hc; cases hc)

theorem minPair_imp_minSlot (i j k : Nat) (a : Assignment)
    (h : (DomConstraint.minPair (.slot i) (.slot j) (.slot k)).SatisfiedBy a) :
    (DomConstraint.minSlot i j k).SatisfiedBy a := by
  obtain ⟨p, q, hp, hq, hr⟩ := h
  simp only [DomIntArg.read_slot] at hp hq hr
  exact ⟨p, q, _, slotBang_int hp, slotBang_int hq, slotBang_int hr, rfl⟩

theorem maxPair_imp_maxSlot (i j k : Nat) (a : Assignment)
    (h : (DomConstraint.maxPair (.slot i) (.slot j) (.slot k)).SatisfiedBy a) :
    (DomConstraint.maxSlot i j k).SatisfiedBy a := by
  obtain ⟨p, q, hp, hq, hr⟩ := h
  simp only [DomIntArg.read_slot] at hp hq hr
  exact ⟨p, q, _, slotBang_int hp, slotBang_int hq, slotBang_int hr, rfl⟩

/-! ## The `int_div`/`int_mod` bound propagators (PLAN L7) -/

/-- The definite value of a divisor operand: a literal's integer, or a
    slot whose domain is EXACTLY the integer singleton `[.int d]` (the
    shape the frame invariant's `FixExpl` explains, which both the
    zero-divisor conflict and the divisor-matching causes consume). -/
def divPin (st : State) : DomIntArg → Option Int
  | .lit d => some d
  | .slot j =>
      match st.domains.getD j [] with
      | [.int d] => some d
      | _ => none

/-- The conflict clause of a divisor pinned to `0`: the removal literal
    `o_j ≠ 0` for a slot, the empty clause for a literal `0`. -/
def divZeroClause : DomIntArg → Clause
  | .lit _ => []
  | .slot j => [posNe j 0]

/-- The divisor-matching causes: `[j ≤ d−1, j ≥ d+1]` on a slot divisor
    (false exactly when the slot reads `d`), nothing on a literal. -/
def divMatchCauses : DomIntArg → Int → Clause
  | .lit _, _ => []
  | .slot j, d => [posLe j (d - 1), negLe j d]

/-- Forward hull of `tdiv` over `[pl, ph]` with divisor `d ≠ 0`. -/
def divResLo (d pl ph : Int) : Int := min (Int.tdiv pl d) (Int.tdiv ph d)
def divResHi (d pl ph : Int) : Int := max (Int.tdiv pl d) (Int.tdiv ph d)

/-- Mod hull over `[pl, ph]` with divisor `d ≠ 0`. -/
def modHullLo (d pl ph : Int) : Int :=
  if Int.tdiv pl d = Int.tdiv ph d then Int.tmod pl d else -(absValue d - 1)
def modHullHi (d pl ph : Int) : Int :=
  if Int.tdiv pl d = Int.tdiv ph d then Int.tmod ph d else absValue d - 1

/-- The `divGen` lower-arm reason: the pivot `k ≥ divResLo d pl ph − 1`
    with the divisor-matching and dividend-bound causes. -/
def divReasonLo (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) : Clause :=
  match o₂ with
  | .lit _ => [negLe k (divResLo d pl ph - 1), posLe i (pl - 1), negLe i ph]
  | .slot j => [negLe k (divResLo d pl ph - 1), posLe j (d - 1), negLe j d,
      posLe i (pl - 1), negLe i ph]

/-- The `divGen` upper-arm reason: the pivot `k ≤ divResHi d pl ph` with
    the divisor-matching and dividend-bound causes. -/
def divReasonHi (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) : Clause :=
  match o₂ with
  | .lit _ => [posLe k (divResHi d pl ph), posLe i (pl - 1), negLe i ph]
  | .slot j => [posLe k (divResHi d pl ph), posLe j (d - 1), negLe j d,
      posLe i (pl - 1), negLe i ph]

/-- The `modGen` lower-arm reason. -/
def modReasonLo (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) : Clause :=
  match o₂ with
  | .lit _ => [negLe k (modHullLo d pl ph - 1), posLe i (pl - 1), negLe i ph]
  | .slot j => [negLe k (modHullLo d pl ph - 1), posLe j (d - 1), negLe j d,
      posLe i (pl - 1), negLe i ph]

/-- The `modGen` upper-arm reason. -/
def modReasonHi (o₂ : DomIntArg) (i k : Nat) (d pl ph : Int) : Clause :=
  match o₂ with
  | .lit _ => [posLe k (modHullHi d pl ph), posLe i (pl - 1), negLe i ph]
  | .slot j => [posLe k (modHullHi d pl ph), posLe j (d - 1), negLe j d,
      posLe i (pl - 1), negLe i ph]

/-- The explained `int_div` bound propagator: with a definite nonzero
    divisor `d` and the dividend slot `i` bounded by `[pl, ph]`, narrow
    the result slot `k` into the truncated-quotient hull.  A divisor
    pinned to `0` is a conflict. -/
def propDiv (st : State) (o₁ o₂ r : DomIntArg) : PropagationResult :=
  match divPin st o₂ with
  | some d =>
      if d = 0 then .conflict (divZeroClause o₂)
      else
        match o₁, r with
        | .slot i, .slot k =>
            match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []) with
            | some pl, some ph =>
                firstEvent
                  [narrowLo st k (divResLo d pl ph) (divReasonLo o₂ i k d pl ph),
                   narrowHi st k (divResHi d pl ph) (divReasonHi o₂ i k d pl ph)]
            | _, _ => .stable
        | _, _ => .stable
  | none => .stable

/-- The explained `int_mod` bound propagator: the `modGen` twin of
    `propDiv`, narrowing the result slot into the truncated-remainder
    hull. -/
def propMod (st : State) (o₁ o₂ r : DomIntArg) : PropagationResult :=
  match divPin st o₂ with
  | some d =>
      if d = 0 then .conflict (divZeroClause o₂)
      else
        match o₁, r with
        | .slot i, .slot k =>
            match domMinI (st.domains.getD i []), domMaxI (st.domains.getD i []) with
            | some pl, some ph =>
                firstEvent
                  [narrowLo st k (modHullLo d pl ph) (modReasonLo o₂ i k d pl ph),
                   narrowHi st k (modHullHi d pl ph) (modReasonHi o₂ i k d pl ph)]
            | _, _ => .stable
        | _, _ => .stable
  | none => .stable

/-! ### The pinned-divisor inversion and reading lemmas -/

/-- The pinned slot domain is exactly the integer singleton `[.int d]`
    (the `FixExpl` shape the zero-divisor conflict consumes). -/
theorem divPin_slot_dom {st : State} {j : Nat} {d : Int}
    (h : divPin st (.slot j) = some d) :
    st.domains.getD j [] = [.int d] := by
  simp only [divPin] at h
  split at h
  · rename_i d' hdom
    injection h with hd
    subst hd
    exact hdom
  · exact absurd h (by simp)

/-- A pinned slot domain's integer extrema are both `d`. -/
theorem divPin_slot {st : State} {j : Nat} {d : Int}
    (h : divPin st (.slot j) = some d) :
    domMinI (st.domains.getD j []) = some d ∧
      domMaxI (st.domains.getD j []) = some d := by
  have hdom := divPin_slot_dom h
  constructor <;> (rw [hdom]; rfl)

/-- A slot int read from a `DomIntArg` bang read. -/
theorem slotInt_of_read_slot {a : Assignment} {i : Nat} {p : Int}
    (h : DomIntArg.read a (.slot i) = .int p) : slotInt a i = some p :=
  slotInt_of_int_read (slotBang_int (by simpa [DomIntArg.read_slot] using h))

/-- At a FITTING assignment, a pinned divisor reads exactly `d`. -/
theorem divPin_read {st : State} {a : Assignment} {o₂ : DomIntArg} {d : Int}
    (hfit : Core.Assignment.Fits st.domains a)
    (hpin : divPin st o₂ = some d) :
    ∀ q, DomIntArg.read a o₂ = .int q → q = d := by
  intro q hq
  cases o₂ with
  | lit d' =>
      have hd' : d' = d := by simpa [divPin] using hpin
      have hqq : d' = q := by simpa [DomIntArg.read_lit] using hq
      omega
  | slot j =>
      obtain ⟨hlo, hhi⟩ := divPin_slot hpin
      have hq' : slotInt a j = some q := slotInt_of_read_slot hq
      have h1 : d ≤ q := fits_min_bound hfit hlo hq'
      have h2 : q ≤ d := fits_max_bound hfit hhi hq'
      omega

/-- At ANY assignment, a pinned divisor either reads `d` or one of the
    divisor-matching causes is true. -/
theorem divMatch_covers {st : State} {a : Assignment} {o₂ : DomIntArg}
    {d : Int} (hpin : divPin st o₂ = some d) :
    ∀ q, DomIntArg.read a o₂ = .int q → q = d ∨
      ∃ l ∈ divMatchCauses o₂ d, l.eval a = some true := by
  intro q hq
  cases o₂ with
  | lit d' =>
      have hd' : d' = d := by simpa [divPin] using hpin
      refine Or.inl ?_
      have hqq : d' = q := by simpa [DomIntArg.read_lit] using hq
      omega
  | slot j =>
      by_cases hqd : q = d
      · exact Or.inl hqd
      · have hq' : slotInt a j = some q := slotInt_of_read_slot hq
        by_cases hlt : q ≤ d - 1
        · exact Or.inr ⟨posLe j (d - 1), by simp [divMatchCauses],
            by rw [eval_posLe_iff]; exact ⟨q, hq', hlt⟩⟩
        · exact Or.inr ⟨negLe j d, by simp [divMatchCauses],
            by rw [eval_negLe_iff]; exact ⟨q, hq', by omega⟩⟩

/-! ### The truncation arithmetic -/

theorem tdiv_eq_neg_tdiv_neg {p d : Int} (_hneg : d < 0) :
    Int.tdiv p d = -(Int.tdiv p (-d)) := by
  have h := Int.tdiv_neg p (-d)
  rw [Int.neg_neg] at h
  exact h

theorem tdiv_mem_hull {p d pl ph : Int} (hd : d ≠ 0)
    (h1 : pl ≤ p) (h2 : p ≤ ph) :
    divResLo d pl ph ≤ Int.tdiv p d ∧ Int.tdiv p d ≤ divResHi d pl ph := by
  rcases Int.lt_trichotomy d 0 with hneg | hzero | hpos
  · have hd' : 0 < -d := by omega
    have e1 : Int.tdiv p d = -(Int.tdiv p (-d)) := tdiv_eq_neg_tdiv_neg hneg
    have e2 : Int.tdiv ph d = -(Int.tdiv ph (-d)) := tdiv_eq_neg_tdiv_neg hneg
    have e3 : Int.tdiv pl d = -(Int.tdiv pl (-d)) := tdiv_eq_neg_tdiv_neg hneg
    have m1 : Int.tdiv pl (-d) ≤ Int.tdiv p (-d) := Int.tdiv_le_tdiv hd' h1
    have m2 : Int.tdiv p (-d) ≤ Int.tdiv ph (-d) := Int.tdiv_le_tdiv hd' h2
    unfold divResLo divResHi
    rw [e1, e2, e3]
    constructor <;> omega
  · exact absurd hzero hd
  · have m1 : Int.tdiv pl d ≤ Int.tdiv p d := Int.tdiv_le_tdiv hpos h1
    have m2 : Int.tdiv p d ≤ Int.tdiv ph d := Int.tdiv_le_tdiv hpos h2
    unfold divResLo divResHi
    constructor <;> omega

theorem tmod_bounds {p d : Int} (hd : d ≠ 0) :
    -(absValue d - 1) ≤ Int.tmod p d ∧ Int.tmod p d ≤ absValue d - 1 := by
  have hpos : ∀ {e : Int}, 0 < e → -e < Int.tmod p e ∧ Int.tmod p e < e := fun h =>
    ⟨Int.lt_tmod_of_pos p h, Int.tmod_lt_of_pos p h⟩
  rcases Int.lt_trichotomy d 0 with hneg | hzero | hgt
  · have hd' : 0 < -d := by omega
    have e : Int.tmod p d = Int.tmod p (-d) := by
      have h := Int.tmod_neg p (-d)
      rw [Int.neg_neg] at h
      exact h
    obtain ⟨hb1, hb2⟩ := hpos hd'
    have ha : absValue d = -d := arith_absValue_of_neg hneg
    rw [e, ha]
    omega
  · exact absurd hzero hd
  · obtain ⟨hb1, hb2⟩ := hpos hgt
    have ha : absValue d = d := arith_absValue_of_nonneg (by omega)
    rw [ha]
    omega

theorem tmod_mem_hull {p d pl ph : Int} (hd : d ≠ 0)
    (h1 : pl ≤ p) (h2 : p ≤ ph) :
    modHullLo d pl ph ≤ Int.tmod p d ∧ Int.tmod p d ≤ modHullHi d pl ph := by
  by_cases hq : Int.tdiv pl d = Int.tdiv ph d
  · have hconst : Int.tdiv p d = Int.tdiv pl d := by
      rcases Int.lt_trichotomy d 0 with hneg | hzero | hpos
      · have hd' : 0 < -d := by omega
        have e1 : Int.tdiv p d = -(Int.tdiv p (-d)) := tdiv_eq_neg_tdiv_neg hneg
        have e2 : Int.tdiv pl d = -(Int.tdiv pl (-d)) := tdiv_eq_neg_tdiv_neg hneg
        have e3 : Int.tdiv ph d = -(Int.tdiv ph (-d)) := tdiv_eq_neg_tdiv_neg hneg
        have m1 : Int.tdiv pl (-d) ≤ Int.tdiv p (-d) := Int.tdiv_le_tdiv hd' h1
        have m2 : Int.tdiv p (-d) ≤ Int.tdiv ph (-d) := Int.tdiv_le_tdiv hd' h2
        have hgh : Int.tdiv ph (-d) = Int.tdiv pl (-d) := by omega
        omega
      · exact absurd hzero hd
      · have m1 : Int.tdiv pl d ≤ Int.tdiv p d := Int.tdiv_le_tdiv hpos h1
        have m2 : Int.tdiv p d ≤ Int.tdiv ph d := Int.tdiv_le_tdiv hpos h2
        omega
    have hid : ∀ x : Int, x - d * (Int.tdiv x d) = Int.tmod x d := by
      intro x
      have h := Int.mul_tdiv_add_tmod x d
      omega
    have hl : modHullLo d pl ph = Int.tmod pl d := by
      unfold modHullLo; rw [if_pos hq]
    have hh : modHullHi d pl ph = Int.tmod ph d := by
      unfold modHullHi; rw [if_pos hq]
    rw [hl, hh, ← hid p, ← hid pl, ← hid ph, hconst, ← hq]
    constructor <;> omega
  · have hl : modHullLo d pl ph = -(absValue d - 1) := by
      unfold modHullLo; rw [if_neg hq]
    have hh : modHullHi d pl ph = absValue d - 1 := by
      unfold modHullHi; rw [if_neg hq]
    rw [hl, hh]
    exact tmod_bounds hd

/-! ### Cause-membership helpers -/

theorem divMatchCauses_mem_lo {o₂ : DomIntArg} {d pl ph : Int} {i k : Nat}
    {l : Literal} (h : l ∈ divMatchCauses o₂ d) :
    l ∈ divReasonLo o₂ i k d pl ph := by
  cases o₂ with
  | lit d' => simp [divMatchCauses] at h
  | slot j =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_of_mem _ (List.mem_cons_self)
      · rw [List.mem_singleton.mp h]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem divMatchCauses_mem_hi {o₂ : DomIntArg} {d pl ph : Int} {i k : Nat}
    {l : Literal} (h : l ∈ divMatchCauses o₂ d) :
    l ∈ divReasonHi o₂ i k d pl ph := by
  cases o₂ with
  | lit d' => simp [divMatchCauses] at h
  | slot j =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_of_mem _ (List.mem_cons_self)
      · rw [List.mem_singleton.mp h]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem divMatchCauses_mem_modlo {o₂ : DomIntArg} {d pl ph : Int} {i k : Nat}
    {l : Literal} (h : l ∈ divMatchCauses o₂ d) :
    l ∈ modReasonLo o₂ i k d pl ph := by
  cases o₂ with
  | lit d' => simp [divMatchCauses] at h
  | slot j =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_of_mem _ (List.mem_cons_self)
      · rw [List.mem_singleton.mp h]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self))

theorem divMatchCauses_mem_modhi {o₂ : DomIntArg} {d pl ph : Int} {i k : Nat}
    {l : Literal} (h : l ∈ divMatchCauses o₂ d) :
    l ∈ modReasonHi o₂ i k d pl ph := by
  cases o₂ with
  | lit d' => simp [divMatchCauses] at h
  | slot j =>
      rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_of_mem _ (List.mem_cons_self)
      · rw [List.mem_singleton.mp h]
        exact List.mem_cons_of_mem _
          (List.mem_cons_of_mem _ (List.mem_cons_self))

/-! ### The nogood kernels -/

/-- `divGen` lower-arm nogood: `[k ≥ lo−1, (divisor causes), i ≤ pl−1,
    i ≥ ph+1]` with `lo = divResLo d pl ph` — if the dividend is below
    `pl` the third literal is true, above `ph` the fourth, and inside
    the interval (with the divisor reading `d`, forced by the cause
    falsity) the hull bound makes the head true. -/
theorem arith_div_nogood_lo_true {a : Assignment} {i k : Nat} {o₂ : DomIntArg}
    {d pl ph : Int} (_hd : d ≠ 0)
    (hdc : ∀ q, DomIntArg.read a o₂ = .int q → q = d ∨
      ∃ l ∈ divMatchCauses o₂ d, l.eval a = some true)
    (hcons : (DomConstraint.divGen (.slot i) o₂ (.slot k)).SatisfiedBy a) :
    ∃ l ∈ divReasonLo o₂ i k d pl ph, l.eval a = some true := by
  obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
  have hp' : slotInt a i = some p := slotInt_of_read_slot hp
  have hr' : slotInt a k = some (Int.tdiv p q) := slotInt_of_read_slot hr
  rcases hdc q hq with hqd | ⟨l, hl, hltrue⟩
  · by_cases h1 : p ≤ pl - 1
    · exact ⟨posLe i (pl - 1), by cases o₂ <;> simp [divReasonLo],
        by rw [eval_posLe_iff]; exact ⟨p, hp', h1⟩⟩
    · by_cases h2 : ph + 1 ≤ p
      · exact ⟨negLe i ph, by cases o₂ <;> simp [divReasonLo],
          by rw [eval_negLe_iff]; exact ⟨p, hp', h2⟩⟩
      · have hb : divResLo d pl ph ≤ Int.tdiv p q := by
          rw [← hqd]
          exact (tdiv_mem_hull hq0 (by omega : pl ≤ p) (by omega : p ≤ ph)).1
        exact ⟨negLe k (divResLo d pl ph - 1),
          by cases o₂ <;> simp [divReasonLo],
          by rw [eval_negLe_iff]; exact ⟨Int.tdiv p q, hr', by omega⟩⟩
  · exact ⟨l, divMatchCauses_mem_lo hl, hltrue⟩

theorem arith_div_nogood_hi_true {a : Assignment} {i k : Nat} {o₂ : DomIntArg}
    {d pl ph : Int} (_hd : d ≠ 0)
    (hdc : ∀ q, DomIntArg.read a o₂ = .int q → q = d ∨
      ∃ l ∈ divMatchCauses o₂ d, l.eval a = some true)
    (hcons : (DomConstraint.divGen (.slot i) o₂ (.slot k)).SatisfiedBy a) :
    ∃ l ∈ divReasonHi o₂ i k d pl ph, l.eval a = some true := by
  obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
  have hp' : slotInt a i = some p := slotInt_of_read_slot hp
  have hr' : slotInt a k = some (Int.tdiv p q) := slotInt_of_read_slot hr
  rcases hdc q hq with hqd | ⟨l, hl, hltrue⟩
  · by_cases h1 : p ≤ pl - 1
    · exact ⟨posLe i (pl - 1), by cases o₂ <;> simp [divReasonHi],
        by rw [eval_posLe_iff]; exact ⟨p, hp', h1⟩⟩
    · by_cases h2 : ph + 1 ≤ p
      · exact ⟨negLe i ph, by cases o₂ <;> simp [divReasonHi],
          by rw [eval_negLe_iff]; exact ⟨p, hp', h2⟩⟩
      · have hb : Int.tdiv p q ≤ divResHi d pl ph := by
          rw [← hqd]
          exact (tdiv_mem_hull hq0 (by omega : pl ≤ p) (by omega : p ≤ ph)).2
        exact ⟨posLe k (divResHi d pl ph),
          by cases o₂ <;> simp [divReasonHi],
          by rw [eval_posLe_iff]; exact ⟨Int.tdiv p q, hr', by omega⟩⟩
  · exact ⟨l, divMatchCauses_mem_hi hl, hltrue⟩

theorem arith_mod_nogood_lo_true {a : Assignment} {i k : Nat} {o₂ : DomIntArg}
    {d pl ph : Int} (_hd : d ≠ 0)
    (hdc : ∀ q, DomIntArg.read a o₂ = .int q → q = d ∨
      ∃ l ∈ divMatchCauses o₂ d, l.eval a = some true)
    (hcons : (DomConstraint.modGen (.slot i) o₂ (.slot k)).SatisfiedBy a) :
    ∃ l ∈ modReasonLo o₂ i k d pl ph, l.eval a = some true := by
  obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
  have hp' : slotInt a i = some p := slotInt_of_read_slot hp
  have hr' : slotInt a k = some (Int.tmod p q) := slotInt_of_read_slot hr
  rcases hdc q hq with hqd | ⟨l, hl, hltrue⟩
  · by_cases h1 : p ≤ pl - 1
    · exact ⟨posLe i (pl - 1), by cases o₂ <;> simp [modReasonLo],
        by rw [eval_posLe_iff]; exact ⟨p, hp', h1⟩⟩
    · by_cases h2 : ph + 1 ≤ p
      · exact ⟨negLe i ph, by cases o₂ <;> simp [modReasonLo],
          by rw [eval_negLe_iff]; exact ⟨p, hp', h2⟩⟩
      · have hb : modHullLo d pl ph ≤ Int.tmod p q := by
          rw [← hqd]
          exact (tmod_mem_hull hq0 (by omega : pl ≤ p) (by omega : p ≤ ph)).1
        exact ⟨negLe k (modHullLo d pl ph - 1),
          by cases o₂ <;> simp [modReasonLo],
          by rw [eval_negLe_iff]; exact ⟨Int.tmod p q, hr', by omega⟩⟩
  · exact ⟨l, divMatchCauses_mem_modlo hl, hltrue⟩

theorem arith_mod_nogood_hi_true {a : Assignment} {i k : Nat} {o₂ : DomIntArg}
    {d pl ph : Int} (_hd : d ≠ 0)
    (hdc : ∀ q, DomIntArg.read a o₂ = .int q → q = d ∨
      ∃ l ∈ divMatchCauses o₂ d, l.eval a = some true)
    (hcons : (DomConstraint.modGen (.slot i) o₂ (.slot k)).SatisfiedBy a) :
    ∃ l ∈ modReasonHi o₂ i k d pl ph, l.eval a = some true := by
  obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
  have hp' : slotInt a i = some p := slotInt_of_read_slot hp
  have hr' : slotInt a k = some (Int.tmod p q) := slotInt_of_read_slot hr
  rcases hdc q hq with hqd | ⟨l, hl, hltrue⟩
  · by_cases h1 : p ≤ pl - 1
    · exact ⟨posLe i (pl - 1), by cases o₂ <;> simp [modReasonHi],
        by rw [eval_posLe_iff]; exact ⟨p, hp', h1⟩⟩
    · by_cases h2 : ph + 1 ≤ p
      · exact ⟨negLe i ph, by cases o₂ <;> simp [modReasonHi],
          by rw [eval_negLe_iff]; exact ⟨p, hp', h2⟩⟩
      · have hb : Int.tmod p q ≤ modHullHi d pl ph := by
          rw [← hqd]
          exact (tmod_mem_hull hq0 (by omega : pl ≤ p) (by omega : p ≤ ph)).2
        exact ⟨posLe k (modHullHi d pl ph),
          by cases o₂ <;> simp [modReasonHi],
          by rw [eval_posLe_iff]; exact ⟨Int.tmod p q, hr', by omega⟩⟩
  · exact ⟨l, divMatchCauses_mem_modhi hl, hltrue⟩

/-- The zero-divisor conflict kernel: `[o_j ≠ 0]` (or the empty clause on
    a literal `0`) carries a true literal at every `divGen`/`modGen`
    solution. -/
theorem arith_div_zero_true {st : State} {a : Assignment} {o₁ o₂ r : DomIntArg}
    {d : Int} (hzero : d = 0) (hpin : divPin st o₂ = some d)
    (hcons : (DomConstraint.divGen o₁ o₂ r).SatisfiedBy a) :
    ∃ l ∈ divZeroClause o₂, l.eval a = some true := by
  obtain ⟨p, q, _hp, hq, hq0, _hr⟩ := hcons
  cases o₂ with
  | lit d' =>
      have hd' : d' = d := by simpa [divPin] using hpin
      have hqd : d' = q := by simpa [DomIntArg.read_lit] using hq
      omega
  | slot j =>
      refine ⟨posNe j 0, by simp [divZeroClause], ?_⟩
      rw [eval_posNe_iff]
      exact ⟨q, slotInt_of_read_slot hq, hq0⟩

theorem arith_mod_zero_true {st : State} {a : Assignment} {o₁ o₂ r : DomIntArg}
    {d : Int} (hzero : d = 0) (hpin : divPin st o₂ = some d)
    (hcons : (DomConstraint.modGen o₁ o₂ r).SatisfiedBy a) :
    ∃ l ∈ divZeroClause o₂, l.eval a = some true := by
  obtain ⟨p, q, _hp, hq, hq0, _hr⟩ := hcons
  cases o₂ with
  | lit d' =>
      have hd' : d' = d := by simpa [divPin] using hpin
      have hqd : d' = q := by simpa [DomIntArg.read_lit] using hq
      omega
  | slot j =>
      refine ⟨posNe j 0, by simp [divZeroClause], ?_⟩
      rw [eval_posNe_iff]
      exact ⟨q, slotInt_of_read_slot hq, hq0⟩


/-! ### The safety triples -/

theorem propDiv_safe (st : State) (o₁ o₂ r : DomIntArg) :
    (∀ l rsn, propDiv st o₁ o₂ r = .implied l rsn →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.divGen o₁ o₂ r).SatisfiedBy a → l.eval a = some true) ∧
    (∀ c, propDiv st o₁ o₂ r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.divGen o₁ o₂ r).SatisfiedBy a → False) ∧
    (∀ c, propDiv st o₁ o₂ r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.divGen o₁ o₂ r).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  have hno : ∀ c, propDiv st o₁ o₂ r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.divGen o₁ o₂ r).SatisfiedBy a → False := by
    intro c hrun a hfit hcons
    unfold propDiv at hrun
    split at hrun
    · rename_i x d hpin
      split at hrun
      · rename_i hd0
        obtain ⟨p, q, _hp, hq, hq0, _hr⟩ := hcons
        have hqeq : q = d := divPin_read hfit hpin q hq
        omega
      · split at hrun
        · rename_i i k
          split at hrun
          · rename_i pl ph hpl hph
            rcases firstEvent_mem
                [narrowLo st k (divResLo d pl ph) (divReasonLo o₂ i k d pl ph),
                 narrowHi st k (divResHi d pl ph) (divReasonHi o₂ i k d pl ph)]
                (.conflict c) hrun with hstable | hmem
            · exact absurd hstable (by intro hc; cases hc)
            · obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
              have hqeq : q = d := divPin_read hfit hpin q hq
              have hp' : slotInt a i = some p := slotInt_of_read_slot hp
              have hrs' : slotInt a k = some (Int.tdiv p q) := slotInt_of_read_slot hr
              have hpl' : pl ≤ p := fits_min_bound hfit hpl hp'
              have hph' : p ≤ ph := fits_max_bound hfit hph hp'
              have hbq := (tdiv_mem_hull hq0 hpl' hph')
              have hdLo : divResLo d pl ph = divResLo q pl ph := by rw [hqeq]
              have hdHi : divResHi d pl ph = divResHi q pl ph := by rw [hqeq]
              have hdt : Int.tdiv p d = Int.tdiv p q := by rw [hqeq]
              rcases List.mem_cons.mp hmem with h1 | hrest
              · obtain ⟨_mn, mx, _hmn, hmx, hlt, _⟩ :=
                  narrowLo_conflict_inv (Eq.symm h1)
                have hrmx : Int.tdiv p q ≤ mx := fits_max_bound hfit hmx hrs'
                omega
              · obtain ⟨mn, _mx, hmn, _hmx, hgt, _⟩ :=
                  narrowHi_conflict_inv (Eq.symm (List.mem_singleton.mp hrest))
                have hrmn : mn ≤ Int.tdiv p q := fits_min_bound hfit hmn hrs'
                omega
          · exact absurd hrun (by intro hc; simp at hc)
        · exact absurd hrun (by intro hc; simp at hc)
    · exact absurd hrun (by intro hc; simp at hc)
  refine ⟨?_, hno, ?_⟩
  · intro l rsn hrun a hfit hcons
    unfold propDiv at hrun
    split at hrun
    · rename_i x d hpin
      split at hrun
      · rename_i hd0
        exact absurd hrun (by intro hc; cases hc)
      · split at hrun
        · rename_i i k
          split at hrun
          · rename_i pl ph hpl hph
            rcases firstEvent_mem
                [narrowLo st k (divResLo d pl ph) (divReasonLo o₂ i k d pl ph),
                 narrowHi st k (divResHi d pl ph) (divReasonHi o₂ i k d pl ph)]
                (.implied l rsn) hrun with hstable | hmem
            · exact absurd hstable (by intro hc; cases hc)
            · obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
              have hqeq : q = d := divPin_read hfit hpin q hq
              have hp' : slotInt a i = some p := slotInt_of_read_slot hp
              have hrs' : slotInt a k = some (Int.tdiv p q) := slotInt_of_read_slot hr
              have hpl' : pl ≤ p := fits_min_bound hfit hpl hp'
              have hph' : p ≤ ph := fits_max_bound hfit hph hp'
              have hbq := (tdiv_mem_hull hq0 hpl' hph')
              have hdLo : divResLo d pl ph = divResLo q pl ph := by rw [hqeq]
              have hdHi : divResHi d pl ph = divResHi q pl ph := by rw [hqeq]
              have hdt : Int.tdiv p d = Int.tdiv p q := by rw [hqeq]
              rcases List.mem_cons.mp hmem with h1 | hrest
              · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1)
                subst hl
                rw [eval_negLe_iff]
                exact ⟨Int.tdiv p q, hrs', by omega⟩
              · obtain ⟨hl, _⟩ := narrowHi_implied_inv
                  (Eq.symm (List.mem_singleton.mp hrest))
                subst hl
                rw [eval_posLe_iff]
                exact ⟨Int.tdiv p q, hrs', by omega⟩
          · exact absurd hrun (by intro hc; simp at hc)
        · exact absurd hrun (by intro hc; simp at hc)
    · exact absurd hrun (by intro hc; simp at hc)
  · intro c hrun a hfit hcons
    exact False.elim (hno c hrun a hfit hcons)

theorem propMod_safe (st : State) (o₁ o₂ r : DomIntArg) :
    (∀ l rsn, propMod st o₁ o₂ r = .implied l rsn →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.modGen o₁ o₂ r).SatisfiedBy a → l.eval a = some true) ∧
    (∀ c, propMod st o₁ o₂ r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.modGen o₁ o₂ r).SatisfiedBy a → False) ∧
    (∀ c, propMod st o₁ o₂ r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.modGen o₁ o₂ r).SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) := by
  have hno : ∀ c, propMod st o₁ o₂ r = .conflict c →
      ∀ a, Core.Assignment.Fits st.domains a →
        (DomConstraint.modGen o₁ o₂ r).SatisfiedBy a → False := by
    intro c hrun a hfit hcons
    unfold propMod at hrun
    split at hrun
    · rename_i x d hpin
      split at hrun
      · rename_i hd0
        obtain ⟨p, q, _hp, hq, hq0, _hr⟩ := hcons
        have hqeq : q = d := divPin_read hfit hpin q hq
        omega
      · split at hrun
        · rename_i i k
          split at hrun
          · rename_i pl ph hpl hph
            rcases firstEvent_mem
                [narrowLo st k (modHullLo d pl ph) (modReasonLo o₂ i k d pl ph),
                 narrowHi st k (modHullHi d pl ph) (modReasonHi o₂ i k d pl ph)]
                (.conflict c) hrun with hstable | hmem
            · exact absurd hstable (by intro hc; cases hc)
            · obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
              have hqeq : q = d := divPin_read hfit hpin q hq
              have hp' : slotInt a i = some p := slotInt_of_read_slot hp
              have hrs' : slotInt a k = some (Int.tmod p q) := slotInt_of_read_slot hr
              have hpl' : pl ≤ p := fits_min_bound hfit hpl hp'
              have hph' : p ≤ ph := fits_max_bound hfit hph hp'
              have hbq := (tmod_mem_hull hq0 hpl' hph')
              have hdLo : modHullLo d pl ph = modHullLo q pl ph := by rw [hqeq]
              have hdHi : modHullHi d pl ph = modHullHi q pl ph := by rw [hqeq]
              have hdt : Int.tmod p d = Int.tmod p q := by rw [hqeq]
              rcases List.mem_cons.mp hmem with h1 | hrest
              · obtain ⟨_mn, mx, _hmn, hmx, hlt, _⟩ :=
                  narrowLo_conflict_inv (Eq.symm h1)
                have hrmx : Int.tmod p q ≤ mx := fits_max_bound hfit hmx hrs'
                omega
              · obtain ⟨mn, _mx, hmn, _hmx, hgt, _⟩ :=
                  narrowHi_conflict_inv (Eq.symm (List.mem_singleton.mp hrest))
                have hrmn : mn ≤ Int.tmod p q := fits_min_bound hfit hmn hrs'
                omega
          · exact absurd hrun (by intro hc; simp at hc)
        · exact absurd hrun (by intro hc; simp at hc)
    · exact absurd hrun (by intro hc; simp at hc)
  refine ⟨?_, hno, ?_⟩
  · intro l rsn hrun a hfit hcons
    unfold propMod at hrun
    split at hrun
    · rename_i x d hpin
      split at hrun
      · rename_i hd0
        exact absurd hrun (by intro hc; cases hc)
      · split at hrun
        · rename_i i k
          split at hrun
          · rename_i pl ph hpl hph
            rcases firstEvent_mem
                [narrowLo st k (modHullLo d pl ph) (modReasonLo o₂ i k d pl ph),
                 narrowHi st k (modHullHi d pl ph) (modReasonHi o₂ i k d pl ph)]
                (.implied l rsn) hrun with hstable | hmem
            · exact absurd hstable (by intro hc; cases hc)
            · obtain ⟨p, q, hp, hq, hq0, hr⟩ := hcons
              have hqeq : q = d := divPin_read hfit hpin q hq
              have hp' : slotInt a i = some p := slotInt_of_read_slot hp
              have hrs' : slotInt a k = some (Int.tmod p q) := slotInt_of_read_slot hr
              have hpl' : pl ≤ p := fits_min_bound hfit hpl hp'
              have hph' : p ≤ ph := fits_max_bound hfit hph hp'
              have hbq := (tmod_mem_hull hq0 hpl' hph')
              have hdLo : modHullLo d pl ph = modHullLo q pl ph := by rw [hqeq]
              have hdHi : modHullHi d pl ph = modHullHi q pl ph := by rw [hqeq]
              have hdt : Int.tmod p d = Int.tmod p q := by rw [hqeq]
              rcases List.mem_cons.mp hmem with h1 | hrest
              · obtain ⟨hl, _⟩ := narrowLo_implied_inv (Eq.symm h1)
                subst hl
                rw [eval_negLe_iff]
                exact ⟨Int.tmod p q, hrs', by omega⟩
              · obtain ⟨hl, _⟩ := narrowHi_implied_inv
                  (Eq.symm (List.mem_singleton.mp hrest))
                subst hl
                rw [eval_posLe_iff]
                exact ⟨Int.tmod p q, hrs', by omega⟩
          · exact absurd hrun (by intro hc; simp at hc)
        · exact absurd hrun (by intro hc; simp at hc)
    · exact absurd hrun (by intro hc; simp at hc)
  · intro c hrun a hfit hcons
    exact False.elim (hno c hrun a hfit hcons)


/-! ### Reason validity and entitlement -/

theorem propDiv_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {o₁ o₂ r : DomIntArg} {l : Literal} {rsn : Reason}
    (hprob : DomConstraint.divGen o₁ o₂ r ∈ problem.constraints)
    (hrun : propDiv st o₁ o₂ r = .implied l rsn) :
    Reason.Valid problem DomConstraint.SatisfiedBy rsn l ∧
      (∀ q ∈ rsn.clause, q = q.norm) := by
  unfold propDiv at hrun
  split at hrun
  · rename_i x d hpin
    split at hrun
    · exact absurd hrun (by intro hc; cases hc)
    · rename_i hd0
      split at hrun
      · rename_i i k
        split at hrun
        · rename_i pl ph hpl hph
          rcases firstEvent_mem
              [narrowLo st k (divResLo d pl ph) (divReasonLo o₂ i k d pl ph),
               narrowHi st k (divResHi d pl ph) (divReasonHi o₂ i k d pl ph)]
              (.implied l rsn) hrun with hstable | hmem
          · exact absurd hstable (by intro hc; cases hc)
          · rcases List.mem_cons.mp hmem with h1 | hrest
            · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h1)
              have hpivmem : l ∈ rsn.clause := by
                subst hl; rw [hcl]; cases o₂ <;> simp [divReasonLo]
              refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
                arith_reason_clause_norm_sf hcl ?_⟩
              · intro a ha
                have hcl2 : rsn.clause = divReasonLo o₂ i k d pl ph := by rw [hcl]
                rw [hcl2]
                exact arith_div_nogood_lo_true hd0 (divMatch_covers hpin)
                  (ha.2 _ hprob)
              · intro q hq
                cases o₂ with
                | lit d' =>
                    simp only [divReasonLo, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl <;> rfl
                | slot j =>
                    simp only [divReasonLo, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl
            · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv
                (Eq.symm (List.mem_singleton.mp hrest))
              have hpivmem : l ∈ rsn.clause := by
                subst hl; rw [hcl]; cases o₂ <;> simp [divReasonHi]
              refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
                arith_reason_clause_norm_sf hcl ?_⟩
              · intro a ha
                have hcl2 : rsn.clause = divReasonHi o₂ i k d pl ph := by rw [hcl]
                rw [hcl2]
                exact arith_div_nogood_hi_true hd0 (divMatch_covers hpin)
                  (ha.2 _ hprob)
              · intro q hq
                cases o₂ with
                | lit d' =>
                    simp only [divReasonHi, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl <;> rfl
                | slot j =>
                    simp only [divReasonHi, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl
        · exact absurd hrun (by intro hc; simp at hc)
      · exact absurd hrun (by intro hc; simp at hc)
  · exact absurd hrun (by intro hc; simp at hc)

theorem propMod_reason_valid
    {problem : Problem DomConstraint Unit}
    {st : State} {o₁ o₂ r : DomIntArg} {l : Literal} {rsn : Reason}
    (hprob : DomConstraint.modGen o₁ o₂ r ∈ problem.constraints)
    (hrun : propMod st o₁ o₂ r = .implied l rsn) :
    Reason.Valid problem DomConstraint.SatisfiedBy rsn l ∧
      (∀ q ∈ rsn.clause, q = q.norm) := by
  unfold propMod at hrun
  split at hrun
  · rename_i x d hpin
    split at hrun
    · exact absurd hrun (by intro hc; cases hc)
    · rename_i hd0
      split at hrun
      · rename_i i k
        split at hrun
        · rename_i pl ph hpl hph
          rcases firstEvent_mem
              [narrowLo st k (modHullLo d pl ph) (modReasonLo o₂ i k d pl ph),
               narrowHi st k (modHullHi d pl ph) (modReasonHi o₂ i k d pl ph)]
              (.implied l rsn) hrun with hstable | hmem
          · exact absurd hstable (by intro hc; cases hc)
          · rcases List.mem_cons.mp hmem with h1 | hrest
            · obtain ⟨hl, hcl⟩ := narrowLo_implied_inv (Eq.symm h1)
              have hpivmem : l ∈ rsn.clause := by
                subst hl; rw [hcl]; cases o₂ <;> simp [modReasonLo]
              refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
                arith_reason_clause_norm_sf hcl ?_⟩
              · intro a ha
                have hcl2 : rsn.clause = modReasonLo o₂ i k d pl ph := by rw [hcl]
                rw [hcl2]
                exact arith_mod_nogood_lo_true hd0 (divMatch_covers hpin)
                  (ha.2 _ hprob)
              · intro q hq
                cases o₂ with
                | lit d' =>
                    simp only [modReasonLo, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl <;> rfl
                | slot j =>
                    simp only [modReasonLo, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl
            · obtain ⟨hl, hcl⟩ := narrowHi_implied_inv
                (Eq.symm (List.mem_singleton.mp hrest))
              have hpivmem : l ∈ rsn.clause := by
                subst hl; rw [hcl]; cases o₂ <;> simp [modReasonHi]
              refine ⟨arith_reason_valid_of_clause_true hpivmem ?_,
                arith_reason_clause_norm_sf hcl ?_⟩
              · intro a ha
                have hcl2 : rsn.clause = modReasonHi o₂ i k d pl ph := by rw [hcl]
                rw [hcl2]
                exact arith_mod_nogood_hi_true hd0 (divMatch_covers hpin)
                  (ha.2 _ hprob)
              · intro q hq
                cases o₂ with
                | lit d' =>
                    simp only [modReasonHi, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl <;> rfl
                | slot j =>
                    simp only [modReasonHi, List.mem_cons, List.mem_nil_iff,
                      or_false] at hq
                    rcases hq with rfl | rfl | rfl | rfl | rfl <;> rfl
        · exact absurd hrun (by intro hc; simp at hc)
      · exact absurd hrun (by intro hc; simp at hc)
  · exact absurd hrun (by intro hc; simp at hc)

theorem propDiv_entitled
    {problem : Problem DomConstraint Unit} {st : State} {o₁ o₂ r : DomIntArg}
    {c : Clause}
    (hprob : DomConstraint.divGen o₁ o₂ r ∈ problem.constraints)
    (hrun : propDiv st o₁ o₂ r = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propDiv at hrun
  split at hrun
  · rename_i x d hpin
    split at hrun
    · rename_i hd0
      have hc : c = divZeroClause o₂ := by
        have hinj := hrun
        simp only [PropagationResult.conflict.injEq] at hinj
        exact hinj.symm
      rw [hc]
      exact arith_div_zero_true hd0 hpin (ha.2 _ hprob)
    · rename_i hd0
      split at hrun
      · rename_i i k
        split at hrun
        · rename_i pl ph hpl hph
          rcases firstEvent_mem
              [narrowLo st k (divResLo d pl ph) (divReasonLo o₂ i k d pl ph),
               narrowHi st k (divResHi d pl ph) (divReasonHi o₂ i k d pl ph)]
              (.conflict c) hrun with hstable | hmem
          · exact absurd hstable (by intro hc; cases hc)
          · rcases List.mem_cons.mp hmem with h1 | hrest
            · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv (Eq.symm h1)
              rw [hcc]
              exact arith_div_nogood_lo_true hd0 (divMatch_covers hpin)
                (ha.2 _ hprob)
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm (List.mem_singleton.mp hrest))
              rw [hcc]
              exact arith_div_nogood_hi_true hd0 (divMatch_covers hpin)
                (ha.2 _ hprob)
        · exact absurd hrun (by intro hc; simp at hc)
      · exact absurd hrun (by intro hc; simp at hc)
  · exact absurd hrun (by intro hc; simp at hc)

theorem propMod_entitled
    {problem : Problem DomConstraint Unit} {st : State} {o₁ o₂ r : DomIntArg}
    {c : Clause}
    (hprob : DomConstraint.modGen o₁ o₂ r ∈ problem.constraints)
    (hrun : propMod st o₁ o₂ r = .conflict c)
    (a : Assignment)
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a) :
    ∃ l ∈ c, l.eval a = some true := by
  unfold propMod at hrun
  split at hrun
  · rename_i x d hpin
    split at hrun
    · rename_i hd0
      have hc : c = divZeroClause o₂ := by
        have hinj := hrun
        simp only [PropagationResult.conflict.injEq] at hinj
        exact hinj.symm
      rw [hc]
      exact arith_mod_zero_true hd0 hpin (ha.2 _ hprob)
    · rename_i hd0
      split at hrun
      · rename_i i k
        split at hrun
        · rename_i pl ph hpl hph
          rcases firstEvent_mem
              [narrowLo st k (modHullLo d pl ph) (modReasonLo o₂ i k d pl ph),
               narrowHi st k (modHullHi d pl ph) (modReasonHi o₂ i k d pl ph)]
              (.conflict c) hrun with hstable | hmem
          · exact absurd hstable (by intro hc; cases hc)
          · rcases List.mem_cons.mp hmem with h1 | hrest
            · obtain ⟨_, _, _, _, _, hcc⟩ := narrowLo_conflict_inv (Eq.symm h1)
              rw [hcc]
              exact arith_mod_nogood_lo_true hd0 (divMatch_covers hpin)
                (ha.2 _ hprob)
            · obtain ⟨_, _, _, _, _, hcc⟩ :=
                narrowHi_conflict_inv (Eq.symm (List.mem_singleton.mp hrest))
              rw [hcc]
              exact arith_mod_nogood_hi_true hd0 (divMatch_covers hpin)
                (ha.2 _ hprob)
        · exact absurd hrun (by intro hc; simp at hc)
      · exact absurd hrun (by intro hc; simp at hc)
  · exact absurd hrun (by intro hc; cases hc)

/-! ## The standalone packaging

A self-contained registration of exactly the three families of
this module, in the shape of Propagators.lean's
`propagatorOfProved` packaging. -/

/-- The propagators of this module's three families: `minSlot`,
    `maxSlot`, `absSlot`. -/
def propagatorOfProvedB6 : DomConstraint → Option Propagator
  | .minSlot i j k =>
      some { watches := [], run := fun st => propMin st i j k }
  | .maxSlot i j k =>
      some { watches := [], run := fun st => propMax st i j k }
  | .absSlot i k =>
      some { watches := [], run := fun st => propAbs st i k }
  | _ => none

/-- Membership inversion for the registration. -/
theorem propagatorOfProvedB6_mem {dcs : List DomConstraint}
    {p : Propagator} (hp : p ∈ dcs.filterMap propagatorOfProvedB6) :
    ∃ dc ∈ dcs, propagatorOfProvedB6 dc = some p := by
  induction dcs with
  | nil => cases hp
  | cons dc rest ih =>
      cases hpdc : propagatorOfProvedB6 dc with
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
    one of the three families' propagators. -/
theorem propagatorOfProvedB6_run {dc : DomConstraint} {p : Propagator}
    {st : State} {res : PropagationResult}
    (hprop : propagatorOfProvedB6 dc = some p)
    (hrun : p.run st = res) :
    (∃ i j k, dc = .minSlot i j k ∧ propMin st i j k = res) ∨
    (∃ i j k, dc = .maxSlot i j k ∧ propMax st i j k = res) ∨
    (∃ i k, dc = .absSlot i k ∧ propAbs st i k = res) := by
  match hdc : dc with
  | .minSlot i j k =>
      simp only [propagatorOfProvedB6] at hprop
      refine Or.inl ⟨i, j, k, rfl, ?_⟩
      have hp2 : p = { watches := [], run := fun st => propMin st i j k } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .maxSlot i j k =>
      simp only [propagatorOfProvedB6] at hprop
      refine Or.inr (Or.inl ⟨i, j, k, rfl, ?_⟩)
      have hp2 : p = { watches := [], run := fun st => propMax st i j k } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .absSlot i k =>
      simp only [propagatorOfProvedB6] at hprop
      refine Or.inr (Or.inr ⟨i, k, rfl, ?_⟩)
      have hp2 : p = { watches := [], run := fun st => propAbs st i k } :=
        (Option.some.inj hprop).symm
      rw [hp2] at hrun
      exact hrun
  | .eqSlot i j =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .neSlot i j =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .leSlot i j =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .constEq i v =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .plusSlot i j k =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .leConstHi i c =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .leConstLo i c =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .allDiff is =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .timesSlot i j k =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .linEq coeffs is b =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .linLe coeffs is b =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .ltSlot i j =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .ltConstHi i c =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .ltConstLo i c =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .boolNotSlot i j =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .boolAndSlot i j k =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)
  | .boolOrSlot i j k =>
      simp only [propagatorOfProvedB6] at hprop
      exact absurd hprop (by intro hc; cases hc)

/-! ## Axiom checks

Every theorem above uses only the standard axioms. -/

#print axioms propMin_safe
#print axioms propMax_safe
#print axioms propAbs_safe
#print axioms propMin_entitled
#print axioms propMax_entitled
#print axioms propAbs_entitled
#print axioms propMin_reason_valid
#print axioms propMax_reason_valid
#print axioms propAbs_reason_valid
#print axioms divPin_slot_dom
#print axioms divPin_slot
#print axioms propDiv_safe
#print axioms propMod_safe
#print axioms propDiv_entitled
#print axioms propMod_entitled
#print axioms propDiv_reason_valid
#print axioms propMod_reason_valid
#print axioms propagatorOfProvedB6_mem
#print axioms propagatorOfProvedB6_run
#print axioms minSlot_pack
#print axioms maxSlot_pack
#print axioms absSlot_pack

/-! ## Smoke checks

One concrete state per family where the propagator fires `.implied`
with the expected literal and reason clause. -/

/-- Smoke state for `propMin`: slots `x ∈ [3,5]`, `y ∈ [1,4]`,
    `z ∈ [2,9]` — the first firing arm is the z-upper-bound
    narrowing to `min 5 4 = 4`. -/
def arith_smoke_min : State where
  domains := [[.int 3, .int 5], [.int 1, .int 4], [.int 2, .int 9]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propMin arith_smoke_min 0 1 2 = .implied (posLe 2 4)
    { clause := [posLe 2 4, negLe 0 5, negLe 1 4] } := by rfl

/-- Smoke state for `propMax`: slots `x ∈ [3,5]`, `y ∈ [1,4]`,
    `z ∈ [1,3]` — the first firing arm is the z-lower-bound
    narrowing to `max 3 1 = 3`. -/
def arith_smoke_max : State where
  domains := [[.int 3, .int 5], [.int 1, .int 4], [.int 1, .int 3]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propMax arith_smoke_max 0 1 2 = .implied (negLe 2 2)
    { clause := [negLe 2 2, posLe 0 2, posLe 1 0] } := by rfl

/-- Smoke state for `propAbs` (nonneg corner): slots `x ∈ [3,7]`,
    `r ∈ [2,9]` — the first firing arm narrows `r`'s lower bound to
    `absCornerMin 3 7 = 3`. -/
def arith_smoke_abs : State where
  domains := [[.int 3, .int 7], [.int 2, .int 9]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propAbs arith_smoke_abs 0 1 = .implied (negLe 1 2)
    { clause := [negLe 1 2, posLe 0 2, negLe 0 7] } := by rfl

/-- Smoke state for `propAbs` (operand upper bound): slots
    `x ∈ [−5,3]`, `r ∈ [0,2]` — the corner arms are stable (the
    interval straddles 0, corners 0 and 5 vs r-bounds 0/9... the
    first firing arm is the x-upper-bound narrowing to `r ≤ 2`). -/
def arith_smoke_abs2 : State where
  domains := [[.int (-5), .int 3], [.int 0, .int 2]]
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

example : propAbs arith_smoke_abs2 0 1 = .implied (posLe 0 2)
    { clause := [posLe 0 2, negLe 1 2] } := by rfl

end LeanFzn.Solver.Propagation
