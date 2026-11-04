/-
File: LeanFzn/Solver/Propagation/Proofs/Fam/Reif.lean

Purpose:
  PLAN L4: the explained propagators of the reified binary comparisons
  `int_le_reif` (`leReifSlot`), `int_eq_reif` (`eqReifSlot`) and
  `int_ne_reif` (`neReifSlot`).  The reified constraints read BOTH operands
  as integers and the reif slot as a Boolean unconditionally
  (`DomConstraint.SatisfiedBy`), so unlike `linLeReif` there is no
  Boolean-read hazard: delegation to the unreified propagator with a single
  escape literal on `r` is sound.

  Pinned direction (reif slot Boolean-pinned): delegate to the underlying
  (or negated) propagator and weave the pin escape into every emitted clause.
-/
import LeanFzn.Solver.Propagation.Proofs.Fam.Lin
import LeanFzn.Solver.Propagation.Proofs.Fam.Bool
import LeanFzn.Solver.Propagation.Propagate
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-- `int_le_reif(x_i, x_j, r)`: `r` pinned true propagates `x_i ≤ x_j`,
    pinned false propagates `x_j < x_i`; the clause of each emission gains the
    escape `r = false` (resp. `r = true`). -/
def propLeReifSlot (st : State) (i j r : Nat) : PropagationResult :=
  if domBoolPin st.domains r true then
    augmentRes [posBool r false] (propLe st i j)
  else if domBoolPin st.domains r false then
    augmentRes [posBool r true] (propLt st j i)
  else .stable

theorem propLeReifSlot_run_true {st : State} {i j r : Nat}
    (h : domBoolPin st.domains r true = true) :
    propLeReifSlot st i j r = augmentRes [posBool r false] (propLe st i j) := by
  simp [propLeReifSlot, h]

theorem propLeReifSlot_run_false {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = true) :
    propLeReifSlot st i j r = augmentRes [posBool r true] (propLt st j i) := by
  simp [propLeReifSlot, h1, h2]

theorem propLeReifSlot_run_stable {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = false) :
    propLeReifSlot st i j r = .stable := by
  simp [propLeReifSlot, h1, h2]

/-- Case split of a run: one of the three branches. -/
theorem propLeReifSlot_cases (st : State) (i j r : Nat) :
    (domBoolPin st.domains r true = true ∧
      propLeReifSlot st i j r = augmentRes [posBool r false] (propLe st i j)) ∨
    (domBoolPin st.domains r true = false ∧ domBoolPin st.domains r false = true ∧
      propLeReifSlot st i j r = augmentRes [posBool r true] (propLt st j i)) ∨
    (propLeReifSlot st i j r = .stable) := by
  cases h1 : domBoolPin st.domains r true with
  | true => exact Or.inl ⟨rfl, propLeReifSlot_run_true h1⟩
  | false =>
      cases h2 : domBoolPin st.domains r false with
      | true => exact Or.inr (Or.inl ⟨rfl, rfl, propLeReifSlot_run_false h1 h2⟩)
      | false => exact Or.inr (Or.inr (propLeReifSlot_run_stable h1 h2))

/-! ## The equality and disequality delegations

`int_eq_reif(x_i, x_j, r)` and `int_ne_reif(x_i, x_j, r)` read BOTH operands
as integers unconditionally, so pinned `true`/`false` rewrites them to
`eqSlot`/`neSlot` and the (already proved) `propEq`/`propNe` propagators
apply, with the `r`-pin escape woven into every emitted clause. -/

/-- `int_eq_reif(x_i, x_j, r)`: `r` pinned true propagates `x_i = x_j`,
    pinned false propagates `x_i ≠ x_j`; the clause of each emission gains the
    escape `r = false` (resp. `r = true`). -/
def propEqReifSlot (st : State) (i j r : Nat) : PropagationResult :=
  if domBoolPin st.domains r true then
    augmentRes [posBool r false] (propEq st i j)
  else if domBoolPin st.domains r false then
    augmentRes [posBool r true] (propNe st i j)
  else .stable

theorem propEqReifSlot_run_true {st : State} {i j r : Nat}
    (h : domBoolPin st.domains r true = true) :
    propEqReifSlot st i j r = augmentRes [posBool r false] (propEq st i j) := by
  simp [propEqReifSlot, h]

theorem propEqReifSlot_run_false {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = true) :
    propEqReifSlot st i j r = augmentRes [posBool r true] (propNe st i j) :=
  by
  simp [propEqReifSlot, h1, h2]

theorem propEqReifSlot_run_stable {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = false) :
    propEqReifSlot st i j r = .stable := by
  simp [propEqReifSlot, h1, h2]

/-- Case split of a run: one of the three branches. -/
theorem propEqReifSlot_cases (st : State) (i j r : Nat) :
    (domBoolPin st.domains r true = true ∧
      propEqReifSlot st i j r = augmentRes [posBool r false] (propEq st i j)) ∨
    (domBoolPin st.domains r true = false ∧ domBoolPin st.domains r false = true ∧
      propEqReifSlot st i j r = augmentRes [posBool r true] (propNe st i j)) ∨
    (propEqReifSlot st i j r = .stable) := by
  cases h1 : domBoolPin st.domains r true with
  | true => exact Or.inl ⟨rfl, propEqReifSlot_run_true h1⟩
  | false =>
      cases h2 : domBoolPin st.domains r false with
      | true => exact Or.inr (Or.inl ⟨rfl, rfl, propEqReifSlot_run_false h1 h2⟩)
      | false => exact Or.inr (Or.inr (propEqReifSlot_run_stable h1 h2))

/-- `int_ne_reif(x_i, x_j, r)`: `r` pinned true propagates `x_i ≠ x_j`,
    pinned false propagates `x_i = x_j`; the clause of each emission gains the
    escape `r = false` (resp. `r = true`). -/
def propNeReifSlot (st : State) (i j r : Nat) : PropagationResult :=
  if domBoolPin st.domains r true then
    augmentRes [posBool r false] (propNe st i j)
  else if domBoolPin st.domains r false then
    augmentRes [posBool r true] (propEq st i j)
  else .stable

theorem propNeReifSlot_run_true {st : State} {i j r : Nat}
    (h : domBoolPin st.domains r true = true) :
    propNeReifSlot st i j r = augmentRes [posBool r false] (propNe st i j) := by
  simp [propNeReifSlot, h]

theorem propNeReifSlot_run_false {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = true) :
    propNeReifSlot st i j r = augmentRes [posBool r true] (propEq st i j) :=
  by
  simp [propNeReifSlot, h1, h2]

theorem propNeReifSlot_run_stable {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = false) :
    propNeReifSlot st i j r = .stable := by
  simp [propNeReifSlot, h1, h2]

/-- Case split of a run: one of the three branches. -/
theorem propNeReifSlot_cases (st : State) (i j r : Nat) :
    (domBoolPin st.domains r true = true ∧
      propNeReifSlot st i j r = augmentRes [posBool r false] (propNe st i j)) ∨
    (domBoolPin st.domains r true = false ∧ domBoolPin st.domains r false = true ∧
      propNeReifSlot st i j r = augmentRes [posBool r true] (propEq st i j)) ∨
    (propNeReifSlot st i j r = .stable) := by
  cases h1 : domBoolPin st.domains r true with
  | true => exact Or.inl ⟨rfl, propNeReifSlot_run_true h1⟩
  | false =>
      cases h2 : domBoolPin st.domains r false with
      | true => exact Or.inr (Or.inl ⟨rfl, rfl, propNeReifSlot_run_false h1 h2⟩)
      | false => exact Or.inr (Or.inr (propNeReifSlot_run_stable h1 h2))

/-! ## Satisfaction bridges -/

theorem leReif_sat_inv {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.leReifSlot i j r).SatisfiedBy a) :
    ∃ (p q : Int) (rb : Bool), a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
      a[r]? = some (.bool rb) ∧ (rb = true ↔ p ≤ q) := h

/-- A reif slot reading `true` forces the underlying `x_i ≤ x_j`. -/
theorem leReif_true_sat {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.leReifSlot i j r).SatisfiedBy a)
    (hr : a[r]? = some (.bool true)) :
    (DomConstraint.leSlot i j).SatisfiedBy a := by
  obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := leReif_sat_inv h
  rw [hr] at hrb
  have hv := Option.some.inj hrb
  cases hv
  exact ⟨p, q, hp, hq, hiff.mp rfl⟩

/-- A reif slot reading `false` forces `x_j < x_i`. -/
theorem leReif_false_sat {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.leReifSlot i j r).SatisfiedBy a)
    (hr : a[r]? = some (.bool false)) :
    (DomConstraint.ltSlot j i).SatisfiedBy a := by
  obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := leReif_sat_inv h
  rw [hr] at hrb
  have hv := Option.some.inj hrb
  cases hv
  exact ⟨q, p, hq, hp, Int.not_le.mp (fun hle => by simpa using hiff.mpr hle)⟩

/-- The slot reads of a satisfied reified comparison are integers. -/
theorem leReif_reads {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.leReifSlot i j r).SatisfiedBy a) :
    ∃ (p q : Int) (rb : Bool), a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
      a[r]? = some (.bool rb) := by
  obtain ⟨p, q, rb, hp, hq, hrb, -⟩ := leReif_sat_inv h
  exact ⟨p, q, rb, hp, hq, hrb⟩

theorem leReif_split_true {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.leReifSlot i j r).SatisfiedBy a) :
    (∃ q ∈ [posBool r false], q.eval a = some true) ∨
      (DomConstraint.leSlot i j).SatisfiedBy a := by
  obtain ⟨-, -, rb, -, -, hrb, -⟩ := leReif_sat_inv h
  cases rb with
  | false => exact Or.inl ⟨posBool r false, List.mem_singleton_self _, posBool_eval_true hrb⟩
  | true => exact Or.inr (leReif_true_sat h hrb)

theorem leReif_split_false {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.leReifSlot i j r).SatisfiedBy a) :
    (∃ q ∈ [posBool r true], q.eval a = some true) ∨
      (DomConstraint.ltSlot j i).SatisfiedBy a := by
  obtain ⟨-, -, rb, -, -, hrb, -⟩ := leReif_sat_inv h
  cases rb with
  | true => exact Or.inl ⟨posBool r true, List.mem_singleton_self _, posBool_eval_true hrb⟩
  | false => exact Or.inr (leReif_false_sat h hrb)

/-! ### `int_eq_reif` (`eqReifSlot`) -/

theorem eqReif_sat_inv {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.eqReifSlot i j r).SatisfiedBy a) :
    ∃ (p q : Int) (rb : Bool), a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
      a[r]? = some (.bool rb) ∧ (rb = true ↔ p = q) := h

/-- A reif slot reading `true` forces the underlying `x_i = x_j`. -/
theorem eqReif_true_sat {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.eqReifSlot i j r).SatisfiedBy a)
    (hr : a[r]? = some (.bool true)) :
    (DomConstraint.eqSlot i j).SatisfiedBy a := by
  obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := eqReif_sat_inv h
  rw [hr] at hrb
  have hv := Option.some.inj hrb
  cases hv
  exact ⟨.int p, .int q, hp, hq, by rw [hiff.mp rfl]⟩

/-- A reif slot reading `false` forces `x_i ≠ x_j`. -/
theorem eqReif_false_sat {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.eqReifSlot i j r).SatisfiedBy a)
    (hr : a[r]? = some (.bool false)) :
    (DomConstraint.neSlot i j).SatisfiedBy a := by
  obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := eqReif_sat_inv h
  rw [hr] at hrb
  have hv := Option.some.inj hrb
  cases hv
  have hpq : p ≠ q := fun hpq => Bool.false_ne_true (hiff.mpr hpq)
  exact ⟨.int p, .int q, hp, hq, fun h => hpq (Value.int.inj h)⟩

/-- The slot reads of a satisfied reified equality are integers. -/
theorem eqReif_reads {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.eqReifSlot i j r).SatisfiedBy a) :
    ∃ (p q : Int) (rb : Bool), a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
      a[r]? = some (.bool rb) := by
  obtain ⟨p, q, rb, hp, hq, hrb, -⟩ := eqReif_sat_inv h
  exact ⟨p, q, rb, hp, hq, hrb⟩

theorem eqReif_split_true {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.eqReifSlot i j r).SatisfiedBy a) :
    (∃ q ∈ [posBool r false], q.eval a = some true) ∨
      (DomConstraint.eqSlot i j).SatisfiedBy a := by
  obtain ⟨-, -, rb, -, -, hrb, -⟩ := eqReif_sat_inv h
  cases rb with
  | false => exact Or.inl ⟨posBool r false, List.mem_singleton_self _, posBool_eval_true hrb⟩
  | true => exact Or.inr (eqReif_true_sat h hrb)

theorem eqReif_split_false {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.eqReifSlot i j r).SatisfiedBy a) :
    (∃ q ∈ [posBool r true], q.eval a = some true) ∨
      (DomConstraint.neSlot i j).SatisfiedBy a := by
  obtain ⟨-, -, rb, -, -, hrb, -⟩ := eqReif_sat_inv h
  cases rb with
  | true => exact Or.inl ⟨posBool r true, List.mem_singleton_self _, posBool_eval_true hrb⟩
  | false => exact Or.inr (eqReif_false_sat h hrb)

/-! ### `int_ne_reif` (`neReifSlot`) -/

theorem neReif_sat_inv {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.neReifSlot i j r).SatisfiedBy a) :
    ∃ (p q : Int) (rb : Bool), a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
      a[r]? = some (.bool rb) ∧ (rb = true ↔ p ≠ q) := h

/-- A reif slot reading `true` forces `x_i ≠ x_j`. -/
theorem neReif_true_sat {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.neReifSlot i j r).SatisfiedBy a)
    (hr : a[r]? = some (.bool true)) :
    (DomConstraint.neSlot i j).SatisfiedBy a := by
  obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := neReif_sat_inv h
  rw [hr] at hrb
  have hv := Option.some.inj hrb
  cases hv
  have hpq : p ≠ q := hiff.mp rfl
  exact ⟨.int p, .int q, hp, hq, fun h => hpq (Value.int.inj h)⟩

/-- A reif slot reading `false` forces `x_i = x_j`. -/
theorem neReif_false_sat {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.neReifSlot i j r).SatisfiedBy a)
    (hr : a[r]? = some (.bool false)) :
    (DomConstraint.eqSlot i j).SatisfiedBy a := by
  obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := neReif_sat_inv h
  rw [hr] at hrb
  have hv := Option.some.inj hrb
  cases hv
  have hpq : p = q := by
    by_cases h : p = q
    · exact h
    · exact absurd (hiff.mpr h) (by simp)
  exact ⟨.int p, .int q, hp, hq, by rw [hpq]⟩

/-- The slot reads of a satisfied reified disequality are integers. -/
theorem neReif_reads {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.neReifSlot i j r).SatisfiedBy a) :
    ∃ (p q : Int) (rb : Bool), a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
      a[r]? = some (.bool rb) := by
  obtain ⟨p, q, rb, hp, hq, hrb, -⟩ := neReif_sat_inv h
  exact ⟨p, q, rb, hp, hq, hrb⟩

theorem neReif_split_true {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.neReifSlot i j r).SatisfiedBy a) :
    (∃ q ∈ [posBool r false], q.eval a = some true) ∨
      (DomConstraint.neSlot i j).SatisfiedBy a := by
  obtain ⟨-, -, rb, -, -, hrb, -⟩ := neReif_sat_inv h
  cases rb with
  | false => exact Or.inl ⟨posBool r false, List.mem_singleton_self _, posBool_eval_true hrb⟩
  | true => exact Or.inr (neReif_true_sat h hrb)

theorem neReif_split_false {a : Assignment} {i j r : Nat}
    (h : (DomConstraint.neReifSlot i j r).SatisfiedBy a) :
    (∃ q ∈ [posBool r true], q.eval a = some true) ∨
      (DomConstraint.eqSlot i j).SatisfiedBy a := by
  obtain ⟨-, -, rb, -, -, hrb, -⟩ := neReif_sat_inv h
  cases rb with
  | true => exact Or.inl ⟨posBool r true, List.mem_singleton_self _, posBool_eval_true hrb⟩
  | false => exact Or.inr (neReif_false_sat h hrb)

/-! ## PLAN G1: the unpinned bounds-decide-`r` arm

With the reif slot unpinned, every pinned delegation of `propLeReifSlot` is
`.stable`: a free reif Boolean is never decided by the operand bounds.  The
bounds arm `propLeReifB` below closes that gap, mirroring `propLinLeReifB`
(`Fam/Lin.lean`): when the operand extrema separate (`max Dᵢ ≤ min Dⱼ`,
resp. `max Dⱼ < min Dᵢ`), the arm implies `r = true` (resp. `r = false`)
with the state bound facts as the (falsified) cause literals.

The arm's entailment is purely arithmetic and state-free: at a solution of
the reified constraint where the pivot is false and both causes are false
at the read values, the causes force `xᵢ ≤ xⱼ` (resp. `xⱼ < xᵢ`),
contradicting the reif reading.  The guards keep every emission well-typed
and Boolean-read safe: the reif slot's domain is Boolean-only and nonempty,
both operands have in-range nonempty integer-only domains, and neither
operand aliases the reif slot.  Empty and mixed domains therefore never
fire. -/

/-- The separation test of the unpinned arm, on explicit extrema:
    `mx_i ≤ mn_j` pins `r = true`; `mx_j < mn_i` pins `r = false`.
    The reason's two non-pivot literals are the state bound facts that
    force the separation (`xᵢ ≤ mx_i` and `xⱼ ≥ mn_j`, respectively
    `xᵢ ≥ mn_i` and `xⱼ ≤ mx_j`): they are false at every fitting
    assignment of the state, and their falsity together with the pivot's
    falsity contradicts the reified constraint. -/
def leReifSepRes (i j r : Nat) (mn_i mx_i mn_j mx_j : Int) : PropagationResult :=
  if mx_i ≤ mn_j then
    .implied (posBool r true)
      { clause := [posBool r true, negLe i mx_i, posLe j (mn_j - 1)] }
  else if mx_j < mn_i then
    .implied (posBool r false)
      { clause := [posBool r false, posLe i (mn_i - 1), negLe j mx_j] }
  else .stable

/-- The unpinned bounds arm of `int_le_reif`: with the reif slot unpinned
    (and Boolean-only, nonempty) and both operands in-range, nonempty,
    integer-only and distinct from the reif slot, the operand extrema
    decide `r` (`leReifSepRes`); every other shape is `.stable`. -/
def propLeReifB (st : State) (i j r : Nat) : PropagationResult :=
  if (domBoolPin st.domains r true || domBoolPin st.domains r false) = true then .stable
  else if (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) && decide (i ≠ r) && decide (j ≠ r)
      && domsIntOnlyB st.domains [i, j]) = true then
    match domMinI (st.domains.getD i Dom.empty), domMaxI (st.domains.getD i Dom.empty),
          domMinI (st.domains.getD j Dom.empty), domMaxI (st.domains.getD j Dom.empty) with
    | some mn_i, some mx_i, some mn_j, some mx_j =>
        leReifSepRes i j r mn_i mx_i mn_j mx_j
    | _, _, _, _ => .stable
  else .stable

/-- Run equation of the `r = true` separation. -/
theorem leReifSepRes_run_true {i j r : Nat} {mn_i mx_i mn_j mx_j : Int}
    (h : mx_i ≤ mn_j) :
    leReifSepRes i j r mn_i mx_i mn_j mx_j =
      .implied (posBool r true)
        { clause := [posBool r true, negLe i mx_i, posLe j (mn_j - 1)] } := by
  simp [leReifSepRes, h]

/-- Run equation of the `r = false` separation. -/
theorem leReifSepRes_run_false {i j r : Nat} {mn_i mx_i mn_j mx_j : Int}
    (h1 : ¬ mx_i ≤ mn_j) (h2 : mx_j < mn_i) :
    leReifSepRes i j r mn_i mx_i mn_j mx_j =
      .implied (posBool r false)
        { clause := [posBool r false, posLe i (mn_i - 1), negLe j mx_j] } := by
  simp [leReifSepRes, h1, h2]

/-- Run equation of the unseparated case. -/
theorem leReifSepRes_run_stable {i j r : Nat} {mn_i mx_i mn_j mx_j : Int}
    (h1 : ¬ mx_i ≤ mn_j) (h2 : ¬ mx_j < mn_i) :
    leReifSepRes i j r mn_i mx_i mn_j mx_j = .stable := by
  simp [leReifSepRes, h1, h2]

/-- A pinned reif slot makes the arm `.stable` (the pinned delegations own
    that case). -/
theorem propLeReifB_stable_of_pin {st : State} {i j r : Nat}
    (h : (domBoolPin st.domains r true || domBoolPin st.domains r false) = true) :
    propLeReifB st i j r = .stable := by
  unfold propLeReifB
  rw [if_pos h]

/-- A failed guard makes the arm `.stable` (empty, mixed or aliased slots). -/
theorem propLeReifB_stable_of_guard {st : State} {i j r : Nat}
    (h1 : (domBoolPin st.domains r true || domBoolPin st.domains r false) = false)
    (h2 : (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) && decide (i ≠ r) && decide (j ≠ r)
      && domsIntOnlyB st.domains [i, j]) = false) :
    propLeReifB st i j r = .stable := by
  unfold propLeReifB
  rw [if_neg (by rw [h1]; simp), if_neg (by rw [h2]; simp)]

/-- Under the guards (and unpinned), the arm reduces to the separation test
    on the four operand extrema. -/
theorem propLeReifB_run_of_extrema {st : State} {i j r : Nat}
    {mn_i mx_i mn_j mx_j : Int}
    (h1 : (domBoolPin st.domains r true || domBoolPin st.domains r false) = false)
    (h2 : (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) && decide (i ≠ r) && decide (j ≠ r)
      && domsIntOnlyB st.domains [i, j]) = true)
    (hmn_i : domMinI (st.domains.getD i Dom.empty) = some mn_i)
    (hmx_i : domMaxI (st.domains.getD i Dom.empty) = some mx_i)
    (hmn_j : domMinI (st.domains.getD j Dom.empty) = some mn_j)
    (hmx_j : domMaxI (st.domains.getD j Dom.empty) = some mx_j) :
    propLeReifB st i j r = leReifSepRes i j r mn_i mx_i mn_j mx_j := by
  unfold propLeReifB
  rw [if_neg (by rw [h1]; simp), if_pos h2]
  simp only [hmn_i, hmx_i, hmn_j, hmx_j]

/-- Emission inversion of the bounds arm: the result is `.stable`, or the
    guards hold and one of the two separation emissions fires with the
    extrema that witness it. -/
theorem propLeReifB_emission_inv {st : State} {i j r : Nat}
    {res : PropagationResult} (h : propLeReifB st i j r = res) :
    res = .stable ∨
    ((domBoolPin st.domains r true || domBoolPin st.domains r false) = false ∧
     domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) = true ∧
     (decide (i ≠ r)) = true ∧ (decide (j ≠ r)) = true ∧
     domsIntOnlyB st.domains [i, j] = true ∧
     ∃ mn_i mx_i mn_j mx_j : Int,
       domMinI (st.domains.getD i Dom.empty) = some mn_i ∧
       domMaxI (st.domains.getD i Dom.empty) = some mx_i ∧
       domMinI (st.domains.getD j Dom.empty) = some mn_j ∧
       domMaxI (st.domains.getD j Dom.empty) = some mx_j ∧
       mx_i ≤ mn_j ∧
       res = .implied (posBool r true)
         { clause := [posBool r true, negLe i mx_i, posLe j (mn_j - 1)] }) ∨
    ((domBoolPin st.domains r true || domBoolPin st.domains r false) = false ∧
     domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) = true ∧
     (decide (i ≠ r)) = true ∧ (decide (j ≠ r)) = true ∧
     domsIntOnlyB st.domains [i, j] = true ∧
     ∃ mn_i mx_i mn_j mx_j : Int,
       domMinI (st.domains.getD i Dom.empty) = some mn_i ∧
       domMaxI (st.domains.getD i Dom.empty) = some mx_i ∧
       domMinI (st.domains.getD j Dom.empty) = some mn_j ∧
       domMaxI (st.domains.getD j Dom.empty) = some mx_j ∧
       mx_j < mn_i ∧
       res = .implied (posBool r false)
         { clause := [posBool r false, posLe i (mn_i - 1), negLe j mx_j] }) := by
  unfold propLeReifB at h
  by_cases h1 : (domBoolPin st.domains r true || domBoolPin st.domains r false) = true
  · rw [if_pos h1] at h
    exact Or.inl h.symm
  · rw [if_neg h1] at h
    by_cases h2 : (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) && decide (i ≠ r)
        && decide (j ≠ r) && domsIntOnlyB st.domains [i, j]) = true
    · rw [if_pos h2] at h
      have h2' := h2
      rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true] at h2'
      obtain ⟨⟨⟨hb, hnei⟩, hnej⟩, hint⟩ := h2'
      cases hmn_i : domMinI (st.domains.getD i Dom.empty) with
      | none =>
          simp only [hmn_i] at h
          exact Or.inl h.symm
      | some mn_i =>
        cases hmx_i : domMaxI (st.domains.getD i Dom.empty) with
        | none =>
            simp only [hmn_i, hmx_i] at h
            exact Or.inl h.symm
        | some mx_i =>
          cases hmn_j : domMinI (st.domains.getD j Dom.empty) with
          | none =>
              simp only [hmn_i, hmx_i, hmn_j] at h
              exact Or.inl h.symm
          | some mn_j =>
            cases hmx_j : domMaxI (st.domains.getD j Dom.empty) with
            | none =>
                simp only [hmn_i, hmx_i, hmn_j, hmx_j] at h
                exact Or.inl h.symm
            | some mx_j =>
                simp only [hmn_i, hmx_i, hmn_j, hmx_j] at h
                by_cases hsep : mx_i ≤ mn_j
                · rw [leReifSepRes_run_true hsep] at h
                  exact Or.inr (Or.inl ⟨Bool.eq_false_iff.mpr h1, hb, hnei, hnej,
                    hint, mn_i, mx_i, mn_j, mx_j, rfl, rfl, rfl, rfl,
                    hsep, h.symm⟩)
                · by_cases hsep2 : mx_j < mn_i
                  · rw [leReifSepRes_run_false hsep hsep2] at h
                    exact Or.inr (Or.inr ⟨Bool.eq_false_iff.mpr h1, hb, hnei, hnej,
                      hint, mn_i, mx_i, mn_j, mx_j, rfl, rfl, rfl, rfl,
                      hsep2, h.symm⟩)
                  · rw [leReifSepRes_run_stable hsep hsep2] at h
                    exact Or.inl h.symm
    · rw [if_neg h2] at h
      exact Or.inl h.symm

/-- The bounds arm never reports a conflict: it is `.stable` or an implied
    separation pin. -/
theorem propLeReifB_ne_conflict {st : State} {i j r : Nat} {c : Clause}
    (h : propLeReifB st i j r = .conflict c) : False := by
  rcases propLeReifB_emission_inv h with hstable |
    ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j, -, -, -, -, -, hres⟩ |
    ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j, -, -, -, -, -, hres⟩
  · cases hstable
  · cases hres
  · cases hres

/-- Complete case split of the arm: `.stable`, or the `r = true` pin (with
    the guards and the separating extrema), or the `r = false` pin.  The
    guards are absorbed into the emission cases. -/
theorem propLeReifB_cases (st : State) (i j r : Nat) :
    propLeReifB st i j r = .stable ∨
    (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) = true ∧ i ≠ r ∧ j ≠ r ∧
      domsIntOnlyB st.domains [i, j] = true ∧
      ∃ mn_i mx_i mn_j mx_j : Int,
        domMinI (st.domains.getD i Dom.empty) = some mn_i ∧
        domMaxI (st.domains.getD i Dom.empty) = some mx_i ∧
        domMinI (st.domains.getD j Dom.empty) = some mn_j ∧
        domMaxI (st.domains.getD j Dom.empty) = some mx_j ∧
        mx_i ≤ mn_j ∧
        propLeReifB st i j r = .implied (posBool r true)
          { clause := [posBool r true, negLe i mx_i, posLe j (mn_j - 1)] }) ∨
    (domBoolOnlyB (Dom.enum (st.domains.getD r Dom.empty)) = true ∧ i ≠ r ∧ j ≠ r ∧
      domsIntOnlyB st.domains [i, j] = true ∧
      ∃ mn_i mx_i mn_j mx_j : Int,
        domMinI (st.domains.getD i Dom.empty) = some mn_i ∧
        domMaxI (st.domains.getD i Dom.empty) = some mx_i ∧
        domMinI (st.domains.getD j Dom.empty) = some mn_j ∧
        domMaxI (st.domains.getD j Dom.empty) = some mx_j ∧
        mx_j < mn_i ∧
        propLeReifB st i j r = .implied (posBool r false)
          { clause := [posBool r false, posLe i (mn_i - 1), negLe j mx_j] }) := by
  rcases propLeReifB_emission_inv (res := propLeReifB st i j r) rfl with hstable |
    ⟨-, hb, hnei, hnej, hint, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, hsep, he⟩ |
    ⟨-, hb, hnei, hnej, hint, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, hsep, he⟩
  · exact Or.inl hstable
  · exact Or.inr (Or.inl ⟨hb, of_decide_eq_true hnei, of_decide_eq_true hnej, hint,
      mn_i, mx_i, mn_j, mx_j, hmn_i, hmx_i, hmn_j, hmx_j, hsep, he⟩)
  · exact Or.inr (Or.inr ⟨hb, of_decide_eq_true hnei, of_decide_eq_true hnej, hint,
      mn_i, mx_i, mn_j, mx_j, hmn_i, hmx_i, hmn_j, hmx_j, hsep, he⟩)

/-! ## PLAN G1: the strengthened `leReifSlot` run function

`propLeReifSlotB` is the G1 candidate to register in place of
`propLeReifSlot`: its two pinned delegations are the same expressions (so
the pinned-direction behavior is byte-identical), and its unpinned case
falls through to the bounds arm `propLeReifB` instead of `.stable`.  The
run equations below are the interface the integration step consumes: the
pinned arms rewrite exactly as `propLeReifSlot_run_true`/`_run_false`, and
the unpinned arm rewrites to `propLeReifB`, whose obligations are the
package above.  Registering it (and re-deriving the downstream obligation
theorems with these equations) is the coordinator-owned wiring step. -/

/-- The strengthened `int_le_reif` run function: pinned `r` delegates
    exactly as `propLeReifSlot`; unpinned `r` runs the bounds arm. -/
def propLeReifSlotB (st : State) (i j r : Nat) : PropagationResult :=
  if domBoolPin st.domains r true then
    augmentRes [posBool r false] (propLe st i j)
  else if domBoolPin st.domains r false then
    augmentRes [posBool r true] (propLt st j i)
  else propLeReifB st i j r

theorem propLeReifSlotB_run_true {st : State} {i j r : Nat}
    (h : domBoolPin st.domains r true = true) :
    propLeReifSlotB st i j r = augmentRes [posBool r false] (propLe st i j) := by
  simp [propLeReifSlotB, h]

theorem propLeReifSlotB_run_false {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = true) :
    propLeReifSlotB st i j r = augmentRes [posBool r true] (propLt st j i) := by
  simp [propLeReifSlotB, h1, h2]

/-- The unpinned arm's run equation: the strengthened function falls
    through to the bounds arm `propLeReifB`. -/
theorem propLeReifSlotB_run_b {st : State} {i j r : Nat}
    (h1 : domBoolPin st.domains r true = false)
    (h2 : domBoolPin st.domains r false = false) :
    propLeReifSlotB st i j r = propLeReifB st i j r := by
  simp [propLeReifSlotB, h1, h2]

/-- The pinned-direction behavior is byte-identical: whenever the reif slot
    is pinned, the strengthened function returns exactly the pinned
    delegation of `propLeReifSlot`. -/
theorem propLeReifSlotB_eq_of_pinned {st : State} {i j r : Nat}
    (h : (domBoolPin st.domains r true || domBoolPin st.domains r false) = true) :
    propLeReifSlotB st i j r = propLeReifSlot st i j r := by
  rw [Bool.or_eq_true] at h
  rcases h with h | h
  · rw [propLeReifSlotB_run_true h, propLeReifSlot_run_true h]
  · have h1 : domBoolPin st.domains r true = false :=
      domBoolPin_excl h (by decide)
    rw [propLeReifSlotB_run_false h1 h, propLeReifSlot_run_false h1 h]

/-- Complete case split of the strengthened run: the original three branches
    with the unpinned case refined to the bounds-arm fallthrough. -/
theorem propLeReifSlotB_cases (st : State) (i j r : Nat) :
    (domBoolPin st.domains r true = true ∧
      propLeReifSlotB st i j r = augmentRes [posBool r false] (propLe st i j)) ∨
    (domBoolPin st.domains r true = false ∧ domBoolPin st.domains r false = true ∧
      propLeReifSlotB st i j r = augmentRes [posBool r true] (propLt st j i)) ∨
    (domBoolPin st.domains r true = false ∧ domBoolPin st.domains r false = false ∧
      propLeReifSlotB st i j r = propLeReifB st i j r) := by
  cases h1 : domBoolPin st.domains r true with
  | true => exact Or.inl ⟨rfl, propLeReifSlotB_run_true h1⟩
  | false =>
      cases h2 : domBoolPin st.domains r false with
      | true => exact Or.inr (Or.inl ⟨rfl, rfl, propLeReifSlotB_run_false h1 h2⟩)
      | false => exact Or.inr (Or.inr ⟨rfl, rfl, propLeReifSlotB_run_b h1 h2⟩)

/-! ## PLAN G1: the arm's obligation package

The arm's emissions are `.implied` pins only (`propLeReifB_ne_conflict`), so
the obligation package is the implied-literal arm of the safe triple
(`propLeReifB_implied_true`), the state-free reason validity with canonical
normal forms (`propLeReifB_reason_valid`), decidedness at internal solutions
(`propLeReifB_implied_decided`), and the faithful falsification of the two
bound causes (`propLeReifB_causes_false_fits`) that the integration lifts to
`SemFalsifiedBefore` via the state's `BoundsExpl`.  The pinned arms of
`propLeReifSlotB` reuse the existing `propLeReifSlot` obligations verbatim
through `propLeReifSlotB_run_true`/`_run_false`. -/

/-- With an integer read, a non-true `negLe` bounds the read above by the
    literal's constant. -/
theorem le_of_negLe_not_true {a : Assignment} {s : Nat} {k : Int} {x : Int}
    (hx : slotInt a s = some x) (h : ¬ (negLe s k).eval a = some true) : x ≤ k := by
  rw [eval_negLe, hx] at h
  simp only [Option.map_some] at h
  cases hd : decide (x ≤ k) with
  | true => exact of_decide_eq_true hd
  | false =>
      rw [hd] at h
      exact absurd rfl h

/-- With an integer read, a non-true `posLe` bounds the read below by the
    literal's constant plus one. -/
theorem lt_of_posLe_not_true {a : Assignment} {s : Nat} {k : Int} {x : Int}
    (hx : slotInt a s = some x) (h : ¬ (posLe s k).eval a = some true) : k < x := by
  rw [eval_posLe, hx] at h
  simp only [Option.map_some] at h
  cases hd : decide (x ≤ k) with
  | true =>
      rw [hd] at h
      exact absurd rfl h
  | false => exact Int.not_le.mp (of_decide_eq_false hd)

/-- Faithful falsification of a max-cause: at every fitting assignment the
    max-cause literal `negLe s (domMaxI …)` of the arm reads false. -/
theorem negLe_eval_false_of_domMaxI {st : State} {a : Assignment} {s : Nat}
    {mx x : Int}
    (hfit : Assignment.Fits st.domains a)
    (hmx : domMaxI (st.domains.getD s Dom.empty) = some mx)
    (hx : slotInt a s = some x) :
    (negLe s mx).eval a = some false := by
  rw [eval_negLe, hx]
  show (some (!(decide (x ≤ mx))) : Option Bool) = some false
  rw [decide_eq_true (fits_max_bound hfit hmx hx)]
  rfl

/-- Faithful falsification of a min-cause: at every fitting assignment the
    min-cause literal `posLe s (domMinI … − 1)` of the arm reads false. -/
theorem posLe_eval_false_of_domMinI {st : State} {a : Assignment} {s : Nat}
    {mn x : Int}
    (hfit : Assignment.Fits st.domains a)
    (hmn : domMinI (st.domains.getD s Dom.empty) = some mn)
    (hx : slotInt a s = some x) :
    (posLe s (mn - 1)).eval a = some false := by
  rw [eval_posLe, hx]
  show (some (decide (x ≤ mn - 1)) : Option Bool) = some false
  rw [decide_eq_false_iff_not.mpr (by have := fits_min_bound hfit hmn hx; omega)]

/-- The arm's four bound causes are falsified by the state's bounds: at every
    fitting assignment under the operand guard, the two causes of either
    emission read false. -/
theorem propLeReifB_causes_false_fits {st : State} {a : Assignment}
    {i j : Nat} {mn_i mx_i mn_j mx_j : Int}
    (hfit : Assignment.Fits st.domains a)
    (hint : domsIntOnlyB st.domains [i, j] = true)
    (hmn_i : domMinI (st.domains.getD i Dom.empty) = some mn_i)
    (hmx_i : domMaxI (st.domains.getD i Dom.empty) = some mx_i)
    (hmn_j : domMinI (st.domains.getD j Dom.empty) = some mn_j)
    (hmx_j : domMaxI (st.domains.getD j Dom.empty) = some mx_j) :
    (negLe i mx_i).eval a = some false ∧
      (posLe j (mn_j - 1)).eval a = some false ∧
      (posLe i (mn_i - 1)).eval a = some false ∧
      (negLe j mx_j).eval a = some false := by
  obtain ⟨xi, hxi⟩ := domsIntOnlyB_fits_read hint hfit i (by simp)
  obtain ⟨xj, hxj⟩ := domsIntOnlyB_fits_read hint hfit j (by simp)
  exact ⟨negLe_eval_false_of_domMaxI hfit hmx_i (slotInt_of_getElem_int hxi),
    posLe_eval_false_of_domMinI hfit hmn_j (slotInt_of_getElem_int hxj),
    posLe_eval_false_of_domMinI hfit hmn_i (slotInt_of_getElem_int hxi),
    negLe_eval_false_of_domMaxI hfit hmx_j (slotInt_of_getElem_int hxj)⟩

/-- Emission shape (typing support): a firing arm emission is one of the two
    separation clauses — the pivot `posBool` on the reif slot and the two
    order literals on the (distinct) operand slots. -/
theorem propLeReifB_implied_clause {st : State} {i j r : Nat}
    {l : Literal} {rs : Reason}
    (hrun : propLeReifB st i j r = .implied l rs) :
    (∃ mn_i mx_i mn_j mx_j : Int,
      domMinI (st.domains.getD i Dom.empty) = some mn_i ∧
      domMaxI (st.domains.getD i Dom.empty) = some mx_i ∧
      domMinI (st.domains.getD j Dom.empty) = some mn_j ∧
      domMaxI (st.domains.getD j Dom.empty) = some mx_j ∧
      l = posBool r true ∧
      rs.clause = [posBool r true, negLe i mx_i, posLe j (mn_j - 1)]) ∨
    (∃ mn_i mx_i mn_j mx_j : Int,
      domMinI (st.domains.getD i Dom.empty) = some mn_i ∧
      domMaxI (st.domains.getD i Dom.empty) = some mx_i ∧
      domMinI (st.domains.getD j Dom.empty) = some mn_j ∧
      domMaxI (st.domains.getD j Dom.empty) = some mx_j ∧
      l = posBool r false ∧
      rs.clause = [posBool r false, posLe i (mn_i - 1), negLe j mx_j]) := by
  rcases propLeReifB_emission_inv hrun with hstable |
    ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, -, hres⟩ |
    ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, -, hres⟩
  · exact absurd hstable (by intro hc; cases hc)
  · have hl : l = posBool r true := by cases hres; rfl
    have hrs : rs = { clause := [posBool r true, negLe i mx_i, posLe j (mn_j - 1)] } := by
      cases hres
      rfl
    exact Or.inl ⟨mn_i, mx_i, mn_j, mx_j, hmn_i, hmx_i, hmn_j, hmx_j,
      hl, by rw [hrs]⟩
  · have hl : l = posBool r false := by cases hres; rfl
    have hrs : rs = { clause := [posBool r false, posLe i (mn_i - 1), negLe j mx_j] } := by
      cases hres
      rfl
    exact Or.inr ⟨mn_i, mx_i, mn_j, mx_j, hmn_i, hmx_i, hmn_j, hmx_j,
      hl, by rw [hrs]⟩

/-- The bounds arm's implied pin is true at every fitting solution of the
    reified constraint (the arm's implied-literal obligation of the safe
    triple): the state bounds force the separation the pivot records. -/
theorem propLeReifB_implied_true {st : State} {i j r : Nat}
    {l : Literal} {rs : Reason}
    (hrun : propLeReifB st i j r = .implied l rs) :
    ∀ a, Assignment.Fits st.domains a →
      (DomConstraint.leReifSlot i j r).SatisfiedBy a →
      l.eval a = some true := by
  intro a hfit hcons
  rcases propLeReifB_emission_inv hrun with hstable |
    ⟨-, -, -, -, hint, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, hsep, hres⟩ |
    ⟨-, -, -, -, hint, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, hsep, hres⟩
  · exact absurd hstable (by intro hc; cases hc)
  · have hl : l = posBool r true := by cases hres; rfl
    rw [hl]
    obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := leReif_sat_inv hcons
    obtain ⟨xi, hxi⟩ := domsIntOnlyB_fits_read hint hfit i (by simp)
    obtain ⟨xj, hxj⟩ := domsIntOnlyB_fits_read hint hfit j (by simp)
    have hki : xi = p := by
      have h1 : a[i]! = .int p := by rw [List.getElem!_eq_getElem?_getD, hp]; rfl
      rw [h1] at hxi
      exact (Value.int.inj hxi).symm
    have hkj : xj = q := by
      have h1 : a[j]! = .int q := by rw [List.getElem!_eq_getElem?_getD, hq]; rfl
      rw [h1] at hxj
      exact (Value.int.inj hxj).symm
    have hslot_i : slotInt a i = some p := by
      rw [slotInt_of_getElem_int hxi, hki]
    have hslot_j : slotInt a j = some q := by
      rw [slotInt_of_getElem_int hxj, hkj]
    have hpi : p ≤ mx_i := fits_max_bound hfit hmx_i hslot_i
    have hqj : mn_j ≤ q := fits_min_bound hfit hmn_j hslot_j
    have hpq : p ≤ q := Int.le_trans hpi (Int.le_trans hsep hqj)
    have hrb' : rb = true := hiff.mpr hpq
    rw [hrb'] at hrb
    exact posBool_eval_true hrb
  · have hl : l = posBool r false := by cases hres; rfl
    rw [hl]
    obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := leReif_sat_inv hcons
    obtain ⟨xi, hxi⟩ := domsIntOnlyB_fits_read hint hfit i (by simp)
    obtain ⟨xj, hxj⟩ := domsIntOnlyB_fits_read hint hfit j (by simp)
    have hki : xi = p := by
      have h1 : a[i]! = .int p := by rw [List.getElem!_eq_getElem?_getD, hp]; rfl
      rw [h1] at hxi
      exact (Value.int.inj hxi).symm
    have hkj : xj = q := by
      have h1 : a[j]! = .int q := by rw [List.getElem!_eq_getElem?_getD, hq]; rfl
      rw [h1] at hxj
      exact (Value.int.inj hxj).symm
    have hslot_i : slotInt a i = some p := by
      rw [slotInt_of_getElem_int hxi, hki]
    have hslot_j : slotInt a j = some q := by
      rw [slotInt_of_getElem_int hxj, hkj]
    have hpi : mn_i ≤ p := fits_min_bound hfit hmn_i hslot_i
    have hqj : q ≤ mx_j := fits_max_bound hfit hmx_j hslot_j
    have hlt : q < p := by omega
    have hrb' : rb = false := by
      cases rb with
      | false => rfl
      | true => exact absurd (hiff.mp rfl) (Int.not_le.mpr hlt)
    rw [hrb'] at hrb
    exact posBool_eval_true hrb

/-- State-free reason validity of the bounds arm (entailment plus canonical
    normal forms): at every internal solution of any problem containing the
    reified constraint, the emitted clause is entailed with the pivot in
    normal form.  Both operand reads are integers at such solutions
    (`leReif_sat_inv`), so no operand-escape literals are needed. -/
theorem propLeReifB_reason_valid {problem : Problem DomConstraint Unit}
    {st : State} {i j r : Nat} {l : Literal} {rs : Reason}
    (hprob : DomConstraint.leReifSlot i j r ∈ problem.constraints)
    (hrun : propLeReifB st i j r = .implied l rs) :
    Reason.Valid problem DomConstraint.SatisfiedBy rs l ∧
      (∀ q ∈ rs.clause, q = q.norm) := by
  rcases propLeReifB_emission_inv hrun with hstable |
    ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, hsep, hres⟩ |
    ⟨-, -, -, -, -, mn_i, mx_i, mn_j, mx_j,
      hmn_i, hmx_i, hmn_j, hmx_j, hsep, hres⟩
  · exact absurd hstable (by intro hc; cases hc)
  · have hl : l = posBool r true := by cases hres; rfl
    have hrs : rs = { clause := [posBool r true, negLe i mx_i, posLe j (mn_j - 1)] } := by
      cases hres
      rfl
    refine ⟨lin2_reason_valid_of_clause_true ?_ ?_, ?_⟩
    · rw [hl, hrs]
      exact List.mem_cons_self
    · intro a ha
      obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := leReif_sat_inv (ha.2 _ hprob)
      rw [hrs]
      cases rb with
      | true => exact ⟨posBool r true, List.mem_cons_self, posBool_eval_true hrb⟩
      | false =>
          by_cases h1 : (negLe i mx_i).eval a = some true
          · exact ⟨negLe i mx_i, by simp, h1⟩
          · by_cases h2 : (posLe j (mn_j - 1)).eval a = some true
            · exact ⟨posLe j (mn_j - 1), by simp, h2⟩
            · exfalso
              have hmp : ¬ p ≤ q := fun hle => Bool.false_ne_true (hiff.mpr hle)
              have hpi : p ≤ mx_i :=
                le_of_negLe_not_true (slotInt_of_int_read hp) h1
              have hqj : mn_j ≤ q := by
                have := lt_of_posLe_not_true (slotInt_of_int_read hq) h2
                omega
              omega
    · intro q hq
      rw [hrs] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (posBool_norm r true).symm
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact (negLe_norm i mx_i).symm
        · rw [List.mem_singleton.mp hq]
          exact (posLe_norm j (mn_j - 1)).symm
  · have hl : l = posBool r false := by cases hres; rfl
    have hrs : rs = { clause := [posBool r false, posLe i (mn_i - 1), negLe j mx_j] } := by
      cases hres
      rfl
    refine ⟨lin2_reason_valid_of_clause_true ?_ ?_, ?_⟩
    · rw [hl, hrs]
      exact List.mem_cons_self
    · intro a ha
      obtain ⟨p, q, rb, hp, hq, hrb, hiff⟩ := leReif_sat_inv (ha.2 _ hprob)
      rw [hrs]
      cases rb with
      | false => exact ⟨posBool r false, List.mem_cons_self, posBool_eval_true hrb⟩
      | true =>
          by_cases h1 : (posLe i (mn_i - 1)).eval a = some true
          · exact ⟨posLe i (mn_i - 1), by simp, h1⟩
          · by_cases h2 : (negLe j mx_j).eval a = some true
            · exact ⟨negLe j mx_j, by simp, h2⟩
            · exfalso
              have hpq : p ≤ q := hiff.mp rfl
              have hpi : mn_i ≤ p := by
                have := lt_of_posLe_not_true (slotInt_of_int_read hp) h1
                omega
              have hqj : q ≤ mx_j :=
                le_of_negLe_not_true (slotInt_of_int_read hq) h2
              omega
    · intro q hq
      rw [hrs] at hq
      rcases List.mem_cons.mp hq with rfl | hq
      · exact (posBool_norm r false).symm
      · rcases List.mem_cons.mp hq with rfl | hq
        · exact (posLe_norm i (mn_i - 1)).symm
        · rw [List.mem_singleton.mp hq]
          exact (negLe_norm j mx_j).symm

/-- The bounds arm's implied pin is decided at every internal solution (the
    reif slot reads a Boolean there). -/
theorem propLeReifB_implied_decided {problem : Problem DomConstraint Unit}
    {st : State} {i j r : Nat} {l : Literal} {rs : Reason} {a : Assignment}
    (ha : ProblemSolution problem DomConstraint.SatisfiedBy a)
    (hprob : DomConstraint.leReifSlot i j r ∈ problem.constraints)
    (hrun : propLeReifB st i j r = .implied l rs) :
    ∃ b, l.eval a = some b := by
  obtain ⟨_, _, _, _, _, hrb, _⟩ := leReif_sat_inv (ha.2 _ hprob)
  rcases propLeReifB_emission_inv hrun with hstable |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hres⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hres⟩
  · exact absurd hstable (by intro hc; cases hc)
  · have hl : l = posBool r true := by cases hres; rfl
    rw [hl]
    exact posBool_eval_bool hrb
  · have hl : l = posBool r false := by cases hres; rfl
    rw [hl]
    exact posBool_eval_bool hrb

end LeanFzn.Solver.Propagation
