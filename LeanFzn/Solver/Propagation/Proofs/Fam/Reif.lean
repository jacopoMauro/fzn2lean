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

end LeanFzn.Solver.Propagation
