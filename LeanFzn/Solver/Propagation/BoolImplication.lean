/-
Purpose: sound, complete finite truth-table implication for Boolean domain slots.
Dependencies: Encoding provides literal evaluation and Boolean integer views;
FrameFilter provides single-value narrowing tests.
DAG: Encoding -> BoolImplication -> future analyzer Boolean completion.
This module does not change the current analyzer or reason-pivot contracts.
-/
import LeanFzn.Solver.Propagation.Encoding
import LeanFzn.Solver.Propagation.FrameFilter
open LeanFzn.Semantics
namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-- Every original value of the slot is Boolean. -/
def booleanSlotB (orig : List Domain) (s : Nat) : Bool :=
  (orig.getD s []).all fun v => match v with | .bool _ => true | _ => false

/-- The truth value of a literal at the Boolean value `c` of its slot (every atom is
defined at a Boolean, read as 0/1). -/
def Literal.truthAtBool (l : Literal) (c : Bool) : Bool :=
  let x := match l.atom with
    | .boolEq _ b => c == b
    | .intLe _ k => decide ((if c then (1 : Int) else 0) ≤ k)
    | .intNe _ v => decide ((if c then (1 : Int) else 0) ≠ v)
  if l.positive then x else !x

/-- The Boolean `c` is an original value of slot `s`. -/
def slotHasBool (orig : List Domain) (s : Nat) (c : Bool) : Bool :=
  (orig.getD s []).any fun v => match v with | .bool x => x == c | _ => false

/-- On a slot whose original values are all Boolean, implication is the truth table over
the original values `{false, true}` of the slot (R3b: complete, including root-false `t`). -/
def boolSlotImp (orig : List Domain) (t g : Literal) : Bool :=
  t.atom.slot == g.atom.slot &&
    ([true, false].all fun c =>
      !slotHasBool orig t.atom.slot c || !t.truthAtBool c || g.truthAtBool c) &&
    booleanSlotB orig t.atom.slot

/-- Introduction: a truth-table implication on a Boolean slot. -/
theorem boolSlotImp_intro {orig : List Domain} {t g : Literal}
    (hs : t.atom.slot = g.atom.slot) (hb : booleanSlotB orig t.atom.slot = true)
    (h : ∀ c : Bool, slotHasBool orig t.atom.slot c = true →
      t.truthAtBool c = true → g.truthAtBool c = true) :
    boolSlotImp orig t g = true := by
  unfold boolSlotImp
  simp only [Bool.and_eq_true, beq_iff_eq]
  refine ⟨⟨hs, ?_⟩, hb⟩
  rw [List.all_eq_true]
  intro c _
  cases hh : slotHasBool orig t.atom.slot c
  · simp
  · cases ht : t.truthAtBool c
    · simp
    · simp [h c hh ht]

/-- Elimination of a truth-table implication. -/
theorem boolSlotImp_elim {orig : List Domain} {t g : Literal}
    (h : boolSlotImp orig t g = true) :
    t.atom.slot = g.atom.slot ∧ booleanSlotB orig t.atom.slot = true ∧
      ∀ c : Bool, slotHasBool orig t.atom.slot c = true →
        t.truthAtBool c = true → g.truthAtBool c = true := by
  unfold boolSlotImp at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hs, hall⟩, hb⟩ := h
  refine ⟨hs, hb, fun c hh ht => ?_⟩
  have := List.all_eq_true.mp hall c (by cases c <;> simp)
  rw [hh, ht] at this
  simpa using this

/-- A literal on a slot holding the Boolean `c` evaluates to its truth-table value. -/
theorem eval_of_boolSlot (l : Literal) (a : Assignment) (c : Bool)
    (hs : a[l.atom.slot]? = some (.bool c)) : l.eval a = some (l.truthAtBool c) := by
  obtain ⟨atom, pos⟩ := l
  have hsi : ∀ s, a[s]? = some (.bool c) → slotInt a s = some (if c then 1 else 0) := by
    intro s h; simp [slotInt, h, Value.intView]
  cases atom with
  | boolEq s b =>
      simp only [Atom.slot] at hs
      cases pos <;> simp [Literal.eval, Atom.eval, Literal.truthAtBool, hs]
  | intLe s k =>
      simp only [Atom.slot] at hs
      cases pos <;> simp [Literal.eval, Atom.eval, Literal.truthAtBool, hsi s hs]
  | intNe s v =>
      simp only [Atom.slot] at hs
      cases pos <;> simp [Literal.eval, Atom.eval, Literal.truthAtBool, hsi s hs]

theorem boolSlotImp_sound {orig : List Domain} {t g : Literal} (h : boolSlotImp orig t g = true)
    {a : Assignment} (hfit : a.Fits orig) (hg : g.eval a = some false) : t.eval a = some false := by
  unfold boolSlotImp at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨hsl, hall⟩, hb⟩ := h
  have hlt : g.atom.slot < a.length := by
    refine Classical.byContradiction fun hnot => ?_
    have hnone : a[g.atom.slot]? = none := List.getElem?_eq_none (by omega)
    obtain ⟨atom, pos⟩ := g
    cases atom <;> simp_all [Literal.eval, Atom.eval, Atom.slot, slotInt]
  have hmem : a[g.atom.slot] ∈ orig.getD g.atom.slot [] :=
    hfit.2 _ _ (List.getElem?_eq_getElem hlt)
  have hmem' : a[g.atom.slot] ∈ orig.getD t.atom.slot [] := by rw [hsl]; exact hmem
  unfold booleanSlotB at hb
  have hbv := List.all_eq_true.mp hb _ hmem'
  obtain ⟨c, hc⟩ : ∃ c, a[g.atom.slot] = Value.bool c := by
    cases hv : a[g.atom.slot] with
    | bool c => exact ⟨c, rfl⟩
    | _ => rw [hv] at hbv; simp at hbv
  have hgs : a[g.atom.slot]? = some (.bool c) := by
    rw [List.getElem?_eq_getElem hlt, hc]
  have hts : a[t.atom.slot]? = some (.bool c) := by rw [hsl]; exact hgs
  rw [eval_of_boolSlot g a c hgs] at hg
  rw [eval_of_boolSlot t a c hts]
  have hgf : g.truthAtBool c = false := Option.some.inj hg
  have hhas : slotHasBool orig t.atom.slot c = true := by
    unfold slotHasBool
    rw [List.any_eq_true]
    exact ⟨_, hmem', by rw [hc]; simp⟩
  have := List.all_eq_true.mp hall c (by cases c <;> simp)
  rw [hgf, hhas] at this
  cases ht : t.truthAtBool c <;> simp_all


/-- Integer-view removal of false explains the corresponding Boolean absence. -/
theorem boolTable_removal_false :
    boolSlotImp [[Value.bool false, Value.bool true]] (posNe 0 0)
      (posBool 0 false).negate.norm = true := by decide

/-- Integer-view removal of true explains the corresponding Boolean absence. -/
theorem boolTable_removal_true :
    boolSlotImp [[Value.bool false, Value.bool true]] (posNe 0 1)
      (posBool 0 true).negate.norm = true := by decide

/-- The extension contributes nothing on an integer slot. -/
theorem boolSlotImp_of_nonBoolean {orig : List Domain} {t g : Literal}
    (h : booleanSlotB orig t.atom.slot = false) : boolSlotImp orig t g = false := by
  simp [boolSlotImp, h]

/-- Literal evaluation at a Boolean agrees with the finite truth table. -/
theorem valueHolds_bool (l : Literal) (b : Bool) :
    l.valueHolds (.bool b) = l.truthAtBool b := by
  obtain ⟨a, p⟩ := l
  cases a <;> cases p <;> cases b <;>
    simp [Literal.valueHolds, Literal.truthAtBool, Value.intView]

/-- A narrowing witness that excludes a Boolean value explains its absence
under the completed implication relation, including on empty frame domains. -/
theorem boolSlotImp_of_excludes {orig : List Domain} {s : Nat} {l : Literal} {b : Bool}
    (hb : booleanSlotB orig s = true) (hs : l.atom.slot = s)
    (he : l.valueHolds (.bool b) = false) :
    boolSlotImp orig l (posBool s b).negate.norm = true := by
  apply boolSlotImp_intro
  · cases b <;> change l.atom.slot = s <;> exact hs
  · rwa [hs]
  · intro c _ ht
    have hfalse : l.truthAtBool b = false := by rwa [valueHolds_bool] at he
    by_cases hcb : c = b
    · subst c
      rw [hfalse] at ht
      cases ht
    · cases b <;> cases c <;>
        simp_all [posBool, Literal.negate, Literal.norm, Literal.truthAtBool]

/-- Boolean truth-table evaluation respects normalized negation. -/
theorem truthAtBool_negate_norm (l : Literal) (b : Bool) :
    l.negate.norm.truthAtBool b = !l.truthAtBool b := by
  obtain ⟨a, p⟩ := l
  cases a <;> cases p <;> cases b <;>
    simp [Literal.negate, Literal.norm, Literal.truthAtBool]

end LeanFzn.Solver.Propagation
