/-
Purpose: Boolean absence explanation and its precise empty-domain limitation for R3b.
Dependencies: LcgRunInvariantFrameShape supplies shape-aware sync and prefix-pin facts;
LcgRunInvariantShape supplies candidate coverage. This leaf module separates Boolean absence
from the existing integer-view frame invariant without changing runtime definitions.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFrameShape
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP
namespace LeanFzn.Solver.UIP.LcgRunInv

/-- Absence under the pre-repair syntactic relation, retained for the historical witness. -/
def BaseAbsentExpl (orig : List Domain) (tr : List TrailEntry) (doms : List Domain) : Prop :=
  ∀ s b, valueMemB (.bool b) (doms.getD s []) = false →
    litFalseAtRoot orig (posBool s b) = true ∨
      ∃ e ∈ tr, impliesBase orig e.literal (posBool s b).negate.norm = true

/-- An abstract empty Boolean frame can have complete value-removal witnesses while its
Boolean absence is unexplained by the pre-repair syntactic implication relation. -/
theorem emptyBool_absence_not_implied_base :
    ¬BaseAbsentExpl [[Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] [[]] := by
  intro h
  have hf := h 0 false rfl
  simp [litFalseAtRoot, posBool, posNe, impliesBase, impliesLit,
    litEqB, Literal.norm, Literal.negate, Literal.intForm, Literal.boolKind,
    Atom.slot, Atom.evalAtValue, negLe] at hf

/-- This witness satisfies the abstract structural invariant and both prefix-pin invariants.
It is deliberately not claimed to be reachable by the scheduler. -/
theorem emptyBool_structural_counterexample_base :
    ShapeTypedDomains [[Value.bool false, Value.bool true]] ∧
    FrameJ [[Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] ([[]], []) ∧
    BoolPinsOn [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] [] ∧
    ¬BaseAbsentExpl [[Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] [[]] := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, emptyBool_absence_not_implied_base⟩
  · intro d hd
    have : d = [Value.bool false, Value.bool true] := List.mem_singleton.mp hd
    subst this
    right
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro s
    cases s <;> simp [ExplSlot, Frame.domains, domMaxI, domMinI, domInts]
  · intro s k hk
    simp at hk
  · intro i w hw _
    cases i with
    | zero =>
      simp only [List.length_nil, Nat.zero_add, List.getD_cons_zero, List.mem_cons,
        List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨⟨posNe 0 0, 0, none⟩, by simp, rfl, rfl⟩
      · exact ⟨⟨posNe 0 1, 0, none⟩, by simp, rfl, rfl⟩
    | succ i => simp at hw
  · intro s v hv
    cases s <;> simp [Frame.domains] at hv
  · intro s e he hs v hv
    cases s <;> simp [Frame.domains] at hv
  · intro s b hb
    simp at hb

/-- The completed relation repairs the retained empty Boolean frame witness. -/
theorem emptyBool_absence_explained :
    AbsentExpl [[Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] [[]] := by
  intro s b _
  cases s with
  | zero =>
      cases b
      · exact Or.inr ⟨⟨posNe 0 0, 0, none⟩, by simp,
          impliesP_of_table boolTable_removal_false⟩
      · exact Or.inr ⟨⟨posNe 0 1, 0, none⟩, by simp,
          impliesP_of_table boolTable_removal_true⟩
  | succ s =>
      left
      simp [litFalseAtRoot, posBool, Atom.slot ]

/-- Complete narrowing witnesses explain every missing Boolean in a remaining
slot, including a domain that has been emptied by successive removals. -/
theorem absent_remaining_shape {orig : List Domain} {tr : List TrailEntry}
    {F : BranchFrame} (hshape : ShapeTypedDomains orig)
    (hnc : NarrowingComplete tr orig F) {s : Nat} {b : Bool}
    (hs : F.2.length ≤ s)
    (hm : valueMemB (.bool b) ((Frame.domains F).getD s []) = false) :
    SemFalsifiedBefore orig tr (posBool s b) := by
  by_cases ho : Value.bool b ∈ orig.getD s []
  · have hbool : booleanSlotB orig s = true := by
      rw [booleanSlotB_eq_slotBoolB]
      apply boolSlot_slotBoolB
      rcases slot_cases hshape s with hi | hb
      · obtain ⟨k, hk⟩ := hi _ ho
        cases hk
      · exact hb
    have hn : Value.bool b ∉ F.1.getD (s - F.2.length) [] := by
      intro hv
      have hv' : Value.bool b ∈ (Frame.domains F).getD s [] := by
        rw [domains_getD_rem F hs]
        exact hv
      have hh := valueMemB_iff.mpr hv'
      rw [hm] at hh
      cases hh
    obtain ⟨e, he, hslot, hfalse⟩ := hnc (s - F.2.length) (.bool b)
      (by simpa only [Nat.add_sub_of_le hs] using ho) hn
    right
    refine ⟨e, he, impliesP_of_table (boolSlotImp_of_excludes hbool ?_ hfalse)⟩
    simpa only [Nat.add_sub_of_le hs] using hslot
  · left
    rw [litFalseAtRoot_iff]
    intro v hv
    have hne : v ≠ Value.bool b := fun h => ho (h ▸ hv)
    cases v <;> cases b <;> simp_all [Literal.valueHolds, posBool]

/-- Boolean prefix pins and complete remaining-slot narrowing together derive
all Boolean absence explanations for a shape-typed frame. -/
theorem absent_of_frameJ_shape {orig : List Domain} {tr : List TrailEntry}
    {F : BranchFrame} (hshape : ShapeTypedDomains orig) (hJ : FrameJ orig tr F)
    (hp : BoolPinsOn tr F.2) : AbsentExpl orig tr (Frame.domains F) := by
  intro s b hm
  by_cases hs : s < F.2.length
  · by_cases ho : Value.bool b ∈ orig.getD s []
    · have hb : BoolSlot orig s := by
        rcases slot_cases hshape s with hi | hb
        · obtain ⟨k, hk⟩ := hi _ ho
          cases hk
        · exact hb
      have hd := domains_getD_pre F hs
      have hv : F.2[s] ∈ orig.getD s [] := hJ.fits s _ (by rw [hd]; simp)
      obtain ⟨c, hc⟩ := hb _ hv
      obtain ⟨e, he, hl⟩ := hp s c (by rw [List.getElem?_eq_getElem hs, hc])
      have hne : c ≠ b := by
        intro heq
        subst c
        have hv' : Value.bool b ∈ (Frame.domains F).getD s [] := by rw [hd, hc]; simp
        have hh := valueMemB_iff.mpr hv'
        rw [hm] at hh
        cases hh
      right
      refine ⟨e, he, impliesP_of_table (boolSlotImp_of_excludes ?_ ?_ ?_)⟩
      · rw [booleanSlotB_eq_slotBoolB]
        exact boolSlot_slotBoolB hb
      · rw [hl]
        rfl
      · rw [hl]
        cases b <;> cases c <;> simp_all [Literal.valueHolds, posBool]
    · left
      rw [litFalseAtRoot_iff]
      intro v hv
      have hne : v ≠ Value.bool b := fun h => ho (h ▸ hv)
      cases v <;> cases b <;> simp_all [Literal.valueHolds, posBool]
  · exact absent_remaining_shape hshape hJ.nc (by omega) hm

/-- The complete frame-explanation contract on mixed integer/Boolean boxes.
Its additional prefix-pin premise must be preserved by the run before public routing. -/
theorem frameExplainedFull_of_frameJ_shape {orig : List Domain} {bs : BranchState leaf}
    (hshape : ShapeTypedDomains orig) (hJ : FrameJ orig bs.trail bs.frame)
    (hp : BoolPinsOn bs.trail bs.frame.2) : FrameExplainedFull orig bs where
  base :=
    { bounds := fun s => (hJ.expl s).1
      absent := absent_of_frameJ_shape hshape hJ hp
      fix := fun s c hc => (hJ.expl s).2.1 c hc }
  holes := fun s k h1 h2 h3 => (hJ.expl s).2.2 k h1 h2 h3

end LeanFzn.Solver.UIP.LcgRunInv
