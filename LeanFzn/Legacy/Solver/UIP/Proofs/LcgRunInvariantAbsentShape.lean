/-
Purpose: Boolean absence explanation and its precise empty-domain limitation for R3b.
Dependencies: LcgRunInvariantFrameShape supplies shape-aware sync and prefix-pin facts;
LcgRunInvariantShape supplies candidate coverage. This leaf module separates Boolean absence
from the existing integer-view frame invariant without changing runtime definitions.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFrameShape
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP
namespace LeanFzn.Solver.UIP.LcgRunInv

/-- Absence under the pre-repair syntactic relation, retained for the historical witness. -/
def BaseAbsentExpl (orig : List Domain) (tr : List TrailEntry) (doms : List Domain) : Prop :=
  ∀ s b, valueMemB (.bool b) (slotEnum doms s) = false →
    litFalseAtRoot orig (posBool s b) = true ∨
      ∃ e ∈ tr, impliesBase orig e.literal (posBool s b).negate.norm = true

/-- An abstract empty Boolean frame can have complete value-removal witnesses while its
Boolean absence is unexplained by the pre-repair syntactic implication relation. -/
theorem emptyBool_absence_not_implied_base :
    ¬BaseAbsentExpl [Dom.ofList [Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] [Dom.empty] := by
  intro h
  have hf := h 0 false (by simp [slotEnum, Dom.enum_empty, valueMemB])
  simp [litFalseAtRoot, posBool, posNe, impliesBase, impliesLit,
    litEqB, Literal.norm, Literal.negate, Literal.intForm, Literal.boolKind,
    Atom.slot, Atom.evalAtValue, negLe] at hf

/-- This witness satisfies the abstract structural invariant and both prefix-pin invariants.
It is deliberately not claimed to be reachable by the scheduler. -/
theorem emptyBool_structural_counterexample_base :
    ShapeTypedDomains [Dom.ofList [Value.bool false, Value.bool true]] ∧
    FrameJ [Dom.ofList [Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] { doms := [Dom.empty], order := [] } ∧
    BoolPinsOn [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] { doms := [Dom.empty], order := [] } ∧
    ¬BaseAbsentExpl [Dom.ofList [Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] [Dom.empty] := by
  refine ⟨?_, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_, emptyBool_absence_not_implied_base⟩
  · intro d hd
    have hd' : d = Dom.ofList [Value.bool false, Value.bool true] := List.mem_singleton.mp hd
    subst hd'
    right
    intro v hv
    simp only [mem_ofList_iff, List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl <;> exact ⟨_, rfl⟩
  · intro s
    cases s <;> simp [ExplSlot, Frame.domains, domMaxI, domMinI, domInts, Dom.enum_empty]
  · intro s hs
    simp at hs
  · intro i _ w hw _
    cases i with
    | zero =>
      simp only [List.getD_cons_zero, mem_ofList_iff, List.mem_cons,
        List.mem_nil_iff, or_false] at hw
      rcases hw with rfl | rfl
      · exact ⟨⟨posNe 0 0, 0, none⟩, by simp, rfl, rfl⟩
      · exact ⟨⟨posNe 0 1, 0, none⟩, by simp, rfl, rfl⟩
    | succ i =>
      simp only [List.getD_cons_succ] at hw
      simp at hw
  · intro s v hv
    cases s <;> simp [Frame.domains, Dom.enum_empty] at hv
  · intro s e he hs v hv
    cases s <;> simp [Frame.domains, Dom.enum_empty] at hv
  · refine ⟨?_, ?_⟩ <;> intro s hs <;> simp at hs

/-- The completed relation repairs the retained empty Boolean frame witness. -/
theorem emptyBool_absence_explained :
    AbsentExpl [Dom.ofList [Value.bool false, Value.bool true]]
      [⟨posNe 0 0, 0, none⟩, ⟨posNe 0 1, 0, none⟩] [Dom.empty] := by
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
      simp [litFalseAtRoot, posBool, Atom.slot, Dom.enum_empty]

/-- Complete narrowing witnesses explain every missing Boolean in a remaining
slot, including a domain that has been emptied by successive removals. -/
theorem absent_remaining_shape {orig : List Domain} {tr : List TrailEntry}
    {F : BranchFrame} (hshape : ShapeTypedDomains orig)
    (hnc : NarrowingComplete tr orig F) {s : Nat} {b : Bool}
    (hs : s ∉ F.order)
    (hm : valueMemB (.bool b) (Dom.enum ((Frame.domains F).getD s Dom.empty)) = false) :
    SemFalsifiedBefore orig tr (posBool s b) := by
  by_cases ho : Value.bool b ∈ orig.getD s Dom.empty
  · have hbool : booleanSlotB orig s = true := by
      rw [booleanSlotB_eq_slotBoolB]
      apply boolSlot_slotBoolB
      rcases slot_cases hshape s with hi | hb
      · obtain ⟨k, hk⟩ := hi _ ho
        cases hk
      · exact hb
    have hn : Value.bool b ∉ F.doms.getD s Dom.empty := by
      intro hv
      have hv' : Value.bool b ∈ (Frame.domains F).getD s Dom.empty := hv
      have hh : valueMemB (.bool b) (Dom.enum ((Frame.domains F).getD s Dom.empty)) = true := by
        rw [valueMemB_iff]
        exact (DomainLike.mem_iff _ _).mp hv'
      rw [hm] at hh
      cases hh
    obtain ⟨e, he, hslot, hfalse⟩ := hnc s hs (.bool b) ho hn
    right
    exact ⟨e, he, impliesP_of_table (boolSlotImp_of_excludes hbool hslot hfalse)⟩
  · left
    rw [litFalseAtRoot_iff]
    intro v hv
    have hvD : v ∈ orig.getD s Dom.empty :=
      (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
    have hne : v ≠ Value.bool b := fun h => ho (h ▸ hvD)
    cases v <;> cases b <;> simp_all [Literal.valueHolds, posBool]

/-- Boolean prefix pins and complete remaining-slot narrowing together derive
all Boolean absence explanations for a shape-typed frame. -/
theorem absent_of_frameJ_shape {orig : List Domain} {tr : List TrailEntry}
    {F : BranchFrame} (hshape : ShapeTypedDomains orig) (hJ : FrameJ orig tr F)
    (_hp : BoolPinsOn tr F) : AbsentExpl orig tr (Frame.domains F) := by
  intro s b hm
  by_cases hs : s ∈ F.order
  · by_cases ho : Value.bool b ∈ orig.getD s Dom.empty
    · obtain ⟨v, l, hv, hl, e, he, hel⟩ := hJ.pins s hs
      have hmem : v ∈ orig.getD s Dom.empty :=
        hJ.fits s v (mem_getD_of_enum_singleton hv)
      rcases slot_cases hshape s with hi | hb
      · obtain ⟨k, hk⟩ := hi _ ho
        cases hk
      · obtain ⟨c, hc⟩ := hb v hmem
        subst v
        have hl' : l = posBool s c := by
          have h := hl
          simp only [valueLiteral, Option.some.injEq] at h
          exact h.symm
        have hne : c ≠ b := by
          intro heq
          subst c
          have hv' : Value.bool b ∈ (Frame.domains F).getD s Dom.empty :=
            mem_getD_of_enum_singleton hv
          have hm' : valueMemB (.bool b)
              (Dom.enum ((Frame.domains F).getD s Dom.empty)) = false := hm
          have hh : valueMemB (.bool b)
              (Dom.enum ((Frame.domains F).getD s Dom.empty)) = true := by
            rw [valueMemB_iff]
            exact (DomainLike.mem_iff _ _).mp hv'
          rw [hm'] at hh
          cases hh
        right
        refine ⟨e, he, impliesP_of_table (boolSlotImp_of_excludes ?_ ?_ ?_)⟩
        · rw [booleanSlotB_eq_slotBoolB]
          exact boolSlot_slotBoolB hb
        · rw [hel, hl']; rfl
        · rw [hel, hl']
          cases b <;> cases c <;> simp_all [Literal.valueHolds, posBool]
    · left
      rw [litFalseAtRoot_iff]
      intro v hv
      have hvD : v ∈ orig.getD s Dom.empty :=
        (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
      have hne : v ≠ Value.bool b := fun h => ho (h ▸ hvD)
      cases v <;> cases b <;> simp_all [Literal.valueHolds, posBool]
  · exact absent_remaining_shape hshape hJ.nc hs hm

/-- The complete frame-explanation contract on mixed integer/Boolean boxes.
Its additional prefix-pin premise must be preserved by the run before public routing. -/
theorem frameExplainedFull_of_frameJ_shape {orig : List Domain} {bs : BranchState leaf}
    (hshape : ShapeTypedDomains orig) (hJ : FrameJ orig bs.trail bs.frame)
    (hp : BoolPinsOn bs.trail bs.frame) : FrameExplainedFull orig bs where
  base :=
    { bounds := fun s => (hJ.expl s).1
      absent := absent_of_frameJ_shape hshape hJ hp
      fix := fun s c hc => (hJ.expl s).2.1 c hc }
  holes := fun s k h1 h2 h3 => (hJ.expl s).2.2 k h1 h2 h3

end LeanFzn.Solver.UIP.LcgRunInv
