/-
Purpose: Boolean prefix-pin explanation helpers for R3b's shape-typed frame proofs.
Dependencies: LcgRunInvariantFrame supplies frame domains and ExplSlot; LcgRunInvariantShape
supplies Boolean-slot and generalized synchronization facts. These helpers are a leaf branch
preparing the scheduler frame invariant generalization.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFrame
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantShape
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP
namespace LeanFzn.Solver.UIP.LcgRunInv

theorem boolRoot_low {orig : List Domain} {tr : List TrailEntry} {s : Nat}
    (hB : BoolSlot orig s) : SemFalsifiedBefore orig tr (posLe s (-1)) := by
  left
  rw [litFalseAtRoot_iff]
  intro v hv
  obtain ⟨b, rfl⟩ := hB v ((DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv))
  cases b <;> simp [Literal.valueHolds, posLe, Value.intView]

theorem boolRoot_high {orig : List Domain} {tr : List TrailEntry} {s : Nat}
    (hB : BoolSlot orig s) : SemFalsifiedBefore orig tr (negLe s 1) := by
  left
  rw [litFalseAtRoot_iff]
  intro v hv
  obtain ⟨b, rfl⟩ := hB v ((DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv))
  cases b <;> simp [Literal.valueHolds, negLe, Value.intView]

/-- A Boolean prefix pin explains the integer-view bounds and holes of its singleton. -/
theorem explSlot_boolPin {orig : List Domain} {tr : List TrailEntry} {doms : List Domain}
    {s : Nat} {b : Bool} {e : TrailEntry} (hB : BoolSlot orig s)
    (he : e ∈ tr) (hl : e.literal = posBool s b)
    (hd : Dom.enum (doms.getD s Dom.empty) = [Value.bool b]) : ExplSlot orig tr doms s := by
  have hbool := boolSlot_slotBoolB hB
  have hmemiff : ∀ v : Value, v ∈ doms.getD s Dom.empty ↔ v ∈ ([Value.bool b] : List Value) := by
    intro v
    rw [DomainLike.mem_iff, domElems_eq_enum, hd]
  cases b <;> unfold ExplSlot <;> rw [hd] <;>
    refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun h0 h1 h2 h3 => ?_⟩
  · have h' : domMaxI ([Value.bool false] : List Value) = some mx := by
      rwa [domMaxI_enum (doms.getD s Dom.empty), hd] at h
    simp [domMaxI, domInts, maxI] at h'
    subst mx
    exact Or.inr ⟨e, he, by rw [hl]; simp [impliesP, impliesBase, impliesLit, litEqB,
      Literal.intForm, Literal.boolKind, Literal.norm, Literal.negate, posBool, negLe, posLe, Atom.slot, hbool]⟩
  · have h' : domMinI ([Value.bool false] : List Value) = some mn := by
      rwa [domMinI_enum (doms.getD s Dom.empty), hd] at h
    simp [domMinI, domInts, minI] at h'
    subst mn
    exact boolRoot_low hB
  · simp at h
  · simp only [hmemiff] at h1 h2 h3
    simp [Value.intView] at h1 h2 h3
    omega
  · have h' : domMaxI ([Value.bool true] : List Value) = some mx := by
      rwa [domMaxI_enum (doms.getD s Dom.empty), hd] at h
    simp [domMaxI, domInts, maxI] at h'
    subst mx
    exact boolRoot_high hB
  · have h' : domMinI ([Value.bool true] : List Value) = some mn := by
      rwa [domMinI_enum (doms.getD s Dom.empty), hd] at h
    simp [domMinI, domInts, minI] at h'
    subst mn
    exact Or.inr ⟨e, he, by rw [hl]; simp [impliesP, impliesBase, impliesLit, litEqB,
      Literal.intForm, Literal.boolKind, Literal.norm, Literal.negate, posBool, negLe, posLe, Atom.slot, hbool]⟩
  · simp at h
  · simp only [hmemiff] at h1 h2 h3
    simp [Value.intView] at h1 h2 h3
    omega

/-- Decided Boolean slots carry their Boolean pin on the trail. -/
def BoolPinsOn (tr : List TrailEntry) (f : BranchFrame) : Prop :=
  (∀ k ∈ f.order, ∃ v : Value, f.doms[k]?.map Dom.enum = some [v]) ∧
    (∀ k ∈ f.order, ∀ b, f.doms[k]?.map Dom.enum = some [Value.bool b] →
      ∃ e ∈ tr, e.literal = posBool k b)

/-- A decided slot is explained by its pin entry (both supported sorts). -/
theorem explSlot_decided_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : ShapeTypedDomains orig) (hpins : PinsOn tr F)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    {s : Nat} (hs : s ∈ F.order) : ExplSlot orig tr (Frame.domains F) s := by
  obtain ⟨v, l, hv, hl, e, he, hel⟩ := hpins s hs
  have hvenum : Dom.enum (F.doms.getD s Dom.empty) = [v] :=
    enum_getD_of_enum_singleton hv
  have hvD : v ∈ (Frame.domains F).getD s Dom.empty :=
    (DomainLike.mem_iff _ v).mpr (by
      rw [domElems_eq_enum]
      show v ∈ Dom.enum (F.doms.getD s Dom.empty)
      rw [hvenum]
      exact List.mem_cons_self)
  have hmem : v ∈ orig.getD s Dom.empty := hfits s v hvD
  rcases slot_cases hint s with hI | hB
  · obtain ⟨k, hk⟩ := hI v hmem
    subst v
    have hl' : negNe s k = l := by simpa [valueLiteral] using hl
    exact explSlot_pin he (by rw [hel, ← hl'])
      (by simpa [Frame.domains] using hvenum)
  · obtain ⟨b, hb⟩ := hB v hmem
    subst v
    have hl' : posBool s b = l := by simpa [valueLiteral] using hl
    exact explSlot_boolPin hB he (by rw [hel, ← hl'])
      (by simpa [Frame.domains] using hvenum)

/-- Remaining domains of a shape-typed frame have integer views. -/
theorem frame_views {orig : List Domain} {F : BranchFrame} (hint : ShapeTypedDomains orig)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty) :
    ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k := by
  intro d hd v hv
  obtain ⟨i, hi, hdi⟩ := List.getElem_of_mem hd
  have hg : (Frame.domains F).getD i Dom.empty = d := by
    rw [Frame.domains, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp [hdi]
  exact slot_viewed hint (hfits _ v (by rw [hg]; exact hv))

theorem explDoms_of_remaining_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : ShapeTypedDomains orig) (hpins : PinsOn tr F) (_hbPins : BoolPinsOn tr F)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    (hrem : ∀ i, i < F.doms.length → i ∉ F.order →
      ExplSlot orig tr (Frame.domains F) i) :
    ExplDoms orig tr (Frame.domains F) := by
  intro s
  by_cases hs : s ∈ F.order
  · exact explSlot_decided_shape hint hpins hfits hs
  · by_cases hi : s < F.doms.length
    · exact hrem s hi hs
    · refine explSlot_none ?_
      rw [List.getElem?_eq_none (by omega)]

/-- `syncAll` establishes the whole-frame invariant from its non-semantic parts. -/
theorem frameJ_syncAll_shape {orig : List Domain} (hint : ShapeTypedDomains orig) (bs : BranchState leaf)
    (hpins : PinsOn bs.trail bs.frame) (hbPins : BoolPinsOn bs.trail bs.frame)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfits : ∀ s v, v ∈ (Frame.domains bs.frame).getD s Dom.empty → v ∈ orig.getD s Dom.empty)
    (hag : ∀ s, SlotAgree bs.trail (Frame.domains bs.frame) s) :
    FrameJ orig (syncAll orig bs).trail bs.frame := by
  have hsub := syncAll_trail_sub orig bs
  have hpins' : PinsOn (syncAll orig bs).trail bs.frame := fun s hs => by
    obtain ⟨v, l, hv, hl, x, hx, hxl⟩ := hpins s hs
    exact ⟨v, l, hv, hl, x, hsub x hx, hxl⟩
  have hbPins' : BoolPinsOn (syncAll orig bs).trail bs.frame :=
    ⟨hbPins.1, fun k hk b hb => by
      obtain ⟨x, hx, hxl⟩ := hbPins.2 k hk b hb
      exact ⟨x, hsub x hx, hxl⟩⟩
  refine ⟨?_, hpins', nc_mono hsub hnc, hfits, fun s => syncAll_slotAgree orig bs s (hag s)⟩
  exact explDoms_of_remaining_shape hint hpins' hbPins' hfits
    (fun i hi hdec => syncAll_explains_shape hint (frame_views hint hfits) hfits hnc hag i hi hdec)

end LeanFzn.Solver.UIP.LcgRunInv
