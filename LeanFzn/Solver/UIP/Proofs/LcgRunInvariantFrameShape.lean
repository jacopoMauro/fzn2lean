/-
Purpose: Boolean prefix-pin explanation helpers for R3b's shape-typed frame proofs.
Dependencies: LcgRunInvariantFrame supplies frame domains and ExplSlot; LcgRunInvariantShape
supplies Boolean-slot and generalized synchronization facts. These helpers are a leaf branch
preparing the scheduler frame invariant generalization.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFrame
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantShape
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP
namespace LeanFzn.Solver.UIP.LcgRunInv

theorem boolRoot_low {orig : List Domain} {tr : List TrailEntry} {s : Nat}
    (hB : BoolSlot orig s) : SemFalsifiedBefore orig tr (posLe s (-1)) := by
  left
  rw [litFalseAtRoot_iff]
  intro v hv
  obtain ⟨b, rfl⟩ := hB v hv
  cases b <;> simp [Literal.valueHolds, posLe, Value.intView]

theorem boolRoot_high {orig : List Domain} {tr : List TrailEntry} {s : Nat}
    (hB : BoolSlot orig s) : SemFalsifiedBefore orig tr (negLe s 1) := by
  left
  rw [litFalseAtRoot_iff]
  intro v hv
  obtain ⟨b, rfl⟩ := hB v hv
  cases b <;> simp [Literal.valueHolds, negLe, Value.intView]

/-- A Boolean prefix pin explains the integer-view bounds and holes of its singleton. -/
theorem explSlot_boolPin {orig : List Domain} {tr : List TrailEntry} {doms : List Domain}
    {s : Nat} {b : Bool} {e : TrailEntry} (hB : BoolSlot orig s)
    (he : e ∈ tr) (hl : e.literal = posBool s b)
    (hd : doms.getD s [] = [Value.bool b]) : ExplSlot orig tr doms s := by
  have hbool := boolSlot_slotBoolB hB
  cases b <;> unfold ExplSlot <;> rw [hd] <;>
    refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun h0 h1 h2 h3 => ?_⟩
  · simp [domMaxI, domInts, maxI] at h
    subst mx
    exact Or.inr ⟨e, he, by rw [hl]; simp [impliesP, impliesBase, impliesLit, litEqB,
      Literal.intForm, Literal.boolKind, Literal.norm, Literal.negate, posBool, negLe, posLe, Atom.slot, hbool]⟩
  · simp [domMinI, domInts, minI] at h
    subst mn
    exact boolRoot_low hB
  · simp at h
  · simp [Value.intView] at h1 h2 h3
    omega
  · simp [domMaxI, domInts, maxI] at h
    subst mx
    exact boolRoot_high hB
  · simp [domMinI, domInts, minI] at h
    subst mn
    exact Or.inr ⟨e, he, by rw [hl]; simp [impliesP, impliesBase, impliesLit, litEqB,
      Literal.intForm, Literal.boolKind, Literal.norm, Literal.negate, posBool, negLe, posLe, Atom.slot, hbool]⟩
  · simp at h
  · simp [Value.intView] at h1 h2 h3
    omega

/-- Boolean prefix positions carry their Boolean pin on the trail. -/
def BoolPinsOn (tr : List TrailEntry) (pre : List Value) : Prop :=
  ∀ s b, pre[s]? = some (Value.bool b) → ∃ e ∈ tr, e.literal = posBool s b

/-- Prefix singleton explanation using pins of both supported sorts. -/
theorem explSlot_prefix_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : ShapeTypedDomains orig) (hpins : PinsOn tr F.2) (hbPins : BoolPinsOn tr F.2)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s [])
    {s : Nat} (hs : s < F.2.length) : ExplSlot orig tr (Frame.domains F) s := by
  have hd := domains_getD_pre F hs
  have hmem : F.2[s] ∈ orig.getD s [] := hfits s _ (by rw [hd]; exact List.mem_cons_self)
  rcases slot_cases hint s with hI | hB
  · obtain ⟨k, hk⟩ := hI _ hmem
    obtain ⟨x, hx, hxl⟩ := hpins s k (by rw [List.getElem?_eq_getElem hs, hk])
    exact explSlot_pin hx hxl (by rw [hd, hk])
  · obtain ⟨b, hb⟩ := hB _ hmem
    obtain ⟨x, hx, hxl⟩ := hbPins s b (by rw [List.getElem?_eq_getElem hs, hb])
    exact explSlot_boolPin hB hx hxl (by rw [hd, hb])

/-- Remaining domains of a shape-typed frame have integer views. -/
theorem frame_views {orig : List Domain} {F : BranchFrame} (hint : ShapeTypedDomains orig)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s []) :
    ∀ d ∈ F.1, ∀ v ∈ d, ∃ k : Int, v.intView = some k := by
  intro d hd v hv
  obtain ⟨i, hi, hdi⟩ := List.getElem_of_mem hd
  have hg : (Frame.domains F).getD (F.2.length + i) [] = d := by
    rw [domains_getD_rem F (by omega)]
    have : F.2.length + i - F.2.length = i := by omega
    rw [this, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp [hdi]
  exact slot_viewed hint (hfits _ v (by rw [hg]; exact hv))

theorem explDoms_of_remaining_shape {orig : List Domain} {tr : List TrailEntry} {F : BranchFrame}
    (hint : ShapeTypedDomains orig) (hpins : PinsOn tr F.2) (hbPins : BoolPinsOn tr F.2)
    (hfits : ∀ s v, v ∈ (Frame.domains F).getD s [] → v ∈ orig.getD s [])
    (hrem : ∀ i, i < F.1.length → ExplSlot orig tr (Frame.domains F) (F.2.length + i)) :
    ExplDoms orig tr (Frame.domains F) := by
  intro s
  by_cases hs : s < F.2.length
  · exact explSlot_prefix_shape hint hpins hbPins hfits hs
  · have hle : F.2.length ≤ s := by omega
    obtain ⟨i, rfl⟩ : ∃ i, s = F.2.length + i := ⟨s - F.2.length, by omega⟩
    by_cases hi : i < F.1.length
    · exact hrem i hi
    · refine explSlot_none hle ?_
      have : F.2.length + i - F.2.length = i := by omega
      rw [this]
      exact List.getElem?_eq_none (by omega)

/-- `syncAll` establishes the whole-frame invariant from its non-semantic parts. -/
theorem frameJ_syncAll_shape {orig : List Domain} (hint : ShapeTypedDomains orig) (bs : BranchState leaf)
    (hpins : PinsOn bs.trail bs.frame.2) (hbPins : BoolPinsOn bs.trail bs.frame.2)
    (hnc : NarrowingComplete bs.trail orig bs.frame)
    (hfits : ∀ s v, v ∈ (Frame.domains bs.frame).getD s [] → v ∈ orig.getD s [])
    (hag : ∀ s, SlotAgree bs.trail (Frame.domains bs.frame) s) :
    FrameJ orig (syncAll orig bs).trail bs.frame := by
  have hsub := syncAll_trail_sub orig bs
  have hpins' : PinsOn (syncAll orig bs).trail bs.frame.2 := fun s k hk => by
    obtain ⟨x, hx, hxl⟩ := hpins s k hk
    exact ⟨x, hsub x hx, hxl⟩
  refine ⟨?_, hpins', nc_mono hsub hnc, hfits, fun s => syncAll_slotAgree orig bs s (hag s)⟩
  exact explDoms_of_remaining_shape hint hpins' (fun s b hb => by
      obtain ⟨e, he, hel⟩ := hbPins s b hb
      exact ⟨e, hsub e he, hel⟩) hfits
    (fun i hi => syncAll_explains_shape hint (frame_views hint hfits) hfits hnc hag i hi)

end LeanFzn.Solver.UIP.LcgRunInv
