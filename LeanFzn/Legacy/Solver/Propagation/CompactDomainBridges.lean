/-
File: LeanFzn/Solver/Propagation/CompactDomainBridges.lean

Purpose:
  The S2 bridges between the compact `Dom` filter and the legacy
  positional `filterSlots`/`prefixFilterFrame` surface.  They lived in
  `Propagation/CompactDomain.lean`, but that module now sits *below*
  `FrameFilter` so the latter can call the structural `filterLit`; moving
  the bridges here keeps the DAG acyclic.

Dependencies: CompactDomain (filterLit and its laws) and FrameFilter
(the positional filters).
DAG: CompactDomain -> CompactDomainBridges; FrameFilter -> CompactDomainBridges.
-/
import LeanFzn.Solver.Propagation.CompactDomain
import LeanFzn.Solver.Propagation.FrameFilter

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

namespace Dom

/-- `filterSlots` on compact domains: filters the selected slot by the
    literal, exactly as `LeanFzn.Solver.Propagation.filterSlots` does on
    legacy list domains. -/
def filterSlotsD (l : Literal) (offset : Nat) : List Dom → List Dom
  | [] => []
  | d :: rest =>
      (if offset = l.atom.slot then filterLit l d else d) :: filterSlotsD l (offset + 1) rest

theorem enum_filterSlotsD (l : Literal) (offset : Nat) (ds : List Dom) :
    (filterSlotsD l offset ds).map enum = (filterSlots l offset ds).map enum := by
  induction ds generalizing offset with
  | nil => rfl
  | cons d rest ih =>
      show ((if offset = l.atom.slot then filterLit l d else d) ::
          filterSlotsD l (offset + 1) rest).map enum =
        ((if offset = l.atom.slot then Dom.filterLitKeep l d else d) ::
          filterSlots l (offset + 1) rest).map enum
      rw [List.map_cons, List.map_cons]
      by_cases h : offset = l.atom.slot
      · rw [if_pos h, if_pos h, enum_filterLit, Dom.enum_filterLitKeep, ih]
      · rw [if_neg h, if_neg h, ih]

theorem filterSlotsD_length (l : Literal) (offset : Nat) (ds : List Dom) :
    (filterSlotsD l offset ds).length = ds.length := by
  induction ds generalizing offset with
  | nil => rfl
  | cons d rest ih => simp [filterSlotsD, ih]

theorem filterSlotsD_mass_le (l : Literal) (offset : Nat) (ds : List Dom) :
    ((filterSlotsD l offset ds).map card).sum ≤ (ds.map card).sum := by
  induction ds generalizing offset with
  | nil => exact Nat.le_refl _
  | cons d rest ih =>
      have hd : card (if offset = l.atom.slot then filterLit l d else d) ≤ card d := by
        split
        · exact card_filterLit_le l d
        · exact Nat.le_refl _
      simp only [filterSlotsD, List.map_cons, List.sum_cons]
      exact Nat.add_le_add hd (ih (offset + 1))

/-- `filterFrame` on compact frames (remaining domains and chosen
    assignment), mirroring `LeanFzn.Solver.Propagation.filterFrame`. -/
def filterFrameD (l : Literal) (f : List Dom × Assignment) : Option (List Dom × Assignment) :=
  if l.atom.slot < f.2.length then
    if l.eval f.2 == some true then some f else none
  else some (filterSlotsD l f.2.length f.1, f.2)

theorem filterFrameD_enum {l : Literal} {f g : List Dom × Assignment}
    (h : filterFrameD l f = some g) :
    ∃ g', prefixFilterFrame l f = some g' ∧
      g'.1.map enum = g.1.map enum ∧ g'.2 = g.2 := by
  unfold filterFrameD at h
  by_cases hlt : l.atom.slot < f.2.length
  · rw [if_pos hlt] at h
    by_cases hev : l.eval f.2 == some true
    · rw [if_pos hev] at h
      obtain rfl := Option.some.inj h
      refine ⟨f, ?_, rfl, rfl⟩
      unfold prefixFilterFrame
      rw [if_pos hlt, if_pos hev]
    · rw [if_neg hev] at h
      exact absurd h (by simp)
  · rw [if_neg hlt] at h
    obtain rfl := Option.some.inj h
    refine ⟨(filterSlots l f.2.length f.1, f.2), ?_, ?_, rfl⟩
    · unfold prefixFilterFrame
      rw [if_neg hlt]
    · show List.map enum (filterSlots l f.2.length f.1) =
        List.map enum (filterSlotsD l f.2.length f.1)
      exact (enum_filterSlotsD l f.2.length f.1).symm

/-- The cardinality-based mass is `Frame.mass` on the enumeration. -/
theorem massD_eq_frameMass (chosen : Assignment) (ds : List Dom) :
    massD ds = PrefixFrame.mass (ds, chosen) := by
  rw [massD_eq_map_length]
  unfold PrefixFrame.mass
  simp only [List.map_map, Function.comp_def, toDomain_eq_enum, ← Dom.length_eq_enum]

end Dom

end LeanFzn.Solver.Propagation
