/-
Purpose: assignment coverage of pending finite-domain frames and branch splitting.
Dependencies: Frontier supplies frames; LeanFzn.Solver.Core.Enumerate specifies finite assignments.
DAG: Frontier + Search -> FrontierSemantics -> pruned and reference search proofs.
-/
import LeanFzn.Solver.Propagation.Frontier
import LeanFzn.Solver.Core.Enumerate
open LeanFzn.Semantics LeanFzn.Solver.Propagation


namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

def FrameCovers (f : BranchFrame) (a : Assignment) : Prop :=
  ∃ tail ∈ allAssigns f.1, a = f.2 ++ tail

def FrontierCovers (pending : List BranchFrame) (a : Assignment) : Prop :=
  ∃ f ∈ pending, FrameCovers f a

theorem covers_split (v : Value) (vs : Domain) (rest : List Domain)
    (chosen a : Assignment) :
    FrameCovers ((v :: vs) :: rest, chosen) a ↔
      FrameCovers (rest, chosen ++ [v]) a ∨ FrameCovers (vs :: rest, chosen) a := by
  constructor
  · rintro ⟨tail, htail, rfl⟩
    obtain ⟨w, hw, suffix, hs, rfl⟩ := (mem_allAssigns_singleton v vs rest tail).mp htail
    rcases List.mem_cons.mp hw with rfl | hw
    · exact Or.inl ⟨suffix, hs, by simp [List.append_assoc]⟩
    · apply Or.inr
      refine ⟨w :: suffix, ?_, rfl⟩
      cases vs with
      | nil => cases hw
      | cons u us => exact (mem_allAssigns_singleton u us rest _).mpr ⟨w, hw, suffix, hs, rfl⟩
  · rintro (⟨tail, ht, rfl⟩ | ⟨tail, ht, rfl⟩)
    · refine ⟨v :: tail, (mem_allAssigns_singleton v vs rest _).mpr
        ⟨v, List.mem_cons_self, tail, ht, rfl⟩, ?_⟩
      simp [List.append_assoc]
    · exact ⟨tail, allAssigns_subset_cons v vs rest tail ht, rfl⟩

end LeanFzn.Solver.Propagation
