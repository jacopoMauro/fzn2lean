import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- FilterMap-membership reflection: a member of a filterMap comes
    from a source member mapping to it. -/
theorem mem_filterMap_src {α β : Type} (F : α → Option β) :
    ∀ (l : List α) (x : β), x ∈ l.filterMap F →
      ∃ a, a ∈ l ∧ F a = some x := by
  intro l
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons a rest ih =>
      intro x hx
      have hex : ∃ a', a' ∈ a :: rest ∧ F a' = some x :=
        List.mem_filterMap.mp hx
      obtain ⟨a', ha'mem, ha'val⟩ := hex
      exact ⟨a', ha'mem, ha'val⟩
