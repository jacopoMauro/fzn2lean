import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- FlatMap-membership reflection: a member of a flatMap comes from a
    source member. -/
theorem mem_flatMap_src {α β : Type} (f : α → List β) :
    ∀ (l : List α) (x : β), x ∈ l.flatMap f → ∃ a, a ∈ l ∧ x ∈ f a := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a rest ih =>
      intro x hx
      rw [List.flatMap_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ⟨a, List.mem_cons_self, hx⟩
      · obtain ⟨a2, ha2mem, ha2mem2⟩ := ih x hx
        exact ⟨a2, List.mem_cons_of_mem _ ha2mem, ha2mem2⟩
