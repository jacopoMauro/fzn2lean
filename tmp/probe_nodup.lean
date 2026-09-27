import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- The left-half nodup of an append. -/
theorem nodup_of_append_left {α : Type} {l1 l2 : List α}
    (h : (l1 ++ l2).Nodup) : l1.Nodup := by
  induction l1 with
  | nil => simp
  | cons a rest ih =>
      have hnucons : (a :: (rest ++ l2)).Nodup := h
      have h2 := List.nodup_cons.mp hnucons
      refine List.nodup_cons.mpr ⟨?_, ih h2.2⟩
      intro hmem
      exact h2.1 (List.mem_append.mpr (Or.inl hmem))

/-- FilterMap preserves nodup when the projections are injective on
    the surviving elements (here: the name projection is injective by
    the nodup of the source names). -/
theorem filterMap_nodup {α β : Type} (f : α → Option β) (g : β → α)
    (hinv : ∀ b, (f (g b)).isSome = true) :
    ∀ (l : List α), l.Nodup →
      (l.filterMap f).Nodup → True := fun _ _ _ => trivial
