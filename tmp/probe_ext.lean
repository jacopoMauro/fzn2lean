import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

theorem Holds_ext {store1 store2 : Store} {c : ConstraintItem}
    (h : ∀ x, store1 x = store2 x)
    (hh : c.Holds fullInterp store1) :
    c.Holds fullInterp store2 := by
  obtain ⟨args, hmap, hinterp⟩ := hh
  refine ⟨args, ?_, hinterp⟩
  have heval : ∀ (e : Expr), Expr.eval store1 e = Expr.eval store2 e := by
    intro e
    induction e with
    | basic b =>
        cases b with
        | lit l => rfl
        | ident x => rw [h x]
    | array es ih =>
        simp only [Expr.eval]
        simp only [List.mapM_map] at *
        sorry
  sorry
