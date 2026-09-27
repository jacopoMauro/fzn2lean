import solver.Direct.Proofs.Compile
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

theorem holds_int_plus_E_inv {store : Store} {c : ConstraintItem}
    {x y : Ident} {k : Int} {E : Expr}
    (hname : c.name.name = "int_plus")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.int p) ∧ store y = some (.int q) ∧
      p + q = k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  simp only [Expr.eval, BasicExpr.eval] at hmap
  cases hsx : store x with
  | none => rw [hsx] at hmap; simp at hmap
  | some vx =>
      rw [hsx] at hmap
      cases hsy : store y with
      | none => rw [hsy] at hmap; simp at hmap
      | some vy =>
          rw [hsy] at hmap
          sorry
