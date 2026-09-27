import solver.Direct.Proofs.Compile
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

example (c : ConstraintItem) (e1 : BasicExpr) (rest : List Expr)
    (hargs : c.args = (.basic e1) :: rest) : argOf c 0 = e1 := by
  unfold argOf
  rw [hargs]
  rfl

example (c : ConstraintItem) (e1 e2 : BasicExpr) (rest : List Expr)
    (hargs : c.args = (.basic e1) :: (.basic e2) :: rest) : argOf c 1 = e2 := by
  unfold argOf
  rw [hargs]
  rfl

example (c : ConstraintItem) (e1 e2 e3 : BasicExpr) (rest : List Expr)
    (hargs : c.args = (.basic e1) :: (.basic e2) :: (.basic e3) :: rest) :
    argOf c 2 = e3 := by
  unfold argOf
  rw [hargs]
  rfl
