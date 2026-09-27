import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- A successful argOf read pins the argument expression. -/
theorem argOf_ok_inv {c : ConstraintItem} {k : Nat} {b : BasicExpr}
    (h : argOf c k = .ok b) :
    c.args[k]! = .basic b := by
  unfold argOf at h
  cases he : c.args[k]! with
  | basic b2 =>
      rw [he] at h
      have : (Except.ok b2 : Except String BasicExpr) = .ok b := h
      injection this with hb
      subst hb
      rfl
  | array es =>
      exfalso
      rw [he] at h
      exact absurd h (by simp)
