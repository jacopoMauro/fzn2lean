import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- If `argOf c k` succeeds with an identifier, the k-th argument is
    that identifier's basic expression. -/
theorem argOf_ident_inv {c : ConstraintItem} {k : Nat} {x : Ident}
    (h : argOf c k = .ok (.ident x)) :
    c.args[k]! = .basic (.ident x) := by
  unfold argOf at h
  cases he : c.args[k]! with
  | basic b =>
      rw [he] at h
      cases hb : b with
      | ident x2 =>
          have hred : BasicExpr.ident x2 = BasicExpr.ident x := by
            have h2 : (Except.ok (BasicExpr.ident x2) :
                Except String BasicExpr) = .ok (.ident x) := by
              rw [← hb]; exact h
            exact (Except.ok.inj h2).symm ▸ rfl
          injection hred with hx
          subst hx
          rfl
      | lit l =>
          exfalso
          have h2 : (Except.ok (BasicExpr.lit l) :
              Except String BasicExpr) = .ok (.ident x) := by
            rw [← hb]; exact h
          cases l <;> exact absurd h2 (by simp)
  | array es =>
      exfalso
      rw [he] at h
      exact absurd h (by simp)

/-- If `argOf c k` succeeds with an int literal, the k-th argument is
    that literal's basic expression or a parameter identifier. -/
theorem argOf_lit_int_inv {c : ConstraintItem} {k : Nat} {v : Int}
    (h : argOf c k = .ok (.lit (.int v))) :
    c.args[k]! = .basic (.lit (.int v)) ∨ ∃ x, c.args[k]! = .basic (.ident x) := by
  unfold argOf at h
  cases he : c.args[k]! with
  | basic b =>
      rw [he] at h
      cases hb : b with
      | ident x2 => exact Or.inr ⟨x2, rfl⟩
      | lit l =>
          cases l with
          | int i2 =>
              have h2 : (Except.ok (BasicExpr.lit (BasicLiteral.int i2)) :
                  Except String BasicExpr) = .ok (.lit (.int v)) := by
                rw [← hb]; exact h
              have h3 : BasicExpr.lit (BasicLiteral.int i2)
                  = BasicExpr.lit (.int v) := (Except.ok.inj h2)
              injection h3 with h4
              injection h4 with h5
              subst h5
              exact Or.inl rfl
          | bool w =>
              exfalso
              have h2 : (Except.ok (BasicExpr.lit (BasicLiteral.bool w)) :
                  Except String BasicExpr) = .ok (.lit (.int v)) := by
                rw [← hb]; exact h
              exact absurd h2 (by simp)
          | set w =>
              exfalso
              have h2 : (Except.ok (BasicExpr.lit (BasicLiteral.set w)) :
                  Except String BasicExpr) = .ok (.lit (.int v)) := by
                rw [← hb]; exact h
              exact absurd h2 (by simp)
  | array es =>
      exfalso
      rw [he] at h
      exact absurd h (by simp)
