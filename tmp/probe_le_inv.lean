import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- A successful fallback compile of `int_le` pins the shape. -/
theorem compileConstraint_le_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_le")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ x E i k, c.args = [Expr.basic (.ident x), E] ∧
      nameIndex names x.name = some i ∧
      (E = Expr.basic (.lit (.int k)) ∧ dc = .leConstHi i k ∨
       ∃ y, E = Expr.basic (.ident y) ∧ env y = some (.int k) ∧
         dc = .leConstHi i k) ∨
    ∃ y E j k, c.args = [E, Expr.basic (.ident y)] ∧
      nameIndex names y.name = some j ∧
      (E = Expr.basic (.lit (.int k)) ∧ dc = .leConstLo j k ∨
       ∃ x, E = Expr.basic (.ident x) ∧ env x = some (.int k) ∧
         dc = .leConstLo j k) := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have hgate : (c.name.name = "int_plus" ∧ c.args.length = 3) = false := by
    simp [hname]
  have hgate2 : (c.name.name = "int_le" ∧ c.args.length = 2) = true := by
    simp [hname, hargs]
  simp only [hgate, hgate2, reduceIte] at h
  match h0 : compileArgVal env names (argOf c 0),
      h1 : compileArgVal env names (argOf c 1) with
  | .ok (.slotRef i), .ok (.litVal (.int k)) =>
      obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv h0
      -- arg0 is the ident x; arg1 is E (lit or param ident)
      have harg0 : c.args[0]! = Expr.basic (.ident x) := by
        show (match c.args[0]! with
          | .basic b => b | .array _ => .lit (.int 0)) = _
        rw [show c.args[0]! = .basic (.ident x) from by
          unfold argOf at hx
          rw [hx] at *
          sorry]
        sorry
      sorry
  | .ok (.litVal (.int k)), .ok (.slotRef j) => sorry
  | .error e, _ => rw [h0, h1] at h; cases h
  | _, .error e => rw [h0, h1] at h; cases h
  | _, _ => rw [h0, h1] at h; cases h
