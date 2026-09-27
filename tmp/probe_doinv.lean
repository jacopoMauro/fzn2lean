import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- The int_le do-block's inversion over concrete basic expressions. -/
theorem le_do_inv {env : Store} {names : List String}
    {b0 b1 : BasicExpr} {dc : DomConstraint}
    (h : (do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.leConstHi i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
            .ok (DomConstraint.leConstLo j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_le argument shapes") = .ok dc) :
    (∃ i k, compileArgVal env names b0 = .ok (.slotRef i) ∧
        compileArgVal env names b1 = .ok (.litVal (.int k)) ∧
        dc = .leConstHi i k) ∨
    (∃ j k, compileArgVal env names b0 = .ok (.litVal (.int k)) ∧
        compileArgVal env names b1 = .ok (.slotRef j) ∧
        dc = .leConstLo j k) := by
  split at h
  next i k h0 h1 =>
      exact Or.inl ⟨i, k, h0, h1, by
        have := (Except.ok.inj h)
        exact this ▸ rfl⟩
  next k j h0 h1 =>
      exact Or.inr ⟨j, k, h0, h1, by
        have := (Except.ok.inj h)
        exact this ▸ rfl⟩
  all_goals exact absurd h (by intro hc; injection hc)
