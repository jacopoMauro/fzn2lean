/-! ## The fallback gate inversions (per family) -/

/-- The source-shape disjunction shared by the two-argument fallback
    families: the non-slot argument is an int literal or a parameter
    identifier (resolving to the literal through the environment,
    with the name NOT a slot name). -/
def IntValuedArg (env : Store) (names : List String)
    (E : Expr) (k : Int) : Prop :=
  E = Expr.basic (.lit (.int k)) ∨ ∃ z, E = Expr.basic (.ident z) ∧
    nameIndex names z.name = none ∧ env z = some (.int k)

/-- The generic two-argument fallback do-block's inversion: a
    successful compile pins the argval pattern and the compiled
    form. -/
theorem fallback2_do_inv {env : Store} {names : List String}
    {b0 b1 : BasicExpr} {dc : DomConstraint}
    {f : Nat → Int → DomConstraint} {g : Int → Nat → DomConstraint}
    (h : ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) => .ok (f i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) => .ok (g k j)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported argument shapes" :
        Except String DomConstraint)) = .ok dc) :
    (∃ i k, compileArgVal env names b0 = .ok (.slotRef i) ∧
        compileArgVal env names b1 = .ok (.litVal (.int k)) ∧
        dc = f i k) ∨
    (∃ j k, compileArgVal env names b0 = .ok (.litVal (.int k)) ∧
        compileArgVal env names b1 = .ok (.slotRef j) ∧
        dc = g k j) := by
  split at h
  next i k hc0 hc1 =>
      exact Or.inl ⟨i, k, hc0, hc1, by
        have := (Except.ok.inj h)
        exact this ▸ rfl⟩
  next k j hc0 hc1 =>
      exact Or.inr ⟨j, k, hc0, hc1, by
        have := (Except.ok.inj h)
        exact this ▸ rfl⟩
  all_goals exact absurd h (by intro hc; injection hc)

/-- The int_le fallback gate: the do-block after the gate chain. -/
theorem fallback2_gate_le {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_le")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.leConstHi i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
            .ok (DomConstraint.leConstLo j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_le argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  have hplus_ne : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h1 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  unfold compileConstraint at h
  simp only [hnone] at h
  rw [if_neg hplus_ne] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e => rw [h0] at h; exact absurd h (by simp)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e => rw [h1] at h; exact absurd h (by simp)
      | .ok b1 =>
          rw [h1] at h
          exact ⟨b0, b1, h0, h1, h⟩

end LeanFzn.Solver.Direct
