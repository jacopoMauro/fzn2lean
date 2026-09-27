import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

example {env : Store} {names : List String} {c : ConstraintItem}
    {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_le")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) : True := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have hgplus : (c.name.name = "int_plus" ∧ c.args.length = 3) = false := by
    simp [hname]
  rw [if_neg (by simp [hgplus] : ¬(c.name.name = "int_plus" ∧
      c.args.length = 3) = true)] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  trivial
