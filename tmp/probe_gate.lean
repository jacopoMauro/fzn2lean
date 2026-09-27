import solver.Direct.Proofs.Compile
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

example (env : Store) (names : List String) (c : ConstraintItem)
    (x y : Ident) (k : Int) (i j : Nat)
    (hname : c.name.name = "int_plus")
    (hargs : c.args.length = 3)
    (harg0 : c.args[0]! = .basic (.ident x))
    (harg1 : c.args[1]! = .basic (.ident y))
    (harg2 : c.args[2]! = .basic (.lit (.int k)))
    (hx : nameIndex names x.name = some i)
    (hy : nameIndex names y.name = some j)
    (hnone : extractConstraint names c = none) :
    compileConstraint env names c = .ok (.linEq [1, 1] [i, j] k) := by
  have h0 : compileArgVal env names (argOf c 0) = .ok (.slotRef i) := by
    have : compileArgVal env names (.ident x) = .ok (.slotRef i) := by
      simp only [compileArgVal]
      rw [hx]
    simp only [argOf, harg0]
    exact this
  have h1 : compileArgVal env names (argOf c 1) = .ok (.slotRef j) := by
    have : compileArgVal env names (.ident y) = .ok (.slotRef j) := by
      simp only [compileArgVal]
      rw [hy]
    simp only [argOf, harg1]
    exact this
  have h2 : compileArgVal env names (argOf c 2) =
      .ok (.litVal (.int k)) := by
    simp only [argOf, harg2]
    rfl
  unfold compileConstraint
  simp only [hnone]
  rw [if_pos ⟨hname, hargs⟩, h0, h1, h2]
