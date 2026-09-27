import solver.Direct.Proofs.Compile
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

theorem three_of_bang {c : ConstraintItem}
    (hlen : c.args.length = 3)
    (h0 : c.args[0]! = Expr.basic b0)
    (h1 : c.args[1]! = Expr.basic b1)
    (h2 : c.args[2]! = Expr.basic b2) :
    c.args = [Expr.basic b0, Expr.basic b1, Expr.basic b2] := by
  match h : c.args with
  | e0 :: e1 :: e2 :: e3 :: rest =>
      exfalso
      rw [h] at hlen
      simp only [List.length_cons] at hlen
      omega
  | e0 :: e1 :: e2 :: [] =>
      rw [h] at h0 h1 h2
      simp only [List.getElem!_cons_zero, List.getElem!_cons_succ,
        List.getElem!_cons_zero] at h0 h1 h2
      rw [h0, h1, h2]
  | e0 :: e1 :: [] =>
      rw [h] at hlen; simp at hlen
  | [e0] => rw [h] at hlen; simp at hlen
  | [] => rw [h] at hlen; simp at hlen
