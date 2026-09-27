import solver.Direct.Proofs.Compile
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

theorem eval_three_inv {store : Store}
    {x y : Ident} {e3 : Expr} {l : List Value}
    (h3 : [Expr.basic (.ident x), Expr.basic (.ident y), e3].mapM
        (Expr.eval store) = some l) :
    ∃ v1 v2 v3, store x = some v1 ∧ store y = some v2 ∧
      Expr.eval store e3 = some v3 ∧ l = [v1, v2, v3] := by
  simp only [List.mapM_cons, List.mapM_nil] at h3
  -- the FULL bind chain with the third symbolic
  have hfull : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
        (fun v2 => Option.bind (Expr.eval store e3)
          (fun v3 => some (v1 :: v2 :: [v3])))) = some l := h3
  sorry
