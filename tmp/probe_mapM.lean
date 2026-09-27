import LeanFzn
open LeanFzn

example (f : Expr → Option Value) (x y : Ident) (e3 : Expr) :
    [Expr.basic (.ident x), Expr.basic (.ident y), e3].mapM f =
      f (Expr.basic (.ident x)) >>= fun v1 =>
      f (Expr.basic (.ident y)) >>= fun v2 =>
      f e3 >>= fun v3 =>
      pure [v1, v2, v3] := by
  simp [List.mapM_cons, List.mapM_nil, Option.bind_assoc]
