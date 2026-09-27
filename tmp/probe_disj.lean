import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

example (m : Model) (slots : List (String × List Value)) (a : List Value)
    (c : ConstraintItem) (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots) (hc : c ∈ m.constraints)
    (hpred : m.predicates = []) (hmem : a ∈ allAssigns (slots.map Prod.snd))
    (h : c.name.name = "int_gt") (x : Ident) (i : Nat)
    (hxarg : Expr.basic (.ident x) ∈ c.args)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i) :
    ∃ p, a[i]! = Value.int p :=
  int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))) hmem x i hxarg hxi
