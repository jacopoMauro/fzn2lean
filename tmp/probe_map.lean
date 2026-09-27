import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-- The bang read of a mapped range list. -/
theorem getElem!_map_range {α β : Type} (f : α → β) (n : Nat)
    (i : Nat) (hlt : i < n) :
    (List.map f (List.range n))[i]! = f i := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem_map,
    List.getElem_range (by omega)]
  rfl
