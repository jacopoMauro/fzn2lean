import LeanFzn.Solver.Propagation.PruningTypes
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

theorem EntailedDB.append {leaf : Assignment → Bool} {xs ys : List Clause}
    (hx : EntailedDB leaf xs) (hy : EntailedDB leaf ys) : EntailedDB leaf (xs ++ ys) := by
  intro c hc a ha
  rcases List.mem_append.mp hc with hc | hc
  · exact hx c hc a ha
  · exact hy c hc a ha

end LeanFzn.Solver.Propagation
