import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

-- probe the exact goal shapes
example (m : Model) (problem : CompiledProblem DomConstraint)
    (slots : List (String × List Value)) (dcs : List DomConstraint)
    (hc : compileModel m = .ok problem)
    (hasm : problem = assemble m slots dcs)
    (hslot : slotsChecked m = .ok slots)
    (store : Store)
    (hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array _ _ _ _ => False)
    : True := by
  have hreads := slot_reads_of_satisfying hc hasm hslot hvars
  trivial
