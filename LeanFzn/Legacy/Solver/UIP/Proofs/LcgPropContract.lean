/-
File: LeanFzn/Solver/UIP/Proofs/LcgPropContract.lean

Contract export for the LCG kit: the `PropagationContract` required by
`LcgRunGood.LcgKit` (field `contract`) for the raw propagator list
`dcs.filterMap propagatorOfProved`, where `dcs` is the compiled problem's
constraint list. The contract is the problem-level one already certified in
`CompiledScheduler` (`CompiledInput.propagationContract`), so the family gate
`lcgFamB` is NOT needed here: `PropagationContract` quantifies over all
registered propagators, and the family restriction only matters for the
semantic (`PropSemContract`) fields, which live in `LcgFamiliesRun`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.CompiledScheduler

namespace LeanFzn.Solver.UIP.LcgPropContract

open LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering

variable {leaf : Assignment → Bool}
  {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}

/-- **`PropagationContract` for the LCG kit's raw list.** For a compiled,
gate-passing problem whose leaf is the compiled chronological leaf, the
registered proved propagators of `dcs = problem.constraints` satisfy the
semantic contract. Premises: `CompiledInput leaf problem` only (executable
gates `gateOk`, `domPruningOkB`, and the leaf identification). -/
theorem propagationContract_of_families (hin : CompiledInput leaf problem)
    (dcs : List DomConstraint) (hdcs : dcs = problem.constraints) :
    PropagationContract leaf (dcs.filterMap propagatorOfProved) := by
  subst hdcs
  exact CompiledInput.propagationContract hin

end LeanFzn.Solver.UIP.LcgPropContract
