/-
File: LeanFzn/Solver/UIP/Proofs/SupportedCertifiedGates.lean

Purpose: the D0 GLUE on the supported chain — the computable entry's verdict
transfers with their terminal obligations DISCHARGED from the supported gate
record (no terminal-correctness conclusion left as an open runtime contract on
this route):

  §1 `solveSupportedPhase_sat_of_gates` — `.sat` from the residual gate
     record: the B4 assembly (`supportedArmsPreserveReach_of_gates` via
     `hc.coreGates`) supplies the branch invariant, and the supported SAT
     terminal (`supportedPhaseNext_sat_solution`) closes the lift.
  §2 `solveSupportedPhase_unsat_of_gates` — `.unsat` from the residual gate
     record + the run's dead-site evidence, root-facts bridge and database
     entailment: the supported invariant discipline
     (`supportedInvariantDiscipline_of_gates`), the run's `hbr` (the premise
     bundle field) and the run's `hclos` (the core field) close the lift.

The remaining explicit hypotheses are exactly the residual PRODUCERS
(`SupportedArmInvGatesCore`'s fields, `SupportedDeadEvidence`, `hbridge`,
`hlent`) — no conclusion of the transfer is assumed.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedCertifiedGates` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedRunAssembly
import LeanFzn.Solver.UIP.Proofs.SupportedCertifiedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 `.sat` from the gate record -/

/-- **D0 SAT, GATE-FED**: a `.sat` verdict of the supported entry is a
solution witness of the run's box, with the terminal obligation discharged
from the residual gate record. -/
theorem solveSupportedPhase_sat_of_gates {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf)
    (hc : SupportedArmInvGatesCore orig original props leaf)
    (hent : LearnedEntailed leaf original)
    {w : Assignment} (hrun : solveSupportedPhase P hent = .sat w) :
    SolutionWitness leaf orig w :=
  solveSupportedPhase_sat_solution P hent
    (fun cfg w hreach _ hstep =>
      supportedSat_of_core hc hreach hstep)
    hrun

/-! ## §2 `.unsat` from the gate record -/

/-- **D0 UNSAT, GATE-FED**: a `.unsat` verdict of the supported entry
excludes every leaf solution of the run's box, with the terminal obligation
discharged from the residual gate record + the run's dead-site evidence,
root-facts bridge and database entailment. -/
theorem solveSupportedPhase_unsat_of_gates {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf)
    (hc : SupportedArmInvGatesCore orig original props leaf)
    (hdead : SupportedDeadEvidence orig original props leaf)
    (hbridge : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      RootFactsBridge leaf cfg.branch)
    (hlent : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      LearnedEntailed leaf cfg.branch.learned)
    (hent : LearnedEntailed leaf original)
    (hrun : solveSupportedPhase P hent = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False :=
  solveSupportedPhase_unsat_excludes P hent
    (fun cfg hreach _ hstep =>
      supportedPhaseNext_unsat_excludes
        (supportedInvariantDiscipline_of_gates hc.toSupportedArmInvGates)
        hdead P.hbr hbridge hlent
        (fun {cfg} hreach => by
          rw [SupportedReach.original_eq hreach, SupportedReach.props_eq hreach]
          exact hc.hclos hreach)
        hreach hstep)
    hrun

end LeanFzn.Solver.UIP
