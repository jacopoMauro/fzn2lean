/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerCertifiedRun.lean

Purpose: D0's whole-run certification assembly home. The D1 transfer
theorems (`solvePhaseCompiled_sat_solution`, `solvePhaseCompiled_unsat_excludes`)
live HERE, moved verbatim from `Proofs/Search.lean` so that Search and its
cone no longer import the run assembly: that import edge
(`Proofs/Search → SchedulerRunAssembly → SchedulerArmsComplete →
SchedulerArmsPreserve`) closed a build cycle once B4's arm assembly needed
`Proofs/SchedulerDecideSkip` (needed in turn for the skip arm's Bool
discharge). Statements and names are unchanged; only the hosting module
moved.

The SAT transfer consumes the branch-reachability premise through
`RunAssembly.phaseNextSatSolution_of_reachPreserve`; the UNSAT transfer
consumes the concrete run premises through
`RunAssembly.phaseNextUnsatTerminal_of_runPremises` — no bare
`PhaseNextSatSolution`/`PhaseUnsatTerminal` and no global exclusion
conclusion remains as a hypothesis.

NO `sorry`, no custom axiom. DAG: Proofs.Search + Proofs.SchedulerRunAssembly
-> this module (D0/D1 outlet; consumed by the public routing task D2).

Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SchedulerCertifiedRun`.
-/

import LeanFzn.Solver.UIP.Proofs.CompiledSearch
import LeanFzn.Solver.UIP.Proofs.SchedulerRunAssembly
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference
open LeanFzn.Solver.UIP.P5
  (ReachablePhaseProgressSelf ReachablePhaseProgressSorted
    reachablePhaseProgressSorted_of_premises
    reachablePhaseKernelSorted runReachable ReachablePhaseKernel)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference
open LeanFzn.Solver.UIP.X2 (runPhaseFrom runPhaseFromSorted runPhase
  runPhase_eq_runReachable)

/-- **B4 AT THE FROZEN NAMES**: ONE `ArmInvGates` record yields BOTH B4
outputs the run assembly consumes — the reach-aware arm assembly (§5 of
`SchedulerArmsPreserve`, through the shared-gate projection) and the
invariant discipline (§6 there, `RunAssembly.ReachableInvariantDiscipline`
definitionally). -/
theorem b4_of_gates {leaf : Assignment → Bool} (hg : ArmInvGates leaf) :
    ReachableArmsPreserveReach leaf ∧
      RunAssembly.ReachableInvariantDiscipline leaf :=
  ⟨reachableArmsPreserveReach_of_gates hg.toArmGates,
    fun {cfg} hreach => reachableInvariantDiscipline_of_gates hg cfg hreach⟩

/-- **D1 SAT TRANSFER**: a `.sat` verdict of the compiled entry is a
solution witness of the run's original box. W1's `run_sat_solution` at
the compiled kernel; the frame is Prem1's PROVED `phaseNextOrigFrame`;
the terminal obligation is DISCHARGED by the assembly wrapper
`RunAssembly.phaseNextSatSolution_of_reachPreserve` from the branch
reachability premise `hpres` (owner B4) — no bare
`PhaseNextSatSolution` remains as a hypothesis (D0). -/
theorem solvePhaseCompiled_sat_solution {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (P : CompiledPhasePremises (leaf := leaf) problem)
    (hpres : ReachableArmsPreserveReach leaf)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) {w : Assignment}
    (hrun : solvePhaseCompiled (leaf := leaf) P original props hent = .sat w) :
    SolutionWitness leaf problem.domains w :=
  W1.run_sat_solution_sorted
    (reachablePhaseProgressSorted_of_premises P.halignDB P.hbr)
    (fun _ _ hreach hsucc => phaseNext_reachable_succ hreach hsucc)
    (phaseNextOrigFrame problem.domains leaf)
    (RunAssembly.phaseNextSatSolution_of_reachPreserve
      (orig := problem.domains) hpres)
    (SchedulerConfig.init problem.domains original props)
    (schedulerReachable_init problem.domains original props hent) rfl hrun

/-- **D1 UNSAT TRANSFER**: a `.unsat` verdict of the compiled entry excludes
every leaf solution of the run's original box. W1's `run_unsat_excludes`;
the terminal obligation is DISCHARGED by the assembly wrapper
`RunAssembly.phaseNextUnsatTerminal_of_runPremises` from the concrete run
premises (invariant discipline, dead-site evidence, branch reachability,
level-0 trail-facts bridge, database entailment, closure contract along the
run) — no bare `PhaseUnsatTerminal` and no global exclusion conclusion
remains as a hypothesis (D0/A1). -/
theorem solvePhaseCompiled_unsat_excludes {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (P : CompiledPhasePremises (leaf := leaf) problem)
    (hinv : RunAssembly.ReachableInvariantDiscipline leaf)
    (hdead : RunAssembly.ReachableDeadEvidence leaf)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = problem.domains → ReachableState leaf problem.domains cfg.branch)
    (hbridge : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = problem.domains → RootFactsBridge leaf cfg.branch)
    (hlent : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      LearnedEntailed leaf cfg.branch.learned)
    (hc : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      cfg.orig = problem.domains →
        ClosureContract leaf problem.domains cfg.original cfg.props)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original)
    (hrun : solvePhaseCompiled (leaf := leaf) P original props hent = .unsat) :
    ∀ a, OriginalLeaves leaf problem.domains a → False :=
  W1.run_unsat_excludes_sorted
    (reachablePhaseProgressSorted_of_premises P.halignDB P.hbr)
    (fun _ _ hreach hsucc => phaseNext_reachable_succ hreach hsucc)
    (phaseNextOrigFrame problem.domains leaf)
    (RunAssembly.phaseNextUnsatTerminal_of_runPremises hinv hdead hbr hbridge
      hlent hc)
    (SchedulerConfig.init problem.domains original props)
    (schedulerReachable_init problem.domains original props hent) rfl hrun

end LeanFzn.Solver.UIP
