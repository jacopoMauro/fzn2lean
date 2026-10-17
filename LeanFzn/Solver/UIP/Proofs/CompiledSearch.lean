/- Compiled conditional first-UIP phase driver. -/
import LeanFzn.Solver.UIP.Scheduler
import LeanFzn.Solver.UIP.Proofs.SchedulerRun
import LeanFzn.Solver.UIP.Proofs.SchedulerReachClosure
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## D1: the compiled phase driver and the W1 transfer

Public driver entry `solvePhaseCompiled`: X2's computable
`runPhaseFromSorted` over the compiled package (D0's `CompiledInput`
gates), started at the compiled box's root configuration
(`SchedulerConfig.init`, reachable by R1's `schedulerReachable_init`). The
kernel comes from P5's `reachablePhaseProgressSorted_of_premises` (C2:
the sorted chain, whose canonical-pool membership is discharged
internally); its named premises are EXPLICIT hypotheses of the entry point
— never axioms, and all SELF-RELATIVE (G1 scoping):

* `halignDB` — C1 (database-side literal-pool alignment at the
  configuration's own box);
* `hdb`      — S4/S5 (`DatabaseUnfalsified` on reachable branches);
* `hbr`      — S5/B4 reachable-branch invariant in SELF-`orig` form.
  Prem1's `hbr_of_reachPreserve` produces it from B4's
  `ReachableArmsPreserveReach`; the self form is taken explicitly here and
  the reduction is documented, not assumed.

The reachability closure (`hclos`) is Prem1's PROVED
`phaseNext_reachable_succ`; the `orig` frame is Prem1's PROVED
`phaseNextOrigFrame`. The ranked instance
(`reachablePhaseProgressRanked_of_premises`, P3-`PhaseRank`) remains
available for reference but is not the routed chain. W1's transfer:
SAT/UNSAT/totality at the entry
(`solvePhaseCompiled_sat_solution`, `solvePhaseCompiled_unsat_excludes`,
`solvePhaseCompiled_total`). D0/A1: the terminal obligations are now
DISCHARGED, not hypothesised — the SAT transfer consumes the branch
reachability premise `hpres` through
`RunAssembly.phaseNextSatSolution_of_reachPreserve`, and the UNSAT transfer
consumes the concrete run premises (invariant discipline, dead-site
evidence, branch reachability, level-0 trail-facts bridge, database
entailment, closure contract along the run) through
`RunAssembly.phaseNextUnsatTerminal_of_runPremises`; no bare
`PhaseNextSatSolution`, `PhaseUnsatTerminal` or global exclusion conclusion
remains. Plus agreement with P5's verified driver through X2's
`runPhase_eq_runReachable`.

EXECUTABLE-TO-THEOREM MAPPING (D1 §5): `solvePhaseCompiled` is the
computable driver carrying the theorems below. The CLI's live certified
route is the chronological `analyzedSolve` path (`solveChronological` is
its named reference; `solveCertified`'s three public statements are
preserved); no live CLI call site consumes the refuted-contract adapters
`DomJumpDiscipline`/`domJumpDecrease`/`solveWithEventsOfJump` (removed
from `LeanFzn/Solver/UIP/DomPruning.lean`). -/

open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.P5
  (ReachablePhaseProgressSelf ReachablePhaseProgressSorted
    reachablePhaseProgressRanked_of_premises reachablePhaseProgressSorted_of_premises
    reachablePhaseKernel reachablePhaseKernelSorted runReachable ReachablePhaseKernel)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.X2 (runPhaseFrom runPhaseFromSorted runPhase runPhase_eq_runReachable)

/-- D1: the explicit-premise bundle consumed by the compiled driver entry.
G1-SCOPED: every premise is SELF-RELATIVE (read at the configuration's own
box `cfg.orig`), so it is provable on the run's own data and does not
quantify over runs on other boxes. The driver runs the SORTED chain (C2),
whose pool-membership component is discharged internally
(`canonicalSorted_mem_sortedClausePool`), so no `hpool` premise remains. -/
structure CompiledPhasePremises {leaf : Assignment → Bool}
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Prop where
  /-- C1: every clause stored in a reachable branch's database has all its
  literals in the OWN box's literal pool (database-side pool alignment). -/
  halignDB : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool cfg.orig
  /-- S5/B4: the reachable branch invariant in SELF-`orig` form
  (production: `hbr_of_reachPreserve` from `ReachableArmsPreserveReach`). -/
  hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    ReachableState leaf cfg.orig cfg.branch

/-- The kernel of the compiled driver from the explicit premise bundle,
SORTED chain (C2). -/
def compiledPhaseKernel {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (P : CompiledPhasePremises (leaf := leaf) problem) : ReachablePhaseKernel leaf :=
  reachablePhaseKernelSorted
    (reachablePhaseProgressSorted_of_premises P.halignDB P.hbr)
    (fun _ _ hreach hsucc => phaseNext_reachable_succ hreach hsucc)

/-- **THE D1 PUBLIC DRIVER ENTRY**: X2's computable `runPhaseFromSorted`
over the compiled package — root configuration of the run's original box,
the sorted-chain P5 kernel from the explicit self-relative premises. No
fuel, no axiom, no hidden premise. -/
def solvePhaseCompiled {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (P : CompiledPhasePremises (leaf := leaf) problem)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) : DriverResult leaf :=
  runPhaseFromSorted
    (reachablePhaseProgressSorted_of_premises P.halignDB P.hbr)
    (fun _ _ hreach hsucc => phaseNext_reachable_succ hreach hsucc)
    (SchedulerConfig.init problem.domains original props)
    (schedulerReachable_init problem.domains original props hent)

/-- Agreement with P5's verified well-founded driver (X2's
`runPhase_eq_runReachable`): the compiled entry returns `runReachable`'s
result on the root configuration. -/
theorem solvePhaseCompiled_eq_runReachable {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (P : CompiledPhasePremises (leaf := leaf) problem)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) :
    solvePhaseCompiled (leaf := leaf) P original props hent =
      runReachable (compiledPhaseKernel P)
        (SchedulerConfig.init problem.domains original props)
        (schedulerReachable_init problem.domains original props hent) := by
  exact runPhase_eq_runReachable _ _ _

/- **D1 SAT/UNSAT TRANSFERS moved to `Proofs/SchedulerCertifiedRun.lean`**
(D0's assembly home): hosting them here forced the import
`Proofs/Search → SchedulerRunAssembly`, which closed a build cycle once
B4's arm assembly needed `Proofs/SchedulerDecideSkip`. Statements and
names are unchanged; see that module. -/

/-- **D1 TOTALITY**: the compiled entry returns a verdict on every supported
input — pure well-founded recursion, no fuel and no runtime contract. -/
theorem solvePhaseCompiled_total {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (P : CompiledPhasePremises (leaf := leaf) problem)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) :
    ∃ r : DriverResult leaf, solvePhaseCompiled (leaf := leaf) P original props hent = r :=
  ⟨_, rfl⟩

end LeanFzn.Solver.UIP
