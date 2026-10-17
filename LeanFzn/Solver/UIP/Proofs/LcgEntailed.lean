/-
File: LeanFzn/Solver/UIP/Proofs/LcgEntailed.lean

Entailment of the learned database and of the trail reasons along supported runs.

`EntailedRun` (LcgRunInvariantFinal.lean) asks that the learned database is globally entailed
at every supported configuration. Its premise `hent` in `lcgRunInvCond_of_residual`
(LcgEvidence.lean) is discharged here from the reachable-branch premise `hbr` alone: the
structure `ReachableState` (Proofs/BranchState.lean) carries `wf : bs.WellFormed`, whose fifth
conjunct is `LearnedEntailed leaf bs.learned` and whose third conjunct gives entailment of every
trail reason clause.

This is NOT an independent induction over `SupportedReach`. The per-arm preservation of `wf`
(the learn/backjump/assert arm via the analyzer lemma `analyzeAtAllowance_learnedEntailed`, the
propagate arm via `ClosureContract.reasonEntailed`, the conflict arm via `conflictEntailed`) is
exactly what the named premise `hbr` packages (`ReachableArmsPreserve`, SchedulerReachClosure).
Discharging `hbr` per arm is the remaining gap.
-/
import LeanFzn.Solver.UIP.Proofs.LcgEvidence
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantFinal

namespace LeanFzn.Solver.UIP.LcgEntailed

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-- Every reachable branch state has a globally entailed learned database. -/
theorem learned_entailed_of_reachable {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) : LearnedEntailed leaf bs.learned :=
  h.wf.2.2.2.2

/-- Every trail reason clause of a reachable branch state is globally entailed. -/
theorem trail_reasons_entailed_of_reachable {orig : List Domain} {bs : BranchState leaf}
    (h : ReachableState leaf orig bs) :
    ∀ e ∈ bs.trail, ∀ r ∈ e.reason, LearnedEntailed leaf [r.clause] :=
  fun e he r hr => (h.wf.2.2.1 e he r hr).1

/-- **EntailedRun from the reachable-branch premise.** The learned database is entailed at
every supported configuration, with no separate `hent` premise. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem entailedRun_of_supportedRun {orig : List Domain} {original : List Clause}
    {props : List Propagator}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch) :
    EntailedRun orig original props leaf := by
  intro cfg hreach
  exact learned_entailed_of_reachable (hbr hreach)

/-- **The conditional run invariant without the `hent` premise.** Same premises as
`lcgRunInvCond_of_residual` minus `hent`; the entailed-database field is derived from `hbr`. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem lcgRunInvCond_of_residual_noEnt {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw)
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, d.Nodup)
    (htyped : ClampPool.EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hfit : ∀ a, leaf a = true → a.Fits orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hA : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → AssertingSem cfg)
    (hlive : DecideLive orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LeanFzn.Solver.UIP.LcgEvidence.LcgRunInv' cfg :=
  LeanFzn.Solver.UIP.LcgEvidence.lcgRunInvCond_of_residual hraw hprops hfam hint hnd htyped horig hfit hbr hA
    (entailedRun_of_supportedRun hbr) hlive

end LeanFzn.Solver.UIP.LcgEntailed
