/-
File: LeanFzn/Solver/UIP/Proofs/LcgPhaseKernel.lean
Purpose: chronology-free sorted progress and concrete supported/reachable kernels.
Dependencies: SupportedPhaseRun supplies the indexed driver and per-arm rank assembly.
Why: the runtime repeated-analysis guard discharges jump novelty independently of semantic
branch invariants. LCG correctness consumers use this leaf instead of the obsolete hbr gate.
DAG: SupportedPhaseRun -> LcgPhaseKernel -> LCG public integration.
-/
import LeanFzn.Solver.UIP.Proofs.SupportedPhaseRun

namespace LeanFzn.Solver.UIP.LcgPhaseKernel
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.P3 LeanFzn.Solver.UIP.P4 LeanFzn.Solver.UIP.P5

/-- Sorted progress on the actual supported run needs no chronological reachability gate.
The only reach-indexed rank premise is novelty, enforced by the runtime repeat guard. -/
theorem supportedPhaseProgressSorted {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    SupportedPhaseProgressSorted orig original props leaf :=
  P5.reachablePhaseProgress_of_arms (leaf := leaf)
    (R := SupportedReach orig original props)
    (Rstep := fun h hs => SupportedReach.step h hs)
    (fun cfg => PhaseRankSorted orig cfg)
    (fun cfg d => P4.phaseRankSorted_lt_propagate orig cfg d)
    (fun cfg v vs doms l hsplit =>
      P4.phaseRankSorted_lt_decide orig cfg v vs doms l hsplit)
    (fun cfg v vs doms l hsplit =>
      P4.phaseRankSorted_lt_decideSkip orig cfg v vs doms l hsplit)
    (fun hp h => P4.phaseRankSorted_lt_consume orig hp h)
    (fun hpe hlt hsucc => P5.phase_compose_consume_generic hpe hlt hsucc)
    (fun hp h => P4.fallback_then_consume_sorted orig hp h)
    (fun hp h => P4.localExclude_then_consume_sorted orig hp h)
    (fun cfg c learned n =>
      P4.phaseRankSorted_analyzeConflictCounted_stutter orig cfg c learned n)
    (fun c0 cp _ev an _restored hreach hconf hana hperf =>
      P4.phaseLtSorted_stepLearnBackjumpAssert
        (hreach.orig_eq ▸ P4.sortedNovelty_of_not_repeats
          (reachable_analysis_novel hreach.reachable hconf hana))
        hperf (planMatchesAnalysis_ofCheckpoint cp c0.branch an))


/-- A computable concrete kernel, applicable in particular to every LCG kit. -/
def supportedPhaseKernel {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    SupportedPhaseKernel orig original props leaf :=
  supportedPhaseKernelSorted (supportedPhaseProgressSorted orig original props)

/-- Sorted self-rank progress on scheduler reachability also needs no semantic gates. -/
theorem reachablePhaseProgressSorted {leaf : Assignment → Bool} :
    ReachablePhaseProgressSorted (leaf := leaf) :=
  reachablePhaseProgress_of_arms (leaf := leaf) (R := SchedulerReachable)
    (Rstep := fun h hs => SchedulerReachable.step rfl hs h) selfRankSorted
    (fun cfg d => by
      show PhaseLt (PhaseRankSorted cfg.orig (stepPropagate cfg d))
        (PhaseRankSorted cfg.orig cfg)
      exact P4.phaseRankSorted_lt_propagate cfg.orig cfg d)
    (fun cfg v vs doms l hsplit => by
      show PhaseLt (PhaseRankSorted cfg.orig (stepDecide cfg v vs doms l))
        (PhaseRankSorted cfg.orig cfg)
      exact P4.phaseRankSorted_lt_decide cfg.orig cfg v vs doms l hsplit)
    (fun cfg v vs doms l hsplit => by
      show PhaseLt (PhaseRankSorted cfg.orig (stepDecideSkip cfg v doms))
        (PhaseRankSorted cfg.orig cfg)
      exact P4.phaseRankSorted_lt_decideSkip cfg.orig cfg v vs doms l hsplit)
    (fun {cfg next f rest} hp h => by
      rw [selfRankSorted_stepConsume h]
      exact P4.phaseRankSorted_lt_consume cfg.orig hp h)
    (fun hpe hlt hsucc => phase_compose_consume_generic hpe hlt hsucc)
    (fun {cfg next r f rest} hp h => by
      rw [selfRankSorted_stepConsume h]
      exact P4.fallback_then_consume_sorted cfg.orig hp h)
    (fun {cfg next learned r f rest} hp h => by
      rw [selfRankSorted_stepConsume h]
      exact P4.localExclude_then_consume_sorted cfg.orig hp h)
    (fun cfg c learned n =>
      selfRankSorted_analyzeConflictCounted_stutter cfg c learned n)
    (fun c0 cp ev an restored hreach hconf hana hperf => by
      show PhaseLt
        (PhaseRankSorted c0.orig (stepLearnBackjumpAssert c0
          (BackjumpPlan.ofCheckpoint cp c0.branch an.asserting an.learned) ev
          restored)) (PhaseRankSorted c0.orig c0)
      exact P4.phaseLtSorted_stepLearnBackjumpAssert
        (P4.sortedNovelty_of_not_repeats (reachable_analysis_novel hreach hconf hana))
        hperf (planMatchesAnalysis_ofCheckpoint cp c0.branch an))


/-- The globally reachable sorted kernel, using actual phase-step closure. -/
def reachablePhaseKernel {leaf : Assignment → Bool} : ReachablePhaseKernel leaf :=
  reachablePhaseKernelSorted reachablePhaseProgressSorted (fun _ _ hr hs => phaseNext_reachable_succ hr hs)

/-- The supported kernel dispatches by the actual phase function. -/
theorem supportedPhaseKernel_step {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    (supportedPhaseKernel (leaf := leaf) orig original props).step = phaseNext := rfl

/-- The fuel-free initialized entry needs only entailment of its initial clause database. -/
def solve {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original) : DriverResult leaf :=
  runSupportedPhase (supportedPhaseKernel orig original props)
    (SchedulerConfig.init orig original props) (SupportedReach.init hent)

end LeanFzn.Solver.UIP.LcgPhaseKernel
