/-
File: LeanFzn/Solver/UIP/Proofs/LcgPhaseKernelSched.lean

Purpose (PLAN task P1): the SCHEDULED certified driver. `runSched` is the
well-founded driver of `SupportedPhaseRun.runSupportedPhase` with the
scheduled phase dispatcher `phaseNextSched` and the `PropScheduler` table
threaded through its state; `runSched_eq_runSupportedPhase` proves it equals
the certified driver under the table invariant and the concrete locality
discharge, so the certified LCG theorems transfer to the scheduled run.

DAG: SchedulerStepSched + LcgPhaseKernel -> this file -> Integration.Lcg.
-/
import LeanFzn.Solver.UIP.Proofs.SchedulerStepSched
import LeanFzn.Solver.UIP.Proofs.LcgPhaseKernel
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering


namespace LeanFzn.Solver.UIP
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.P3 (phaseLt_of_inst)
open LeanFzn.Solver.UIP.C3b

/-- **THE SCHEDULED DRIVER**: the certified kernel's well-founded recursion
with the scheduled dispatcher; the `PropScheduler` table is threaded through
the recursion (its consistency proof `hok` is erased, the table itself is
live). -/
def runSched {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : LeanFzn.Solver.Core.Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) : DriverResult leaf :=
  match hstep : (phaseNextSched cfg sched).1 with
  | .sat w => .sat w
  | .unsat => .unsat
  | .propagate n =>
      runSched k hloc n (phaseNextSched cfg sched).2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .propagate n := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .decide n l =>
      runSched k hloc n (phaseNextSched cfg sched).2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .decide n l := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .analyzeConflict n c =>
      runSched k hloc n (phaseNextSched cfg sched).2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .analyzeConflict n c := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .learnBackjumpAssert n l st =>
      runSched k hloc n (phaseNextSched cfg sched).2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .learnBackjumpAssert n l st := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .localExclude n =>
      runSched k hloc n (phaseNextSched cfg sched).2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .localExclude n := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .chronologicalFallback n =>
      runSched k hloc n (phaseNextSched cfg sched).2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .chronologicalFallback n := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
termination_by k.rank cfg
decreasing_by
  all_goals
    have hs : (k.step cfg).successor = some n := by
      rw [k.step_eq cfg hreach,
        ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
          (hok.of_props_eq (SupportedReach.props_eq hreach))
          (hloc.of_props_eq (SupportedReach.props_eq hreach))]
      rw [hstep]
      simp
    exact phaseLt_of_inst (k.decrease cfg n hreach hs)

/-- The certified step at a reachable configuration is the scheduled one's
successor class. -/
theorem runSched_eq_runSupportedPhase {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) :
    runSched k hloc cfg sched hreach hok = runSupportedPhase k cfg hreach := by
  induction cfg, sched, hreach, hok using runSched.induct k hloc with
  | case1 cfg sched hreach hok w hstep =>
      have hk : k.step cfg = .sat w := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_sat k cfg hreach w hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first | rfl)
  | case2 cfg sched hreach hok hstep =>
      have hk : k.step cfg = .unsat := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_unsat k cfg hreach hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first | rfl)
  | case3 cfg sched hreach hok n hstep ih =>
      have hk : k.step cfg = .propagate n := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_propagate k cfg hreach n hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first
            | rfl
            | exact ih.trans (runSupportedPhase_reach_congr k n _ _))
  | case4 cfg sched hreach hok n l hstep ih =>
      have hk : k.step cfg = .decide n l := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_decide k cfg hreach n l hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first
            | rfl
            | exact ih.trans (runSupportedPhase_reach_congr k n _ _))
  | case5 cfg sched hreach hok n c hstep ih =>
      have hk : k.step cfg = .analyzeConflict n c := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_analyzeConflict k cfg hreach n c hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first
            | rfl
            | exact ih.trans (runSupportedPhase_reach_congr k n _ _))
  | case6 cfg sched hreach hok n l st hstep ih =>
      have hk : k.step cfg = .learnBackjumpAssert n l st := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_learnBackjumpAssert k cfg hreach n l st hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first
            | rfl
            | exact ih.trans (runSupportedPhase_reach_congr k n _ _))
  | case7 cfg sched hreach hok n hstep ih =>
      have hk : k.step cfg = .localExclude n := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_localExclude k cfg hreach n hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first
            | rfl
            | exact ih.trans (runSupportedPhase_reach_congr k n _ _))
  | case8 cfg sched hreach hok n hstep ih =>
      have hk : k.step cfg = .chronologicalFallback n := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_chronologicalFallback k cfg hreach n hk]
      unfold runSched
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> first
            | rfl
            | exact ih.trans (runSupportedPhase_reach_congr k n _ _))

/-! ## The initialized scheduled entry -/

/-- The fuel-free initialized scheduled entry: `LcgPhaseKernel.solve` with the
scheduled dispatcher over a scheduler table (`hloc` is the concrete locality
discharge of the propagator list, `hok` the table's consistency). -/
def solve_sched {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original)
    (sched : PropScheduler) (hloc : PropLocal props) (hok : PropSchedulerOK props sched) :
    DriverResult leaf :=
  runSched (LcgPhaseKernel.supportedPhaseKernel orig original props) hloc
    (SchedulerConfig.init orig original props) sched (SupportedReach.init hent) hok

/-- **VERDICT EQUALITY**: the scheduled entry's verdict is exactly the
certified kernel's verdict, so every certified LCG consumer transfers to the
scheduled route unchanged (no re-proved semantics). -/
theorem solve_sched_eq {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original)
    (sched : PropScheduler) (hloc : PropLocal props) (hok : PropSchedulerOK props sched) :
    solve_sched orig original props hent sched hloc hok
      = LcgPhaseKernel.solve orig original props hent :=
  runSched_eq_runSupportedPhase _ _ _ _ _ _

/-- The scheduled entry reports `.sat w` only where the certified kernel does. -/
theorem solve_sched_sat {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {hent : LearnedEntailed leaf original} {sched : PropScheduler}
    {hloc : PropLocal props} {hok : PropSchedulerOK props sched} {w : Assignment}
    (h : solve_sched orig original props hent sched hloc hok = .sat w) :
    LcgPhaseKernel.solve orig original props hent = .sat w :=
  (solve_sched_eq orig original props hent sched hloc hok) ▸ h

/-- The scheduled entry reports `.unsat` only where the certified kernel does. -/
theorem solve_sched_unsat {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {hent : LearnedEntailed leaf original} {sched : PropScheduler}
    {hloc : PropLocal props} {hok : PropSchedulerOK props sched}
    (h : solve_sched orig original props hent sched hloc hok = .unsat) :
    LcgPhaseKernel.solve orig original props hent = .unsat :=
  (solve_sched_eq orig original props hent sched hloc hok) ▸ h

end LeanFzn.Solver.UIP
