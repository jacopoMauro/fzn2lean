/-
File: LeanFzn/Solver/UIP/Runtime/Scheduled.lean

Purpose (PLAN task P1): the SCHEDULED certified driver. `runSched` is the
well-founded driver of `SupportedPhaseRun.runSupportedPhase` with the
scheduled phase dispatcher `phaseNextSched` and the `PropScheduler` table
threaded through its state; `runSched_eq_runSupportedPhase` proves it equals
the certified driver under the table invariant and the concrete locality
discharge, so the certified LCG theorems transfer to the scheduled run.

DAG: SchedulerStepSched + LcgPhaseKernel -> this file -> Integration.Lcg.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStepSched
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseKernel
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
  let p := phaseNextSched cfg sched
  match hstep : p.1 with
  | .sat w => .sat w
  | .unsat => .unsat
  | .propagate n =>
      runSched k hloc n p.2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .propagate n := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (SupportedReach.cacheAligned hreach)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .decide n l =>
      runSched k hloc n p.2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .decide n l := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (SupportedReach.cacheAligned hreach)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .analyzeConflict n c =>
      runSched k hloc n p.2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .analyzeConflict n c := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (SupportedReach.cacheAligned hreach)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .learnBackjumpAssert n l st =>
      runSched k hloc n p.2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .learnBackjumpAssert n l st := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (SupportedReach.cacheAligned hreach)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .localExclude n =>
      runSched k hloc n p.2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .localExclude n := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (SupportedReach.cacheAligned hreach)
                (hok.of_props_eq (SupportedReach.props_eq hreach))
                (hloc.of_props_eq (SupportedReach.props_eq hreach))]
            exact hstep
          rw [ht]; simp))
        ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
          (SupportedReach.props_eq hreach).symm)
  | .chronologicalFallback n =>
      runSched k hloc n p.2
        (k.reach cfg n hreach (by
          have ht : k.step cfg = .chronologicalFallback n := by
            rw [k.step_eq cfg hreach,
              ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                (SupportedReach.cacheAligned hreach)
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
          (SupportedReach.cacheAligned hreach)
          (hok.of_props_eq (SupportedReach.props_eq hreach))
          (hloc.of_props_eq (SupportedReach.props_eq hreach))]
      have hp : p = phaseNextSched cfg sched := rfl
      rw [hp] at hstep
      rw [hstep]
      simp
    exact phaseLt_of_inst (k.decrease cfg n hreach hs)

/-! ## Equation lemmas for the scheduled driver

The driver binds the scheduled prompt pair ONCE per step (`let p :=
phaseNextSched cfg sched`); these lemmas expose each arm at an explicit
prompt transition, with the same successor-reachability and table-consistency
proofs the definition uses.  They are the seam for `runSchedDb_fst` below and
for the single-binding comparison with the old recursion. -/

/-- The driver is proof-irrelevant in its reachability and table witnesses. -/
theorem runSched_congr {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (p1 p2 : SupportedReach orig original props cfg)
    (q1 q2 : PropSchedulerOK props sched) :
    runSched k hloc cfg sched p1 q1 = runSched k hloc cfg sched p2 q2 := by
  rw [Subsingleton.elim p1 p2, Subsingleton.elim q1 q2]

theorem runSched_sat {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (w : Assignment)
    (h : (phaseNextSched cfg sched).1 = .sat w) :
    runSched k hloc cfg sched hreach hok = .sat w := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

theorem runSched_unsat {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched)
    (h : (phaseNextSched cfg sched).1 = .unsat) :
    runSched k hloc cfg sched hreach hok = .unsat := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

theorem runSched_propagate {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (h : (phaseNextSched cfg sched).1 = .propagate n) :
    runSched k hloc cfg sched hreach hok
      = runSched k hloc n (phaseNextSched cfg sched).2
          (k.reach cfg n hreach (by
            have ht : k.step cfg = .propagate n := by
              rw [k.step_eq cfg hreach,
                ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                  (SupportedReach.cacheAligned hreach)
                  (hok.of_props_eq (SupportedReach.props_eq hreach))
                  (hloc.of_props_eq (SupportedReach.props_eq hreach))]
              exact h
            rw [ht]; simp))
          ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
              (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
            (SupportedReach.props_eq hreach).symm) := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

theorem runSched_decide {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf) (l : Literal)
    (h : (phaseNextSched cfg sched).1 = .decide n l) :
    runSched k hloc cfg sched hreach hok
      = runSched k hloc n (phaseNextSched cfg sched).2
          (k.reach cfg n hreach (by
            have ht : k.step cfg = .decide n l := by
              rw [k.step_eq cfg hreach,
                ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                  (SupportedReach.cacheAligned hreach)
                  (hok.of_props_eq (SupportedReach.props_eq hreach))
                  (hloc.of_props_eq (SupportedReach.props_eq hreach))]
              exact h
            rw [ht]; simp))
          ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
              (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
            (SupportedReach.props_eq hreach).symm) := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

theorem runSched_analyzeConflict {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf) (c : Clause)
    (h : (phaseNextSched cfg sched).1 = .analyzeConflict n c) :
    runSched k hloc cfg sched hreach hok
      = runSched k hloc n (phaseNextSched cfg sched).2
          (k.reach cfg n hreach (by
            have ht : k.step cfg = .analyzeConflict n c := by
              rw [k.step_eq cfg hreach,
                ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                  (SupportedReach.cacheAligned hreach)
                  (hok.of_props_eq (SupportedReach.props_eq hreach))
                  (hloc.of_props_eq (SupportedReach.props_eq hreach))]
              exact h
            rw [ht]; simp))
          ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
              (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
            (SupportedReach.props_eq hreach).symm) := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

theorem runSched_learnBackjumpAssert {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (an : ConflictAnalysis)
    (h : (phaseNextSched cfg sched).1 = .learnBackjumpAssert n p an) :
    runSched k hloc cfg sched hreach hok
      = runSched k hloc n (phaseNextSched cfg sched).2
          (k.reach cfg n hreach (by
            have ht : k.step cfg = .learnBackjumpAssert n p an := by
              rw [k.step_eq cfg hreach,
                ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                  (SupportedReach.cacheAligned hreach)
                  (hok.of_props_eq (SupportedReach.props_eq hreach))
                  (hloc.of_props_eq (SupportedReach.props_eq hreach))]
              exact h
            rw [ht]; simp))
          ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
              (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
            (SupportedReach.props_eq hreach).symm) := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

theorem runSched_localExclude {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (h : (phaseNextSched cfg sched).1 = .localExclude n) :
    runSched k hloc cfg sched hreach hok
      = runSched k hloc n (phaseNextSched cfg sched).2
          (k.reach cfg n hreach (by
            have ht : k.step cfg = .localExclude n := by
              rw [k.step_eq cfg hreach,
                ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                  (SupportedReach.cacheAligned hreach)
                  (hok.of_props_eq (SupportedReach.props_eq hreach))
                  (hloc.of_props_eq (SupportedReach.props_eq hreach))]
              exact h
            rw [ht]; simp))
          ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
              (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
            (SupportedReach.props_eq hreach).symm) := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

theorem runSched_chronologicalFallback {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (hloc : PropLocal props)
    (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (h : (phaseNextSched cfg sched).1 = .chronologicalFallback n) :
    runSched k hloc cfg sched hreach hok
      = runSched k hloc n (phaseNextSched cfg sched).2
          (k.reach cfg n hreach (by
            have ht : k.step cfg = .chronologicalFallback n := by
              rw [k.step_eq cfg hreach,
                ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
                  (SupportedReach.cacheAligned hreach)
                  (hok.of_props_eq (SupportedReach.props_eq hreach))
                  (hloc.of_props_eq (SupportedReach.props_eq hreach))]
              exact h
            rw [ht]; simp))
          ((phaseNextSched_OK (hok.of_props_eq (SupportedReach.props_eq hreach))
              (hloc.of_props_eq (SupportedReach.props_eq hreach))).of_props_eq
            (SupportedReach.props_eq hreach).symm) := by
  rw [runSched]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSched_congr k hloc cfg sched _ _ _ _)

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
  | case1 cfg sched hreach hok _p w hstep =>
      have hk : k.step cfg = .sat w := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_sat k cfg hreach w hk,
        runSched_sat k hloc cfg sched hreach hok w hstep]
  | case2 cfg sched hreach hok _p hstep =>
      have hk : k.step cfg = .unsat := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_unsat k cfg hreach hk,
        runSched_unsat k hloc cfg sched hreach hok hstep]
  | case3 cfg sched hreach hok _p n hstep ih =>
      have hk : k.step cfg = .propagate n := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_propagate k cfg hreach n hk,
        runSched_propagate k hloc cfg sched hreach hok n hstep]
      exact ih.trans (runSupportedPhase_reach_congr k n _ _)
  | case4 cfg sched hreach hok _p n l hstep ih =>
      have hk : k.step cfg = .decide n l := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_decide k cfg hreach n l hk,
        runSched_decide k hloc cfg sched hreach hok n l hstep]
      exact ih.trans (runSupportedPhase_reach_congr k n _ _)
  | case5 cfg sched hreach hok _p n c hstep ih =>
      have hk : k.step cfg = .analyzeConflict n c := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_analyzeConflict k cfg hreach n c hk,
        runSched_analyzeConflict k hloc cfg sched hreach hok n c hstep]
      exact ih.trans (runSupportedPhase_reach_congr k n _ _)
  | case6 cfg sched hreach hok _p n l st hstep ih =>
      have hk : k.step cfg = .learnBackjumpAssert n l st := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_learnBackjumpAssert k cfg hreach n l st hk,
        runSched_learnBackjumpAssert k hloc cfg sched hreach hok n l st hstep]
      exact ih.trans (runSupportedPhase_reach_congr k n _ _)
  | case7 cfg sched hreach hok _p n hstep ih =>
      have hk : k.step cfg = .localExclude n := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_localExclude k cfg hreach n hk,
        runSched_localExclude k hloc cfg sched hreach hok n hstep]
      exact ih.trans (runSupportedPhase_reach_congr k n _ _)
  | case8 cfg sched hreach hok _p n hstep ih =>
      have hk : k.step cfg = .chronologicalFallback n := by
        rw [k.step_eq cfg hreach,
          ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
            (SupportedReach.cacheAligned hreach)
            (hok.of_props_eq (SupportedReach.props_eq hreach))
            (hloc.of_props_eq (SupportedReach.props_eq hreach))]
        exact hstep
      rw [runSupportedPhase_chronologicalFallback k cfg hreach n hk,
        runSched_chronologicalFallback k hloc cfg sched hreach hok n hstep]
      exact ih.trans (runSupportedPhase_reach_congr k n _ _)

/-! ## The initialized scheduled entry -/

/-- The fuel-free initialized scheduled entry: `LcgPhaseKernel.solve` with the
scheduled dispatcher over a scheduler table (`hloc` is the concrete locality
discharge of the propagator list, `hok` the table's consistency). `prio` and
`actBump` are the heuristic slot-selection inputs (default: the S1 rule). -/
def solve_sched {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original)
    (sched : PropScheduler) (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult leaf :=
  runSched (LcgPhaseKernel.supportedPhaseKernel orig original props hgate) hloc
    (SchedulerConfig.init orig original props prio actBump) sched (SupportedReach.init hent) hok

/-- **VERDICT EQUALITY**: the scheduled entry's verdict is exactly the
certified kernel's verdict, so every certified LCG consumer transfers to the
scheduled route unchanged (no re-proved semantics). -/
theorem solve_sched_eq {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original)
    (sched : PropScheduler) (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    solve_sched orig original props hent sched hloc hok hgate prio actBump
      = LcgPhaseKernel.solve orig original props hent hgate prio actBump :=
  runSched_eq_runSupportedPhase _ _ _ _ _ _

/-- The scheduled entry reports `.sat w` only where the certified kernel does. -/
theorem solve_sched_sat {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {hent : LearnedEntailed leaf original} {sched : PropScheduler}
    {hloc : PropLocal props} {hok : PropSchedulerOK props sched} {w : Assignment}
    {hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg}
    {prio : List Nat} {actBump : Bool}
    (h : solve_sched orig original props hent sched hloc hok hgate prio actBump = .sat w) :
    LcgPhaseKernel.solve orig original props hent hgate prio actBump = .sat w :=
  (solve_sched_eq orig original props hent sched hloc hok hgate prio actBump) ▸ h

/-- The scheduled entry reports `.unsat` only where the certified kernel does. -/
theorem solve_sched_unsat {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {hent : LearnedEntailed leaf original} {sched : PropScheduler}
    {hloc : PropLocal props} {hok : PropSchedulerOK props sched}
    {hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg}
    {prio : List Nat} {actBump : Bool}
    (h : solve_sched orig original props hent sched hloc hok hgate prio actBump = .unsat) :
    LcgPhaseKernel.solve orig original props hent hgate prio actBump = .unsat :=
  (solve_sched_eq orig original props hent sched hloc hok hgate prio actBump) ▸ h

end LeanFzn.Solver.UIP
