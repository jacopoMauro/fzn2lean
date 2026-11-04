/-
File: LeanFzn/Solver/UIP/Runtime/ScheduledDb.lean

Purpose (PLAN task K0b): the SCHEDULED DB-producing twin of the certified
scheduled driver `runSched`.  `runSchedDb` runs exactly the same recursion as
`runSched` (the scheduled dispatcher `phaseNextSched`, the `PropScheduler`
table threaded through the state) but returns, besides the verdict, the
TERMINAL `SchedulerConfig` of the run.  Its first component agrees with
`runSched` (`runSchedDb_fst`) and its terminal configuration is
supported-reachable (`runSchedDb_reach`).

Both drivers bind the scheduled prompt pair ONCE per recursive step
(`let p := phaseNextSched cfg sched`); all arms read the transition and the
next table off that single evaluation.  `solve_schedDb` is the initialized
twin of `solve_sched`, and `solve_schedDbStats` reads the terminal counters
off it, so the default stats route exercises the scheduled propagation path
(`phaseNextSched` / `promptOf`) rather than the reference dispatcher.

DAG: LcgPhaseKernelSched -> this file -> SchedulerStats.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Solver.UIP.Runtime.Scheduled

namespace LeanFzn.Solver.UIP.LcgPhaseSchedDb
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.P3 (PhaseLt phaseLt_of_inst phaseLt_wf)

variable {orig : List Domain} {original : List Clause} {props : List Propagator}
  {leaf : Assignment → Bool}

/-! ## §1 The scheduled DB-producing driver -/

/-- The scheduled driver that also returns the TERMINAL configuration (the
configuration at which the verdict was produced).  Identical recursion and
rank decrease as `runSched`, with the scheduled prompt pair bound once per
step; the verdict is its first component (`_fst`), the terminal configuration
is supported-reachable (`_reach`). -/
def runSchedDb {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : LeanFzn.Solver.Core.Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) :
    DriverResult leaf × SchedulerConfig leaf :=
  let p := phaseNextSched cfg sched
  match hstep : p.1 with
  | .sat w => (.sat w, cfg)
  | .unsat => (.unsat, cfg)
  | .propagate n =>
      runSchedDb k hloc n p.2
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
      runSchedDb k hloc n p.2
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
      runSchedDb k hloc n p.2
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
      runSchedDb k hloc n p.2
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
      runSchedDb k hloc n p.2
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
      runSchedDb k hloc n p.2
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

/-- The scheduled successor decreases the kernel rank (the kernel decrease
transported through the scheduled dispatcher's first projection). -/
theorem phaseNextSched_decrease (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) {cfg cfg' : SchedulerConfig leaf} {sched : PropScheduler}
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched)
    (hsucc : (phaseNextSched cfg sched).1.successor = some cfg') :
    PhaseLt (k.rank cfg') (k.rank cfg) :=
  k.decrease cfg cfg' hreach (by
    have hs : (k.step cfg).successor = some cfg' := by
      rw [k.step_eq cfg hreach,
        ← phaseNextSched_fst_eq (cfg := cfg) (sched := sched)
          (SupportedReach.cacheAligned hreach)
          (hok.of_props_eq (SupportedReach.props_eq hreach))
          (hloc.of_props_eq (SupportedReach.props_eq hreach))]
      exact hsucc
    exact hs)

/-! ## §2 Equation lemmas for the arms -/

/-- The driver is proof-irrelevant in its reachability and table witnesses. -/
theorem runSchedDb_congr (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (p1 p2 : SupportedReach orig original props cfg)
    (q1 q2 : PropSchedulerOK props sched) :
    runSchedDb k hloc cfg sched p1 q1 = runSchedDb k hloc cfg sched p2 q2 := by
  rw [Subsingleton.elim p1 p2, Subsingleton.elim q1 q2]

/-- Equation lemma, terminal `.sat` arm. -/
theorem runSchedDb_sat (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (w : Assignment)
    (h : (phaseNextSched cfg sched).1 = .sat w) :
    runSchedDb k hloc cfg sched hreach hok = (.sat w, cfg) := by
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-- Equation lemma, terminal `.unsat` arm. -/
theorem runSchedDb_unsat (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched)
    (h : (phaseNextSched cfg sched).1 = .unsat) :
    runSchedDb k hloc cfg sched hreach hok = (.unsat, cfg) := by
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-- Equation lemma, `.propagate` arm. -/
theorem runSchedDb_propagate (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (h : (phaseNextSched cfg sched).1 = .propagate n) :
    runSchedDb k hloc cfg sched hreach hok
      = runSchedDb k hloc n (phaseNextSched cfg sched).2
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
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-- Equation lemma, `.decide` arm. -/
theorem runSchedDb_decide (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf) (l : Literal)
    (h : (phaseNextSched cfg sched).1 = .decide n l) :
    runSchedDb k hloc cfg sched hreach hok
      = runSchedDb k hloc n (phaseNextSched cfg sched).2
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
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-- Equation lemma, `.analyzeConflict` arm. -/
theorem runSchedDb_analyzeConflict (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf) (c : Clause)
    (h : (phaseNextSched cfg sched).1 = .analyzeConflict n c) :
    runSchedDb k hloc cfg sched hreach hok
      = runSchedDb k hloc n (phaseNextSched cfg sched).2
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
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-- Equation lemma, `.learnBackjumpAssert` arm. -/
theorem runSchedDb_learnBackjumpAssert (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (an : ConflictAnalysis)
    (h : (phaseNextSched cfg sched).1 = .learnBackjumpAssert n p an) :
    runSchedDb k hloc cfg sched hreach hok
      = runSchedDb k hloc n (phaseNextSched cfg sched).2
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
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-- Equation lemma, `.localExclude` arm. -/
theorem runSchedDb_localExclude (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (h : (phaseNextSched cfg sched).1 = .localExclude n) :
    runSchedDb k hloc cfg sched hreach hok
      = runSchedDb k hloc n (phaseNextSched cfg sched).2
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
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-- Equation lemma, `.chronologicalFallback` arm. -/
theorem runSchedDb_chronologicalFallback (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) (n : SchedulerConfig leaf)
    (h : (phaseNextSched cfg sched).1 = .chronologicalFallback n) :
    runSchedDb k hloc cfg sched hreach hok
      = runSchedDb k hloc n (phaseNextSched cfg sched).2
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
  rw [runSchedDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSchedDb_congr k hloc cfg sched _ _ _ _)

/-! ## §3 Verdict and terminal-reachability -/

/-- **VERDICT AGREEMENT**: the scheduled DB-producing driver returns the
verdict of the scheduled driver on the same kernel, configuration and table. -/
theorem runSchedDb_fst (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) :
    (runSchedDb k hloc cfg sched hreach hok).1
      = runSched k hloc cfg sched hreach hok := by
  have main : ∀ (c : SchedulerConfig leaf) (s : PropScheduler)
      (hc : SupportedReach orig original props c) (ho : PropSchedulerOK props s),
      (runSchedDb k hloc c s hc ho).1 = runSched k hloc c s hc ho := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => ∀ (s : PropScheduler)
        (hc : SupportedReach orig original props c) (ho : PropSchedulerOK props s),
        (runSchedDb k hloc c s hc ho).1 = runSched k hloc c s hc ho) ?_
    intro c ih s hc ho
    cases hstep : (phaseNextSched c s).1 with
    | sat w =>
        rw [runSchedDb_sat k hloc c s hc ho w hstep,
          runSched_sat k hloc c s hc ho w hstep]
    | unsat =>
        rw [runSchedDb_unsat k hloc c s hc ho hstep,
          runSched_unsat k hloc c s hc ho hstep]
    | propagate n =>
        rw [runSchedDb_propagate k hloc c s hc ho n hstep,
          runSched_propagate k hloc c s hc ho n hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | decide n l =>
        rw [runSchedDb_decide k hloc c s hc ho n l hstep,
          runSched_decide k hloc c s hc ho n l hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | analyzeConflict n c' =>
        rw [runSchedDb_analyzeConflict k hloc c s hc ho n c' hstep,
          runSched_analyzeConflict k hloc c s hc ho n c' hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | learnBackjumpAssert n l st =>
        rw [runSchedDb_learnBackjumpAssert k hloc c s hc ho n l st hstep,
          runSched_learnBackjumpAssert k hloc c s hc ho n l st hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | localExclude n =>
        rw [runSchedDb_localExclude k hloc c s hc ho n hstep,
          runSched_localExclude k hloc c s hc ho n hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | chronologicalFallback n =>
        rw [runSchedDb_chronologicalFallback k hloc c s hc ho n hstep,
          runSched_chronologicalFallback k hloc c s hc ho n hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
  exact main cfg sched hreach hok

/-- **TERMINAL SUPPORTED-REACHABILITY**: the returned terminal configuration is
supported-reachable from the same initializer. -/
theorem runSchedDb_reach (k : SupportedPhaseKernel orig original props leaf)
    (hloc : PropLocal props) (cfg : SchedulerConfig leaf) (sched : PropScheduler)
    (hreach : SupportedReach orig original props cfg)
    (hok : PropSchedulerOK props sched) :
    SupportedReach orig original props (runSchedDb k hloc cfg sched hreach hok).2 := by
  have main : ∀ (c : SchedulerConfig leaf) (s : PropScheduler)
      (hc : SupportedReach orig original props c) (ho : PropSchedulerOK props s),
      SupportedReach orig original props (runSchedDb k hloc c s hc ho).2 := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => ∀ (s : PropScheduler)
        (hc : SupportedReach orig original props c) (ho : PropSchedulerOK props s),
        SupportedReach orig original props (runSchedDb k hloc c s hc ho).2) ?_
    intro c ih s hc ho
    cases hstep : (phaseNextSched c s).1 with
    | sat w =>
        rw [runSchedDb_sat k hloc c s hc ho w hstep]
        exact hc
    | unsat =>
        rw [runSchedDb_unsat k hloc c s hc ho hstep]
        exact hc
    | propagate n =>
        rw [runSchedDb_propagate k hloc c s hc ho n hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | decide n l =>
        rw [runSchedDb_decide k hloc c s hc ho n l hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | analyzeConflict n c' =>
        rw [runSchedDb_analyzeConflict k hloc c s hc ho n c' hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | learnBackjumpAssert n l st =>
        rw [runSchedDb_learnBackjumpAssert k hloc c s hc ho n l st hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | localExclude n =>
        rw [runSchedDb_localExclude k hloc c s hc ho n hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
    | chronologicalFallback n =>
        rw [runSchedDb_chronologicalFallback k hloc c s hc ho n hstep]
        exact ih n (phaseNextSched_decrease k hloc hc ho (by rw [hstep]; rfl))
          (phaseNextSched c s).2 _ _
  exact main cfg sched hreach hok

/-! ## §4 The initialized scheduled DB entry and its stats pair -/

/-- The initialized scheduled DB-producing entry: the same initializer and
kernel as `solve_sched`, additionally returning the terminal configuration. -/
def solve_schedDb {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original)
    (sched : PropScheduler) (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult leaf × SchedulerConfig leaf :=
  runSchedDb (LeanFzn.Solver.UIP.LcgPhaseKernel.supportedPhaseKernel orig original props hgate)
    hloc (SchedulerConfig.init orig original props prio actBump) sched
    (SupportedReach.init hent) hok

/-- **VERDICT AGREEMENT WITH `solve_sched`**. -/
theorem solve_schedDb_fst {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) (sched : PropScheduler)
    (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solve_schedDb orig original props hent sched hloc hok hgate prio actBump).1
      = solve_sched orig original props hent sched hloc hok hgate prio actBump :=
  runSchedDb_fst _ _ _ _ _ _

/-- Stats pair of the scheduled DB entry: the verdict together with the
terminal work counters of the identical scheduled run. -/
def solve_schedDbStats {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) (sched : PropScheduler)
    (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult leaf × SearchStats :=
  let r := solve_schedDb orig original props hent sched hloc hok hgate prio actBump
  (r.1, r.2.stats)

/-- **THE INSTRUMENTED SCHEDULED ENTRY DECIDES EXACTLY `solve_sched`**. -/
theorem solve_schedDbStats_fst {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) (sched : PropScheduler)
    (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solve_schedDbStats orig original props hent sched hloc hok hgate prio actBump).1
      = solve_sched orig original props hent sched hloc hok hgate prio actBump := by
  simpa only [solve_schedDbStats] using
    solve_schedDb_fst (leaf := leaf) orig original props hent sched hloc hok hgate prio actBump

/-- **THE TERMINAL COUNTER RECORD (scheduled route)**: the second component is
the stats field of the terminal configuration of the scheduled DB run. -/
theorem solve_schedDbStats_snd {leaf : Assignment → Bool} (orig : List Domain)
    (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original) (sched : PropScheduler)
    (hloc : PropLocal props) (hok : PropSchedulerOK props sched)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solve_schedDbStats orig original props hent sched hloc hok hgate prio actBump).2
      = (runSchedDb
          (LeanFzn.Solver.UIP.LcgPhaseKernel.supportedPhaseKernel orig original props hgate)
          hloc (SchedulerConfig.init orig original props prio actBump) sched
          (SupportedReach.init hent) hok).2.stats :=
  rfl

end LeanFzn.Solver.UIP.LcgPhaseSchedDb
