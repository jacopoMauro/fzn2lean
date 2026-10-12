/-
File: LeanFzn/Solver/UIP/Scheduler.lean

Purpose:
  The PUBLIC entry point of the fuel-free scheduler driver. It re-exports the
  well-founded recursion core from `Proofs/Scheduler.lean`, instantiated with
  the PHASE-AWARE kernel `phaseKernel` (step = `phaseNext`, which composes each
  stutter arm with its FORCED real successor). NO fuel parameter, NO `partial`,
  NO `decide`/`native_decide`; `noncomputable` only because `WellFounded.fix`
  is.

  The single named premise is `PhaseProgress` (owner C3b/integration). Its
  two forced-consume sites are PROVED in `Proofs/Scheduler.lean`
  (`phase_localExclude_succ`, `phase_fallback_succ`, via C3a's composites
  `arm_localExclude_then_consume` / `arm_fallback_then_consume`); the residual
  content is the `.analyzeConflict` phase advancing onto the jump/fallback arms
  (the jump arm being the OPEN `JumpDecrease`).

  NOT REACHED here (honest): O1 event wiring (`AnalysisEvents`) and the T1
  oracle comparison. No fabricated counters are introduced by this module.

DAG: Proofs.Scheduler (C3b) -> this module.

X2 ADDENDUM (PLAN.md task X2): the COMPUTABLE fuel-free driver
`X2.runPhase` over P5's reachable-progress obligation, compiled with
`termination_by P3.PhaseRank` + `decreasing_by` (X1's proof-erased
pattern), with equation-level lemmas, agreement with P5's `runReachable`,
and the event-returning terminal-config variant. The reachability
witness is an ERASED proof argument; the only runtime data is the kernel's
`step` and the computed rank.
-/

import LeanFzn.Solver.UIP.Proofs.Scheduler
import LeanFzn.Solver.UIP.Proofs.SchedulerPhaseProgress
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.C3b
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
/-- The fuel-free phase-aware driver: `WellFounded.fix` over C3a's
`schedulerRank_wf`, stepping by the REAL phase dispatcher `phaseNext`
(stutter arms composed with their forced successors). -/
noncomputable def schedulerRun (h : PhaseProgress leaf)
    (cfg : SchedulerConfig leaf) : DriverResult leaf :=
  runSchedulerPhase h cfg

/-- TOTALITY of the public driver: for every phase obligation and every
configuration a result exists — no fuel. -/
theorem schedulerRun_total (h : PhaseProgress leaf)
    (cfg : SchedulerConfig leaf) :
    ∃ r : DriverResult leaf, schedulerRun h cfg = r :=
  ⟨schedulerRun h cfg, rfl⟩

/-- The public driver over the NAIVE (refuted) obligation, kept so the
refutation record is consumable from this module too. -/
noncomputable def schedulerRunNaive (h : DispatcherProgressNaive leaf)
    (cfg : SchedulerConfig leaf) : DriverResult leaf :=
  runScheduler h cfg

end LeanFzn.Solver.UIP.C3b
namespace LeanFzn.Solver.UIP.X2
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.P3 (PhaseRank PhaseLt phaseLt_of_inst)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.P5 (ReachablePhaseKernel ReachablePhaseProgressSelf
  ReachablePhaseProgressSorted reachablePhaseKernel reachablePhaseKernelSorted
  runReachable)

/-! ## §1 The COMPUTABLE fuel-free driver (X1 pattern)

`runPhase` is a plain `def` — NOT `noncomputable`, NOT `partial`, NO fuel.
It recurses on P5's `ReachablePhaseKernel`: an erased proof kernel carrying
the real phase dispatcher `step`, its reachability closure `reach`, its
agreement `step_eq`, and the ranked decrease `decrease`. The compile-time
decrease proof `decreasing_by` consumes the kernel's `decrease` field
(P5 §4); at runtime every proof field is erased by proof irrelevance, so
the compiled loop evaluates `step` alone, exactly as X1's prototype. -/

/-- **THE COMPUTABLE FULL DRIVER**: well-founded recursion on the kernel's
rank FUNCTION (a kernel field since C2/G1 — the historical self rank or the
sorted self rank), following X1's exact `termination_by` +
`decreasing_by` style. The reachability witness `hreach` and the kernel's
proof fields are erased arguments: the runtime carries no proofs. -/
def runPhase {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf) (cfg : SchedulerConfig leaf)
    (hreach : SchedulerReachable cfg) : DriverResult leaf :=
  match hstep : k.step cfg with
  | .sat w => .sat w
  | .unsat => .unsat
  | .propagate n => runPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .decide n _ => runPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .analyzeConflict n _ => runPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .learnBackjumpAssert n _ _ => runPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .localExclude n => runPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .chronologicalFallback n => runPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
termination_by k.rank cfg
decreasing_by
  all_goals exact phaseLt_of_inst (k.decrease cfg n hreach (by rw [hstep]; rfl))

/-- The P5-signature entry point (historical ranked instance): the driver
over the reachable-progress theorem `h` plus the reachability-closure field
P5's kernel names (owner S5/W1), glued through P5's own
`reachablePhaseKernel` (whose rank is the configuration's SELF P3 rank). -/
def runPhaseFrom {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSelf (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg')
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg) :
    DriverResult leaf :=
  runPhase (reachablePhaseKernel h hclos) cfg hreach

/-- The SORTED instance entry (C2): the same computable driver over the
kernel built from the order-insensitive obligation. -/
def runPhaseFromSorted {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSorted (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg')
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg) :
    DriverResult leaf :=
  runPhase (reachablePhaseKernelSorted h hclos) cfg hreach

/-- The driver is insensitive to the (erased) reachability proof argument. -/
theorem runPhase_reach_congr (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (p1 p2 : SchedulerReachable cfg) :
    runPhase k cfg p1 = runPhase k cfg p2 :=
  congrArg (runPhase k cfg) (Subsingleton.elim p1 p2)

/-- P5's `runReachable` is insensitive to the (erased) reachability proof. -/
theorem runReachable_reach_congr (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (p1 p2 : SchedulerReachable cfg) :
    runReachable k cfg p1 = runReachable k cfg p2 :=
  congrArg (runReachable k cfg) (Subsingleton.elim p1 p2)

/-- The kernel built by P5's `reachablePhaseKernel` steps by the REAL
`C3b.phaseNext` (its `step_eq` field is definitionally `rfl`). -/
theorem reachablePhaseKernel_step {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSelf (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg') :
    (reachablePhaseKernel h hclos).step = phaseNext := rfl

/-- The sorted kernel's step is the REAL `C3b.phaseNext` as well. -/
theorem reachablePhaseKernelSorted_step {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSorted (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg') :
    (reachablePhaseKernelSorted h hclos).step = phaseNext := rfl

/-- **FULL AGREEMENT with P5's `runReachable`**: the compiled driver and the
verified well-founded driver return the same result on every reachable
configuration, by functional induction on `runPhase.induct` — the two
recursions consume the same `k.step` match and the same successor facts
(the `WellFounded.fix_eq` unfolding of `runReachable` is matched arm by
arm). Together with `reachablePhaseKernel_step` this is equation-level and
result-level agreement with both P5's driver and the real `phaseNext`. -/
theorem runPhase_eq_runReachable (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg) :
    runPhase k cfg hreach = runReachable k cfg hreach := by
  fun_induction runPhase k cfg hreach with
  | case1 cfg hreach w hstep =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> rfl)
  | case2 cfg hreach hstep =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;> first
        | rfl
        | (cases heq.symm.trans hstep <;> rfl)
  | case3 cfg hreach n hstep ih =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;>
        (cases heq.symm.trans hstep <;> first
          | rfl
          | exact (runPhase_reach_congr k _ _ _).trans
              (ih.trans (runReachable_reach_congr k _ _ _)))
  | case4 cfg hreach n decision hstep ih =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;>
        (cases heq.symm.trans hstep <;> first
          | rfl
          | exact (runPhase_reach_congr k _ _ _).trans
              (ih.trans (runReachable_reach_congr k _ _ _)))
  | case5 cfg hreach n conflict hstep ih =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;>
        (cases heq.symm.trans hstep <;> first
          | rfl
          | exact (runPhase_reach_congr k _ _ _).trans
              (ih.trans (runReachable_reach_congr k _ _ _)))
  | case6 cfg hreach n plan analysis hstep ih =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;>
        (cases heq.symm.trans hstep <;> first
          | rfl
          | exact (runPhase_reach_congr k _ _ _).trans
              (ih.trans (runReachable_reach_congr k _ _ _)))
  | case7 cfg hreach n hstep ih =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;>
        (cases heq.symm.trans hstep <;> first
          | rfl
          | exact (runPhase_reach_congr k _ _ _).trans
              (ih.trans (runReachable_reach_congr k _ _ _)))
  | case8 cfg hreach n hstep ih =>
      rw [runReachable, WellFounded.fix_eq]
      split <;> rename_i heq <;>
        (cases heq.symm.trans hstep <;> first
          | rfl
          | exact (runPhase_reach_congr k _ _ _).trans
              (ih.trans (runReachable_reach_congr k _ _ _)))

/-! ## §2 Equation-level lemmas for the compiled driver

Per-constructor unfolding lemmas: they are literally the recursion
equations of P5's `runReachable` (compare `runReachable`'s `WellFounded.fix`
body), and they invoke the REAL `C3b.phaseNext` because the kernel is
`reachablePhaseKernel` (`step_eq := fun _ _ => rfl`). -/

/-- Terminal arm: a recorded SAT witness is the result. -/
theorem runPhase_sat (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (w : Assignment) (h : k.step cfg = .sat w) :
    runPhase k cfg hreach = .sat w := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

/-- Terminal arm: exhaustion (or a root contradiction) is the result. -/
theorem runPhase_unsat (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (h : k.step cfg = .unsat) :
    runPhase k cfg hreach = .unsat := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

theorem runPhase_propagate (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .propagate n) :
    runPhase k cfg hreach
      = runPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

theorem runPhase_decide (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (n : SchedulerConfig leaf) (l : Literal) (h : k.step cfg = .decide n l) :
    runPhase k cfg hreach
      = runPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

theorem runPhase_analyzeConflict (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (n : SchedulerConfig leaf) (c : Clause)
    (h : k.step cfg = .analyzeConflict n c) :
    runPhase k cfg hreach
      = runPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

theorem runPhase_learnBackjumpAssert (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (n : SchedulerConfig leaf) (p : BackjumpPlan leaf) (an : ConflictAnalysis)
    (h : k.step cfg = .learnBackjumpAssert n p an) :
    runPhase k cfg hreach
      = runPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

theorem runPhase_localExclude (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .localExclude n) :
    runPhase k cfg hreach
      = runPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

theorem runPhase_chronologicalFallback (k : ReachablePhaseKernel leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .chronologicalFallback n) :
    runPhase k cfg hreach
      = runPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl | exact runPhase_reach_congr k _ _ _)

/-! ## §3 The event-returning variant

`runPhaseConfig` returns the TERMINAL configuration; `runPhaseEvents`
projects its `RuntimeEvents` (O1's counted accumulators) alongside the
verdict. Same computable recursion, same erased kernel. -/

def runPhaseConfig {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf) (cfg : SchedulerConfig leaf)
    (hreach : SchedulerReachable cfg) : SchedulerConfig leaf :=
  match hstep : k.step cfg with
  | .sat _ => cfg
  | .unsat => cfg
  | .propagate n => runPhaseConfig k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .decide n _ => runPhaseConfig k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .analyzeConflict n _ => runPhaseConfig k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .learnBackjumpAssert n _ _ => runPhaseConfig k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .localExclude n => runPhaseConfig k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .chronologicalFallback n => runPhaseConfig k n (k.reach cfg n hreach (by rw [hstep]; rfl))
termination_by k.rank cfg
decreasing_by
  all_goals exact phaseLt_of_inst (k.decrease cfg n hreach (by rw [hstep]; rfl))

/-- The verdict together with the terminal configuration's runtime events. -/
def runPhaseEvents {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf) (cfg : SchedulerConfig leaf)
    (hreach : SchedulerReachable cfg) : DriverResult leaf × RuntimeEvents :=
  let c := runPhaseConfig k cfg hreach
  (runPhase k cfg hreach, c.events)

end LeanFzn.Solver.UIP.X2
