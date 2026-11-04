/-
Purpose: fuel-free observation of the exact supported phase kernel, with a
proved verdict projection equal to the production supported driver.
Dependencies: LcgPhaseKernel supplies the kernel, rank, and driver equations.
DAG: LcgPhaseKernel -> this optional observer -> integration regression tests.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseKernel

namespace LeanFzn.Solver.UIP.LcgPhaseObserved
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.UIP.X2 LeanFzn.Solver.UIP.P3

structure Observations where
  events : RuntimeEvents := {}
  maxResolutions : Nat := 0
  nonunitLearned : Nat := 0
  skippedJumps : Nat := 0
  assertionPropagation : Nat := 0
  deriving Repr

/-- Read actual transition differences. The assertion-propagation count
requires a nonunit learned clause and the performed jump's final frame to
differ from its restored, asserted, synchronized frame, so synchronization
alone cannot pass it. The closure runs inside the performed jump. -/
def record {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (t : SchedulerTransition leaf) (o : Observations) : Observations :=
  let o := match t.successor with
    | some n => { o with maxResolutions := max o.maxResolutions (n.events.reasonResolutions - cfg.events.reasonResolutions) }
    | none => o
  match t with
  | .learnBackjumpAssert n plan an =>
      { o with
        nonunitLearned := o.nonunitLearned + (if an.learned.length > 1 then 1 else 0)
        skippedJumps := o.skippedJumps + (if cfg.branch.level > an.backjumpLevel + 1 then 1 else 0)
        assertionPropagation := o.assertionPropagation +
          (if an.learned.length > 1 && (match plan.restoreNarrow cfg.branch with
            | some s => n.branch.frame != (syncAll cfg.orig s).frame
            | none => false) then 1 else 0) }
  | _ => o

def run {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (cfg : SchedulerConfig leaf)
    (hr : SupportedReach orig original props cfg) : DriverResult leaf × Observations :=
  match hs : k.step cfg with
  | .sat w => (.sat w, { events := cfg.events })
  | .unsat => (.unsat, { events := cfg.events })
  | .propagate n | .decide n _ | .analyzeConflict n _ |
    .learnBackjumpAssert n _ _ | .localExclude n | .chronologicalFallback n =>
      let r := run k n (k.reach cfg n hr (by rw [hs]; rfl))
      (r.1, record cfg (k.step cfg) r.2)
termination_by k.rank cfg
decreasing_by
  all_goals exact phaseLt_of_inst (k.decrease cfg n hr (by rw [hs]; rfl))

theorem run_fst {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (cfg : SchedulerConfig leaf)
    (hr : SupportedReach orig original props cfg) :
    (run k cfg hr).1 = runSupportedPhase k cfg hr := by
  rw [run, runSupportedPhase]
  split <;> rename_i hs
  all_goals split <;> rename_i ht
  all_goals first
    | (cases hs.symm.trans ht <;> rfl)
    | (cases hs.symm.trans ht <;> exact run_fst k _ _)

termination_by k.rank cfg
decreasing_by
  all_goals apply phaseLt_of_inst; apply k.decrease cfg _ hr; simp_all

def solve {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg) :
    DriverResult leaf × Observations :=
  run (LcgPhaseKernel.supportedPhaseKernel orig original props hgate)
    (SchedulerConfig.init orig original props) (SupportedReach.init hent)

theorem solve_fst {leaf : Assignment → Bool} (orig : List Domain) (original : List Clause)
    (props : List Propagator) (hent : LearnedEntailed leaf original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg) :
    (solve orig original props hent hgate).1
      = LcgPhaseKernel.solve orig original props hent hgate :=
  run_fst _ _ _

end LeanFzn.Solver.UIP.LcgPhaseObserved
