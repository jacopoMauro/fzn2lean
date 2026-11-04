/- Conditional UIP phase driver with runtime events. -/
import LeanFzn.Legacy.Solver.Propagation.DomPruningKit
import LeanFzn.Legacy.Solver.UIP.Scheduler
import LeanFzn.Legacy.Solver.UIP.SchedulerState
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

/-! ## D1b: driver-routed solving + the named chronological reference -/

/-- The trace-carrying phase run: the REAL phase dispatcher (`C3b.phaseNext`)
under well-founded recursion over C3a's `schedulerRank_wf` — NO fuel. It
returns the driver outcome together with the `RuntimeEvents` record of the
TERMINAL configuration reached, i.e. exactly the counters the run's real
transitions accumulated (`SchedulerConfig.countResolutions` at the analyze
site, `RuntimeEvents.recordBackjump` at the jump site). No counter is
fabricated here, and the run is the same phase dispatcher that
`C3b.schedulerRun` executes. -/
noncomputable def runPhaseWithEvents {leaf : Assignment → Bool}
    (h : C3b.PhaseProgress leaf) :
    SchedulerConfig leaf → C3b.DriverResult leaf × RuntimeEvents :=
  WellFounded.fix (C3a.schedulerRank_wf (leaf := leaf)) (fun cfg rec =>
    match hstep : C3b.phaseNext cfg with
    | .sat w => (C3b.DriverResult.sat w, cfg.events)
    | .unsat => (C3b.DriverResult.unsat, cfg.events)
    | .propagate n => rec n (h cfg n (by rw [hstep]; rfl))
    | .decide n _ => rec n (h cfg n (by rw [hstep]; rfl))
    | .analyzeConflict n _ => rec n (h cfg n (by rw [hstep]; rfl))
    | .learnBackjumpAssert n _ _ => rec n (h cfg n (by rw [hstep]; rfl))
    | .localExclude n => rec n (h cfg n (by rw [hstep]; rfl))
    | .chronologicalFallback n => rec n (h cfg n (by rw [hstep]; rfl)))

/-- TOTALITY of the event-carrying run: for every phase obligation and every
configuration an outcome and an event record exist — no fuel. -/
theorem runPhaseWithEvents_total {leaf : Assignment → Bool}
    (h : C3b.PhaseProgress leaf) (cfg : SchedulerConfig leaf) :
    ∃ (r : C3b.DriverResult leaf) (e : RuntimeEvents),
      runPhaseWithEvents h cfg = (r, e) :=
  ⟨_, _, rfl⟩

/-- **D1b public driver accessor (the `solveWithEvents` route)**: run the
specialised public domain problem through the C3b fuel-free phase driver over
the REAL transition system, exposing BOTH the driver outcome and the run's
runtime events. The phase obligation is an EXPLICIT hypothesis: the open
`C3b.JumpDecrease` premise is substitutable (never assumed silently) via
`C3b.phaseProgress_of_jumpDecrease : JumpDecrease leaf → PhaseProgress leaf`.
The chronological source route remains callable (`solveChronological`). -/
noncomputable def solveWithEvents (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Objective)
    (h : C3b.PhaseProgress
      (chronologicalLeaf (feasibilityProblem problem) DomConstraint.satisfiedB)) :
    C3b.DriverResult
        (chronologicalLeaf (feasibilityProblem problem) DomConstraint.satisfiedB) ×
      RuntimeEvents :=
  runPhaseWithEvents (leaf := chronologicalLeaf (feasibilityProblem problem)
      DomConstraint.satisfiedB)
    h (SchedulerConfig.init (leaf := chronologicalLeaf (feasibilityProblem problem)
      DomConstraint.satisfiedB) problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved))

/-! ### D1b × `JumpDecrease`: the jump-discipline adapter

`C3b.phaseProgress_of_jumpDecrease` turns the single open dispatcher
premise `C3b.JumpDecrease` into the phase obligation `solveWithEvents`
consumes. The adapter below instantiates
`C3b.jumpDecrease_of_frontier_eq_of_mass` at the specialised public leaf,
so the premise has a concrete, named shape at exactly that leaf:

  after a performed jump (`BackjumpPlan.perform` returns `restored`) the
  successor's frontier cost equals the pre-jump frontier's AND the
  restored frame is strictly lighter than the conflict frame.

REMOVED (D1, 2026-10-10): the refuted-premise adapters
`DomJumpDiscipline`, `domJumpDecrease` and `solveWithEventsOfJump` were
deleted from the active dependency cone. The refutation stands: the
decrease content they packaged is NOT derivable at this leaf and no live
caller exists (verified by grep). `solveWithEvents` keeps its bare
`PhaseProgress` hypothesis and remains the only event-routed entry; the
PROVED chronological route below is the named reference. -/

end LeanFzn.Solver.UIP
