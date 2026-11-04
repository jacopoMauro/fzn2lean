/-
File: LeanFzn/Solver/Propagation/ClosureFast.lean

Purpose (performance task F): module-level FAST TWINS of the explained
propagation closure. The runtime already routes the ACTIVE-step event prompt
through the indexed database scan (`nextPruningEventSched` in
`ScheduledPropagation.lean`), but the closure resumed by a BACKJUMP
(`BackjumpPlan.perform` -> `explainedClosure`) still runs the UNINDEXED
reference `scanDatabase`. Measured on FBDk04 at the same state: the reference
scan costs 534 us against the indexed `scanDatabaseFast`'s 121 us, inside
`BackjumpPlan.perform`'s ~1.9 ms share of each late jump.

This module defines byte-for-byte twins of the scan chain
(`nextPruningEvent` -> `explainedDeduction` -> `explainedClosure`) and of
`BackjumpPlan.perform`, with ONLY the database scan replaced by the certified
indexed scan, together with the UNCONDITIONAL equalities that transport the
whole established closure theory (`scanDatabaseFast_eq` is unconditional, so
no locality/table premise is needed here). Nothing else changes: the twins
call the same `TrailRedundant`, `filterFrame`, `stepNarrowSync`, `syncAll`
and `ProductiveDeduction` payloads, and the recursions use the same
`Frame.mass` termination measure.

The wiring into the SCHEDULED dispatcher (`backjumpStepFast` in
`Solver/UIP/Proofs/SchedulerStepSched.lean`) and therefore the certified
reference definitions stay untouched.

DAG: DbScanIndex + ExplainedPropagation + BackjumpFrontier -> ClosureFast.
-/
import LeanFzn.Legacy.Solver.Propagation.DbScanIndex
import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Legacy.Solver.Propagation.BackjumpFrontier
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The fast event prompt -/

/-- `nextPruningEvent` with the indexed `scanDatabaseFast` in place of the
reference `scanDatabase`. Every other branch (`frameViewedB`,
`scanPropagators`, `frameLiveB`) is byte-identical. -/
def nextPruningEventFast (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) : PruningEvent :=
  match scanDatabaseFast original f db with
  | .stable => if frameViewedB f then scanPropagators f props else .stable
  | .conflict cs => .conflict cs
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then .implied l c learnReason fromLearned else .stable

/-- The fast event prompt returns exactly the certified prompt
(unconditional: `scanDatabaseFast_eq` has no side condition). -/
theorem nextPruningEventFast_eq (original : List Clause) (props : List Propagator)
    (f : BranchFrame) (db : List Clause) :
    nextPruningEventFast original props f db = nextPruningEvent original props f db := by
  rw [nextPruningEventFast, nextPruningEvent, scanDatabaseFast_eq]
  rfl

/-! ## The fast productive deduction -/

/-- `explainedDeduction` with the fast event prompt. All other calls
(`TrailRedundant`, `filterFrame`, the `learned` computation and the
`ProductiveDeduction` payload fields) are unchanged. -/
def explainedDeductionFast (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) : Option (ProductiveDeduction leaf bs) :=
  match nextPruningEventFast original props bs.frame bs.learned with
  | .stable => none
  | .conflict _ => none
  | .implied l c learnReason fromLearned =>
      let learned := if learnReason && !(bs.learned.contains c) then [c] else []
      match TrailRedundant bs.trail l with
      | true => none
      | false =>
          match hf : filterFrame l bs.frame with
          | none => none
          | some g =>
              if hm : Frame.mass g < Frame.mass bs.frame then
                some { literal := l, reason := c, learned := learned, frame := g,
                       filtered := hf, decreases := hm }
              else none

/-- The fast deduction scan returns exactly the certified `explainedDeduction`
(the event prompt is `nextPruningEventFast_eq`). -/
theorem explainedDeductionFast_eq (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) :
    explainedDeductionFast original props bs = explainedDeduction original props bs := by
  rw [explainedDeductionFast, explainedDeduction, nextPruningEventFast_eq]
  rfl

/-! ## The fast closure -/

/-- `explainedClosure` with the fast deduction scan. The recursion is on the
same `Frame.mass bs.frame` measure with the same `stepNarrowSync` payload and
decrease proof. -/
def explainedClosureFast (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) : BranchState leaf :=
  match hd : explainedDeductionFast original props bs with
  | none => bs
  | some d => explainedClosureFast orig original props (stepNarrowSync orig bs d)
termination_by Frame.mass bs.frame
decreasing_by
  have := d.decreases
  simpa using this

/-- The fast closure returns exactly the certified `explainedClosure`, by
well-founded induction on the closure's own measure (`explainedClosure.induct`)
and the unconditional deduction equality at each step. -/
theorem explainedClosureFast_eq (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) :
    explainedClosureFast orig original props bs
      = explainedClosure orig original props bs := by
  refine explainedClosure.induct orig original props
    (fun bs => explainedClosureFast orig original props bs
      = explainedClosure orig original props bs) ?_ ?_ bs
  · intro x hnone
    rw [explainedClosureFast, explainedClosure, explainedDeductionFast_eq, hnone]
  · intro x d hsome ih
    rw [explainedClosureFast, explainedClosure, explainedDeductionFast_eq, hsome]
    exact ih

/-! ## The fast backjump plan step -/

/-- `BackjumpPlan.perform` with the fast closure. Same insertion, restoration,
assertion narrowing and `syncAll` synchronisation; only the resumed closure is
the fast twin. -/
def BackjumpPlan.performFast (p : BackjumpPlan leaf) (bs : BranchState leaf)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    Option (BranchState leaf) :=
  (p.restoreNarrow bs).map fun s => explainedClosureFast orig original props (syncAll orig s)

/-- The fast backjump plan step returns exactly the certified
`BackjumpPlan.perform` (map congruence and `explainedClosureFast_eq`). -/
theorem BackjumpPlan.performFast_eq (p : BackjumpPlan leaf) (bs : BranchState leaf)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    p.performFast bs orig original props = p.perform bs orig original props := by
  unfold BackjumpPlan.performFast BackjumpPlan.perform
  congr 1
  funext s
  rw [explainedClosureFast_eq]

end LeanFzn.Solver.Propagation
