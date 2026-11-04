/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerStepSched.lean

Purpose (PLAN task P1): the SCHEDULED runtime dispatch. `phaseNextSched` is
`phaseNext` with the two event scans of the active arm taken through the
scheduled scan (`nextPruningEventSched`), threading the `PropScheduler` table
across the transition; every other arm is the verbatim dispatcher arm. The
equality `phaseNextSched_fst_eq` (under the table invariant and the concrete
locality discharge) is what lets the scheduled driver be certified by the
certified `phaseNext` theorems.

ONE SCAN PER STEP (P1 round 2): the active arm evaluates the scheduled event
prompt exactly ONCE (`schedulerNextSchedActive` computes `nextPruningEventSched`
into `np` and reads both the transition — the deduction continuation at
`np.1`, or the terminal continuation at that SAME event — and the table `np.2`
off it), and `phaseNextSched` calls `schedulerNextSched` once. The
`explainedDeductionSched`/`terminalResultSched` pair is kept as the reference
form of the two continuations: they are the defs the certified equivalences
`explainedDeductionSched_fst_eq`/`terminalResultSched_fst_eq` are stated about,
and the active arm's equivalence (`schedulerNextSchedActive_fst_eq`) is proved
against the same certified `explainedDeduction`/`terminalResult` at the
certified event.

Dependencies: SchedulerStep/Proofs.Scheduler (the certified dispatch) +
Propagation.ScheduledPropagation (the scheduled scan) +
Propagation.ScheduledFamilies (the concrete locality).

DAG: SchedulerStep -> this file -> LcgPhaseKernelSched.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.Scheduler
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerCache
import LeanFzn.Legacy.Solver.Propagation.ScheduledPropagation
import LeanFzn.Legacy.Solver.Propagation.ScheduledFamilies
import LeanFzn.Legacy.Solver.Propagation.ClosureFast
import LeanFzn.Legacy.Solver.Propagation.WorkQueue
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering


namespace LeanFzn.Solver.UIP
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.C3b

/-! ## The scheduled deduction / terminal scans

Both scans are factored through an event-consuming helper (`*Of`) that is
*definitionally* the certified scan at the certified event: the helper exists
only to state the scheduled twin against the same continuation code. -/

/-- The deduction continuation of `explainedDeduction`, with the event made
explicit. Definitionally its instance at `nextPruningEvent`. -/
def explainedDeductionOf (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) (ev : PruningEvent) :
    Option (ProductiveDeduction leaf bs) :=
  match ev with
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

/-- The certified deduction scan is the helper at the certified event. -/
theorem explainedDeductionOf_event (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) :
    explainedDeductionOf original props bs
      (nextPruningEvent original props bs.frame bs.learned)
      = explainedDeduction original props bs := rfl

/-! ## The E1 event-keyed work-queue prompt (PLAN task E1)

The queued prompt replaces the content-keyed watch-stamp reuse by the
version/event-keyed work queue: on a frame transition the queue enqueues
exactly the units subscribed to some produced event (`frameEvents`, computed
once per step); the scan then walks the propagator list IN REFERENCE ORDER,
re-runs each pending unit (reusing its record when its reference frame is
`quietB`-silent), replays clean units from their records, and stops at the
first productive implied/conflict exactly like `scanPropagators`
(`WorkQueue.scanQueue`, `scanQueue_event_eq`). Units after the stopping index
stay pending with their records. The DB scan and the liveness gates are the
certified ones; the equality to `nextPruningEvent` is the E1 core, consumed
below.

The stamp path stays available: both prompts are proved equal to the
certified event, so the runtime `queuePolicy` is a pure performance switch
with no new soundness argument. Measured (same session, alternating runs):
43-instance battery 147 ms queued vs 222-226 ms stamp with strictly fewer
propagator runs (10,533 vs 10,733 over the same 2,167 steps); FBDk04's
bounded route is 356/357 footprint-less and the policy routes it to the
stamp path (3.30-3.40 s, byte-identical stdout). -/

/-- The queued event prompt: certified fast DB scan first; at a viewed frame,
sync the queue from its stored frame (`enqueueEvents`), run the index-order
early-exit queued scan (`scanQueue`), and return its event. The returned
scheduler carries the updated queue and the new sync frame; the stamp table
rides along untouched (the queue path leaves it consistent, and vice versa). -/
def nextPruningEventQueuedSched (original : List Clause) (props : List Propagator)
    (sched : PropScheduler) (f : BranchFrame) (db : List Clause) :
    PruningEvent × PropScheduler :=
  match scanDatabaseFast original f db with
  | .stable =>
      if frameViewedB f then
        let q' := (sched.work.enqueueEvents props sched.qframe f).scanQueue props f
        (q'.1, { sched with work := q'.2, qframe := f })
      else (.stable, sched)
  | .conflict cs => (.conflict cs, sched)
  | .implied l c learnReason fromLearned =>
      if frameLiveB f then (.implied l c learnReason fromLearned, sched) else (.stable, sched)

/-- **EQUIVALENCE (queued prompt)**: a consistent scheduler (table AND queue)
together with the registered locality makes the queued prompt produce the
certified `nextPruningEvent`. The queue side is the E1 chain:
`QueueOK_enqueueEvents` -> `scanQueue_event_eq`. -/
theorem nextPruningEventQueuedSched_fst_eq {original : List Clause}
    {props : List Propagator} {sched : PropScheduler} {f : BranchFrame} {db : List Clause}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    (nextPruningEventQueuedSched original props sched f db).1
      = nextPruningEvent original props f db := by
  unfold nextPruningEventQueuedSched
  rw [scanDatabaseFast_eq]
  cases hdb : scanDatabase original f db with
  | stable =>
      simp only [hdb, nextPruningEvent]
      by_cases hv : frameViewedB f = true
      · simp only [hv, if_pos]
        exact scanQueue_event_eq (QueueOK_enqueueEvents hok.2) hloc
      · simp only [hv, Bool.false_eq_true, if_false]
  | conflict cs => simp only [hdb, nextPruningEvent]
  | implied l c lr fl =>
      simp only [hdb, nextPruningEvent]
      by_cases hl : frameLiveB f = true
      · simp only [hl, if_pos]
      · simp only [hl, Bool.false_eq_true, if_false]

/-- **PRESERVATION (queued prompt)**: the E1 invariant survives the queued
step: the stamp table is untouched, and the queue is re-established by
`enqueueEvents` and by the early-exit scan. -/
theorem nextPruningEventQueuedSched_OK {original : List Clause}
    {props : List Propagator} {sched : PropScheduler} {f : BranchFrame} {db : List Clause}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    PropSchedulerOK props (nextPruningEventQueuedSched original props sched f db).2 := by
  unfold nextPruningEventQueuedSched
  split
  · split
    · refine ⟨?_, ?_⟩
      · simpa using hok.1
      · show QueueOK props
          ((sched.work.enqueueEvents props sched.qframe f).scanQueue props f).2 f
        exact scanQueue_OK (QueueOK_enqueueEvents hok.2) hloc
    · exact hok
  · exact hok
  · split <;> exact hok

/-- The stamp path stays consistent across the scheduled event selection. -/
theorem nextPruningEventSched_OK {original : List Clause} {props : List Propagator}
    {sched : PropScheduler} {f : BranchFrame} {db : List Clause}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    PropSchedulerOK props (nextPruningEventSched original props sched f db).2 := by
  unfold nextPruningEventSched
  split
  · split
    · exact scanPropagatorsSched_OK hok hloc
    · exact hok
  · exact hok
  · split <;> exact hok

/-- The runtime policy bound: the queued prompt's per-step extraction is
O(frame mass); above this mass the watch-stamp scan is preferred. Both are
proved equal to the certified event, so this is a pure performance knob
(tuned by `Tests/Legacy/Benchmarks/DbScanCounts`). -/
def queueMassLimit : Nat := 4096

/-- Unit-count cutoff for the queue policy. The stamp path's per-unit
version check is O(1) and its scan is cache-friendly; the queue's
enqueue/dedup bookkeeping grows with the number of units. Measured on the
FBD family (clean alternating runs): FBDk04 (356 units, all watched after
PLAN P3) is 1.89 s on the stamp path vs 3.07 s on the queue, and FBDk06
(1621 units, all watched) loses incumbents under the queue (2 vs 4 in the
10 s cap). The battery's instances are all far below this cutoff; nonogram
(870 all-watched units) and spot5 are already excluded by the mass limit. -/
def queueUnitLimit : Nat := 256

/-- The runtime policy: the E1 work queue is used when at least HALF of the
units declare a nonempty footprint, the frame is not wide, and the unit list
is not too long. The discriminator is measured, not assumed: footprint-less
units (`watches := []`) cannot be reused by EITHER path, so an
all-footprint-less workload pays the queue's enqueue/dedup bookkeeping with
none of the reuse benefit, while the 43-instance battery is 1385/1420
watched and the queue is a clear win there (150 ms queued vs 226 ms stamp,
fewer propagator runs). After PLAN P3 the linear families also declare
footprints, but FBDk04's 356 all-watched units are faster on the stamp path
(1.89 s vs 3.07 s on the queue), so `queueUnitLimit` keeps the long FBD
instances off the queue; FBDk06's 1621 units must stay there to preserve its
incumbents. Both prompts are proved equal to the certified event, so the
switch needs no soundness argument (`promptOf_fst_eq`/`_OK`). -/
def queuePolicy (props : List Propagator) (f : BranchFrame) : Bool :=
  decide (Frame.mass f ≤ queueMassLimit) &&
    decide (props.length ≤ queueUnitLimit) &&
    decide (props.length ≤
      2 * props.foldl (fun a p => if p.watches.isEmpty then a else a + 1) 0)

/-- The dispatcher's event prompt with the runtime policy switch. -/
def promptOf (original : List Clause) (props : List Propagator) (sched : PropScheduler)
    (f : BranchFrame) (db : List Clause) : PruningEvent × PropScheduler :=
  if queuePolicy props f then
    nextPruningEventQueuedSched original props sched f db
  else
    nextPruningEventSched original props sched f db

/-- **EQUIVALENCE (policy prompt)**: both policy branches are the certified
event, so the switch needs no soundness argument. -/
theorem promptOf_fst_eq {original : List Clause} {props : List Propagator}
    {sched : PropScheduler} {f : BranchFrame} {db : List Clause}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    (promptOf original props sched f db).1 = nextPruningEvent original props f db := by
  unfold promptOf
  split
  · exact nextPruningEventQueuedSched_fst_eq hok hloc
  · exact nextPruningEventSched_fst_eq original props sched f db hok hloc

/-- **PRESERVATION (policy prompt)**. -/
theorem promptOf_OK {original : List Clause} {props : List Propagator}
    {sched : PropScheduler} {f : BranchFrame} {db : List Clause}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    PropSchedulerOK props (promptOf original props sched f db).2 := by
  unfold promptOf
  split
  · exact nextPruningEventQueuedSched_OK hok hloc
  · exact nextPruningEventSched_OK hok hloc

/-- The scheduler component of the scheduled event prompt (the single
computation the scans share). -/
def schedAfterEvent (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) (sched : PropScheduler) : PropScheduler :=
  (nextPruningEventSched original props sched bs.frame bs.learned).2

/-- `explainedDeduction` with the scheduled event scan (the scheduler table
threaded through the step). -/
def explainedDeductionSched (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) (sched : PropScheduler) :
    Option (ProductiveDeduction leaf bs) × PropScheduler :=
  let np := nextPruningEventSched original props sched bs.frame bs.learned
  (explainedDeductionOf original props bs np.1, np.2)

theorem explainedDeductionSched_snd (original : List Clause) (props : List Propagator)
    (bs : BranchState leaf) (sched : PropScheduler) :
    (explainedDeductionSched original props bs sched).2
      = (nextPruningEventSched original props sched bs.frame bs.learned).2 := rfl

/-- The terminal continuation of `terminalResult`, with the event explicit. -/
def terminalResultOf (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) (ev : PruningEvent) :
    ClosureResult leaf :=
  match ev with
  | .stable =>
      match wipeoutClause orig bs.trail bs.frame with
      | some w => .conflict bs [w] []
      | none => .stable bs
  | .conflict cs =>
      .conflict bs cs (cs.filter fun c => !(bs.learned.contains c))
  | .implied l c lr fl =>
      match filterFrame l bs.frame with
      | none => .conflict bs [c]
          (if lr && !(bs.learned.contains c) then [c] else [])
      | some _ => .stable bs

/-- The certified terminal scan is the helper at the certified event. -/
theorem terminalResultOf_event (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) :
    terminalResultOf orig original props bs
      (nextPruningEvent original props bs.frame bs.learned)
      = terminalResult orig original props bs := rfl

/-- `terminalResult` with the scheduled event scan. -/
def terminalResultSched (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) (sched : PropScheduler) :
    ClosureResult leaf × PropScheduler :=
  let np := nextPruningEventSched original props sched bs.frame bs.learned
  (terminalResultOf orig original props bs np.1, np.2)

theorem terminalResultSched_snd (orig : List Domain) (original : List Clause)
    (props : List Propagator) (bs : BranchState leaf) (sched : PropScheduler) :
    (terminalResultSched orig original props bs sched).2
      = (nextPruningEventSched original props sched bs.frame bs.learned).2 := rfl

/-- **EQUIVALENCE (deduction form)**: under a consistent table, the scheduled
deduction step is the certified one. -/
theorem explainedDeductionSched_fst_eq {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {sched : PropScheduler}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    (explainedDeductionSched original props bs sched).1
      = explainedDeduction original props bs := by
  have hNE : (nextPruningEventSched original props sched bs.frame bs.learned).1
      = nextPruningEvent original props bs.frame bs.learned :=
    nextPruningEventSched_fst_eq (original := original) (props := props)
      (sched := sched) (f := bs.frame) (db := bs.learned) hok hloc
  cases hev : nextPruningEventSched original props sched bs.frame bs.learned with
  | mk ev sched' =>
      have hev' : ev = nextPruningEvent original props bs.frame bs.learned := by
        have h := hNE
        rw [hev] at h
        exact h
      simp only [explainedDeductionSched, hev]
      rw [hev', explainedDeductionOf_event]

/-- **EQUIVALENCE (terminal form)**. -/
theorem terminalResultSched_fst_eq {orig : List Domain} {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf} {sched : PropScheduler}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    (terminalResultSched orig original props bs sched).1
      = terminalResult orig original props bs := by
  have hNE : (nextPruningEventSched original props sched bs.frame bs.learned).1
      = nextPruningEvent original props bs.frame bs.learned :=
    nextPruningEventSched_fst_eq (original := original) (props := props)
      (sched := sched) (f := bs.frame) (db := bs.learned) hok hloc
  cases hev : nextPruningEventSched original props sched bs.frame bs.learned with
  | mk ev sched' =>
      have hev' : ev = nextPruningEvent original props bs.frame bs.learned := by
        have h := hNE
        rw [hev] at h
        exact h
      simp only [terminalResultSched, hev]
      rw [hev', terminalResultOf_event]

theorem explainedDeductionSched_OK {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {sched : PropScheduler}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    PropSchedulerOK props (explainedDeductionSched original props bs sched).2 := by
  rw [explainedDeductionSched_snd]
  exact nextPruningEventSched_OK (original := original) (props := props)
    (sched := sched) (f := bs.frame) (db := bs.learned) hok hloc

theorem terminalResultSched_OK {orig : List Domain} {original : List Clause}
    {props : List Propagator} {bs : BranchState leaf} {sched : PropScheduler}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    PropSchedulerOK props (terminalResultSched orig original props bs sched).2 := by
  rw [terminalResultSched_snd]
  exact nextPruningEventSched_OK (original := original) (props := props)
    (sched := sched) (f := bs.frame) (db := bs.learned) hok hloc

/-! ## The scheduled dispatcher -/

/-- The scheduler after the scheduled event prompt is consistent whenever
the incoming one is. -/
theorem schedAfterEvent_OK {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {sched : PropScheduler}
    (hok : PropSchedulerOK props sched) (hloc : PropLocal props) :
    PropSchedulerOK props (schedAfterEvent original props bs sched) := by
  rw [show schedAfterEvent original props bs sched
        = (explainedDeductionSched original props bs sched).2 from
      explainedDeductionSched_snd original props bs sched ▸ rfl]
  exact explainedDeductionSched_OK hok hloc

/-- The ACTIVE ARM of the scheduled dispatch with ONE scan evaluation: the
scheduled event prompt is computed once (`np`), and BOTH the transition and
the scheduler component are read off that single evaluation (never a second
scan). The queued E1 prompt (`nextPruningEventQueuedSched`) is certified and
available via `promptOf`, but the measured public route keeps the watch-stamp
scan: the queue's conservative full drain runs the whole dirty set per step,
while this scan exits at the first productive event (see the E1 report). -/
def schedulerNextSchedActive (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf × PropScheduler :=
  match promptOf cfg.original cfg.props sched cfg.branch.frame cfg.branch.learned with
  | (ev, sched') =>
      (match explainedDeductionOf cfg.original cfg.props cfg.branch ev with
       | some d => .propagate (stepPropagate cfg d)
       | none =>
           match terminalResultOf cfg.orig cfg.original cfg.props cfg.branch ev with
           | .stable _ => stableStepGuarded cfg
           | .conflict _ cs learned => conflictStepFast cfg cs learned
           | .localExcluded _ _ _ learned =>
               .localExclude (stepLocalExclude cfg learned (branchRegion cfg)),
       sched')

/-- The recorded-conflict dispatch with the FAST resumed closure: the body of
`backjumpStep` with the single change `p.perform` -> `p.performFast`
(`ClosureFast.lean`), so the post-backjump closure uses the indexed database
scan. Everything else (fallback, checkpoint lookup, exclusion, learn arm) is
verbatim. -/
def backjumpStepFast (cfg : SchedulerConfig leaf) (ev : ConflictEvidence) :
    SchedulerTransition leaf :=
  match ev.analysis with
  | none => .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg))
  | some an =>
      match checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg))
      | some cp =>
          let p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned
          match p.performFast cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              -- the assertion rejects the restored ancestor: the CHECKPOINT's
              -- prefix is the dead region, not the current branch's
              .localExclude (stepLocalExclude cfg ev.learned (checkpointRegion cp))
          | some restored =>
              .learnBackjumpAssert (stepLearnBackjumpAssert cfg p ev restored) p an

/-- **EQUIVALENCE (fast backjump)**: the fast recorded-conflict dispatch is the
certified `backjumpStep` (`BackjumpPlan.performFast_eq` under the shared
matches). -/
theorem backjumpStepFast_eq (cfg : SchedulerConfig leaf) (ev : ConflictEvidence) :
    backjumpStepFast cfg ev = backjumpStep cfg ev := by
  unfold backjumpStepFast backjumpStep
  simp only [BackjumpPlan.performFast_eq]
  rfl

/-- `schedulerNext` with the scheduled scan in the active arm: ONE scan
evaluation per dispatch (the certified arms are verbatim). -/
def schedulerNextSched (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf × PropScheduler :=
  match cfg.conflict with
  | some ev => (backjumpStepFast cfg ev, sched)
  | none =>
      match cfg.status with
      | .dead => (consumeStep cfg, sched)
      | .active => schedulerNextSchedActive cfg sched

/-- The scheduled successor's transition component (the shared step's first
projection — no extra scan). -/
def schedulerNextSchedTrans (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf :=
  (schedulerNextSched cfg sched).1

/-- The scheduled successor's scheduler component (the shared step's second
projection — no extra scan). -/
def schedulerNextSchedSched (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    PropScheduler :=
  (schedulerNextSched cfg sched).2

theorem schedulerNextSched_fst (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    (schedulerNextSched cfg sched).1 = schedulerNextSchedTrans cfg sched := rfl

theorem schedulerNextSched_snd (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    (schedulerNextSched cfg sched).2 = schedulerNextSchedSched cfg sched := rfl

/-- **EQUIVALENCE (active arm)**: at the single evaluated event, the active
arm's transition is the deduction continuation at that event — or, when
none exists, the terminal continuation at the SAME event. -/
theorem schedulerNextSchedActive_fst_eq {cfg : SchedulerConfig leaf} {sched : PropScheduler}
    (hcache : cfg.CacheAligned)
    (hok : PropSchedulerOK cfg.props sched) (hloc : PropLocal cfg.props) :
    (schedulerNextSchedActive cfg sched).1
      = (match explainedDeduction cfg.original cfg.props cfg.branch with
         | some d => .propagate (stepPropagate cfg d)
         | none =>
             match terminalResult cfg.orig cfg.original cfg.props cfg.branch with
             | .stable _ => stableStepGuarded cfg
             | .conflict _ cs learned => conflictStep cfg cs learned
             | .localExcluded _ _ _ learned =>
                 .localExclude (stepLocalExclude cfg learned (branchRegion cfg))) := by
  have h1 := promptOf_fst_eq (original := cfg.original)
    (props := cfg.props) (sched := sched) (f := cfg.branch.frame)
    (db := cfg.branch.learned) hok hloc
  unfold schedulerNextSchedActive
  cases hev : promptOf cfg.original cfg.props sched cfg.branch.frame
      cfg.branch.learned with
  | mk ev sched' =>
      have hev' : ev = nextPruningEvent cfg.original cfg.props cfg.branch.frame
          cfg.branch.learned := by
        rw [hev] at h1
        exact h1
      simp only [hev]
      rw [hev', explainedDeductionOf_event, terminalResultOf_event]
      simp only [conflictStepFast_eq hcache.1 hcache.2.1 hcache.2.2]

/-- **EQUIVALENCE (dispatch form)**: under a consistent table the scheduled
dispatcher takes the certified transition. -/
theorem schedulerNextSched_fst_eq {cfg : SchedulerConfig leaf} {sched : PropScheduler}
    (hcache : cfg.CacheAligned)
    (hok : PropSchedulerOK cfg.props sched) (hloc : PropLocal cfg.props) :
    (schedulerNextSched cfg sched).1 = schedulerNext cfg := by
  unfold schedulerNextSched schedulerNext
  cases hc : cfg.conflict with
  | some ev => simp only [hc, backjumpStepFast_eq]
  | none =>
      cases hs : cfg.status with
      | dead => simp only [hc, hs]
      | active =>
          simp only [hc, hs]
          exact schedulerNextSchedActive_fst_eq hcache hok hloc

/-- The table stays consistent across the scheduled dispatch (the scheduler
is only modified by the scan of the active arm). -/
theorem schedulerNextSched_OK {cfg : SchedulerConfig leaf} {sched : PropScheduler}
    (hok : PropSchedulerOK cfg.props sched) (hloc : PropLocal cfg.props) :
    PropSchedulerOK cfg.props (schedulerNextSched cfg sched).2 := by
  unfold schedulerNextSched
  cases hc : cfg.conflict with
  | some ev => simp only [hc]; exact hok
  | none =>
      cases hs : cfg.status with
      | dead => simp only [hc, hs]; exact hok
      | active =>
          have hnext := promptOf_OK (original := cfg.original)
            (props := cfg.props) (sched := sched) (f := cfg.branch.frame)
            (db := cfg.branch.learned) hok hloc
          unfold schedulerNextSchedActive
          cases hev : promptOf cfg.original cfg.props sched cfg.branch.frame
              cfg.branch.learned with
          | mk ev sched' =>
              have hnext' : PropSchedulerOK cfg.props sched' := by
                rw [hev] at hnext
                exact hnext
              simp only [hev]
              exact hnext'

/-! ## The scheduled phase dispatcher -/

/-- The phase-landing resolution (the certified `phaseNext` body): the
consume compositions for the stuttering `.localExclude` /
`.chronologicalFallback` / `.analyzeConflict` landings. -/
def phaseResolve (cfg : SchedulerConfig leaf) : SchedulerTransition leaf → SchedulerTransition leaf
  | .localExclude n =>
      match stepConsume n with
      | some next => .chronologicalFallback next
      | none => .unsat
  | .chronologicalFallback n =>
      match cfg.conflict with
      | some _ =>
          match stepConsume n with
          | some next => .chronologicalFallback next
          | none => .unsat
      | none => .chronologicalFallback n
  | .analyzeConflict n c =>
      match n.conflict with
      | some ev =>
          match backjumpStepFast n ev with
          | .chronologicalFallback n' =>
              match stepConsume n' with
              | some next => .chronologicalFallback next
              | none => .unsat
          | .localExclude n' =>
              match stepConsume n' with
              | some next => .chronologicalFallback next
              | none => .unsat
          | t' => t'
      | none => .analyzeConflict n c
  | t' => t'

/-- The certified `phaseNext` is the resolution at the certified dispatcher's
transition. -/
theorem phaseNext_eq_resolve (cfg : SchedulerConfig leaf) :
    phaseNext cfg = phaseResolve cfg (schedulerNext cfg) := by
  unfold phaseNext phaseResolve
  simp only [backjumpStepFast_eq]
  rfl

/-- `phaseNext` with the scheduled dispatcher: ONE scheduled step evaluation
feeds both the phase-landing resolution and the scheduler component. -/
def phaseNextSched (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf × PropScheduler :=
  let pr := schedulerNextSched cfg sched
  (phaseResolve cfg pr.1, pr.2)

/-- The phase-landing resolution of the scheduled dispatcher's transition
(no extra scan: the transition is the shared step's projection). -/
def phaseNextSchedTrans (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    SchedulerTransition leaf :=
  phaseResolve cfg (schedulerNextSched cfg sched).1

/-- The scheduler component of the scheduled phase dispatcher (the phase
landing resolution never changes the branch, so it is the dispatcher's). -/
def phaseNextSchedSched (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    PropScheduler :=
  (schedulerNextSched cfg sched).2

theorem phaseNextSched_fst (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    (phaseNextSched cfg sched).1 = phaseNextSchedTrans cfg sched := rfl

theorem phaseNextSched_snd (cfg : SchedulerConfig leaf) (sched : PropScheduler) :
    (phaseNextSched cfg sched).2 = (schedulerNextSched cfg sched).2 := rfl

/-- **EQUIVALENCE (phase form)**: the scheduled phase dispatcher takes the
certified `phaseNext` transition under a consistent table. -/
theorem phaseNextSched_fst_eq {cfg : SchedulerConfig leaf} {sched : PropScheduler}
    (hcache : cfg.CacheAligned)
    (hok : PropSchedulerOK cfg.props sched) (hloc : PropLocal cfg.props) :
    (phaseNextSched cfg sched).1 = phaseNext cfg := by
  rw [phaseNextSched_fst]
  unfold phaseNextSchedTrans
  rw [schedulerNextSched_fst_eq hcache hok hloc]
  exact (phaseNext_eq_resolve cfg).symm

/-- The table stays consistent across the scheduled phase dispatch. -/
theorem phaseNextSched_OK {cfg : SchedulerConfig leaf} {sched : PropScheduler}
    (hok : PropSchedulerOK cfg.props sched) (hloc : PropLocal cfg.props) :
    PropSchedulerOK cfg.props (phaseNextSched cfg sched).2 := by
  rw [phaseNextSched_snd]
  exact schedulerNextSched_OK hok hloc

end LeanFzn.Solver.UIP
