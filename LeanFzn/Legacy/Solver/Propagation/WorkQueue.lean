/-
File: LeanFzn/Solver/Propagation/WorkQueue.lean

Purpose (PLAN task E1): a PERSISTENT CERTIFIED WORK QUEUE over propagator
indices with conservative, EVENT-keyed invalidation, WIRED into the scheduled
dispatcher as `nextPruningEventQueuedSched` / `promptOf`
(SchedulerStepSched.lean) under the measured `queuePolicy`. The queue's scan
(`scanQueue`) walks in REFERENCE ORDER and exits at the first productive
event like `scanPropagators`, so the earlier whole-dirty-set drain (a 3.5x
FBDk04 loss) is gone: the 43-instance battery runs 147 ms queued vs 222-226
ms stamp with strictly fewer propagator runs, and the policy routes
footprint-less-dominated workloads (FBDk04's bounded route is 356/357
footprint-less) to the stamp path (3.30-3.40 s, byte-identical stdout).
The measurable residual: where no unit can be reused the queue's
enqueue/dedup bookkeeping is pure overhead.

## Why event-keyed (not content-keyed)

The earlier watch-stamp scheduler (`ScheduledPropagation.scanPropagatorsSched`)
decides reuse from the CONTENT of a unit's watched domains. The measured
43-instance ablation in the PLAN session records showed that rebuilding and
comparing those stamps costs more than re-running the cheap propagators on
small domains; on wide domains the stamp is always stale. E1 therefore fixes
the dependency contract at the level of the OBSERVABLE EVENTS of a frame
transition (`DomainEvent` / `frameEvents`, E0 = `EventContract.lean`) and lets
the queue remember, per unit, only (a) the reference frame at which the unit
last ran and (b) the result recorded there. A unit is skipped exactly when
every event between its reference frame and the current frame is one its
declared footprint does not subscribe to; that skip is certified by the
frozen E0 obligation `SkipSound` (`SkipsStable` in list form).

## State

`WorkQueue` is a pair of first-order lists:
* `seen : List (Option (BranchFrame × PropagationResult))`, aligned with the
  caller's propagator list: the reference frame and the recorded result of
  each unit that has already run (the dependency bookkeeping; which events a
  queued unit depends on is decided at pop time from its reference frame and
  E0's `PropagatorSubscribes`);
* `pending : List Nat`, the queued unit indices. Deduplication is
  structural: `enqueue` consults `List.contains`, so no index ever occurs
  twice; `QueueShape` records this (`pending.Nodup`) together with alignment
  (`seen.length = props.length`) and in-range indices.

The CARRIER and the invariant predicates (`QueueQuiet`, `QueueShape`,
`QueueRecords`, `QueueCovered`, `QueueOK`) are declared in
`ScheduledPropagation.lean`, because the runtime dispatcher threads them
through `PropScheduler` and this module sits above it in the import DAG
(E0). Everything below — operations and proofs — is this module's.

Operations (all computable, all pure):
* `init` queues every unit (conservative start);
* `enqueueEvents` adds exactly the units subscribed to some event of a frame
  transition, deduplicated, in ascending index order;
* `step` pops one unit and records `(current frame, result)`; when the unit's
  recorded reference is event-silent to the current frame it REUSES the
  recorded result (no run) — `stepSeen_skip` / `step_correct` certify the
  reuse;
* `drain` consumes the whole pending list structurally (no fuel, no
  `partial`; the pending list is the measure);
* `rebuild` re-queues everything (restore / database change; conservative);
* `enqueueAll` inserts new work for learned clauses (every unit);
* `extendUnits` appends new propagators (each new unit is queued).

## The certified core

`QueueShape` / `QueueRecords` / `QueueCovered` / `QueueOK` (all `Prop`s,
declared in ScheduledPropagation):
* `QueueRecords`: every stored result really is the run's result at its
  stored reference frame;
* `QueueCovered`: every unit is EITHER queued OR its stored reference frame is
  `QueueQuiet` to the current frame. `QueueQuiet` is the E0-free certificate
  E0 event-silence implies (`eventSilent_imp_quiet`): `Frame.domains`
  agreement on an empty footprint (then `frameState` is equal) and
  `watchStamp` agreement on a nonempty one (then the registered
  `PropLocalOne` locality applies). The event vocabulary itself is only
  consumed by `step`'s skip test;
* The core theorems:
  - `step_correct` / `stepSeen_skip`: the unit popped by `step` reports
    exactly its run's result at the current frame (skip branch: the
    recorded reference frame is event-silent and `SkipSound` at that pair
    turns the reuse into the unit's current run);
  - `empty_complete_scan` / `empty_complete`: an empty covered queue's
    recorded results replay EXACTLY the certified full scan at the current
    frame (`nextPruningEvent` on the replay equals `nextPruningEvent` on the
    real list);
  - `empty_complete_replayAt`: the uniform-reference-frame packaging through
    E0's `skipsComplete_proof`;
  - preservation of `QueueOK` by `init`, `enqueueEvents` (uses only event
    silence algebra — no locality consumed there), `step`, `drain`,
    `rebuild`, `enqueueAll`, `extendUnits`.
* Progress: `queueMeasure := pending.length`; `step_measure_lt` (every step
  strictly decreases it), `drain_pending` (a completed drain has an empty
  pending list), `drainSeen` recurses structurally on the pending list. A
  productive outcome is a justified finite-progress terminator:
  `productive_frame` shows `productive l f = true` gives either
  `filterFrame l f = none` (branch closed) or a frame whose `Frame.mass`
  strictly decreases — the existing closure argument, not new fuel.
* Quiescence: `NoPostponed original props q g db` says the classification
  computed from the queue's records at `g` is EXACTLY the certified full
  scan's classification. `noPostponed_of_drain` discharges it for the
  drain-then-classify policy; `noPostponed_rebuild` for the rebuild-on-restore
  policy (rebuild -> drain -> classify), because `QueueOK_rebuild` holds
  unconditionally. The standing hypothesis is only the registered locality
  `PropLocal props` (the dispatch's own hypothesis), which also discharges
  `SkipsStableAll` (`skipsStableAll_of_propLocal`) where `step`/`drain`
  consume E0's `SkipSound`.

## The early-exit scan and the runtime policy (measured)

`WorkQueue.scanQueue` is the E1 fix-2 classifier: it walks `props` in
reference order, re-runs each PENDING unit at the current frame (reusing its
record when its reference frame is `quietB`-silent, via `QueueQuiet` +
`PropLocalOne`), replays clean units from their records, and STOPS at the
first productive implied/conflict exactly like the reference `scanPropagators`
— the units after the stopping index stay pending. `scanQueueAux_spec` is the
master theorem: the event equals `scanPropagators f props`, every processed
unit is recorded at the current frame with its current run, the unprocessed
suffix passes through unchanged, and the scan never reports an index below
its start. The threaded form (`nextPruningEventQueuedSched`, proved by
`scanQueue_event_eq`/`scanQueue_OK`) plus the `queuePolicy` switch is on the
PUBLIC route (`schedulerNextSchedActive` -> `promptOf`).

MEASURED (this session, same tree, alternating runs; `Tests/E1/DbScanCounts`):
* 43-instance battery: **147 ms queued vs 222-226 ms stamp** (the `sched`
  best-window totals, reps=3), and the independent queue twin performs
  **10,533 propagator runs vs the stamp twin's 10,733** on the same 2,167
  scan steps / 2,349 productive deductions (4,48 vs 4,57 per deduction;
  certificate skips 323, record replays 89,437). Strictly fewer runs and a
  34% wall-clock win.
* FBDk04 `leanfzn solve`: after PLAN P3 every one of its 356 units declares a
  footprint (351 `linNe` + 4 `linLe` + 1 `linEq`).  The queue path measured
  3.07 s against 1.87 s on the stamp path, so `queueUnitLimit` (256) keeps it
  on the stamp path; final P3 vs P2c is **1.868 s vs 1.841 s** (+1.5%, 5
  alternating runs, stdout byte-identical).  The earlier 4.3-4.4 s
  forced-queue figure was the pre-P3 all-footprint-less ablation.
* `nextPruningEventQueued` (this module) remains the full-drain reference
  (kept, with its own `_fst_eq`), superseded in the wiring by `scanQueue`.
The audited-footprint refinement is now landed for the three linear families
(PLAN P1 for `linEq`, PLAN P3 for `linLe`/`linNe`): their units are reusable
at `is.map (fun i => Atom.intLe i 0)` through the declared watches.  The
queue serves the small watched workloads; `queueUnitLimit` keeps long
all-linear instances (FBDk04/FBDk06) on the stamp path.

## Audit notes

* NO OPEN OBLIGATIONS. The completeness/quiescence/wiring theorems take only
  the registered locality `PropLocal props` (the dispatch's own hypothesis);
  the step/drain soundness takes `SkipsStableAll`, derived from `PropLocal`
  by `skipsStableAll_of_propLocal` (through E0's `skipSound_of_localOrEmpty`)
  and discharged unconditionally for the registered list by
  `clampProps_skipsStableAll`. `QueueOK_enqueueEvents` consumes no locality at
  all. The refined audited-footprint route (linear families) is available
  through `Propagator.withFootprint` /
  `skipSoundOn_iff_skipSound_withFootprint` and E0's `..._skipSoundOn`
  instances; no family obligation is reopened.
* The invalidation is conservative at the DECLARED footprint
  (`PropagatorSubscribes`): a `watches := []` registration subscribes to
  everything and is never skipped, exactly as in E0. This is also why the
  measured verdict above is negative on FBDk04: its linear registrations are
  footprint-less.
* Clauses are deliberately OUT OF SCOPE (W1 owns the clause index); DB
  changes re-queue propagators via `enqueueAll`/`rebuild` in the API. Note
  the runtime wiring does not need the db-length check: propagators run on
  `frameState` and do not read the clause database (`PropLocalOne` reads
  domains only), and `QueueOK` mentions neither `State.clauses` nor
  `learned`, so a database change cannot break the queue invariant.
* One subtlety the certificate proofs handle explicitly: event silence at a
  footprint implies the E0-free `QueueQuiet` certificate
  (`eventSilent_imp_quiet`); the per-slot extraction lemmas
  (`getD_eq_of_eventSilentOn`, `length_lt_iff_of_eventSilentOn`) and the
  truncation-completeness lemmas (`frameEventsAux_truncated_left/right`)
  cover the EMPTY-domain truncation case where stamps alone would be too
  weak. `QueueQuiet` is transitive (`QueueQuiet.trans`), which is what keeps
  clean units certified across un-enqueued frame moves.

DAG: Pruning + ScheduledFamilies + EventContract -> WorkQueue ->
SchedulerStepSched (the threaded early-exit queued prompt, on the public
route under `queuePolicy`). This module touches no runtime file; the
dispatcher wiring lives in `SchedulerStepSched.lean`.
-/
import LeanFzn.Legacy.Solver.Propagation.EventContract
open LeanFzn.Semantics LeanFzn.Solver.Core

set_option linter.unusedVariables false

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver.Propagation.DomainFiltering

/-! ## 0. Uniform stability and footprint bridges -/

/-- The queue's standing locality hypothesis in uniform-pair form: every unit
is `SkipSound` for EVERY pair of frames (its declared footprint is silent
exactly when the run is unchanged). E0's `clampProps_skipsStable` is already
uniform in the frame pair, so the concrete certified list discharges this. -/
def SkipsStableAll (original : List Clause) (props : List Propagator)
    (db : List Clause) : Prop :=
  ∀ p ∈ props, ∀ f g : BranchFrame, SkipSound p f g

/-- **DISCHARGED CONCRETE INSTANCE**: the certified LCG propagator list
(`clampProps orig (dcs.filterMap propagatorOfProved)`) satisfies the uniform
stability hypothesis for every frame pair. -/
theorem clampProps_skipsStableAll (orig : List Domain) (dcs : List DomConstraint)
    (original : List Clause) (db : List Clause) :
    SkipsStableAll original (clampProps orig (dcs.filterMap propagatorOfProved)) db :=
  fun p hp f g => clampProps_skipsStable orig dcs original db p hp

/-- A uniform list obligation is a uniform stability hypothesis. -/
theorem skipsStableAll_of_uniform {original : List Clause} {props : List Propagator}
    {db : List Clause} (h : ∀ f g : BranchFrame, SkipsStable original props f g db) :
    SkipsStableAll original props db :=
  fun p hp f g => h f g p hp

/-- **THE DISPATCHER BRIDGE**: the registered locality hypothesis
(`PropLocal`, what the runtime kernel threads) discharges the uniform
stability hypothesis, through E0's `skipSound_of_localOrEmpty`: a nonempty
footprint is handled by `PropLocalOne`, an empty footprint by
`skipSoundOn_nil` (its transition premise forces equal domain lists). -/
theorem skipsStableAll_of_propLocal {original : List Clause} {props : List Propagator}
    {db : List Clause} (hloc : PropLocal props) :
    SkipsStableAll original props db :=
  fun p hp f g => skipSound_of_localOrEmpty p (fun hne => hloc p hp hne)

/-- Restrict `SkipsStableAll` to a member. -/
theorem SkipsStableAll.mem {original props db} (h : SkipsStableAll original props db)
    {p : Propagator} (hp : p ∈ props) {f g : BranchFrame} : SkipSound p f g :=
  h p hp f g

namespace Propagator

/-- Wrap a propagator with an audited footprint: the run is untouched, only
the subscription test changes. This is how a refined per-family footprint
(the linear families' audited slots) is consumed by the queue without
reopening any family obligation. -/
def withFootprint (p : Propagator) (fp : List Atom) : Propagator :=
  { p with watches := fp }

/-- The wrapped run is the original run. -/
theorem withFootprint_run {p : Propagator} {fp : List Atom} :
    (p.withFootprint fp).run = p.run := rfl

/-- The wrapper preserves and reflects the local-soundness obligation. -/
theorem skipSoundOn_iff_skipSound_withFootprint {p : Propagator} {fp : List Atom}
    {f g : BranchFrame} :
    SkipSoundOn fp p f g ↔ SkipSound (p.withFootprint fp) f g :=
  Iff.rfl

end Propagator

/-! ## 1. Event silence at a footprint: extraction algebra

`EventSilentOn ws f g` is E0's "every event of the transition is unsubscribed
by the footprint `ws`" premise. The lemmas below extract, from silence, the
per-slot DOMAIN equality and the POSITION agreement of the two domain lists,
and reconstruct silence from both. The position part is essential: the
truncation rules of `frameEventsAux` emit `replaced` at a watched slot even
between two empty domains, so stamp-style reasoning alone would be unsound
there. -/

/-- The event-silence premise of E0's `SkipSoundOn` for a footprint. -/
def EventSilentOn (ws : List Atom) (f g : BranchFrame) : Prop :=
  ∀ e ∈ frameEvents f g, PropagatorSubscribesOn ws e = false

/-- The event-silence premise at a propagator's declared footprint. -/
def EventSilent (p : Propagator) (f g : BranchFrame) : Prop :=
  EventSilentOn p.watches f g

/-- The footprint form is the propagator form (definitionally). -/
theorem eventSilent_iff {p : Propagator} {f g : BranchFrame} :
    EventSilent p f g ↔ ∀ e ∈ frameEvents f g, PropagatorSubscribes p e = false :=
  Iff.rfl

/-- An event at a footprint slot is subscribed. -/
theorem propagatorSubscribesOn_of_mem_slot {ws : List Atom} {e : DomainEvent}
    (h : ∃ a ∈ ws, a.slot = e.slot) : PropagatorSubscribesOn ws e = true := by
  cases hb : PropagatorSubscribesOn ws e with
  | true => rfl
  | false =>
      obtain ⟨-, hall⟩ := propagatorSubscribesOn_eq_false_iff.mp hb
      obtain ⟨a, ha, hslot⟩ := h
      exact absurd hslot (hall a ha)

/-- Event silence at a footprint forces the footprint slots' domains equal. -/
theorem getD_eq_of_eventSilentOn {ws : List Atom} {f g : BranchFrame}
    (h : EventSilentOn ws f g) {s : Nat} (hs : ∃ a ∈ ws, a.slot = s) :
    (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty :=
  domain_eq_of_eventSilent fun e he => by
    intro hslot
    have hfalse := h e he
    rw [propagatorSubscribesOn_of_mem_slot
      (by obtain ⟨a, ha, has⟩ := hs; exact ⟨a, ha, has.trans hslot.symm⟩)] at hfalse
    exact absurd hfalse (by simp)

/-- Every tail event sits at a position of the (one-sided) domain list. -/
theorem frameEventsTail_event_pos (s : Nat) :
    ∀ (es : List Domain) {e : DomainEvent}, e ∈ frameEventsTail s es →
      ∃ k, k < es.length ∧ e.slot = s + k := by
  intro es
  induction es generalizing s with
  | nil => intro e he; cases he
  | cons d es ih =>
      intro e he
      rw [show frameEventsTail s (d :: es) = ⟨s, .replaced⟩ :: frameEventsTail (s + 1) es
        from rfl] at he
      rcases List.mem_cons.mp he with rfl | he
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨k, hk, hslot⟩ := ih (s + 1) he
        exact ⟨k + 1, by simpa using hk, by rw [hslot]; omega⟩

/-- Every position of a domain list carries a tail event. -/
theorem frameEventsTail_exists_event (s : Nat) :
    ∀ (es : List Domain) {k : Nat}, k < es.length →
      ∃ e ∈ frameEventsTail s es, e.slot = s + k := by
  intro es
  induction es generalizing s with
  | nil => intro k hk; simp at hk
  | cons d es ih =>
      intro k hk
      cases k with
      | zero => exact ⟨⟨s, .replaced⟩, by simp [frameEventsTail], by simp⟩
      | succ k =>
          obtain ⟨e, he, hslot⟩ := ih (s + 1) (by simpa using hk)
          exact ⟨e, by simp [frameEventsTail, he], by rw [hslot]; omega⟩

/-- Truncation completeness (left side): a position present on the left but
beyond the right list carries an event, even when its domain is empty. -/
theorem frameEventsAux_truncated_left (s : Nat) :
    ∀ (ds es : List Domain) {i : Nat}, i < ds.length → es.length ≤ i →
      ∃ e ∈ frameEventsAux s ds es, e.slot = s + i := by
  intro ds
  induction ds generalizing s with
  | nil => intro es i hi _; simp at hi
  | cons d ds ih =>
      intro es i hi hle
      cases es with
      | nil => exact frameEventsTail_exists_event s (d :: ds) hi
      | cons e es =>
          cases i with
          | zero => simp at hle
          | succ i =>
              obtain ⟨ev, hev, hslot⟩ := ih (s + 1) es (by simpa using hi)
                (by simpa using hle)
              exact ⟨ev, by simp only [frameEventsAux]; exact List.mem_append_right _ hev,
                by rw [hslot]; omega⟩

/-- Truncation completeness (right side). -/
theorem frameEventsAux_truncated_right (s : Nat) :
    ∀ (ds es : List Domain) {i : Nat}, i < es.length → ds.length ≤ i →
      ∃ e ∈ frameEventsAux s ds es, e.slot = s + i := by
  intro ds
  induction ds generalizing s with
  | nil =>
      intro es i hi hle
      cases es with
      | nil => simp at hi
      | cons d es => exact frameEventsTail_exists_event s (d :: es) hi
  | cons d ds ih =>
      intro es i hi hle
      cases es with
      | nil => simp at hi
      | cons e es =>
          cases i with
          | zero => simp at hle
          | succ i =>
              obtain ⟨ev, hev, hslot⟩ := ih (s + 1) es (by simpa using hi)
                (by simpa using hle)
              exact ⟨ev, by simp only [frameEventsAux]; exact List.mem_append_right _ hev,
                by rw [hslot]; omega⟩

/-- Event silence at a footprint also forces position agreement: a watched
slot cannot be present on one side and truncated away on the other. -/
theorem length_lt_iff_of_eventSilentOn {ws : List Atom} {f g : BranchFrame}
    (h : EventSilentOn ws f g) {s : Nat} (hs : ∃ a ∈ ws, a.slot = s) :
    s < (Frame.domains f).length ↔ s < (Frame.domains g).length := by
  constructor
  · intro hf
    by_cases hg : s < (Frame.domains g).length
    · exact hg
    · exfalso
      have hle : (Frame.domains g).length ≤ s := by omega
      obtain ⟨e, he, hslot⟩ :=
        frameEventsAux_truncated_left 0 (Frame.domains f) (Frame.domains g) hf hle
      have hfalse := h e he
      rw [propagatorSubscribesOn_of_mem_slot
        (by obtain ⟨a, ha, has⟩ := hs; exact ⟨a, ha, by rw [hslot]; simpa using has⟩)]
        at hfalse
      exact absurd hfalse (by simp)
  · intro hg
    by_cases hf : s < (Frame.domains f).length
    · exact hf
    · exfalso
      have hle : (Frame.domains f).length ≤ s := by omega
      obtain ⟨e, he, hslot⟩ :=
        frameEventsAux_truncated_right 0 (Frame.domains f) (Frame.domains g) hg hle
      have hfalse := h e he
      rw [propagatorSubscribesOn_of_mem_slot
        (by obtain ⟨a, ha, has⟩ := hs; exact ⟨a, ha, by rw [hslot]; simpa using has⟩)]
        at hfalse
      exact absurd hfalse (by simp)

/-- Slot agreement (domain equality plus position agreement) at every
footprint slot reconstructs event silence. -/
theorem frameEventsAux_unsubscribed_of_agree (ws : List Atom) (hne : ws ≠ [])
    (s0 : Nat) :
    ∀ (ds es : List Domain),
      (∀ j, (∃ a ∈ ws, a.slot = s0 + j) →
        ds.getD j Dom.empty = es.getD j Dom.empty ∧ (j < ds.length ↔ j < es.length)) →
      ∀ e ∈ frameEventsAux s0 ds es, PropagatorSubscribesOn ws e = false := by
  intro ds
  induction ds generalizing s0 with
  | nil =>
      intro es hagree e he
      cases es with
      | nil => cases he
      | cons d es =>
          rw [propagatorSubscribesOn_eq_false_iff]
          refine ⟨hne, ?_⟩
          intro a ha hsloteq
          obtain ⟨k, hk, hslot⟩ := frameEventsTail_event_pos s0 (d :: es) he
          have hmem : ∃ a' ∈ ws, a'.slot = s0 + k := ⟨a, ha, hsloteq.trans hslot⟩
          exact absurd ((hagree k hmem).2.mpr hk) (Nat.not_lt_zero k)
  | cons d ds ih =>
      intro es hagree e he
      cases es with
      | nil =>
          rw [propagatorSubscribesOn_eq_false_iff]
          refine ⟨hne, ?_⟩
          intro a ha hsloteq
          obtain ⟨k, hk, hslot⟩ := frameEventsTail_event_pos s0 (d :: ds) he
          have hmem : ∃ a' ∈ ws, a'.slot = s0 + k := ⟨a, ha, hsloteq.trans hslot⟩
          exact absurd ((hagree k hmem).2.mp hk) (Nat.not_lt_zero k)
      | cons e' es =>
          rw [show frameEventsAux s0 (d :: ds) (e' :: es)
                = slotEvents s0 d e' ++ frameEventsAux (s0 + 1) ds es from rfl] at he
          rcases List.mem_append.mp he with he | he
          · rw [propagatorSubscribesOn_eq_false_iff]
            refine ⟨hne, ?_⟩
            intro a ha hsloteq
            have hslot : e.slot = s0 := mem_slotEvents_slot he
            have hmem : ∃ a' ∈ ws, a'.slot = s0 + 0 := ⟨a, ha, hsloteq.trans hslot⟩
            have hd : d = e' := by
              have := (hagree 0 hmem).1
              simpa using this
            have hnil : slotEvents s0 d d = [] := (slotEvents_nil_iff s0 d d).mpr rfl
            rw [← hd] at he
            rw [hnil] at he
            cases he
          · refine ih (s0 + 1) es (fun j hj => ?_) e he
            have heq : s0 + (j + 1) = (s0 + 1) + j := by omega
            have h0 := hagree (j + 1) (by simpa [heq] using hj)
            exact ⟨by simpa using h0.1, by simpa using h0.2⟩

/-- Silence at a NONEMPTY footprint follows from per-slot domain equality
and position agreement. -/
theorem eventSilentOn_of_agree {ws : List Atom} (hne : ws ≠ [])
    {f g : BranchFrame}
    (hgetD : ∀ s, (∃ a ∈ ws, a.slot = s) →
      (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty)
    (hlen : ∀ s, (∃ a ∈ ws, a.slot = s) →
      (s < (Frame.domains f).length ↔ s < (Frame.domains g).length)) :
    EventSilentOn ws f g :=
  frameEventsAux_unsubscribed_of_agree ws hne 0 (Frame.domains f) (Frame.domains g)
    (fun j hj => ⟨hgetD j (by simpa using hj), hlen j (by simpa using hj)⟩)

/-- **EVENT SILENCE IS TRANSITIVE**: a transition composed of two silent
transitions is silent. This is what lets a clean queue unit stay certified
across a frame move that did not enqueue it. -/
theorem eventSilentOn_trans {ws : List Atom} {f g h : BranchFrame}
    (hfg : EventSilentOn ws f g) (hgh : EventSilentOn ws g h) :
    EventSilentOn ws f h := by
  by_cases hne : ws = []
  · have h1 : frameEvents f g = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      have hc := hfg e he
      rw [hne] at hc
      simp [PropagatorSubscribesOn] at hc
    have h2 : frameEvents g h = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro e he
      have hc := hgh e he
      rw [hne] at hc
      simp [PropagatorSubscribesOn] at hc
    have hd : Frame.domains f = Frame.domains h :=
      (frameEvents_nil_iff.mp h1).trans (frameEvents_nil_iff.mp h2)
    have h3 : frameEvents f h = [] := frameEvents_nil_iff.mpr hd
    intro e he
    rw [h3] at he
    cases he
  · exact eventSilentOn_of_agree hne
      (fun s hs =>
        (getD_eq_of_eventSilentOn hfg hs).trans (getD_eq_of_eventSilentOn hgh hs))
      (fun s hs =>
        (length_lt_iff_of_eventSilentOn hfg hs).trans (length_lt_iff_of_eventSilentOn hgh hs))

/-- Transitivity at a propagator's declared footprint. -/
theorem EventSilent.trans {p : Propagator} {f g h : BranchFrame}
    (hfg : EventSilent p f g) (hgh : EventSilent p g h) : EventSilent p f h :=
  eventSilentOn_trans hfg hgh

/-- Same-frame silence is automatic. -/
theorem eventSilent_self (p : Propagator) (f : BranchFrame) : EventSilent p f f := by
  intro e he
  rw [frameEvents_nil_iff.mpr rfl] at he
  cases he

/-- An event-silent transition at the empty footprint is event-free. -/
theorem frameEvents_nil_of_eventSilentOn_nil {f g : BranchFrame}
    (h : EventSilentOn [] f g) : frameEvents f g = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro e he
  have hc := h e he
  simp [PropagatorSubscribesOn] at hc

/-! ## 2. The queue state and its operations

The carrier (`WorkQueue`) and the invariant predicates (`QueueQuiet`,
`QueueShape`, `QueueRecords`, `QueueCovered`, `QueueOK`) are declared in
`ScheduledPropagation.lean` so the runtime dispatcher can thread them through
`PropScheduler` without an import cycle; this section defines the operations
and the certified algebra over them. -/

/-- Watch-projection agreement from pointwise `getD` agreement. -/
theorem watchStamp_eq_of_getD {ws : List Atom} {f g : BranchFrame}
    (h : ∀ s, (∃ a ∈ ws, a.slot = s) →
      (Frame.domains f).getD s Dom.empty = (Frame.domains g).getD s Dom.empty) :
    watchStamp f ws = watchStamp g ws := by
  induction ws with
  | nil => rfl
  | cons a as ih =>
      simp only [watchStamp, List.map_cons, List.cons.injEq]
      refine ⟨h a.slot ⟨a, List.mem_cons_self .., rfl⟩, ih fun s hs => ?_⟩
      exact h s ⟨hs.choose, List.mem_cons_of_mem a hs.choose_spec.1, hs.choose_spec.2⟩

/-- Event silence at a footprint forces watch-projection agreement. -/
theorem watchStamp_eq_of_eventSilentOn {ws : List Atom} {f g : BranchFrame}
    (h : EventSilentOn ws f g) : watchStamp f ws = watchStamp g ws :=
  watchStamp_eq_of_getD fun _s hs => getD_eq_of_eventSilentOn h hs

/-- Event silence at a footprint implies the E0-free queue certificate: on a
nonempty footprint at least the watch projection is unchanged, and on an
empty footprint the whole domain list is unchanged (`frameEvents` is empty
exactly then). -/
theorem watchQuietOn_of_eventSilentOn {ws : List Atom} {f g : BranchFrame}
    (h : EventSilentOn ws f g) :
    (ws = [] ∧ Frame.domains f = Frame.domains g) ∨
      (ws ≠ [] ∧ watchStamp f ws = watchStamp g ws) := by
  by_cases hne : ws = []
  · refine Or.inl ⟨hne, ?_⟩
    subst hne
    exact frameEvents_nil_iff.mp (frameEvents_nil_of_eventSilentOn_nil h)
  · exact Or.inr ⟨hne, watchStamp_eq_of_eventSilentOn h⟩

/-- The certificate of a propagator, in `Propagator` form. -/
theorem eventSilent_imp_quiet {p : Propagator} {f g : BranchFrame}
    (h : EventSilent p f g) : QueueQuiet p f g :=
  watchQuietOn_of_eventSilentOn h

/-- Certificate transitivity: a transition composed of two quiet transitions
is quiet. -/
theorem QueueQuiet.trans {p : Propagator} {f g h : BranchFrame}
    (hfg : QueueQuiet p f g) (hgh : QueueQuiet p g h) : QueueQuiet p f h := by
  by_cases hne : p.watches = []
  · rcases hfg with ⟨-, h1⟩ | ⟨h2, -⟩
    · rcases hgh with ⟨-, h2⟩ | ⟨h3, -⟩
      · exact Or.inl ⟨hne, h1.trans h2⟩
      · exact absurd hne h3
    · exact absurd hne h2
  · rcases hfg with ⟨h1, -⟩ | ⟨-, h1⟩
    · exact absurd h1 hne
    · rcases hgh with ⟨h2, -⟩ | ⟨-, h2⟩
      · exact absurd h2 hne
      · exact Or.inr ⟨hne, h1.trans h2⟩

/-- Certificates are reflexive. -/
theorem QueueQuiet.refl (p : Propagator) (f : BranchFrame) : QueueQuiet p f f := by
  by_cases hne : p.watches = []
  · exact Or.inl ⟨hne, rfl⟩
  · exact Or.inr ⟨hne, rfl⟩

namespace WorkQueue

/-- Deduplicated single-unit enqueue. -/
def enqueue (q : WorkQueue) (i : Nat) : WorkQueue :=
  if q.pending.contains i then q else { q with pending := q.pending ++ [i] }

theorem enqueue_seen (q : WorkQueue) (i : Nat) : (q.enqueue i).seen = q.seen := by
  unfold enqueue
  split <;> rfl

theorem mem_enqueue {q : WorkQueue} {i j : Nat} :
    j ∈ (q.enqueue i).pending ↔ j = i ∨ j ∈ q.pending := by
  unfold enqueue
  split
  · rename_i hc
    have hi : i ∈ q.pending := List.contains_iff_mem.mp hc
    constructor
    · exact fun hj => Or.inr hj
    · rintro (rfl | hj)
      · exact hi
      · exact hj
  · constructor
    · intro hj
      rcases List.mem_append.mp hj with hj | hj
      · exact Or.inr hj
      · exact Or.inl (List.mem_singleton.mp hj)
    · rintro (rfl | hj)
      · exact List.mem_append_right _ (by simp)
      · exact List.mem_append_left _ hj

theorem enqueue_mem (q : WorkQueue) (i : Nat) : i ∈ (q.enqueue i).pending :=
  (mem_enqueue (q := q) (i := i) (j := i)).mpr (Or.inl rfl)

theorem mem_of_mem_enqueue {q : WorkQueue} {i j : Nat} (h : j ∈ q.pending) :
    j ∈ (q.enqueue i).pending :=
  (mem_enqueue (q := q) (i := i) (j := j)).mpr (Or.inr h)

theorem enqueue_nodup {q : WorkQueue} {i : Nat} (h : q.pending.Nodup) :
    (q.enqueue i).pending.Nodup := by
  unfold enqueue
  split
  · exact h
  · rename_i hc
    have hi : i ∉ q.pending := fun hi => hc (List.contains_iff_mem.mpr hi)
    refine List.nodup_append.mpr ⟨h, by simp, ?_⟩
    intro a ha b hb
    obtain rfl := List.mem_singleton.mp hb
    intro heq
    exact hi (heq ▸ ha)

theorem enqueue_bounds {q : WorkQueue} {i n : Nat} (hi : i < n)
    (hq : ∀ j ∈ q.pending, j < n) : ∀ j ∈ (q.enqueue i).pending, j < n := by
  intro j hj
  rcases (mem_enqueue (q := q) (i := i) (j := j)).mp hj with rfl | hj
  · exact hi
  · exact hq j hj

/-- Enqueue every index of a list, deduplicated. -/
def enqueueAllFrom (q : WorkQueue) : List Nat → WorkQueue
  | [] => q
  | i :: is => enqueueAllFrom (q.enqueue i) is

theorem enqueueAllFrom_seen (q : WorkQueue) (is : List Nat) :
    (q.enqueueAllFrom is).seen = q.seen := by
  induction is generalizing q with
  | nil => simp [enqueueAllFrom]
  | cons i is ih =>
      simp only [enqueueAllFrom]
      rw [ih (q := q.enqueue i), enqueue_seen]

theorem mem_enqueueAllFrom {q : WorkQueue} {is : List Nat} {j : Nat} :
    j ∈ (q.enqueueAllFrom is).pending ↔ j ∈ q.pending ∨ j ∈ is := by
  induction is generalizing q with
  | nil => simp [enqueueAllFrom]
  | cons i is ih =>
      simp only [enqueueAllFrom]
      rw [ih (q := q.enqueue i), mem_enqueue]
      constructor
      · rintro ((heq | hj) | hj)
        · subst heq; exact Or.inr (List.mem_cons_self ..)
        · exact Or.inl hj
        · exact Or.inr (List.mem_cons_of_mem _ hj)
      · rintro (hj | hj)
        · exact Or.inl (Or.inr hj)
        · rcases List.mem_cons.mp hj with rfl | hj
          · exact Or.inl (Or.inl rfl)
          · exact Or.inr hj

theorem enqueueAllFrom_nodup {q : WorkQueue} {is : List Nat} (h : q.pending.Nodup) :
    (q.enqueueAllFrom is).pending.Nodup := by
  induction is generalizing q with
  | nil => simpa [enqueueAllFrom] using h
  | cons i is ih =>
      simp only [enqueueAllFrom]
      exact ih (enqueue_nodup h)

theorem enqueueAllFrom_bounds {q : WorkQueue} {is : List Nat} {n : Nat}
    (hq : ∀ j ∈ q.pending, j < n) (his : ∀ j ∈ is, j < n) :
    ∀ j ∈ (q.enqueueAllFrom is).pending, j < n := by
  induction is generalizing q with
  | nil => simpa [enqueueAllFrom] using hq
  | cons i is ih =>
      simp only [enqueueAllFrom]
      refine ih (q := q.enqueue i)
        (enqueue_bounds (his i (List.mem_cons_self ..)) hq)
        (fun j hj => his j (List.mem_cons_of_mem _ hj))

/-- Learned clause / new generic work: queue every unit. -/
def enqueueAll (q : WorkQueue) (props : List Propagator) : WorkQueue :=
  q.enqueueAllFrom (List.range props.length)

theorem enqueueAll_seen (q : WorkQueue) (props : List Propagator) :
    (q.enqueueAll props).seen = q.seen :=
  enqueueAllFrom_seen q (List.range props.length)

theorem mem_enqueueAll {q : WorkQueue} {props : List Propagator} {j : Nat} :
    j ∈ (q.enqueueAll props).pending ↔ j ∈ q.pending ∨ j < props.length := by
  rw [enqueueAll, mem_enqueueAllFrom, List.mem_range]

/-- One unit's transition enqueue at a PRECOMPUTED event list: when the unit
subscribes to some produced event it is added (deduplicated); otherwise it is
untouched. Taking the events as an argument keeps the extraction O(mass) once
per transition instead of once per unit. -/
def enqueueEventsUnit (q : WorkQueue) (props : List Propagator)
    (events : List DomainEvent) (i : Nat) : WorkQueue :=
  match props[i]? with
  | some p => if events.any (PropagatorSubscribes p) then q.enqueue i else q
  | none => q

theorem enqueueEventsUnit_seen (q props events i) :
    (enqueueEventsUnit q props events i).seen = q.seen := by
  unfold enqueueEventsUnit
  split
  · split
    · exact enqueue_seen q i
    · rfl
  · rfl

theorem enqueueEventsUnit_mono (q : WorkQueue) (props : List Propagator)
    (events : List DomainEvent) (i : Nat) :
    ∀ j ∈ q.pending, j ∈ (enqueueEventsUnit q props events i).pending := by
  intro j hj
  unfold enqueueEventsUnit
  split
  · split
    · exact mem_of_mem_enqueue hj
    · exact hj
  · exact hj

theorem enqueueEventsUnit_mem_self {q : WorkQueue} {props : List Propagator}
    {events : List DomainEvent} {i : Nat} {p : Propagator}
    (hp : props[i]? = some p)
    (hsub : events.any (PropagatorSubscribes p) = true) :
    i ∈ (enqueueEventsUnit q props events i).pending := by
  unfold enqueueEventsUnit
  rw [hp]
  dsimp only
  rw [if_pos hsub]
  exact enqueue_mem q i

theorem mem_enqueueEventsUnit_cases {q : WorkQueue} {props : List Propagator}
    {events : List DomainEvent} {i j : Nat}
    (h : j ∈ (enqueueEventsUnit q props events i).pending) :
    j ∈ q.pending ∨ j = i := by
  unfold enqueueEventsUnit at h
  split at h
  · split at h
    · rcases mem_enqueue.mp h with heq | hj
      · exact Or.inr heq
      · exact Or.inl hj
    · exact Or.inl h
  · exact Or.inl h

/-- The event-keyed transition enqueue at a precomputed event list. -/
def enqueueEventsFrom (q : WorkQueue) (props : List Propagator)
    (events : List DomainEvent) : List Nat → WorkQueue
  | [] => q
  | i :: is => enqueueEventsFrom (enqueueEventsUnit q props events i) props events is

theorem enqueueEventsFrom_seen (q : WorkQueue) (props : List Propagator)
    (events : List DomainEvent) (is : List Nat) :
    (enqueueEventsFrom q props events is).seen = q.seen := by
  induction is generalizing q with
  | nil => simp [enqueueEventsFrom]
  | cons i is ih =>
      simp only [enqueueEventsFrom]
      rw [ih (q := enqueueEventsUnit q props events i), enqueueEventsUnit_seen]

theorem enqueueEventsFrom_mono {q : WorkQueue} {props : List Propagator}
    {events : List DomainEvent} {is : List Nat} {j : Nat} (h : j ∈ q.pending) :
    j ∈ (enqueueEventsFrom q props events is).pending := by
  induction is generalizing q with
  | nil => simpa [enqueueEventsFrom] using h
  | cons i is ih =>
      simp only [enqueueEventsFrom]
      exact ih (enqueueEventsUnit_mono q props events i j h)

theorem mem_enqueueEventsFrom_cases {q : WorkQueue} {props : List Propagator}
    {events : List DomainEvent} {is : List Nat} {j : Nat}
    (h : j ∈ (enqueueEventsFrom q props events is).pending) :
    j ∈ q.pending ∨ j ∈ is := by
  induction is generalizing q with
  | nil => simpa [enqueueEventsFrom] using h
  | cons i is ih =>
      simp only [enqueueEventsFrom] at h
      rcases ih (q := enqueueEventsUnit q props events i) h with hq | his
      · rcases mem_enqueueEventsUnit_cases hq with hj | rfl
        · exact Or.inl hj
        · exact Or.inr (List.mem_cons_self ..)
      · exact Or.inr (List.mem_cons_of_mem _ his)

theorem enqueueEventsFrom_mem_of_subscribed {q : WorkQueue} {props : List Propagator}
    {events : List DomainEvent} {is : List Nat} {i : Nat} {p : Propagator}
    (hi : i ∈ is) (hp : props[i]? = some p)
    (hsub : events.any (PropagatorSubscribes p) = true) :
    i ∈ (enqueueEventsFrom q props events is).pending := by
  induction is generalizing q with
  | nil => cases hi
  | cons j js ih =>
      rcases List.mem_cons.mp hi with rfl | hi
      · exact enqueueEventsFrom_mono
          (q := enqueueEventsUnit q props events i) (enqueueEventsUnit_mem_self hp hsub)
      · simp only [enqueueEventsFrom]
        exact ih (q := enqueueEventsUnit q props events j) hi

theorem enqueueEventsFrom_nodup {q : WorkQueue} {props : List Propagator}
    {events : List DomainEvent} {is : List Nat} (h : q.pending.Nodup) :
    (enqueueEventsFrom q props events is).pending.Nodup := by
  induction is generalizing q with
  | nil => simpa [enqueueEventsFrom] using h
  | cons i is ih =>
      simp only [enqueueEventsFrom]
      refine ih ?_
      unfold enqueueEventsUnit
      split
      · split
        · exact enqueue_nodup h
        · exact h
      · exact h

theorem enqueueEventsFrom_bounds {q : WorkQueue} {props : List Propagator}
    {events : List DomainEvent} {is : List Nat} {n : Nat}
    (hq : ∀ j ∈ q.pending, j < n) (his : ∀ j ∈ is, j < n) :
    ∀ j ∈ (enqueueEventsFrom q props events is).pending, j < n := by
  induction is generalizing q with
  | nil => simpa [enqueueEventsFrom] using hq
  | cons i is ih =>
      simp only [enqueueEventsFrom]
      refine ih ?_ (fun j hj => his j (List.mem_cons_of_mem _ hj))
      intro j hj
      rcases mem_enqueueEventsUnit_cases hj with hj | heq
      · exact hq j hj
      · exact his j (by rw [heq]; exact List.mem_cons_self ..)

/-- The frame-transition enqueue over all registered units: the event list is
extracted ONCE from the two frames and the membership loop is pure index
bookkeeping plus one subscription test per unit. -/
def enqueueEvents (q : WorkQueue) (props : List Propagator)
    (old new : BranchFrame) : WorkQueue :=
  enqueueEventsFrom q props (frameEvents old new) (List.range props.length)

theorem enqueueEvents_seen (q : WorkQueue) (props : List Propagator)
    (old new : BranchFrame) :
    (q.enqueueEvents props old new).seen = q.seen :=
  enqueueEventsFrom_seen q props (frameEvents old new) (List.range props.length)

/-- The extraction is shared: `enqueueEvents` is the precomputed-list form at
`frameEvents old new`. -/
theorem enqueueEvents_eq_from {q : WorkQueue} {props : List Propagator}
    {old new : BranchFrame} :
    q.enqueueEvents props old new
      = enqueueEventsFrom q props (frameEvents old new) (List.range props.length) := rfl

/-- A unit that was NOT enqueued by a transition is event-silent for it
(contrapositive of `enqueueEventsFrom_mem_of_subscribed`). -/
theorem not_subscribed_of_not_mem_enqueueEvents {q : WorkQueue}
    {props : List Propagator} {old new : BranchFrame} {i : Nat} {p : Propagator}
    (hi : i < props.length) (hp : props[i]? = some p)
    (hnot : i ∉ (WorkQueue.enqueueEvents q props old new).pending) :
    (frameEvents old new).any (PropagatorSubscribes p) = false := by
  cases hb : (frameEvents old new).any (PropagatorSubscribes p) with
  | false => rfl
  | true =>
      exact absurd (enqueueEventsFrom_mem_of_subscribed
        (List.mem_range.mpr hi) hp hb) hnot

/-- Insert new propagators (appended after the current list): fresh record
slots, each new unit queued. The fresh indices are the mapped range
`q.seen.length, ..., q.seen.length + n - 1`, enqueued through the
deduplicating `enqueueAllFrom`. -/
def extendUnits (q : WorkQueue) (n : Nat) : WorkQueue :=
  { q.enqueueAllFrom ((List.range n).map (fun k => q.seen.length + k)) with
    seen := q.seen ++ List.replicate n none }

theorem extendUnits_seen (q : WorkQueue) (n : Nat) :
    (q.extendUnits n).seen = q.seen ++ List.replicate n none := rfl

theorem extendUnits_pending (q : WorkQueue) (n : Nat) :
    (q.extendUnits n).pending
      = (q.enqueueAllFrom ((List.range n).map (fun k => q.seen.length + k))).pending := rfl

theorem mem_extendUnits {q : WorkQueue} {n j : Nat} :
    j ∈ (q.extendUnits n).pending ↔
      j ∈ q.pending ∨ (q.seen.length ≤ j ∧ j < q.seen.length + n) := by
  rw [extendUnits_pending, mem_enqueueAllFrom]
  constructor
  · rintro (h | hmem)
    · exact Or.inl h
    · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hmem
      exact Or.inr ⟨Nat.le_add_right _ _, by have := List.mem_range.mp hk; omega⟩
  · rintro (h | ⟨hle, hlt⟩)
    · exact Or.inl h
    · exact Or.inr (List.mem_map.mpr
        ⟨j - q.seen.length, List.mem_range.mpr (by omega), by omega⟩)

theorem extendUnits_nodup {q : WorkQueue} {n : Nat} (h : q.pending.Nodup) :
    (q.extendUnits n).pending.Nodup := by
  rw [extendUnits_pending]
  exact enqueueAllFrom_nodup h

theorem extendUnits_bounds {q : WorkQueue} {n m : Nat}
    (h : ∀ j ∈ q.pending, j < m) (hm : q.seen.length + n ≤ m) :
    ∀ j ∈ (q.extendUnits n).pending, j < m := by
  rw [extendUnits_pending]
  refine enqueueAllFrom_bounds h ?_
  intro j hj
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hj
  have := List.mem_range.mp hk
  omega

end WorkQueue

/-! ## 3. Step, drain, and the record/replay functions -/

/-- What one `step` reports: which unit, its result, and whether the result
was actually recomputed (`reran = false` means the recorded result was reused
because the reference frame is event-silent). -/
structure StepOutcome where
  unit : Nat
  result : PropagationResult
  reran : Bool

/-- One step at the seen-list level: the pop itself is the caller's business;
this reads the record of unit `i` and produces the outcome together with the
updated records. When the recorded reference frame `f` is event-silent to
the current frame `g`, the recorded result `r` is reused (no run) and the
record is refreshed to `(g, r)`. -/
def stepSeenHead (g : BranchFrame) (i : Nat) (p : Propagator)
    (seen : List (Option (BranchFrame × PropagationResult)))
    (s : Option (Option (BranchFrame × PropagationResult))) :
    StepOutcome × List (Option (BranchFrame × PropagationResult)) :=
  match s with
  | none => (⟨i, p.run (frameState g), true⟩, seen.set i (some (g, p.run (frameState g))))
  | some none => (⟨i, p.run (frameState g), true⟩,
      seen.set i (some (g, p.run (frameState g))))
  | some (some (f, r)) =>
      if (frameEvents f g).all (fun e => !PropagatorSubscribes p e) then
        (⟨i, r, false⟩, seen.set i (some (g, r)))
      else
        (⟨i, p.run (frameState g), true⟩, seen.set i (some (g, p.run (frameState g))))

/-- The record-level step for unit `i` at frame `g`. -/
def stepSeen (props : List Propagator) (g : BranchFrame) (i : Nat)
    (seen : List (Option (BranchFrame × PropagationResult))) :
    StepOutcome × List (Option (BranchFrame × PropagationResult)) :=
  match props[i]? with
  | none => (⟨i, .stable, false⟩, seen)
  | some p => stepSeenHead g i p seen seen[i]?

/-- The updated records always rewrite position `i` with the outcome's result
at the current frame. -/
theorem stepSeenHead_seen (g : BranchFrame) (i : Nat) (p : Propagator)
    (seen : List (Option (BranchFrame × PropagationResult)))
    (s : Option (Option (BranchFrame × PropagationResult))) :
    (stepSeenHead g i p seen s).2
      = seen.set i (some (g, (stepSeenHead g i p seen s).1.result)) := by
  cases s with
  | none => rfl
  | some t =>
      cases t with
      | none => rfl
      | some fr =>
          obtain ⟨f, r⟩ := fr
          dsimp only [stepSeenHead]
          split <;> rfl

/-- **STEP SOUNDNESS (skip branch)**: when `step` reuses the recorded result,
the recorded reference frame is event-silent to the current frame and the
recorded result is exactly the recorded frame's result — the two facts E0's
`SkipSound` consumes to turn the reuse into the unit's current run. -/
theorem stepSeenHead_skip (g : BranchFrame) (i : Nat) (p : Propagator)
    (seen : List (Option (BranchFrame × PropagationResult)))
    (s : Option (Option (BranchFrame × PropagationResult)))
    (hskip : (stepSeenHead g i p seen s).1.reran = false) :
    ∃ f r, s = some (some (f, r)) ∧ (stepSeenHead g i p seen s).1.result = r ∧
      (∀ e ∈ frameEvents f g, PropagatorSubscribes p e = false) := by
  cases s with
  | none => cases hskip
  | some t =>
      cases t with
      | none => cases hskip
      | some fr =>
          obtain ⟨f, r⟩ := fr
          dsimp only [stepSeenHead] at hskip ⊢
          split
          · rename_i hall
            exact ⟨f, r, rfl, rfl, fun e he => by
              have h := List.all_eq_true.mp hall e he
              simpa using h⟩
          · rename_i hnot
            rw [if_neg hnot] at hskip
            cases hskip

/-- The outcome's result is the unit's run at the current frame, whichever
branch ran (the skip branch consumes `SkipSound` for the recorded pair). -/
theorem stepSeenHead_result_eq_run (g : BranchFrame) (i : Nat) (p : Propagator)
    (seen : List (Option (BranchFrame × PropagationResult)))
    (s : Option (Option (BranchFrame × PropagationResult)))
    (hrec : ∀ f r, s = some (some (f, r)) → r = p.run (frameState f))
    (hskip : ∀ f, SkipSound p f g) :
    p.run (frameState g) = (stepSeenHead g i p seen s).1.result := by
  cases s with
  | none => rfl
  | some t =>
      cases t with
      | none => rfl
      | some fr =>
          obtain ⟨f, r⟩ := fr
          dsimp only [stepSeenHead]
          split
          · rename_i hall
            have hsil : ∀ e ∈ frameEvents f g, PropagatorSubscribes p e = false := by
              intro e he
              have h := List.all_eq_true.mp hall e he
              simpa using h
            rw [hskip f hsil, hrec f r rfl]
          · rfl

/-- Indexed form of the `stepSeenHead` equation. -/
theorem stepSeen_of_some {props : List Propagator} {g : BranchFrame} {i : Nat}
    {seen : List (Option (BranchFrame × PropagationResult))} {p : Propagator}
    (hp : props[i]? = some p) :
    stepSeen props g i seen = stepSeenHead g i p seen seen[i]? := by
  rw [stepSeen.eq_1, hp]

/-- The head step reports the index it was called with. -/
theorem stepSeenHead_unit (g : BranchFrame) (i : Nat) (p : Propagator)
    (seen : List (Option (BranchFrame × PropagationResult)))
    (s : Option (Option (BranchFrame × PropagationResult))) :
    (stepSeenHead g i p seen s).1.unit = i := by
  cases s with
  | none => rfl
  | some t =>
      cases t with
      | none => rfl
      | some fr =>
          obtain ⟨f, r⟩ := fr
          dsimp only [stepSeenHead]
          split <;> rfl

/-- The step reports the unit index it was called with. -/
theorem stepSeen_unit (props : List Propagator) (g : BranchFrame) (i : Nat)
    (seen : List (Option (BranchFrame × PropagationResult))) :
    (stepSeen props g i seen).1.unit = i := by
  cases hsp : props[i]? with
  | none => rw [stepSeen.eq_1, hsp]
  | some p => rw [stepSeen_of_some hsp]; exact stepSeenHead_unit g i p seen seen[i]?

/-- Indexed form of the record rewrite. -/
theorem stepSeen_seen {props : List Propagator} {g : BranchFrame} {i : Nat}
    {seen : List (Option (BranchFrame × PropagationResult))} {p : Propagator}
    (hp : props[i]? = some p) :
    (stepSeen props g i seen).2
      = seen.set i (some (g, (stepSeen props g i seen).1.result)) := by
  rw [stepSeen_of_some hp, stepSeenHead_seen]

/-- The `stepSeen`-level run equality. -/
theorem stepSeen_result_eq_run {props : List Propagator} {g : BranchFrame} {i : Nat}
    {seen : List (Option (BranchFrame × PropagationResult))} {p : Propagator}
    (hp : props[i]? = some p)
    (hrec : ∀ f r, seen[i]? = some (some (f, r)) → r = p.run (frameState f))
    (hskip : ∀ f, SkipSound p f g) :
    p.run (frameState g) = (stepSeen props g i seen).1.result := by
  rw [stepSeen_of_some hp]
  exact stepSeenHead_result_eq_run g i p seen seen[i]? hrec hskip

/-- The skip-branch statement at the indexed level. -/
theorem stepSeen_skip {props : List Propagator} {g : BranchFrame} {i : Nat}
    {seen : List (Option (BranchFrame × PropagationResult))} {p : Propagator}
    (hp : props[i]? = some p)
    (hskip : (stepSeen props g i seen).1.reran = false) :
    ∃ f r, seen[i]? = some (some (f, r)) ∧ (stepSeen props g i seen).1.result = r ∧
      (∀ e ∈ frameEvents f g, PropagatorSubscribes p e = false) := by
  rw [stepSeen_of_some hp] at hskip ⊢
  exact stepSeenHead_skip g i p seen seen[i]? hskip

/-- Records are write-once per step and never change length. -/
theorem stepSeen_length (props : List Propagator) (g : BranchFrame) (i : Nat)
    (seen : List (Option (BranchFrame × PropagationResult))) :
    (stepSeen props g i seen).2.length = seen.length := by
  cases hsp : props[i]? with
  | none => rw [stepSeen.eq_1, hsp]
  | some p =>
      rw [stepSeen_of_some hsp, stepSeenHead_seen]
      exact List.length_set

/-- The record of the stepped unit, read back. -/
theorem stepSeen_record_self {props : List Propagator} {g : BranchFrame} {i : Nat}
    {seen : List (Option (BranchFrame × PropagationResult))} {p : Propagator}
    (hp : props[i]? = some p) (hlen : i < seen.length) :
    (stepSeen props g i seen).2[i]?
      = some (some (g, (stepSeen props g i seen).1.result)) := by
  rw [stepSeen_of_some hp, stepSeenHead_seen]
  exact List.getElem?_set_self hlen

namespace WorkQueue

/-- Pop one unit and record its result at the current frame. `none` exactly
when the queue is empty. -/
def step (q : WorkQueue) (g : BranchFrame) (props : List Propagator) :
    Option (StepOutcome × WorkQueue) :=
  match q.pending with
  | [] => none
  | i :: rest =>
      let o := stepSeen props g i q.seen
      some (o.1, { seen := o.2, pending := rest })

theorem step_none_iff (q : WorkQueue) (g : BranchFrame) (props : List Propagator) :
    q.step g props = none ↔ q.pending = [] := by
  cases h : q.pending with
  | nil => simp [step.eq_1, h]
  | cons i rest => simp [step.eq_1, h]

theorem step_cons (q : WorkQueue) (g : BranchFrame) (props : List Propagator)
    {i : Nat} {rest : List Nat} (h : q.pending = i :: rest) :
    q.step g props = some ((stepSeen props g i q.seen).1,
      { seen := (stepSeen props g i q.seen).2, pending := rest }) := by
  simp only [step.eq_1, h]

theorem step_pending_eq {q : WorkQueue} {g : BranchFrame} {props : List Propagator}
    {o : StepOutcome} {q' : WorkQueue} (hstep : q.step g props = some (o, q')) :
    q'.pending = q.pending.tail := by
  cases h : q.pending with
  | nil =>
      rw [(step_none_iff q g props).mpr h] at hstep
      cases hstep
  | cons i rest =>
      rw [step_cons q g props h] at hstep
      cases hstep
      rfl

theorem step_seen_length {q : WorkQueue} {g : BranchFrame} {props : List Propagator}
    {o : StepOutcome} {q' : WorkQueue} (hstep : q.step g props = some (o, q')) :
    q'.seen.length = q.seen.length := by
  cases h : q.pending with
  | nil =>
      rw [(step_none_iff q g props).mpr h] at hstep
      cases hstep
  | cons i rest =>
      rw [step_cons q g props h] at hstep
      cases hstep
      exact stepSeen_length props g i q.seen

/-- **PROGRESS**: every `step` strictly decreases `queueMeasure`. -/
theorem step_measure_lt {q : WorkQueue} {g : BranchFrame} {props : List Propagator}
    {o : StepOutcome} {q' : WorkQueue} (hstep : q.step g props = some (o, q')) :
    queueMeasure q' < queueMeasure q := by
  have hp := step_pending_eq hstep
  unfold queueMeasure
  rw [hp]
  cases h : q.pending with
  | nil =>
      rw [(step_none_iff q g props).mpr h] at hstep
      cases hstep
  | cons i rest => simp only [List.tail_cons, List.length_cons]; omega

/-- The record-level drain: consume the pending list structurally, stepping
each unit at the current frame. No fuel, no `partial`; the pending list is
the structural measure. -/
def drainSeen (props : List Propagator) (g : BranchFrame) :
    List (Option (BranchFrame × PropagationResult)) → List Nat →
      List (Option (BranchFrame × PropagationResult))
  | seen, [] => seen
  | seen, i :: rest => drainSeen props g (stepSeen props g i seen).2 rest

/-- Drain the whole queue at the current frame. -/
def drain (q : WorkQueue) (g : BranchFrame) (props : List Propagator) : WorkQueue :=
  { seen := drainSeen props g q.seen q.pending, pending := [] }

theorem drain_pending (q : WorkQueue) (g : BranchFrame) (props : List Propagator) :
    (q.drain g props).pending = [] := rfl

theorem drain_seen (q : WorkQueue) (g : BranchFrame) (props : List Propagator) :
    (q.drain g props).seen = drainSeen props g q.seen q.pending := rfl

theorem drainSeen_length (props : List Propagator) (g : BranchFrame) :
    ∀ (seen : List (Option (BranchFrame × PropagationResult))) (is : List Nat),
      (drainSeen props g seen is).length = seen.length := by
  intro seen is
  induction is generalizing seen with
  | nil => simp [drainSeen]
  | cons i rest ih =>
      simp only [drainSeen]
      rw [ih, stepSeen_length]

end WorkQueue

/-! ## 4. The queue invariant: certificate algebra

The invariant predicates themselves (`QueueQuiet`, `QueueShape`,
`QueueRecords`, `QueueCovered`, `QueueOK`) live in
`ScheduledPropagation.lean` (the dispatcher thread needs them without an
import cycle). This section proves the certificate arithmetic the invariant's
preservation consumes. -/

/-- **PROVABLY UNCHANGED (clean unit)**: a non-pending covered unit's current
run is exactly its recorded result. On an empty footprint the whole domain
list agrees (`frameState` is equal); on a nonempty footprint the watch
projection agrees and the registered locality `PropLocalOne` applies. -/
theorem QueueCovered.run_eq_of_clean {props q g} (hrec : QueueRecords props q)
    (hcov : QueueCovered props q g) (hloc : PropLocal props)
    {i : Nat} {p : Propagator} {f : BranchFrame} {r : PropagationResult}
    (hp : props[i]? = some p) (hnot : i ∉ q.pending)
    (hseen : q.seen[i]? = some (some (f, r))) :
    p.run (frameState g) = r := by
  rcases hcov i p hp with hpend | ⟨f', r', hseen', hquiet⟩
  · exact absurd hpend hnot
  · have hpair : (f, r) = (f', r') := by
      rw [hseen] at hseen'
      exact Option.some.inj (Option.some.inj hseen')
    obtain ⟨hfeq, hreq⟩ := Prod.ext_iff.mp hpair
    subst hfeq
    subst hreq
    have hrun : p.run (frameState g) = p.run (frameState f) := by
      rcases hquiet with ⟨-, hdom⟩ | ⟨hne, hstamp⟩
      · have hfs : frameState f = frameState g := by simp only [frameState, hdom]
        rw [hfs]
      · exact (hloc p (List.mem_of_getElem? hp) hne f g hstamp).symm
    exact hrun.trans (hrec i p f r hp hseen).symm

/-- **POSSIBLY-PRODUCTIVE MEANS QUEUED**: if a unit's recorded result is not
its current run, the unit is in the queue. -/
theorem QueueCovered.mem_pending_of_run_ne {props q g} (hrec : QueueRecords props q)
    (hcov : QueueCovered props q g) (hloc : PropLocal props)
    {i : Nat} {p : Propagator} {f : BranchFrame} {r : PropagationResult}
    (hp : props[i]? = some p) (hseen : q.seen[i]? = some (some (f, r)))
    (hne : p.run (frameState g) ≠ r) : i ∈ q.pending := by
  by_cases hmem : i ∈ q.pending
  · exact hmem
  · exact absurd (QueueCovered.run_eq_of_clean hrec hcov hloc hp hmem hseen) hne

/-! ## 5. Preservation of the invariant -/

/-- **PRESERVATION (frame transition)**: `enqueueEvents` re-establishes
coverage at the new frame. Clean units stay certified by transitivity of the
quiet certificate (via event silence of the un-enqueued units); no locality is
consumed here. -/
theorem QueueOK_enqueueEvents {props : List Propagator} {q : WorkQueue}
    {g g' : BranchFrame} (hok : QueueOK props q g) :
    QueueOK props (q.enqueueEvents props g g') g' := by
  obtain ⟨⟨hlen, hnd, hbnd⟩, hrec, hcov⟩ := hok
  have hseen : (q.enqueueEvents props g g').seen = q.seen :=
    WorkQueue.enqueueEvents_seen q props g g'
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hseen]; exact hlen
  · exact WorkQueue.enqueueEventsFrom_nodup hnd
  · intro j hj
    exact WorkQueue.enqueueEventsFrom_bounds hbnd (fun j hj => List.mem_range.mp hj) j hj
  · intro i p f r hp hseenj
    rw [hseen] at hseenj
    exact hrec i p f r hp hseenj
  · intro i p hp
    by_cases hmem : i ∈ (q.enqueueEvents props g g').pending
    · exact Or.inl hmem
    · rcases hcov i p hp with hpend | ⟨f, r, hseeni, hquiet⟩
      · exact absurd (WorkQueue.enqueueEventsFrom_mono hpend) hmem
      · have hnotsub := WorkQueue.not_subscribed_of_not_mem_enqueueEvents
          (List.getElem?_eq_some_iff.mp hp).1 hp hmem
        have hsil' : EventSilent p g g' := fun e he => by
          change PropagatorSubscribes p e = false
          have h := List.any_eq_false.mp hnotsub e he
          cases hb : PropagatorSubscribes p e with
          | false => rfl
          | true => exact absurd hb h
        refine Or.inr ⟨f, r, ?_, hquiet.trans (eventSilent_imp_quiet hsil')⟩
        rw [hseen]
        exact hseeni

/-- **PRESERVATION (pop/step)**: the popped unit is covered by its fresh
record at the current frame; every other unit is untouched. -/
theorem QueueOK_step {props : List Propagator} {q : WorkQueue} {g : BranchFrame}
    {o : StepOutcome} {q' : WorkQueue} (hok : QueueOK props q g)
    (hstable : SkipsStableAll original props db) (hstep : q.step g props = some (o, q')) :
    QueueOK props q' g := by
  obtain ⟨⟨hlen, hnd, hbnd⟩, hrec, hcov⟩ := hok
  cases h : q.pending with
  | nil =>
      rw [(WorkQueue.step_none_iff q g props).mpr h] at hstep
      cases hstep
  | cons i rest =>
      rw [WorkQueue.step_cons q g props h] at hstep
      cases hstep
      have hi_lt : i < props.length := hbnd i (by rw [h]; exact List.mem_cons_self ..)
      obtain ⟨p0, hp0⟩ : ∃ p0 : Propagator, props[i]? = some p0 :=
        ⟨props[i], List.getElem?_eq_getElem hi_lt⟩
      have hseen_i := stepSeen_seen (props := props) (g := g) (i := i) (seen := q.seen)
        (p := p0) hp0
      have hrun_i := stepSeen_result_eq_run (props := props) (g := g) (i := i)
        (seen := q.seen) (p := p0) hp0
        (fun f r hseen => hrec i p0 f r hp0 hseen)
        (fun f => hstable p0 (List.mem_of_getElem? hp0) f g)
      refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
      · rw [stepSeen_length]; exact hlen
      · rw [h] at hnd
        exact (List.nodup_cons.mp hnd).2
      · intro j hj
        exact hbnd j (by rw [h]; exact List.mem_cons_of_mem i hj)
      · intro j p f r hp hseenj
        have hlenj : j < q.seen.length := by
          have := (List.getElem?_eq_some_iff.mp hp).1
          omega
        by_cases hji : j = i
        · rw [hji] at hp hlenj hseenj
          have hpp : p = p0 := Option.some.inj (hp.symm.trans hp0)
          subst hpp
          rw [hseen_i, List.getElem?_set_self hlenj] at hseenj
          have hpair : (g, (stepSeen props g i q.seen).1.result) = (f, r) :=
            Option.some.inj (Option.some.inj hseenj)
          injection hpair with hfg hr
          subst hfg
          rw [← hr]
          exact hrun_i.symm
        · rw [hseen_i, List.getElem?_set_ne (Ne.symm hji)] at hseenj
          exact hrec j p f r hp hseenj
      · intro j p hp
        by_cases hji : j = i
        · rw [hji] at hp ⊢
          have hpp : p = p0 := Option.some.inj (hp.symm.trans hp0)
          subst hpp
          refine Or.inr ⟨g, (stepSeen props g i q.seen).1.result, ?_,
            QueueQuiet.refl p g⟩
          rw [stepSeen_record_self hp0 (by omega)]
        · rcases hcov j p hp with hpend | ⟨f, r, hseenj, hsil⟩
          · refine Or.inl ?_
            rw [h] at hpend
            rcases List.mem_cons.mp hpend with heq | hj
            · exact absurd heq hji
            · exact hj
          · refine Or.inr ⟨f, r, ?_, hsil⟩
            rw [hseen_i, List.getElem?_set_ne (Ne.symm hji)]
            exact hseenj

/-- **STEP CORRECTNESS**: the unit `step` pops reports exactly its run's
result at the current frame, whichever branch ran (the skip branch is
certified by `SkipSound` of the recorded pair). -/
theorem WorkQueue.step_correct {props : List Propagator} {q : WorkQueue} {g : BranchFrame}
    {o : StepOutcome} {q' : WorkQueue} (hok : QueueOK props q g)
    (hstable : SkipsStableAll original props db) (hstep : q.step g props = some (o, q'))
    {p : Propagator} (hp : props[o.unit]? = some p) :
    p.run (frameState g) = o.result := by
  cases h : q.pending with
  | nil =>
      rw [(WorkQueue.step_none_iff q g props).mpr h] at hstep
      cases hstep
  | cons i rest =>
      rw [WorkQueue.step_cons q g props h] at hstep
      cases hstep
      have hi_lt : i < props.length := hok.1.2.2 i (by rw [h]; exact List.mem_cons_self ..)
      have hunit : (stepSeen props g i q.seen).1.unit = i :=
        stepSeen_unit props g i q.seen
      have hp' : props[i]? = some p := by rw [← hunit]; exact hp
      exact stepSeen_result_eq_run hp'
        (fun f r hseen => hok.2.1 i p f r hp' hseen)
        (fun f => hstable p (List.mem_of_getElem? hp') f g)

/-- **STEP SOUNDNESS**: when `step` reuses the recorded result, the popped
unit's recorded reference frame is event-silent to the current frame, its
recorded result is exactly the run at that reference frame, and (via
`SkipSound`) the reused result is the unit's current run. -/
theorem WorkQueue.step_sound {props : List Propagator} {q : WorkQueue} {g : BranchFrame}
    {o : StepOutcome} {q' : WorkQueue} (hok : QueueOK props q g)
    (hstable : SkipsStableAll original props db) (hstep : q.step g props = some (o, q'))
    (hskip : o.reran = false) {p : Propagator} (hp : props[o.unit]? = some p) :
    ∃ f r, q.seen[o.unit]? = some (some (f, r)) ∧ o.result = r ∧
      (∀ e ∈ frameEvents f g, PropagatorSubscribes p e = false) ∧
      r = p.run (frameState f) ∧ p.run (frameState g) = r := by
  cases h : q.pending with
  | nil =>
      rw [(WorkQueue.step_none_iff q g props).mpr h] at hstep
      cases hstep
  | cons i rest =>
      rw [WorkQueue.step_cons q g props h] at hstep
      cases hstep
      have hunit : (stepSeen props g i q.seen).1.unit = i :=
        stepSeen_unit props g i q.seen
      have hp' : props[i]? = some p := by rw [← hunit]; exact hp
      obtain ⟨f, r, hseen, hres, hsil⟩ :=
        stepSeen_skip (props := props) (g := g) (i := i) (seen := q.seen) (p := p)
          hp' hskip
      have hrec := hok.2.1 i p f r hp' hseen
      refine ⟨f, r, ?_, hres, hsil, hrec, ?_⟩
      · rw [hunit]; exact hseen
      · exact (hstable p (List.mem_of_getElem? hp') f g hsil).trans hrec.symm

/-- **PRESERVATION (drain)**: a completed drain is covered at the frame it
was run at and its pending list is empty. -/
theorem QueueOK_drain {props : List Propagator} {q : WorkQueue} {g : BranchFrame}
    (hstable : SkipsStableAll original props db) (hok : QueueOK props q g) :
    QueueOK props (q.drain g props) g := by
  suffices ∀ (is : List Nat) (seen : List (Option (BranchFrame × PropagationResult))),
      QueueOK props ⟨seen, is⟩ g →
      QueueOK props ⟨WorkQueue.drainSeen props g seen is, []⟩ g by
    exact this q.pending q.seen hok
  intro is
  induction is with
  | nil => intro seen h; simpa [WorkQueue.drainSeen] using h
  | cons i rest ih =>
      intro seen h
      have hstep : (⟨seen, i :: rest⟩ : WorkQueue).step g props
          = some ((stepSeen props g i seen).1,
              ⟨(stepSeen props g i seen).2, rest⟩) :=
        WorkQueue.step_cons _ g props rfl
      have h' : QueueOK props ⟨(stepSeen props g i seen).2, rest⟩ g :=
        QueueOK_step h hstable hstep
      simp only [WorkQueue.drainSeen]
      exact ih _ h'

/-- **PRESERVATION (learned work)**: `enqueueAll` queues every unit, so
coverage is immediate. -/
theorem QueueOK_enqueueAll {props : List Propagator} {q : WorkQueue}
    {g : BranchFrame} (hok : QueueOK props q g) :
    QueueOK props (q.enqueueAll props) g := by
  obtain ⟨⟨hlen, hnd, hbnd⟩, hrec, -⟩ := hok
  have hseen : (q.enqueueAll props).seen = q.seen := WorkQueue.enqueueAll_seen q props
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [hseen]; exact hlen
  · exact WorkQueue.enqueueAllFrom_nodup hnd
  · intro j hj
    exact WorkQueue.enqueueAllFrom_bounds hbnd (fun j hj => List.mem_range.mp hj) j hj
  · intro i p f r hp hseenj
    rw [hseen] at hseenj
    exact hrec i p f r hp hseenj
  · intro i p hp
    exact Or.inl ((WorkQueue.mem_enqueueAll (q := q) (props := props)).mpr
      (Or.inr (List.getElem?_eq_some_iff.mp hp).1))

/-- **PRESERVATION (new propagators)**: appending `newProps` and queueing the
fresh indices keeps the invariant. -/
theorem QueueOK_extendUnits {props : List Propagator} {q : WorkQueue}
    {g : BranchFrame} {newProps : List Propagator} (hok : QueueOK props q g) :
    QueueOK (props ++ newProps) (q.extendUnits newProps.length) g := by
  obtain ⟨⟨hlen, hnd, hbnd⟩, hrec, hcov⟩ := hok
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · rw [WorkQueue.extendUnits_seen]
    simp only [List.length_append, List.length_replicate]
    omega
  · exact WorkQueue.extendUnits_nodup hnd
  · refine WorkQueue.extendUnits_bounds (fun j hj => ?_) ?_
    · have := hbnd j hj
      simp only [List.length_append]
      omega
    · simp only [List.length_append]
      omega
  · intro i p f r hp hseen
    rw [WorkQueue.extendUnits_seen] at hseen
    by_cases hi : i < q.seen.length
    · have hp' : props[i]? = some p := by
        have hleft := List.getElem?_append_left (l₁ := props) (l₂ := newProps)
          (by omega : i < props.length)
        rw [hleft] at hp
        exact hp
      rw [List.getElem?_append_left hi] at hseen
      exact hrec i p f r hp' hseen
    · have hright := List.getElem?_append_right (l₁ := q.seen)
          (l₂ := List.replicate newProps.length none) (by omega : q.seen.length ≤ i)
      rw [hright] at hseen
      have hlt : i - q.seen.length < newProps.length := by
        have := (List.getElem?_eq_some_iff.mp hp).1
        simp only [List.length_append] at this
        omega
      rw [List.getElem?_replicate, if_pos hlt] at hseen
      simp at hseen
  · intro i p hp
    rw [WorkQueue.mem_extendUnits]
    by_cases hi : i < q.seen.length
    · have hp' : props[i]? = some p := by
        have hleft := List.getElem?_append_left (l₁ := props) (l₂ := newProps)
          (by omega : i < props.length)
        rw [hleft] at hp
        exact hp
      rcases hcov i p hp' with hpend | hclean
      · exact Or.inl (Or.inl hpend)
      · rcases hclean with ⟨f, r, hseen, hsil⟩
        refine Or.inr ⟨f, r, ?_, hsil⟩
        rw [WorkQueue.extendUnits_seen, List.getElem?_append_left hi]
        exact hseen
    · have hlt : i < (props ++ newProps).length := (List.getElem?_eq_some_iff.mp hp).1
      have hlt' : i < props.length + newProps.length := by simpa using hlt
      have hle : q.seen.length ≤ i := by omega
      exact Or.inl (Or.inr ⟨hle, by omega⟩)

/-! ## 6. The index-order, early-exit queued scan (E1 fix 2)

The first drained design processed the WHOLE pending set before classifying,
so a queued prompt ran every dirty unit of the step; the reference
`scanPropagators` (and the wired stamp scan) instead walk the propagator list
IN ORDER and stop at the first productive implied/conflict. `scanQueue` below
is the same walk driven by the queue's records and dirty set: each PENDING
unit is re-run at the current frame (after a cheap `quietB` reuse check), each
clean unit replays its recorded result, and the walk exits at the first
productive event — leaving the units after it pending with their records.
`scanQueue_event_eq` proves the event is EXACTLY `scanPropagators f props`;
`scanQueue_OK` keeps the queue invariant. -/

/-- Boolean form of the E0-free certificate: the watch projection (nonempty
footprint) or the whole domain list (empty footprint) is unchanged. Cheap
per-unit reuse test: O(|watches|) and no event extraction. -/
def quietB (p : Propagator) (fr f : BranchFrame) : Bool :=
  match p.watches with
  | [] => stampEqB (Frame.domains fr) (Frame.domains f)
  | _ => stampEqB (watchStamp fr p.watches) (watchStamp f p.watches)

/-- `quietB` is sound for the queue certificate. -/
theorem quietB_sound {p : Propagator} {fr f : BranchFrame} (h : quietB p fr f = true) :
    QueueQuiet p fr f := by
  cases hw : p.watches with
  | nil =>
      simp only [hw, quietB] at h
      exact Or.inl ⟨hw, stampEqB_sound h⟩
  | cons a as =>
      simp only [hw, quietB] at h
      refine Or.inr ⟨by simp [hw], ?_⟩
      simpa [hw] using stampEqB_sound h

/-- The certificate's run equality (the `PropLocalOne` content). -/
theorem QueueQuiet.run_eq {props : List Propagator} (hloc : PropLocal props)
    {p : Propagator} (hp : p ∈ props) {fr f : BranchFrame} (hq : QueueQuiet p fr f) :
    p.run (frameState f) = p.run (frameState fr) := by
  rcases hq with ⟨hw, hdom⟩ | ⟨hne, hstamp⟩
  · have hfs : frameState fr = frameState f := by simp only [frameState, hdom]
    rw [hfs]
  · exact (hloc p hp hne fr f hstamp).symm

/-- One unit's result at the early-exit scan: a PENDING unit is re-run unless
its recorded reference is `quietB` to the current frame (then its record is
reused); a clean unit replays its record. -/
def queueUnitResult (f : BranchFrame) (i : Nat) (p : Propagator)
    (s : Option (BranchFrame × PropagationResult)) (pend : List Nat) : PropagationResult :=
  if pend.contains i then
    match s with
    | some (fr, rr) => if quietB p fr f then rr else p.run (frameState f)
    | none => p.run (frameState f)
  else
    match s with
    | some (_, rr) => rr
    | none => p.run (frameState f)

/-- The per-unit run equality the scan consumes: whichever branch fires, the
result is the unit's run at the current frame (records via `QueueRecords`,
reuse via `quietB`/`QueueQuiet`, clean replay via coverage). -/
theorem queueUnitResult_run {f : BranchFrame} {i : Nat} {p : Propagator}
    {s : Option (BranchFrame × PropagationResult)} {pend : List Nat}
    (hrec : ∀ fr rr, s = some (fr, rr) → rr = p.run (frameState fr))
    (hquietB : ∀ fr, quietB p fr f = true → p.run (frameState f) = p.run (frameState fr))
    (hquiet : ∀ fr, QueueQuiet p fr f → p.run (frameState f) = p.run (frameState fr))
    (hcov : pend.contains i = false →
      ∃ fr rr, s = some (fr, rr) ∧ QueueQuiet p fr f) :
    queueUnitResult f i p s pend = p.run (frameState f) := by
  unfold queueUnitResult
  by_cases hc : pend.contains i = true
  · rw [if_pos hc]
    cases s with
    | none => rfl
    | some fr =>
        obtain ⟨fr0, rr⟩ := fr
        dsimp only
        by_cases hq : quietB p fr0 f = true
        · rw [if_pos hq]
          exact (hrec fr0 rr rfl).trans (hquietB fr0 hq).symm
        · rw [if_neg hq]
  · have hcf : pend.contains i = false := by
      cases h : pend.contains i <;> simp_all
    rw [if_neg hc]
    obtain ⟨fr0, rr, hs, hQ⟩ := hcov hcf
    rw [hs]
    simp only
    exact (hrec fr0 rr hs).trans (hquiet fr0 hQ).symm

/-- The index-order early-exit scan core. Walks `props`/`seens` in lockstep
from index `i` (with `seens` the aligned suffix), tests pending membership in
`pend` by index, and returns the event, the updated records (every processed
entry recorded at the current frame `f`; the untouched suffix passed through)
and the first unprocessed index `k`. -/
def scanQueueAux (f : BranchFrame) (i : Nat) :
    List Propagator → List (Option (BranchFrame × PropagationResult)) → List Nat →
      PruningEvent × List (Option (BranchFrame × PropagationResult)) × Nat
  | [], _, _ => (.stable, [], i)
  | _ :: _, [], _ => (.stable, [], i)
  | p :: ps, s :: ss, pend =>
      let r := queueUnitResult f i p s pend
      match r with
      | .stable =>
          let (ev, seens', k) := scanQueueAux f (i + 1) ps ss pend
          (ev, some (f, r) :: seens', k)
      | .conflict c => (.conflict (if c.isEmpty then [] else [c]), some (f, r) :: ss, i + 1)
      | .implied l rr =>
          if productive l f then
            (.implied l rr.clause false false, some (f, r) :: ss, i + 1)
          else
            let (ev, seens', k) := scanQueueAux f (i + 1) ps ss pend
            (ev, some (f, r) :: seens', k)

/-- Arithmetic helper (no projections involved, so `omega`/`rw` stay stable). -/
theorem Nat.sub_succ_of_le {a b : Nat} (h : b + 1 ≤ a) : a - b = a - (b + 1) + 1 := by
  omega

/-- **THE MASTER SPEC (early-exit scan)**: under the aligned per-unit record
and coverage hypotheses the index-order scan (1) reports exactly the reference
`scanPropagators` event, (2) keeps the record-list length, (3) records every
processed unit at the current frame with its current run, (4) passes the
unprocessed suffix through unchanged, and (5) never reports an index below its
start. -/
theorem scanQueueAux_spec (f : BranchFrame) {props : List Propagator}
    (hloc : PropLocal props) :
    ∀ (i : Nat) (ps : List Propagator) (seens : List (Option (BranchFrame × PropagationResult))) (pend : List Nat),
      seens.length = ps.length →
      (∀ (j : Nat) (p : Propagator), ps[j]? = some p → p ∈ props) →
      (∀ (j : Nat) (p : Propagator) (fr : BranchFrame) (rr : PropagationResult),
        ps[j]? = some p → seens[j]? = some (some (fr, rr)) →
        rr = p.run (frameState fr)) →
      (∀ (j : Nat) (p : Propagator), ps[j]? = some p → pend.contains (i + j) = false →
        ∃ (fr : BranchFrame) (rr : PropagationResult),
          seens[j]? = some (some (fr, rr)) ∧ QueueQuiet p fr f) →
      (scanQueueAux f i ps seens pend).1 = scanPropagators f ps ∧
      (scanQueueAux f i ps seens pend).2.1.length = seens.length ∧
      (∀ j, j < (scanQueueAux f i ps seens pend).2.2 - i →
        ∃ (p : Propagator) (r : PropagationResult), ps[j]? = some p ∧
          (scanQueueAux f i ps seens pend).2.1[j]? = some (some (f, r)) ∧
          r = p.run (frameState f)) ∧
      (∀ j, (scanQueueAux f i ps seens pend).2.2 - i ≤ j →
        (scanQueueAux f i ps seens pend).2.1[j]? = seens[j]?) ∧
      i ≤ (scanQueueAux f i ps seens pend).2.2 := by
  intro i ps
  induction ps generalizing i with
  | nil =>
      intro seens pend hlen hmem hrecs hcovs
      have hseens : seens = [] := List.length_eq_zero_iff.mp (by simpa using hlen)
      subst hseens
      refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp [scanQueueAux, scanPropagators]
  | cons p ps ih =>
      intro seens pend hlen hmem hrecs hcovs
      cases seens with
      | nil => simp at hlen
      | cons s ss =>
          have hlen' : ss.length = ps.length := by simpa using hlen
          have hmem' : ∀ (j : Nat) (q : Propagator), ps[j]? = some q → q ∈ props :=
            fun j q hq => hmem (j + 1) q (by simpa [List.getElem?_cons_succ] using hq)
          have hrecs' : ∀ (j : Nat) (q : Propagator) (fr : BranchFrame) (rr : PropagationResult),
              ps[j]? = some q → ss[j]? = some (some (fr, rr)) → rr = q.run (frameState fr) :=
            fun j q fr rr hq hs => hrecs (j + 1) q fr rr
              (by simpa [List.getElem?_cons_succ] using hq)
              (by simpa [List.getElem?_cons_succ] using hs)
          have hcovs' : ∀ (j : Nat) (q : Propagator),
              ps[j]? = some q → pend.contains ((i + 1) + j) = false →
              ∃ fr rr, ss[j]? = some (some (fr, rr)) ∧ QueueQuiet q fr f :=
            fun j q hq hc => hcovs (j + 1) q (by simpa [List.getElem?_cons_succ] using hq)
              (by have heq : i + (j + 1) = (i + 1) + j := by omega
                  simpa [heq] using hc)
          have hpmem : p ∈ props := hmem 0 p (by simp)
          have hrec0 : ∀ fr rr, s = some (fr, rr) → rr = p.run (frameState fr) :=
            fun fr rr hs => hrecs 0 p fr rr (by simp) (by simpa using hs)
          have hquietB : ∀ fr, quietB p fr f = true →
              p.run (frameState f) = p.run (frameState fr) :=
            fun fr hq => QueueQuiet.run_eq hloc hpmem (quietB_sound hq)
          have hquiet : ∀ fr, QueueQuiet p fr f →
              p.run (frameState f) = p.run (frameState fr) :=
            fun fr hq => QueueQuiet.run_eq hloc hpmem hq
          have hcov0 : pend.contains i = false →
              ∃ fr rr, s = some (fr, rr) ∧ QueueQuiet p fr f := by
            intro hc
            obtain ⟨fr, rr, hs, hQ⟩ := hcovs 0 p (by simp) hc
            exact ⟨fr, rr, by simpa using hs, hQ⟩
          have hrun : queueUnitResult f i p s pend = p.run (frameState f) :=
            queueUnitResult_run hrec0 hquietB hquiet hcov0
          obtain ⟨hev, hlenI, hpreI, htailI, hgeI⟩ :=
            ih (i + 1) ss pend hlen' hmem' hrecs' hcovs'
          cases hq : queueUnitResult f i p s pend with
          | stable =>
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · -- event
                simp only [scanQueueAux, hq, scanPropagators]
                rw [← hrun]
                simp only [hq]
                exact hev
              · -- length
                simp only [scanQueueAux, hq, List.length_cons]
                rw [hlenI]
              · -- prefix
                intro j hj
                cases j with
                | zero =>
                    refine ⟨p, queueUnitResult f i p s pend, by simp, ?_, ?_⟩
                    · simp only [scanQueueAux, hq, List.getElem?_cons_zero]
                    · simpa [scanQueueAux, hq] using hrun
                | succ j =>
                    have hj' : j < (scanQueueAux f (i + 1) ps ss pend).2.2 - (i + 1) := by
                      have h1 : j + 1 < (scanQueueAux f (i + 1) ps ss pend).2.2 - i := by
                        simpa only [scanQueueAux, hq] using hj
                      rw [Nat.sub_succ_of_le hgeI] at h1
                      exact Nat.succ_lt_succ_iff.mp h1
                    obtain ⟨p', r', hp', hget', hrun'⟩ := hpreI j hj'
                    refine ⟨p', r', by simpa using hp', ?_, ?_⟩
                    · simp only [scanQueueAux, hq, List.getElem?_cons_succ]
                      exact hget'
                    · exact hrun'
              · -- tail
                intro j hj
                cases j with
                | zero =>
                    exfalso
                    have h1 : (scanQueueAux f (i + 1) ps ss pend).2.2 - i ≤ 0 := by
                      simpa only [scanQueueAux, hq] using hj
                    rw [Nat.sub_succ_of_le hgeI] at h1
                    exact absurd h1 (by omega)
                | succ j =>
                    have hj' : (scanQueueAux f (i + 1) ps ss pend).2.2 - (i + 1) ≤ j := by
                      have h1 : (scanQueueAux f (i + 1) ps ss pend).2.2 - i ≤ j + 1 := by
                        simpa only [scanQueueAux, hq] using hj
                      rw [Nat.sub_succ_of_le hgeI] at h1
                      exact Nat.succ_le_succ_iff.mp h1
                    simp only [scanQueueAux, hq, List.getElem?_cons_succ]
                    exact htailI j hj'
              · -- ge
                simp only [scanQueueAux, hq]
                exact Nat.le_trans (Nat.le_succ i) hgeI
          | conflict c =>
              refine ⟨?_, ?_, ?_, ?_, ?_⟩
              · simp only [scanQueueAux, hq, scanPropagators]
                rw [← hrun]
                simp only [hq]
              · simp only [scanQueueAux, hq, List.length_cons]
              · intro j hj
                cases j with
                | zero =>
                    refine ⟨p, queueUnitResult f i p s pend, by simp, ?_, ?_⟩
                    · simp only [scanQueueAux, hq, List.getElem?_cons_zero]
                    · simpa [scanQueueAux, hq] using hrun
                | succ j =>
                    exfalso
                    have h1 : j + 1 < (i + 1) - i := by
                      simpa only [scanQueueAux, hq] using hj
                    have h2 : (i + 1) - i = 1 := by omega
                    rw [h2] at h1
                    exact absurd (Nat.succ_lt_succ_iff.mp h1) (Nat.not_lt_zero j)
              · intro j hj
                cases j with
                | zero =>
                    exfalso
                    have h1 : (i + 1) - i ≤ 0 := by
                      simpa only [scanQueueAux, hq] using hj
                    have h2 : (i + 1) - i = 1 := by omega
                    rw [h2] at h1
                    exact absurd h1 (by omega)
                | succ j => simp only [scanQueueAux, hq, List.getElem?_cons_succ]
              · simp only [scanQueueAux, hq]
                exact Nat.le_succ i
          | implied l rr =>
              by_cases hprod : productive l f = true
              · refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simp only [scanQueueAux, hq, hprod, if_pos, scanPropagators]
                  rw [← hrun]
                  simp only [hq, hprod, if_pos]
                · simp only [scanQueueAux, hq, hprod, if_pos, List.length_cons]
                · intro j hj
                  cases j with
                  | zero =>
                      refine ⟨p, queueUnitResult f i p s pend, by simp, ?_, ?_⟩
                      · simp only [scanQueueAux, hq, hprod, if_pos, List.getElem?_cons_zero]
                      · simpa [scanQueueAux, hq, hprod, if_pos] using hrun
                  | succ j =>
                      exfalso
                      have h1 : j + 1 < (i + 1) - i := by
                        simpa only [scanQueueAux, hq, hprod, if_pos] using hj
                      have h2 : (i + 1) - i = 1 := by omega
                      rw [h2] at h1
                      exact absurd (Nat.succ_lt_succ_iff.mp h1) (Nat.not_lt_zero j)
                · intro j hj
                  cases j with
                  | zero =>
                      exfalso
                      have h1 : (i + 1) - i ≤ 0 := by
                        simpa only [scanQueueAux, hq, hprod, if_pos] using hj
                      have h2 : (i + 1) - i = 1 := by omega
                      rw [h2] at h1
                      exact absurd h1 (by omega)
                  | succ j =>
                      simp only [scanQueueAux, hq, hprod, if_pos, List.getElem?_cons_succ]
                · simp only [scanQueueAux, hq, hprod, if_pos]
                  exact Nat.le_succ i
              · refine ⟨?_, ?_, ?_, ?_, ?_⟩
                · simp only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false,
                    scanPropagators]
                  rw [← hrun]
                  simp only [hq, hprod, Bool.false_eq_true, if_false]
                  exact hev
                · simp only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false,
                    List.length_cons]
                  rw [hlenI]
                · intro j hj
                  cases j with
                  | zero =>
                      refine ⟨p, queueUnitResult f i p s pend, by simp, ?_, ?_⟩
                      · simp only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false,
                          List.getElem?_cons_zero]
                      · simpa [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false] using hrun
                  | succ j =>
                      have hj' : j < (scanQueueAux f (i + 1) ps ss pend).2.2 - (i + 1) := by
                        have h1 : j + 1 < (scanQueueAux f (i + 1) ps ss pend).2.2 - i := by
                          simpa only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false] using hj
                        rw [Nat.sub_succ_of_le hgeI] at h1
                        exact Nat.succ_lt_succ_iff.mp h1
                      obtain ⟨p', r', hp', hget', hrun'⟩ := hpreI j hj'
                      refine ⟨p', r', by simpa using hp', ?_, ?_⟩
                      · simp only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false,
                          List.getElem?_cons_succ]
                        exact hget'
                      · exact hrun'
                · intro j hj
                  cases j with
                  | zero =>
                      exfalso
                      have h1 : (scanQueueAux f (i + 1) ps ss pend).2.2 - i ≤ 0 := by
                        simpa only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false] using hj
                      rw [Nat.sub_succ_of_le hgeI] at h1
                      exact absurd h1 (by omega)
                  | succ j =>
                      have hj' : (scanQueueAux f (i + 1) ps ss pend).2.2 - (i + 1) ≤ j := by
                        have h1 : (scanQueueAux f (i + 1) ps ss pend).2.2 - i ≤ j + 1 := by
                          simpa only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false] using hj
                        rw [Nat.sub_succ_of_le hgeI] at h1
                        exact Nat.succ_le_succ_iff.mp h1
                      simp only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false,
                        List.getElem?_cons_succ]
                      exact htailI j hj'
                · simp only [scanQueueAux, hq, hprod, Bool.false_eq_true, if_false]
                  exact Nat.le_trans (Nat.le_succ i) hgeI

/-- The index-order early-exit queued scan. -/
def WorkQueue.scanQueue (q : WorkQueue) (props : List Propagator) (f : BranchFrame) :
    PruningEvent × WorkQueue :=
  let out := scanQueueAux f 0 props q.seen q.pending
  (out.1, { seen := out.2.1, pending := q.pending.filter (fun j => out.2.2 ≤ j) })

/-- The aligned hypotheses at the wrapper (index 0) from the queue invariant. -/
theorem scanQueueAux_spec_zero {props : List Propagator} {q : WorkQueue} {f : BranchFrame}
    (hok : QueueOK props q f) (hloc : PropLocal props) :
    (scanQueueAux f 0 props q.seen q.pending).1 = scanPropagators f props ∧
    (scanQueueAux f 0 props q.seen q.pending).2.1.length = q.seen.length ∧
    (∀ j, j < (scanQueueAux f 0 props q.seen q.pending).2.2 →
      ∃ p r, props[j]? = some p ∧
        (scanQueueAux f 0 props q.seen q.pending).2.1[j]? = some (some (f, r)) ∧
        r = p.run (frameState f)) ∧
    (∀ j, (scanQueueAux f 0 props q.seen q.pending).2.2 ≤ j →
      (scanQueueAux f 0 props q.seen q.pending).2.1[j]? = q.seen[j]?) ∧
    0 ≤ (scanQueueAux f 0 props q.seen q.pending).2.2 := by
  obtain ⟨⟨hlen, -, -⟩, hrecs, hcovs⟩ := hok
  exact scanQueueAux_spec f hloc 0 props q.seen q.pending hlen
    (fun j p hp => List.mem_of_getElem? hp)
    (fun j p fr rr hp hs => hrecs j p fr rr hp hs)
    (fun j p hp hc => by
      rcases hcovs j p hp with hmem | hclean
      · have hcj : q.pending.contains j = false := by
          have hc' := hc
          rw [Nat.zero_add] at hc'
          exact hc'
        rw [List.contains_iff_mem.mpr hmem] at hcj
        cases hcj
      · exact hclean)

/-- **EVENT EQUALITY (early-exit queued scan)**: a covered queue classifies
the current frame exactly as the certified full scan. -/
theorem scanQueue_event_eq {props : List Propagator} {q : WorkQueue} {f : BranchFrame}
    (hok : QueueOK props q f) (hloc : PropLocal props) :
    (q.scanQueue props f).1 = scanPropagators f props :=
  (scanQueueAux_spec_zero hok hloc).1

/-- **PRESERVATION (early-exit queued scan)**: the queue invariant survives
the scan; units after the stopping index stay pending with their records. -/
theorem scanQueue_OK {props : List Propagator} {q : WorkQueue} {f : BranchFrame}
    (hok : QueueOK props q f) (hloc : PropLocal props) :
    QueueOK props (q.scanQueue props f).2 f := by
  obtain ⟨hlen, hnd, hbnd⟩ := hok.1
  obtain ⟨hrecs, hcovs⟩ := hok.2
  have hspec := scanQueueAux_spec_zero hok hloc
  obtain ⟨-, hlenOut, hpre, htail, -⟩ := hspec
  refine ⟨⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · show (scanQueueAux f 0 props q.seen q.pending).2.1.length = props.length
    rw [hlenOut]; exact hlen
  · exact hnd.filter _
  · intro j hj
    exact hbnd j (List.mem_filter.mp hj).1
  · intro j p fr rr hp hs
    by_cases hj : j < (scanQueueAux f 0 props q.seen q.pending).2.2
    · obtain ⟨p', r', hp', hget', hrun'⟩ := hpre j hj
      have hpp : p' = p := by
        rw [hp] at hp'
        exact (Option.some.inj hp').symm
      subst hpp
      have hpair : (f, r') = (fr, rr) :=
        Option.some.inj (Option.some.inj (hget'.symm.trans hs))
      injection hpair with hfr hrr
      rw [← hfr, ← hrr]
      exact hrun'
    · have htailj := htail j (by omega)
      have hq' : (q.seen[j]?) = some (some (fr, rr)) := by
        rw [← htailj]
        exact hs
      exact hrecs j p fr rr hp hq'
  · intro j p hp
    by_cases hj : j < (scanQueueAux f 0 props q.seen q.pending).2.2
    · obtain ⟨p', r', hp', hget', -⟩ := hpre j hj
      refine Or.inr ⟨f, r', ?_, QueueQuiet.refl p f⟩
      show (scanQueueAux f 0 props q.seen q.pending).2.1[j]? = some (some (f, r'))
      exact hget'
    · rcases hcovs j p hp with hmem | hclean
      · refine Or.inl (List.mem_filter.mpr ⟨hmem, ?_⟩)
        exact decide_eq_true (by omega)
      · obtain ⟨fr, rr, hs, hQ⟩ := hclean
        have htailj := htail j (by omega)
        refine Or.inr ⟨fr, rr, ?_, hQ⟩
        show (scanQueueAux f 0 props q.seen q.pending).2.1[j]? = some (some (fr, rr))
        rw [htailj]
        exact hs

/-! ## 7. Records, replay, and the certified core -/

/-- Extract the recorded results (aligned with the records). -/
def seenResults : List (Option (BranchFrame × PropagationResult)) → List PropagationResult
  | [] => []
  | some (_, r) :: ss => r :: seenResults ss
  | none :: ss => .stable :: seenResults ss

/-- Replace each unit's run by a recorded result (aligned lists; the mismatch
cases are unreachable under `RecsAt`). -/
def replayResults : List Propagator → List PropagationResult → List Propagator
  | [], _ => []
  | p :: ps, rs =>
      match rs with
      | [] => []
      | r :: rs' => { p with run := fun _ => r } :: replayResults ps rs'

/-- Pointwise admissibility of recorded results at a frame. -/
def RecsAt (g : BranchFrame) : List Propagator → List PropagationResult → Prop
  | [], [] => True
  | p :: ps, r :: rs => p.run (frameState g) = r ∧ RecsAt g ps rs
  | _, _ => False

/-- **REPLAY = FULL SCAN**: admissible records replay exactly the certified
propagator scan (same order, same early exit). -/
theorem scanPropagators_replay_eq (g : BranchFrame) :
    ∀ (ps : List Propagator) (rs : List PropagationResult),
      RecsAt g ps rs → scanPropagators g (replayResults ps rs) = scanPropagators g ps := by
  intro ps
  induction ps with
  | nil =>
      intro rs h
      cases rs with
      | nil => rfl
      | cons r rs => simp [RecsAt] at h
  | cons p ps ih =>
      intro rs h
      cases rs with
      | nil => simp [RecsAt] at h
      | cons r rs =>
          have hp : p.run (frameState g) = r := by
            rw [RecsAt.eq_2] at h; exact h.1
          have ht : RecsAt g ps rs := by
            rw [RecsAt.eq_2] at h; exact h.2
          show scanPropagators g ({ p with run := fun _ => r } :: replayResults ps rs)
              = scanPropagators g (p :: ps)
          rw [scanPropagators, scanPropagators, hp]
          cases r with
          | stable => simp only; rw [ih rs ht]
          | conflict c => simp only
          | implied l r' =>
              by_cases hprod : productive l g = true
              · simp only [hprod, if_pos]
              · simp only [hprod, Bool.false_eq_true, if_false]; rw [ih rs ht]

/-- **REPLAY = FULL SCAN (event-selection form)**. -/
theorem nextPruningEvent_replay_eq (original : List Clause) (props : List Propagator)
    (rs : List PropagationResult) (g : BranchFrame) (db : List Clause)
    (h : RecsAt g props rs) :
    nextPruningEvent original (replayResults props rs) g db
      = nextPruningEvent original props g db := by
  cases hdb : scanDatabase original g db with
  | stable =>
      have hscan := scanPropagators_replay_eq g props rs h
      simp only [nextPruningEvent, hdb]
      by_cases hv : frameViewedB g = true
      · simp only [hv, if_pos, hscan]
      · simp only [hv, Bool.false_eq_true, if_false]
  | conflict cs => simp only [nextPruningEvent, hdb]
  | implied l c lr fl => simp only [nextPruningEvent, hdb]

/-- Aligned records produce admissible results at the current frame. -/
theorem recsAt_seenResults (g : BranchFrame) :
    ∀ (props : List Propagator) (ss : List (Option (BranchFrame × PropagationResult))),
      ss.length = props.length →
      (∀ (i : Nat) (p : Propagator), props[i]? = some p →
        ∃ f r, ss[i]? = some (some (f, r)) ∧ p.run (frameState g) = r) →
      RecsAt g props (seenResults ss) := by
  intro props
  induction props with
  | nil =>
      intro ss hlen h
      cases ss with
      | nil => simp [RecsAt, seenResults]
      | cons s ss => simp at hlen
  | cons p ps ih =>
      intro ss hlen h
      cases ss with
      | nil => simp at hlen
      | cons s ss =>
          cases s with
          | none =>
              obtain ⟨f, r, hc, -⟩ := h 0 p (by simp)
              simp at hc
          | some fr =>
              obtain ⟨f, r⟩ := fr
              obtain ⟨f0, r0, hc, hrun⟩ := h 0 p (by simp)
              have hpair : (f, r) = (f0, r0) :=
                Option.some.inj (Option.some.inj (by simpa using hc))
              obtain ⟨h1, h2⟩ := Prod.ext_iff.mp hpair
              subst h1
              subst h2
              refine ⟨hrun, ih ss ?_ ?_⟩
              · simp only [List.length_cons] at hlen ⊢; omega
              · intro i q hq
                obtain ⟨f', r', hc, hrun'⟩ := h (i + 1) q (by simpa using hq)
                exact ⟨f', r', by simpa using hc, hrun'⟩

/-- **EMPTY + COVERAGE => RECORD REPLAY = FULL SCAN**: the stable-event
classification at the current frame is computed exactly by the records. -/
theorem empty_complete_scan {props : List Propagator} {q : WorkQueue} {g : BranchFrame}
    (hshape : QueueShape props q) (hrec : QueueRecords props q)
    (hcov : QueueCovered props q g) (hempty : q.pending = [])
    (hloc : PropLocal props) :
    scanPropagators g (replayResults props (seenResults q.seen))
      = scanPropagators g props := by
  apply scanPropagators_replay_eq
  apply recsAt_seenResults g
  · exact hshape.1
  · intro i p hp
    rcases hcov i p hp with hpend | ⟨f, r, hseen, hquiet⟩
    · rw [hempty] at hpend
      exact absurd hpend (by simp)
    · exact ⟨f, r, hseen, QueueCovered.run_eq_of_clean hrec hcov hloc hp
        (by rw [hempty]; simp) hseen⟩

/-- **EMPTY COMPLETENESS**: an empty covered queue's records classify the
current frame exactly as the certified full scan does. -/
theorem empty_complete {props : List Propagator} {q : WorkQueue} {g : BranchFrame}
    {original : List Clause} {db : List Clause}
    (hshape : QueueShape props q) (hrec : QueueRecords props q)
    (hcov : QueueCovered props q g) (hempty : q.pending = [])
    (hloc : PropLocal props) :
    nextPruningEvent original (replayResults props (seenResults q.seen)) g db
      = nextPruningEvent original props g db := by
  apply nextPruningEvent_replay_eq
  apply recsAt_seenResults g
  · exact hshape.1
  · intro i p hp
    rcases hcov i p hp with hpend | ⟨f, r, hseen, hquiet⟩
    · rw [hempty] at hpend
      exact absurd hpend (by simp)
    · exact ⟨f, r, hseen, QueueCovered.run_eq_of_clean hrec hcov hloc hp
        (by rw [hempty]; simp) hseen⟩

/-- **EMPTY COMPLETENESS via E0's `SkipsComplete`**: the uniform-reference
packaging for a queue whose certificates are E0 EVENT SILENCE (not merely the
laxer `QueueQuiet`): every unit is either pending or recorded at `f0` with all
of `frameEvents f0 g` unsubscribed. E0's `skipsComplete_proof` then applies
directly, with the locality supplied by `PropLocal`. -/
theorem empty_complete_replayAt {props : List Propagator} {q : WorkQueue}
    {g f0 : BranchFrame} {original : List Clause} {db : List Clause}
    (hempty : q.pending = []) (hloc : PropLocal props)
    (hsil : ∀ (i : Nat) (p : Propagator), props[i]? = some p →
      i ∈ q.pending ∨
        ∃ f r, q.seen[i]? = some (some (f, r)) ∧ f = f0 ∧
          (∀ e ∈ frameEvents f0 g, PropagatorSubscribes p e = false)) :
    nextPruningEvent original (props.map (Propagator.replayAt f0)) g db
      = nextPruningEvent original props g db := by
  have hstable : SkipsStable original props f0 g db := fun p hp =>
    (skipsStableAll_of_propLocal (original := original) (db := db) hloc) p hp f0 g
  apply skipsComplete_proof original props f0 g db hstable
  intro p hp e he
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hp
  rcases hsil i p hi with hpend | ⟨f, r, hseen, hf, hsilent⟩
  · rw [hempty] at hpend
    exact absurd hpend (by simp)
  · exact hsilent e he

/-! ## 7. Quiescence: no productive work postponed -/

/-- **NO PRODUCTIVE WORK POSTPONED (quiescence obligation)**: at the drained
frame the classification computed from the queue's records is EXACTLY the
certified full scan's. A queue satisfying this at every frame of a run cannot
return `.stable` (or a conflict) while a productive deduction or a different
conflict is still available from its records; the "forever" induction is the
dispatcher policy's responsibility (drain before classify, move the frame
only through `enqueueEvents`/`rebuild`). -/
def NoPostponed (original : List Clause) (props : List Propagator)
    (q : WorkQueue) (g : BranchFrame) (db : List Clause) : Prop :=
  nextPruningEvent original (replayResults props (seenResults q.seen)) g db
    = nextPruningEvent original props g db

/-- **DISCHARGE (drain policy)**: after a complete drain the obligation holds,
from `QueueOK_drain` and `empty_complete`. -/
theorem noPostponed_of_drain {original : List Clause} {props : List Propagator}
    {db : List Clause} {q : WorkQueue} {g : BranchFrame}
    (hloc : PropLocal props) (hok : QueueOK props q g) :
    NoPostponed original props (q.drain g props) g db :=
  let hstable := skipsStableAll_of_propLocal (original := original) (db := db) hloc
  let hok' := QueueOK_drain hstable hok
  empty_complete hok'.1 hok'.2.1 hok'.2.2 (WorkQueue.drain_pending q g props) hloc

/-- **DISCHARGE (rebuild-on-restore policy)**: rebuilding re-queues
everything, and the subsequent drain discharges the obligation; no hypothesis
beyond `PropLocal` is needed because `QueueOK_rebuild` holds
unconditionally. -/
theorem noPostponed_rebuild {original : List Clause} {props : List Propagator}
    {db : List Clause} {q : WorkQueue} {g : BranchFrame}
    (hloc : PropLocal props) :
    NoPostponed original props ((q.rebuild props).drain g props) g db :=
  noPostponed_of_drain hloc (QueueOK_rebuild props q g)

/-- **DISCHARGE (concrete certified list)**: the rebuild-on-restore policy for
`clampProps orig (dcs.filterMap propagatorOfProved)`. -/
theorem noPostponed_clampProps (orig : List Domain) (dcs : List DomConstraint)
    (original : List Clause) (db : List Clause) (q : WorkQueue) (g : BranchFrame) :
    NoPostponed original (clampProps orig (dcs.filterMap propagatorOfProved))
      ((q.rebuild (clampProps orig (dcs.filterMap propagatorOfProved))).drain g
        (clampProps orig (dcs.filterMap propagatorOfProved))) g db :=
  noPostponed_rebuild (clampProps_local orig dcs)

/-- A productive implied deduction is a justified finite-progress terminator:
either the branch is closed (`filterFrame = none`) or the next frame is
strictly lighter (`Frame.mass` decreases) — the existing closure argument. -/
theorem productive_frame {l : Literal} {f : BranchFrame} (h : productive l f = true) :
    filterFrame l f = none ∨ ∃ g, filterFrame l f = some g ∧ Frame.mass g < Frame.mass f := by
  unfold productive at h
  split at h
  · rename_i hnone
    exact Or.inl hnone
  · rename_i g hg
    exact Or.inr ⟨g, hg, of_decide_eq_true h⟩

/-! ## 8. Ablation-ready dispatcher reference -/

/-- A drop-in queued dispatcher reference: the certified fast DB scan first;
at a viewed live frame, a full drain followed by the record-based replay
classification. The returned queue is the drained queue. -/
def nextPruningEventQueued (original : List Clause) (props : List Propagator)
    (q : WorkQueue) (g : BranchFrame) (db : List Clause) : PruningEvent × WorkQueue :=
  match scanDatabaseFast original g db with
  | .stable =>
      if frameViewedB g then
        let q' := q.drain g props
        (scanPropagators g (replayResults props (seenResults q'.seen)), q')
      else (.stable, q)
  | .conflict cs => (.conflict cs, q)
  | .implied l c learnReason fromLearned =>
      if frameLiveB g then (.implied l c learnReason fromLearned, q) else (.stable, q)

/-- **THE WIRING EQUALITY**: under `QueueOK` and the registered locality
`PropLocal`, the queued dispatcher reference produces exactly the certified
`nextPruningEvent` (first projection), in the style of
`nextPruningEventSched_fst_eq`. -/
theorem nextPruningEventQueued_fst_eq {original : List Clause}
    {props : List Propagator} {q : WorkQueue} {g : BranchFrame} {db : List Clause}
    (hok : QueueOK props q g) (hloc : PropLocal props) :
    (nextPruningEventQueued original props q g db).1
      = nextPruningEvent original props g db := by
  unfold nextPruningEventQueued
  rw [scanDatabaseFast_eq]
  cases hdb : scanDatabase original g db with
  | stable =>
      simp only [hdb, nextPruningEvent]
      by_cases hv : frameViewedB g = true
      · simp only [hv, if_pos]
        have hstable := skipsStableAll_of_propLocal (original := original) (db := db) hloc
        have hok' := QueueOK_drain hstable hok
        exact empty_complete_scan hok'.1 hok'.2.1 hok'.2.2
          (WorkQueue.drain_pending q g props) hloc
      · simp only [hv, Bool.false_eq_true, if_false]
  | conflict cs => simp only [hdb, nextPruningEvent]
  | implied l c lr fl =>
      simp only [hdb, nextPruningEvent]
      by_cases hl : frameLiveB g = true
      · simp only [hl, if_pos]
      · simp only [hl, Bool.false_eq_true, if_false]

/-- The concrete-list wiring equality. -/
theorem nextPruningEventQueued_clampProps_fst_eq (orig : List Domain)
    (dcs : List DomConstraint) (original : List Clause) (db : List Clause)
    (q : WorkQueue) (g : BranchFrame) (hok : QueueOK
      (clampProps orig (dcs.filterMap propagatorOfProved)) q g) :
    (nextPruningEventQueued original
        (clampProps orig (dcs.filterMap propagatorOfProved)) q g db).1
      = nextPruningEvent original (clampProps orig (dcs.filterMap propagatorOfProved)) g db :=
  nextPruningEventQueued_fst_eq hok (clampProps_local orig dcs)

end LeanFzn.Solver.Propagation
