/-
File: Tests/UIP/SchedulerActivation.lean

Purpose: convert the three PENDING activation predicates of
`Tests.UIP.SchedulerFixtures` (`PendingMultiResolutionExact`,
`PendingSkippedLevelJumpExact`, `PendingPostAssertionPropagation`) into REAL
checks of OBSERVED `RuntimeEvents`, produced by the REAL dispatcher.

HONESTY NOTES (read before citing):

* `runPhaseEvents` / `solvePhaseCompiled` (D1) are NOT used here: their
  premise bundle `CompiledPhasePremises {hpool, hdb, hbr}` quantifies over
  EVERY `SchedulerReachable` configuration — including initializations at
  OTHER boxes — so it is not instantiable on any fixture today:
  - `hpool` (owner P2 / obligation P1-a: `canonicalClause an.learned <+
    litPool orig` from the analyzer construction order) is open;
  - `hdb` (owner S4/S5) is open, and the unqualified `DatabaseUnfalsified`
    has a kernel witness against it (`Proofs/DatabaseUnfalsified.lean`);
  - `hbr` (owner S5: `ReachableArmsPreserveReach`) still has named
    per-arm residuals (`RestorationPreReachable`, `LearnedEntailed`).
  This module therefore observes the SAME `RuntimeEvents` through the SAME
  `schedulerNext` equations the driver runs (`SchedulerTransition.successor`
  chain, exactly `runPhaseConfig`'s recursion), on CONCRETE fixture
  configurations. The starting configurations of the activation fixtures are
  NOT proved `SchedulerReachable` from `init` (that is the R1/S3/S5
  execution-chain residual) — no reachability claim is made for them. The
  from-init run below is threaded through the PROVED
  `schedulerReachable_successor`, so its observations carry reachability.

* No `sorry`, no custom axiom, no `noncomputable`, no `native_decide`.
  Every observed value below is a kernel-`rfl`/`decide` fact about the
  real transition functions; none is a fixture counter.

The fixture (an extension of T1's `mTrail`/`mConflict`):
  * 5-slot int box; branch trail = `mTrail` (levels 1,2,3 with two
    reason-carrying implications), level 3;
  * a real propagator `conflictProp` reports `mConflict` on any 5-slot box,
    so the dispatch's OWN conflict route (not a direct call) runs the REAL
    analyzer at the analyze site and records the counted expansions;
  * a checkpoint at level 1 with slot 1 = {7,9} makes the recorded
    3 → 1 jump perform (assertion `¬(x1 ≤ 7)` leaves {9}).

Observed driver-level values (`driveN` = the dispatcher's own successor
chain, exactly like `runPhaseConfig`):
  step 1 (analyze site): `reasonResolutions = 2` = `mExpansions`;
  step 2 (learn/backjump/assert): `backjumps = 1`, `sourceLevel = 3`,
  `targetLevel = 1 = mTargetLevel`, `assertingEnqueues = 1`.

Negative controls (the gate "bypassing the analyzer must fail tests"):
  * level-0 dispatch → root `.unsat`, NO analyzer call: resolutions 0;
  * recorded evidence with `analysis := none` → fallback, NO jump: backjumps 0.
-/

import Tests.UIP.SchedulerFixtures
import LeanFzn.Solver.UIP.Proofs.Scheduler
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration
open T1Oracle

namespace T3Activation

/-! ## 1. The dispatcher-stepped driver (bounded, computable, no fuel axiom)

`driveN n cfg` follows the REAL `schedulerNext`/`successor` equations for at
most `n` steps, stopping at terminal transitions — the same recursion shape
as X2's `runPhaseConfig`, but bounded by a literal count so the observation
is decidable by kernel computation here. It is NOT a totality claim. -/

/-- Bounded real-dispatcher run (structural recursion on the step budget). -/
def driveN {leaf : Assignment → Bool} : Nat → SchedulerConfig leaf →
    SchedulerConfig leaf
  | 0, cfg => cfg
  | n + 1, cfg =>
      let t := schedulerNext cfg
      match t.successor with
      | some cfg' => driveN n cfg'
      | none => cfg

/-- The same bounded run, carrying the PROVED reachability closure
(`schedulerReachable_successor`) at every step: from a reachable start the
observed configuration is reachable. -/
def driveReachN {leaf : Assignment → Bool} (n : Nat) (cfg : SchedulerConfig leaf)
    (hreach : SchedulerReachable cfg) :
    { cfg' : SchedulerConfig leaf // SchedulerReachable cfg' } :=
  match n with
  | 0 => ⟨cfg, hreach⟩
  | k + 1 =>
      match hsucc : (schedulerNext cfg).successor with
      | some cfg' =>
          driveReachN k cfg' (schedulerReachable_successor hreach hsucc)
      | none => ⟨cfg, hreach⟩

/-! ## 2. The activation fixture -/

/-- The 5-slot int box: slot 1 holds {7,9} for the assertion `x1 > 7`. -/
def actBox : List Domain :=
  [[.int 0, .int 1], [.int 7, .int 9], [.int 0, .int 1], [.int 0, .int 1],
   [.int 0, .int 1]]

/-- A real propagator: reports T1's `mConflict` on any 5-slot box (all its
values are int-viewed, so the box is scanned). -/
def conflictProp : Propagator :=
  { watches := [],
    run := fun st => if st.domains.length == 5 then .conflict mConflict else .stable }

/-- The level-1 checkpoint: slot 0 already at {0,1} (the level-1 decision
`x0 ≤ 5`), slot 1 at {7,9} so `¬(x1 ≤ 7)` narrows it to {9}. -/
def actCheckpoint : DecisionCheckpoint (fun _ : Assignment => true) :=
  { level := 1, frame := (actBox, []), trail := [] }

/-- The activation configuration: `mTrail` at level 3, no recorded evidence
yet (the dispatcher must PRODUCE the conflict through its own route). -/
def actCfg : SchedulerConfig (fun _ : Assignment => true) :=
  { orig := actBox, original := [], props := [conflictProp],
    branch := { frame := (actBox, []), trail := mTrail, level := 3,
                learned := [] },
    checkpoints := [actCheckpoint], pending := [], log := {} }

/-! ## 3. The observed driver-level events (kernel-checked values) -/

/-- Step 1: the real dispatcher reaches the analyze site. -/
def afterAnalyze : SchedulerConfig (fun _ : Assignment => true) :=
  driveN 1 actCfg

/-- Steps 1–2: the recorded evidence is resolved by the REAL jump. -/
def afterJump : SchedulerConfig (fun _ : Assignment => true) :=
  driveN 2 actCfg

-- The analyze site really fired: the counted analyzer expansions of the
-- multi-resolution conflict ARE the observed driver counter (2).
example : afterAnalyze.events.reasonResolutions = 2 := rfl
example : afterAnalyze.events.backjumps = 0 := rfl
example : afterAnalyze.conflict.isSome = true := rfl

-- The jump really fired: one backjump from source level 3 to the proved
-- UIP target 1 — the impossible level 2 (only `x3 ≠ 1`) is skipped — with
-- exactly one asserting enqueue.
example : afterJump.events.reasonResolutions = 2 := rfl
example : afterJump.events.backjumps = 1 := rfl
example : afterJump.events.sourceLevel = 3 := rfl
example : afterJump.events.targetLevel = mTargetLevel := rfl
example : afterJump.events.assertingEnqueues = 1 := rfl

/-- THE THREE PENDING PREDICATES, APPLIED FOR REAL (T1 §8 conversion):
each is now a kernel-proved statement about events OBSERVED on a real
dispatcher run of this fixture. -/
example : T2Fixtures.PendingMultiResolutionExact afterAnalyze.events := rfl

example : T2Fixtures.PendingSkippedLevelJumpExact afterJump.events := by
  refine ⟨rfl, rfl, rfl⟩

example : T2Fixtures.PendingPostAssertionPropagation afterJump.events paState := by
  refine ⟨by decide, rfl⟩

/-! ## 4. Negative controls — bypassing the analyzer fails these tests -/

/-- Same branch, level 0: the dispatcher's root-contradiction route reports
`.unsat` WITHOUT calling the analyzer. -/
def rootCfg : SchedulerConfig (fun _ : Assignment => true) :=
  { actCfg with branch := { actCfg.branch with trail := [], level := 0 } }

/-- Recorded evidence whose analysis is `none`: the dispatcher falls back
chronologically — no learn/backjump/assert, no jump counters. -/
def noAnalysisCfg : SchedulerConfig (fun _ : Assignment => true) :=
  { actCfg with
    conflict := some { clause := mConflict, learned := [], analysis := none } }

-- The root route never reaches the analyzer: zero resolutions observed.
example : (driveN 2 rootCfg).events.reasonResolutions = 0 := rfl
example : (driveN 2 rootCfg).events.backjumps = 0 := rfl

-- Zero resolutions is NOT the multi-resolution expectation: a test that
-- bypassed the analyze site would fail `PendingMultiResolutionExact`.
example : ¬ T2Fixtures.PendingMultiResolutionExact (driveN 2 rootCfg).events := by
  unfold T2Fixtures.PendingMultiResolutionExact T2Fixtures.mExpansions
  decide

-- Without a recorded analysis there is no jump: 0 backjumps observed.
example : (driveN 2 noAnalysisCfg).events.backjumps = 0 := rfl
example : (driveN 2 noAnalysisCfg).events.assertingEnqueues = 0 := rfl

-- So a run that bypassed the analyzer cannot satisfy the jump predicate.
example : ¬ T2Fixtures.PendingSkippedLevelJumpExact
    (driveN 2 noAnalysisCfg).events := by
  unfold T2Fixtures.PendingSkippedLevelJumpExact
  decide

/-! ## 5. From-`init` reachable run (reachability carried, SAT path)

The root configuration of a tiny box is dispatched by the real
`schedulerNext`; every successor is `SchedulerReachable` by the PROVED
`schedulerReachable_successor`. The observation is honest about what a
conflict-free SAT prefix does to the counters: nothing (all zero). -/

/-- Tiny SAT model: one slot `{0,1}` with the leaf `x0 = 0`. -/
def satLeaf : Assignment → Bool := fun a => a.head? == some (Value.int 0)

def satCfg : SchedulerConfig satLeaf :=
  SchedulerConfig.init (leaf := satLeaf) [[.int 0, .int 1]] [] []

/-- The real dispatcher run from `init`, threaded with the PROVED
reachability closure. -/
def satRun := driveReachN 4 satCfg (schedulerReachable_init _ _ _)

-- The from-init prefix observed on the SAT path records no reason
-- resolutions, no backjump and no asserting enqueue (nothing to learn).
example : satRun.1.events.reasonResolutions = 0 := by decide
example : satRun.1.events.backjumps = 0 := by decide
example : satRun.1.events.assertingEnqueues = 0 := by decide

/-! ## 6. Runtime suite -/

/-- Re-evaluates the observed values (runtime) and reports exit status. -/
def main : IO UInt32 := do
  IO.println "-- T1 activation: dispatcher-observed RuntimeEvents --"
  IO.println s!"  analyze site : reasonResolutions = {afterAnalyze.events.reasonResolutions}"
  IO.println s!"  after jump   : backjumps = {afterJump.events.backjumps}, \
    source = {afterJump.events.sourceLevel}, target = {afterJump.events.targetLevel}, \
    asserting = {afterJump.events.assertingEnqueues}"
  IO.println s!"  controls     : root resolutions = {(driveN 2 rootCfg).events.reasonResolutions}, \
    no-analysis backjumps = {(driveN 2 noAnalysisCfg).events.backjumps}"
  IO.println s!"  from-init SAT prefix: resolutions = {satRun.1.events.reasonResolutions}"
  if afterAnalyze.events.reasonResolutions == 2 &&
      afterJump.events.backjumps == 1 &&
      afterJump.events.sourceLevel == 3 &&
      afterJump.events.targetLevel == 1 &&
      afterJump.events.assertingEnqueues == 1 &&
      (driveN 2 rootCfg).events.reasonResolutions == 0 &&
      (driveN 2 noAnalysisCfg).events.backjumps == 0 then
    IO.println "T1 ACTIVATION OBSERVATIONS CONFIRMED"
    return 0
  else
    IO.eprintln "T1 ACTIVATION OBSERVATIONS FAILED"
    return 1

end T3Activation
