/-
File: Tests/UIP/SchedulerFixtures.lean

Purpose (PREPARATION task; the new scheduler path is NOT activated here):

  * deterministic SAT/UNSAT models with INDEPENDENTLY checked verdicts and
    SAT witnesses: the exhaustive oracle of T1 (`Tests.UIP.OracleFixtures`,
    imported and REUSED — no oracle is re-implemented here) enumerates the
    solutions, and the certified reference-driver theorems
    (`reference_sat_oracleWitness` / `reference_unsat_oracleSat`) tie the
    current public driver's verdict to it;
  * scheduler fixtures covering the T2a list: root conflict, local
    explanation (branch dead but the problem is NOT globally UNSAT),
    repeated conflicts, duplicate/forced decisions, restored exhaustion and
    sparse/typed boundaries — each expectation either a kernel-checked
    `example ... := rfl` (evaluated today) or a proved theorem;
  * the three activation behaviours (multi-resolution, skipped-level jump,
    post-assertion propagation) as named PENDING predicates over the REAL
    runtime event APIs (`RuntimeEvents` from `SchedulerState`, and O1's
    `AnalysisEvents` counted run `analyzeEvents`/`EventCounts`). The
    fixture-derived expectations (`mExpansions`, `mTargetLevel`) are PROVED
    from the real analyzer run; the driver-level observation is PENDING
    until D1b wires the counter sites. NO counter value is fabricated and
    none of the PENDING predicates is ever applied to a value here.

Why the checks are kernel-checked: `main` (registered by the coordinator)
re-evaluates the `Bool` checks, while each has a `rfl`-proved companion.
`native_decide` is NOT used (it would introduce a trusted axiom); this
module has no `sorry`/`admit`/custom axiom and no Mathlib dependency.

Registration (owned by the coordinator — `lakefile.toml` is NOT edited here):
  [[lean_exe]]
  name = "tests_lcg_scheduler_fixtures"
  root = "Tests.UIP.SchedulerFixtures"

Dependencies: Tests.UIP.OracleFixtures (T1's accepted oracle, reference-driver
theorems, `TestState` runner and the multi-resolution/analyzer fixtures),
LeanFzn.Solver.UIP.AnalysisEvents (O1's exact event counts).
-/

import Tests.UIP.OracleFixtures
import LeanFzn.Solver.UIP.AnalysisEvents
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


open LeanFzn LeanFzn.Solver LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Integration LeanFzn.Solver.Core
open T1Oracle

namespace T2Fixtures

/-! ## 1. Deterministic SAT/UNSAT models and independent verdict checks

The battery reuses T1's accepted problems and adds one local-exclusion model
over the same `LeanFzn.Solver.Propagation.Problem DomConstraint Unit` shape. Counts and witnesses are
checked by the oracle alone (exhaustive enumeration; no propagation, trail,
learning or backjumping is involved). -/

/-- A SAT model with a locally dead branch: `x0 ≤ x1` over
`{0,1} × {0}` — only `(0,0)` is a solution, so the branch `x0 = 1` is dead
while the problem is satisfiable. -/
def famLocalExclude : LeanFzn.Solver.Propagation.Problem DomConstraint Unit :=
  { names := [], domains := [[.int 0, .int 1], [.int 0]],
    constraints := [.leSlot 0 1], objective := (), clauses := [] }

/-- The T2a verdict battery: name, model, expected oracle solution count. -/
def t2Battery : List (String × LeanFzn.Solver.Propagation.Problem DomConstraint Unit × Nat) :=
  [ ("two-ne-int", famTwoNeInt, 2)
  , ("ne-unsat", famNeUnsat, 0)
  , ("bool-not", famBoolNot, 2)
  , ("neg-bounds", famNegBounds, 2)
  , ("sparse", famSparse, 1)
  , ("root-unsat", famRootUnsat, 0)
  , ("long-clause", famLongClause, 8)
  , ("local-exclude", famLocalExclude, 1) ]

/-- The T2a SAT-witness battery: each witness must be accepted by the
independent oracle (fit the boxes, satisfy every constraint and clause). -/
def t2Witnesses : List (String × LeanFzn.Solver.Propagation.Problem DomConstraint Unit × Assignment) :=
  [ ("two-ne-int", famTwoNeInt, [.int 0, .int 1])
  , ("bool-not", famBoolNot, [.bool true, .bool false])
  , ("neg-bounds", famNegBounds, [.int (-3), .int (-2)])
  , ("sparse", famSparse, [.int 5, .int 5])
  , ("long-clause", famLongClause, [.int 0, .int 1])
  , ("local-exclude", famLocalExclude, [.int 0, .int 0]) ]

def checkT2BatteryCounts : Bool :=
  t2Battery.all fun b => oracleCount b.2.1 == b.2.2

def checkT2Witnesses : Bool :=
  t2Witnesses.all fun b => oracleWitnessOk b.2.1 b.2.2

example : checkT2BatteryCounts = true := rfl
example : checkT2Witnesses = true := rfl

/-- Independent verdicts: for every battery model, whatever the current
public reference driver returns is confirmed by the exhaustive oracle
(T1's generic theorem, instantiated over the T2a battery). -/
theorem t2Battery_reference_agrees (b : String × LeanFzn.Solver.Propagation.Problem DomConstraint Unit × Nat)
    (_hb : b ∈ t2Battery) : ReferenceAgrees b.2.1 :=
  referenceAgrees b.2.1

-- The two UNSAT models: the oracle's empty solution list pins the reference
-- verdict through the certified theorem chain (no evaluation of the driver).
theorem t2_neUnsat_driver_unsat : (solveDomWithStats famNeUnsat).1 = .unsat :=
  reference_unsat_of_oracleSat_false rfl

theorem t2_rootUnsat_driver_unsat : (solveDomWithStats famRootUnsat).1 = .unsat :=
  reference_unsat_of_oracleSat_false rfl

-- A SAT witness from the driver (accepted by the oracle) for the
-- local-exclusion model: the dead branch never becomes a global claim.
theorem t2_localExclude_driver_sat :
    ∃ a, (solveDomWithStats famLocalExclude).1 = .sat a :=
  reference_sat_of_oracle_witness (a₀ := [.int 0, .int 0]) rfl

/-! ## 2. Root conflict (level 0)

`famRootUnsat` is UNSAT by the oracle; the scheduler dispatch reports UNSAT
only for a NONEMPTY reported clause at level 0, while an empty clause list
stays LOCAL (`ConflictShape.ofConflict`). -/

/-- The T2a root scheduler configuration over the local-exclusion box. -/
def t2RootCfg : SchedulerConfig (fun _ : Assignment => true) :=
  SchedulerConfig.init (leaf := fun _ => true) [[.int 0, .int 1], [.int 0]] [] []

def t2RootUnsatTag : Bool :=
  match conflictStep t2RootCfg [[negLe 0 5]] [] with
  | .unsat => true
  | _ => false

def t2LocalExcludeTag : Bool :=
  match conflictStep t2RootCfg [] [] with
  | .localExclude _ => true
  | _ => false

def checkT2RootConflict : Bool :=
  t2RootUnsatTag && t2LocalExcludeTag &&
  decide (ConflictShape.ofConflict 0 [posLe 0 1] = .root) &&
  decide (ConflictShape.ofConflict 0 [] = .local) &&
  decide (ConflictShape.ofConflict 3 [] = .local) &&
  (oracleCount famRootUnsat == 0)

example : checkT2RootConflict = true := rfl

/-! ## 3. Local explanation (branch dead, NOT global UNSAT)

The state below is the branch `x0 = 1` of `famLocalExclude` with the learned
unit `x0 ≤ 0` recorded; the closure excludes the branch with an EMPTY local
explanation (no analyzer call, no global claim — INTERFACES §9.3). The
problem itself is SAT with oracle witness `(0,0)`. -/

/-- The dead branch: frame `x0 ∈ {1}`, the decision recorded, the learned
unit `x0 ≤ 0` falsified by the frame. -/
def localDeadState : BranchState (fun _ : Assignment => true) :=
  { frame := ([[.int 1]], []), trail := [mkDec (negNe 0 1) 1], level := 1,
    learned := [[posLe 0 0]] }

def checkT2LocalExplanation : Bool :=
  (match explainedStep [] [] localDeadState with
   | .excluded _ => true
   | _ => false) &&
  (oracleCount famLocalExclude == 1) &&
  oracleWitnessOk famLocalExclude [.int 0, .int 0] &&
  decide (ConflictShape.ofConflict 1 [] = .local)

example : explainedStep [] [] localDeadState = .excluded [] := rfl
example : checkT2LocalExplanation = true := rfl

/-! ## 4. Repeated conflicts

Two conflict clauses on the SAME trail (T1's multi-resolution trail): the
full conflict `mConflict` and the level-3-only sub-conflict `mConflict2`,
both analyzed to completion. Counter accumulation across the two conflict
events is exercised through the REAL `RuntimeEvents.recordResolutions` API
(two `analyzeConflict` sites): 2 + 2 resolutions, no backjump. These are
API-level accumulations, NOT observations of a driver run (D1b wires the
site; the PENDING predicates below state what must then be observed). -/

/-- The level-3-only sub-conflict of T1's multi-resolution trail. -/
def mConflict2 : Clause := [negLe 2 9, negLe 4 2]

/-- Two `analyzeConflict`-site accumulations of the fixture's expansion
counts through the real counter API (no driver is involved). -/
def twoConflictEvents : RuntimeEvents :=
  (({} : RuntimeEvents).recordResolutions 2).recordResolutions 2

def checkT2RepeatedConflicts : Bool :=
  decide (analyzeTrail mTrail 3 mConflict = some ([(negLe 0 5, 1)], posLe 1 7)) &&
  decide (analyzeTrail mTrail 3 mConflict2 = some ([], posLe 2 9)) &&
  (twoConflictEvents.reasonResolutions == 4) &&
  (twoConflictEvents.backjumps == 0) &&
  (twoConflictEvents.sourceLevel == 0) &&
  (twoConflictEvents.targetLevel == 0)

-- Independent second analysis of the same trail: the sub-conflict resolves
-- with an empty below-level part and UIP `x2 ≤ 9` (deterministic evaluation).
example : analyzeTrail mTrail 3 mConflict2 = some ([], posLe 2 9) := rfl

-- The accumulated counters of the two conflict sites.
example : twoConflictEvents.reasonResolutions = 4 := rfl
example : twoConflictEvents.backjumps = 0 := rfl

example : checkT2RepeatedConflicts = true := rfl

/-! ## 5. Duplicate and forced decisions

A genuine branch counts one decision; pinning a singleton head domain is
NOT counted (`stepDecide`'s `vs.isEmpty` guard). A deduction that was
already consumed is skipped on re-dispatch (`.none`), and the recorded
literal is `TrailRedundant`. -/

/-- A database unit `x0 ≠ 0` on the box `{0,1}` (T2's own state; the
oracle-independent half of the duplicate-decision fixture). -/
def t2DupState : BranchState (fun _ : Assignment => true) :=
  { frame := ([[.int 0, .int 1]], []), trail := [], level := 0,
    learned := [[posNe 0 0]] }

/-- The successor after the unit was consumed: `0` removed, one entry
recorded. -/
def t2DupState2 : BranchState (fun _ : Assignment => true) :=
  narrowState t2DupState ([[.int 1]], []) (posNe 0 0) [posNe 0 0] []

def checkT2Decisions : Bool :=
  (stepDecide t2RootCfg (.int 1) [.int 0] [] (negNe 0 1)).stats.decisions == 1 &&
  (stepDecide t2RootCfg (.int 0) [] [] (negNe 0 0)).stats.decisions == 0 &&
  (stepDecide t2RootCfg (.int 1) [.int 0] [] (negNe 0 1)).branch.level == 1 &&
  (explainedDeduction [] [] t2DupState).isSome &&
  decide ((explainedDeduction [] [] t2DupState).map (fun d => d.literal)
    = some (posNe 0 0)) &&
  (explainedDeduction [] [] t2DupState2).isNone &&
  TrailRedundant t2DupState2.trail (posNe 0 0)

example : checkT2Decisions = true := rfl

/-! ## 6. Restored exhaustion

The dead branch `x0 = 1` of `famLocalExclude` is registered as a permanent
dead region; a learn/backjump/assert transition must leave the log intact
and record exactly one backjump + asserting enqueue. The registered region
excludes the dead branch but NOT the surviving SAT witness `(0,0)`. -/

/-- The configuration whose permanent log holds the dead-branch region. -/
def t2ExCfg : SchedulerConfig (fun _ : Assignment => true) :=
  { orig := [[.int 0, .int 1], [.int 0]], original := [], props := [],
    branch := { frame := ([[.int 0, .int 1], [.int 0]], []), trail := [],
                level := 0, learned := [] },
    checkpoints := [], pending := [],
    log := ({} : ExhaustionLog).register
      (DeadRegion.byPrefix ([.int 1, .int 0] : Assignment)) }

/-- The level-0 plan state of the T2a restored-exhaustion fixture. -/
def t2ExCpState : BranchState (fun _ : Assignment => true) :=
  { frame := ([[.int 0, .int 1], [.int 0]], []), trail := [], level := 0,
    learned := [] }

/-- A level-0 plan asserting `x0 = 0` (the sibling of the dead branch). -/
def t2ExPlan : BackjumpPlan (fun _ : Assignment => true) :=
  { target := 0, checkpoint := t2ExCpState, asserting := negNe 0 0,
    learned := [negNe 0 0] }

/-- Recorded conflict evidence of the T2a restored-exhaustion fixture. -/
def t2ExEv : ConflictEvidence :=
  { clause := [negNe 0 0], learned := [], analysis := none }

/-- The restored/narrowed state of the jump. -/
def t2ExRestored : BranchState (fun _ : Assignment => true) :=
  { frame := ([[.int 0]], [.int 0, .int 1]), trail := [], level := 0,
    learned := [] }

/-- The T2a learn/backjump/assert successor. -/
def t2JumpResult : SchedulerConfig (fun _ : Assignment => true) :=
  stepLearnBackjumpAssert t2ExCfg t2ExPlan t2ExEv t2ExRestored

def checkT2RestoredExhaustion : Bool :=
  t2JumpResult.log.regions.any (fun r => r.mem [.int 1, .int 0]) &&
  !(t2JumpResult.log.regions.any (fun r => r.mem [.int 0, .int 0])) &&
  t2JumpResult.log.regions.length == 1 &&
  t2JumpResult.events.backjumps == 1 &&
  t2JumpResult.events.sourceLevel == 0 &&
  t2JumpResult.events.targetLevel == 0 &&
  t2JumpResult.events.assertingEnqueues == 1

-- The jump keeps the permanent log: the dead branch still answers, the SAT
-- witness `(0,0)` was never registered, and the §2.7 counters are recorded.
example : t2JumpResult.log.regions.any (fun r => r.mem [.int 1, .int 0]) = true := rfl
example : t2JumpResult.log.regions.any (fun r => r.mem [.int 0, .int 0]) = false := rfl
example : t2JumpResult.log.regions.length = 1 := rfl
example : t2JumpResult.events.backjumps = 1 := rfl
example : t2JumpResult.events.sourceLevel = 0 := rfl
example : t2JumpResult.events.targetLevel = 0 := rfl
example : t2JumpResult.events.assertingEnqueues = 1 := rfl
example : checkT2RestoredExhaustion = true := rfl

-- Permanence of the registered region under any further registration.
example (log : ExhaustionLog) {p : DeadRegion} (h : p ∈ log.regions)
    (extra : List DeadRegion) :
    p ∈ (extra.foldl ExhaustionLog.register log).regions :=
  ExhaustionLog.registered_permanent h extra

/-! ## 7. Sparse and typed boundaries

The typed 0/1 view (`Value.intView`) makes Boolean and integer values share
the integer read used by bound regions; the decision-literal constructors
keep them separate. Sparse removals collapse exactly as recorded. -/

/-- Three removals for slot 0 (`x0 ≠ 0`, `x0 ≠ 2`, `x0 ≠ 4`). -/
def t2SparseTrail : List TrailEntry :=
  [mkDec (posNe 0 0) 1, mkDec (posNe 0 2) 1, mkDec (posNe 0 4) 1]

def checkT2Boundaries : Bool :=
  decide (Value.intView (.bool true) = some 1) &&
  decide (Value.intView (.int (-3)) = some (-3)) &&
  decide (valueLiteral 0 (.bool true) = some (posBool 0 true)) &&
  decide (valueLiteral 1 (.int 3) = some (negNe 1 3)) &&
  decide ((DeadRegion.below 0 1).mem [.bool true] = false) &&
  decide ((DeadRegion.below 0 1).mem [.bool false] = true) &&
  decide ((DeadRegion.below 0 2).mem [.bool true] = true) &&
  decide ((DeadRegion.above 0 0).mem [.bool true] = true) &&
  decide (removedValues t2SparseTrail 0 = [0, 2, 4])

-- Typed boundary: `.bool true` reads as integer 1 and `.bool false` as 0,
-- while the decision literals stay in their own constructor (`posBool` vs
-- `negNe`), so the two layers never silently mix.
example : (DeadRegion.below 0 1).mem [.bool true] = false := rfl
example : (DeadRegion.below 0 1).mem [.bool false] = true := rfl
example : (DeadRegion.below 0 1).mem [.int 1] = false := rfl
example : (DeadRegion.below 0 1).mem [.int 0] = true := rfl
example : (DeadRegion.below 0 2).mem [.bool true] = true := rfl
example : (DeadRegion.above 0 0).mem [.bool true] = true := rfl
example : removedValues t2SparseTrail 0 = [0, 2, 4] := rfl
example : checkT2Boundaries = true := rfl

/-! ## 8. The three activation behaviours: PENDING D1b predicates

Each predicate is stated over the REAL runtime event APIs — `RuntimeEvents`
(the driver-level record, `SchedulerState.lean`) and, for the anchor values,
O1's counted run `analyzeEvents : ... → Option (EventCounts × _)`.

The anchors are PROVED from the real analyzer run below (they are the
fixture's own analyzer facts, not observed driver counters):

* `mCounts` — the `EventCounts` of the completed counted run of T1's
  multi-resolution conflict: two reason expansions (`mExpansions = 2`),
  then ten scans and three current-level marks;
* `mTargetLevel` — the UIP target of that conflict (`1`, from source 3,
  skipping the irrelevant level 2).

These predicates become RUNTIME OBSERVATIONS only after D1b wires the
counter sites; they are stated and NEVER applied to a value in this module,
so no driver-level counter value is ever assumed.

T1 CONVERSION (done, `Tests/SchedulerActivation`): all three predicates are
now APPLIED FOR REAL to `RuntimeEvents` observed on a real `schedulerNext`
run of the `mTrail`/`mConflict` fixture — `PendingMultiResolutionExact`,
`PendingSkippedLevelJumpExact` and `PendingPostAssertionPropagation` are
kernel-proved there (`rfl`-level), with negative controls showing that a
level-0 bypass and a `none`-analysis fallback fail them. X2's
`runPhaseEvents` itself remains BLOCKED by the D1 premise bundle
(`hpool` — P2/P1-a; `hdb` — S4/S5; `hbr` — S5), which quantifies over every
reachable configuration and is therefore not fixture-instantiable today. -/

/-- The completed counted analyzer run of the multi-resolution fixture. -/
def mEventRun : Option (EventCounts × Option (List (Literal × Nat) × Literal)) :=
  analyzeEvents mTrail 3 (analysisFuel mTrail mConflict)
    (initAnalysisState mConflict)

/-- The event counts of that run (derived, not a driver observation). -/
def mCounts : Option EventCounts := mEventRun.map fun p => p.1

/-- The fixture's reason-expansion count (the multi-resolution anchor). -/
def mExpansions : Nat := (mCounts.map fun c => c.expansions).getD 0

-- The counted run completed at the executable allowance with exactly two
-- reason expansions; `2 + 10 + 1 = 13` decomposes T1's observed trace.
example : mEventRun = some ({ expansions := 2, scans := 10, marks := 3 },
    some ([(negLe 0 5, 1)], posLe 1 7)) := rfl

example : mCounts = some { expansions := 2, scans := 10, marks := 3 } := rfl
example : mExpansions = 2 := rfl
example : mTargetLevel = 1 := rfl

-- O1's exactness theorem instantiated on the fixture: the derived counts
-- decompose the executed trace (expansions + scans + 1 = k), so `2` is the
-- completed run's expansion count, not a fuel bound or a guess.
example : ∃ k : Nat,
    analyzeTrace mTrail 3 (analysisFuel mTrail mConflict)
        (initAnalysisState mConflict)
      = some (k, some ([(negLe 0 5, 1)], posLe 1 7)) ∧
    2 + 10 + 1 = k := by
  obtain ⟨k, hk, har⟩ := analyzeEvents_trace_of_events mTrail 3
    (analysisFuel mTrail mConflict) (initAnalysisState mConflict)
    { expansions := 2, scans := 10, marks := 3 }
    (some ([(negLe 0 5, 1)], posLe 1 7)) rfl
  exact ⟨k, hk, har⟩

/-- PENDING D1b activation — MULTI-RESOLUTION. A scheduled run of this
fixture must observe, through `RuntimeEvents.reasonResolutions` (incremented
only at the `analyzeConflict` site), the fixture's own analyzer count: the
two reason expansions proved in `mExpansions`. This predicate is a
specification; it is NOT applied to any driver value here (there is no
producer before D1b, and asserting one would be fabricated). -/
def PendingMultiResolutionExact (e : RuntimeEvents) : Prop :=
  e.reasonResolutions = mExpansions

/-- PENDING D1b activation — SKIPPED-LEVEL JUMP. A scheduled run of this
fixture must complete exactly one backjump recording source level 3 and the
fixture's proved target `mTargetLevel = 1` — level 2, which carries only the
irrelevant decision `x3 ≠ 1`, is jumped over. Specification only; never
applied to a value here. -/
def PendingSkippedLevelJumpExact (e : RuntimeEvents) : Prop :=
  e.backjumps = 1 ∧ e.sourceLevel = 3 ∧ e.targetLevel = mTargetLevel

/-- PENDING D1b activation — POST-ASSERTION PROPAGATION. The runtime half
(`0 < assertingEnqueues`, recorded at the `learnBackjumpAssert` site) is
PENDING; the second conjunct is the already-executable requirement that the
restored/asserted state admits a productive explained deduction. It is
PROVED below for the accepted post-assertion shape `paState` (T1), so only
the event half must wait for D1b. Specification only; never applied to a
driver value. -/
def PendingPostAssertionPropagation {leaf : Assignment → Bool}
    (e : RuntimeEvents) (post : BranchState leaf) : Prop :=
  0 < e.assertingEnqueues ∧ (explainedDeduction [] [] post).isSome

-- The post-assertion half is checkable TODAY (T1's accepted shape: the
-- assertion `x0 = 0` is enqueued, its reason recorded, and the surviving
-- unit `x1 ≤ 0` is selected); only the `assertingEnqueues` half is PENDING.
example : (explainedDeduction [] [] paState).isSome = true := rfl

/-! ## 9. Executable checks and the runtime suite (`main`) -/

/-- Every executable T2a check. -/
def checkAll : Bool :=
  checkT2BatteryCounts && checkT2Witnesses && checkT2RootConflict &&
  checkT2LocalExplanation && checkT2RepeatedConflicts && checkT2Decisions &&
  checkT2RestoredExhaustion && checkT2Boundaries

example : checkAll = true := rfl

/-- Runtime suite (T1's `main` style; the coordinator registers it). NOTE:
`Tests.UIP.OracleFixtures` declares the top-level name `main` (its own runner),
so this module cannot redeclare a root-level `main`; the registerable root
is a one-line wrapper owned by the coordinator:
`Tests/SchedulerRunner.lean` with
`import Tests.UIP.SchedulerFixtures` + `def main : IO UInt32 := T2Fixtures.main`.
Re-evaluates every executable T2a check and lists the PENDING D1b activation
predicates without asserting any driver-level counter value. -/
def main : IO UInt32 := do
  let mut st : TestState := { passed := 0, failed := 0 }
  IO.println "-- T2a scheduler fixtures (prepared; activation PENDING D1b) --"
  st ← st.check "SAT/UNSAT battery: oracle counts" checkT2BatteryCounts
  st ← st.check "SAT witnesses accepted by the independent oracle" checkT2Witnesses
  st ← st.check "root conflict (level 0) and local empty-clause dispatch"
    checkT2RootConflict
  st ← st.check "local explanation: branch dead, problem globally SAT"
    checkT2LocalExplanation
  st ← st.check "repeated conflicts: two analyses, accumulated event API"
    checkT2RepeatedConflicts
  st ← st.check "duplicate/forced decisions and duplicate deductions"
    checkT2Decisions
  st ← st.check "restored exhaustion: log preserved, counters recorded"
    checkT2RestoredExhaustion
  st ← st.check "sparse/typed boundaries" checkT2Boundaries
  IO.println "PENDING D1b predicates are now APPLIED FOR REAL in Tests/SchedulerActivation"
  IO.println "  (dispatcher-observed values; runPhaseEvents itself blocked by CompiledPhasePremises):"
  IO.println "  T2Fixtures.PendingMultiResolutionExact      (RuntimeEvents.reasonResolutions)"
  IO.println "  T2Fixtures.PendingSkippedLevelJumpExact     (RuntimeEvents.backjumps/source/target)"
  IO.println "  T2Fixtures.PendingPostAssertionPropagation  (RuntimeEvents.assertingEnqueues)"
  if st.failed == 0 then
    IO.println s!"ALL {st.passed} T2a SCHEDULER FIXTURE CHECKS PASSED"
    return 0
  else
    IO.eprintln s!"{st.failed} T2a SCHEDULER FIXTURE CHECKS FAILED ({st.passed} passed)"
    return 1

end T2Fixtures
