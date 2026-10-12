/-
File: LeanFzn/Solver/UIP/Proofs/SupportedGates.lean

Purpose: S2's frozen interface for the concrete gate producers. Each record
field below is the supported-run restatement of the corresponding
`ArmGates`/`ArmInvGates`/`ArmInvGatesCore` field: the index is
`SupportedReach orig original props` (one run, fixed triple) and the branch
premises use the RUN's `orig` directly (no `cfg.orig` side condition).

Design note (S2 + the PLAN obstruction): the typed-pin fields keep the
`Fits`-restricted shape WITHOUT a per-field shape hypothesis — the shape
discipline is a field of the run's `SupportedInput` hypothesis, so the gate
RECORD PRODUCER (which receives that hypothesis) discharges the pins via
`decidePinFits_int`/`decidePinTyped_int_of_shape`/`decideSkipPrefixTyped_int`.
No shape threading through the assemblers is needed, because the supported
index already fixes the run.

Contents:
  §1 `SupportedArmsPreserveReach` — the supported successor form.
  §2 `supportedReachableBranch_of_preserve` — the `hbr` induction on a
     supported run (root `reachable_init`, step the supported form).
  §3 `SupportedArmGates` (9 fields) and `SupportedArmInvGates` (20 fields):
     the frozen producer targets, signatures copied from the raw records
     with the index substituted.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedGates` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedPhaseRun
import LeanFzn.Solver.UIP.Proofs.SchedulerArmsPreserve
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The supported successor form -/

/-- The reach-aware successor invariant on ONE supported run: every real
dispatcher successor of a supported configuration preserves the branch's
`ReachableState` over the RUN's own box. -/
def SupportedArmsPreserveReach (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg cfg' : SchedulerConfig leaf},
    SupportedReach orig original props cfg →
    (schedulerNext cfg).successor = some cfg' →
    ReachableState leaf orig cfg.branch →
      ReachableState leaf orig cfg'.branch

/-! ## §2 The `hbr` induction on a supported run -/

/-- The supported branch invariant: every supported configuration's branch
is a reachable branch state over the RUN's box. -/
def SupportedBranchInvariant (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf},
    SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch

/-- The `hbr` reduction on a supported run: root `reachable_init`, step the
supported successor form. No `orig` transport is needed (the index fixes
it). -/
theorem supportedReachableBranch_of_preserve {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hpres : SupportedArmsPreserveReach orig original props leaf) :
    SupportedBranchInvariant orig original props leaf := by
  intro cfg h
  induction h with
  | init => exact reachable_init leaf orig
  | step hrec heq ih => exact hpres hrec heq ih

/-- The supported `hbr` premise exactly as the gate fields consume it. -/
theorem supportedHbr_of_preserve {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hpres : SupportedArmsPreserveReach orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch :=
  fun h => supportedReachableBranch_of_preserve hpres h

/-! ## §3 The frozen supported gate records -/

/-- The supported counterpart of `ArmGates`: the per-arm site obligations of
one supported run. The typed-pin fields keep the `Fits`-restricted shape;
their producers consume the run's `SupportedInput.shape` discipline. -/
structure SupportedArmGates (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop where
  /-- the closure contract along the supported run -/
  hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ClosureContract leaf orig original props
  /-- the branch database's unit discipline along the supported run
      (P1 round-2 repair gate; supplied from N1's run invariant) -/
  hunit : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    UnitDB cfg.branch.learned
  /-- the closure's per-deduction payload maintenance step (supplied by
      `unitPayload_of_unitKit` against the unit kit profile) -/
  hpay : UnitPayload original props
  /-- the RECORDED analysis's learned clause is a normalized unit clause
      (the jump plan's inserted clause; N1's recorded-evidence component) -/
  hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → UnitDB [an.learned]
  /-- the recorded evidence's payload is entailed -/
  hentEv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
      LearnedEntailed leaf ev.learned
  /-- the fresh pin is typed at supported split sites over the run's box
      (producer: `decidePinFits_int` with the run's shape discipline) -/
  hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = false →
      ∀ a : Assignment, Assignment.Fits orig a →
        (l.norm.eval a = some true ↔
          a[cfg.branch.frame.2.length]? = some v)
  /-- the redundant pin's extended prefix is typed -/
  hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = true →
      DecideSkipPrefixTyped orig cfg v
  /-- restoration pre-reachability at ACTUAL successful supported jump
      sites: the SUCCESSFUL-perform equation is part of the site
      (`backjumpStep`'s `some restored` branch) and the conflict state's
      branch reachability is the per-site input the producer consumes
      (the same shape as `hpin`/`hskip`). The REJECTION route is a
      separate obligation (`hdeadCheckpointRegion`, E1); the former
      rejection-free shape was uninhabitable because at a rejecting site
      `RestorationPreReachable`'s filter conjunct is false. -/
  hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf},
    SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = some restored →
    RestorationPreReachable leaf orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch
  /-- the consumed pending alternative resumes a reachable branch -/
  hconsume : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}, SupportedReach orig original props cfg →
    cfg.pending = f :: rest → stepConsume cfg = some next →
      ReachableState leaf orig next.branch

/-- The supported counterpart of the 15-field `ArmInvGatesCore`: the residual
gate obligations of one supported run, frozen for the producers. -/
structure SupportedArmInvGatesCore (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop where
  hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ClosureContract leaf orig original props
  /-- the branch database's unit discipline along the supported run
      (P1 round-2 repair gate; see `SupportedArmGates.hunit`) -/
  hunit : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    UnitDB cfg.branch.learned
  /-- the closure's per-deduction payload maintenance step (see
      `SupportedArmGates.hpay`) -/
  hpay : UnitPayload original props
  /-- the RECORDED analysis's learned clause is a normalized unit clause
      (see `SupportedArmGates.hplanU`) -/
  hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → UnitDB [an.learned]
  hlevel : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    CheckpointsBelow cfg
  hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = false →
      ∀ a : Assignment, Assignment.Fits orig a →
        (l.norm.eval a = some true ↔
          a[cfg.branch.frame.2.length]? = some v)
  hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = true →
      DecideSkipPrefixTyped orig cfg v
  hentEv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
      LearnedEntailed leaf ev.learned
  /-- restoration pre-reachability at ACTUAL successful supported jump
      sites: SUCCESS-GUARDED restatement (the rejection-free shape was
      uninhabitable); see `SupportedArmGates.hpre`. -/
  hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf},
    SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = some restored →
    RestorationPreReachable leaf orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch
  hident : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf}, SupportedReach orig original props cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = some restored →
      ∀ cp' ∈ (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored).checkpoints,
        cp'.Identifies (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored).branch cp'.level
  hbc : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf}, SupportedReach orig original props cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = some restored →
      BackjumpCovers leaf orig cfg
        (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored)
  hdeadStableNone : ∀ {cfg : SchedulerConfig leaf} {bs : BranchState leaf},
    SupportedReach orig original props cfg →
    terminalResult cfg.original cfg.props cfg.branch = .stable bs →
    leafWitness leaf cfg = none →
    splitData cfg.branch.frame = none →
      ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  hdeadFallbackNone : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
    ev.analysis = none →
      ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  hdeadFallbackNoCp : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis}, SupportedReach orig original props cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = none →
      ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  /-- the checkpoint-rejection site's registered region is sound. The
      REJECTION premise `perform = none` is part of the site (E1 round:
      the rejection-free shape is refutable). -/
  hdeadCheckpointRegion : ∀ {cfg : SchedulerConfig leaf}
    {cp : DecisionCheckpoint leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis}, SupportedReach orig original props cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = none →
      DeadRegion.Sound leaf (checkpointRegion cp)
  hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}, SupportedReach orig original props cfg →
    cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
      SchedulerInvariant next
  hconsume : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}, SupportedReach orig original props cfg →
    cfg.pending = f :: rest → stepConsume cfg = some next →
      ReachableState leaf orig next.branch
  /-- the REDUNDANT-site pin is typed (`DecidePinTyped`) -/
  hpinSkip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = true → DecidePinTyped cfg l v

/-- The supported counterpart of `ArmInvGates` (17 fields): the shared gates
plus the dead-site gates already produced by `SchedulerDeadSites` at the
supported index. -/
structure SupportedArmInvGates (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop where
  core : SupportedArmInvGatesCore orig original props leaf
  /-- the branch database's unit discipline along the supported run
      (P1 round-2 repair gate; the direct copy of the core field so a
      record-only consumer needs no projection) -/
  hunit : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    UnitDB cfg.branch.learned
  /-- the closure's per-deduction payload maintenance step (see
      `SupportedArmInvGatesCore.hpay`) -/
  hpay : UnitPayload original props
  /-- the RECORDED analysis's learned clause is a normalized unit clause
      (see `SupportedArmInvGatesCore.hplanU`) -/
  hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → UnitDB [an.learned]
  hdeadConflictNil : ∀ {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {cs learned : List Clause}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    terminalResult cfg.original cfg.props cfg.branch = .conflict bs cs learned →
    cs = [] → ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  hdeadLocalExcluded : ∀ {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {lit : Option Literal} {reason : Option Clause} {learned : List Clause},
    SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch →
    terminalResult cfg.original cfg.props cfg.branch =
      .localExcluded bs lit reason learned →
      ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False

end LeanFzn.Solver.UIP
