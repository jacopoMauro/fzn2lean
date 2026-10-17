/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerArmGatesProduced.lean

Purpose: B4's CONCRETE RECORD PRODUCER. `ArmInvGates` — the §6 gate record of
`Proofs/SchedulerArmsPreserve.lean` — has two dead-site fields that are now
DISCHARGED by the verified producers in `Proofs/SchedulerDeadSites.lean`:
`hdeadConflictNil` and `hdeadLocalExcluded` (both restated with an explicit
branch-reachability premise `ReachableState leaf cfg.orig cfg.branch`, which
is exactly what the producers consume). This module names the residual
obligations in `ArmInvGatesCore` and derives the FULL record from them.

CONTENT.

  * `ArmInvGatesCore` — `ArmInvGates` MINUS `hdeadConflictNil` and
    `hdeadLocalExcluded`, signatures copied verbatim. Its 18 fields are the
    named residual obligations that still have no producer: `hclos`,
    `hunit`, `hpay`, `hplanU`, `hlevel`, `hpin`, `hskip`, `hentEv`, `hpre`,
    `hident`, `hbc`, `hdeadStableNone` (needs the witness premise),
    `hdeadFallbackNone`, `hdeadFallbackNoCp`, `hdeadCheckpointRegion`,
    `hconsumeInv`, `hconsume`, `hpinSkip`.

  * `ArmInvGatesCore.toArmInvGates` — fills the full record: the core fields
    directly, and the two dead-site fields by
    `deadConflictNil_of_terminalEvent` / `deadLocalExcluded_of_terminalEvent`
    applied to the core closure gate at the configuration under
    quantification (`hc.hclos hreach`) and the gate's own branch
    reachability premise.

DAG edge:
  Proofs.SchedulerArmsPreserve + Proofs.SchedulerDeadSites -> this module.
  (`SchedulerDeadSites` already imports `SchedulerArmsPreserve` transitively
  through `SchedulerRunAssembly`, so this module is the shallowest place the
  two names can meet; `SchedulerArmsPreserve` itself must NOT import
  `SchedulerDeadSites` — that would close an import cycle.)

NO sorry, NO custom axiom.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerArmsPreserve
import LeanFzn.Solver.UIP.Proofs.SchedulerDeadSites
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The residual gate record (dead-site fields removed) -/

/-- `ArmInvGates` minus the two dead-site fields already produced by
`Proofs.SchedulerDeadSites.lean` (`hdeadConflictNil`, `hdeadLocalExcluded`).
All 18 remaining fields are copied VERBATIM from `ArmInvGates` and are the
named residual obligations still owed producers. -/
structure ArmInvGatesCore (leaf : Assignment → Bool) : Prop where
  hclos : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    ClosureContract leaf cfg.orig cfg.original cfg.props
  /-- the branch database's unit discipline along the run (P1 round-2
      repair gate; same as `ArmGates.hunit`) -/
  hunit : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    UnitDB cfg.branch.learned
  /-- the closure's per-deduction payload maintenance step (same as
      `ArmGates.hpay`) -/
  hpay : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    UnitPayload cfg.original cfg.props
  /-- the RECORDED analysis's learned clause is a normalized unit clause
      (same as `ArmGates.hplanU`) -/
  hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis},
    SchedulerReachable cfg → cfg.conflict = some ev → ev.analysis = some an →
      UnitDB [an.learned]
  hlevel : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    CheckpointsBelow cfg
  hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SchedulerReachable cfg →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = false →
      ∀ a : Assignment, a.Fits cfg.orig →
        (l.norm.eval a = some true ↔
          a[cfg.branch.frame.2.length]? = some v)
  hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SchedulerReachable cfg →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = true →
      DecideSkipPrefixTyped cfg.orig cfg v
  hentEv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence},
    SchedulerReachable cfg → cfg.conflict = some ev →
      LearnedEntailed leaf ev.learned
  /-- restoration pre-reachability at ACTUAL successful jump sites
      (SUCCESS-GUARDED; the rejection-free shape was uninhabitable). -/
  hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf}, SchedulerReachable cfg →
    ReachableState leaf cfg.orig cfg.branch →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
    RestorationPreReachable leaf cfg.orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch
  hident : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf}, SchedulerReachable cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
      ∀ cp' ∈ (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored).checkpoints,
        cp'.Identifies (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored).branch cp'.level
  hbc : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf}, SchedulerReachable cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
      BackjumpCovers leaf cfg.orig cfg
        (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored)
  hdeadStableNone : ∀ {cfg : SchedulerConfig leaf} {bs : BranchState leaf},
    SchedulerReachable cfg →
    terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs →
    leafWitness leaf cfg = none →
    splitData cfg.branch.frame = none →
      ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  hdeadFallbackNone : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence},
    SchedulerReachable cfg → cfg.conflict = some ev → ev.analysis = none →
      ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  hdeadFallbackNoCp : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis}, SchedulerReachable cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = none →
      ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  /-- the checkpoint-rejection site's registered region is sound (its
      prefix region, `checkpointRegion cp`). RESTATED (E1 round): the
      REJECTION premise `perform = none` is part of the site. -/
  hdeadCheckpointRegion : ∀ {cfg : SchedulerConfig leaf}
    {cp : DecisionCheckpoint leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis}, SchedulerReachable cfg →
    cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = none →
      DeadRegion.Sound leaf (checkpointRegion cp)
  hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}, SchedulerReachable cfg →
    cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
      SchedulerInvariant next
  /-- the consumed pending alternative resumes a reachable branch (B2/B3;
      §5's gate — carried here so ONE gate record serves both assemblies) -/
  hconsume : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}, SchedulerReachable cfg →
    cfg.pending = f :: rest → stepConsume cfg = some next →
      ReachableState leaf cfg.orig next.branch
  /-- the REDUNDANT-site pin is typed (the skip arm's `DecidePinTyped`;
      Bool discharged internally by `decidePinTyped_bool`) -/
  hpinSkip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SchedulerReachable cfg →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = true → DecidePinTyped cfg l v

/-! ## §2 The full record from the residuals -/

/-- **B4's CONCRETE RECORD PRODUCER**: the full `ArmInvGates` from
`ArmInvGatesCore`. The 18 core fields pass through directly; the two
dead-site fields are DISCHARGED by the axiom-clean `SchedulerDeadSites`
producers, each fed with the core closure gate at the configuration under
quantification (`hc.hclos hreach`) and the field's own branch-reachability
premise. The core fields are exactly the named residual obligations: `hclos`,
`hunit`, `hpay`, `hplanU`, `hlevel`, `hpin`, `hskip`, `hentEv`, `hpre`,
`hident`, `hbc`, `hdeadStableNone` (with its witness premise),
`hdeadFallbackNone`, `hdeadFallbackNoCp`, `hdeadCheckpointRegion`,
`hconsumeInv`, `hconsume`, `hpinSkip`. -/
theorem ArmInvGatesCore.toArmInvGates {leaf : Assignment → Bool}
    (hc : ArmInvGatesCore leaf) : ArmInvGates leaf where
  hclos := hc.hclos
  hunit := hc.hunit
  hpay := hc.hpay
  hplanU := hc.hplanU
  hlevel := hc.hlevel
  hpin := hc.hpin
  hskip := hc.hskip
  hentEv := hc.hentEv
  hpre := hc.hpre
  hident := hc.hident
  hbc := hc.hbc
  hdeadStableNone := hc.hdeadStableNone
  hdeadConflictNil := fun hreach hbs ht hcs =>
    deadConflictNil_of_terminalEvent (hc.hclos hreach) hbs ht hcs
  hdeadLocalExcluded := fun hreach hbs ht =>
    deadLocalExcluded_of_terminalEvent (hc.hclos hreach) hbs ht
  hdeadFallbackNone := hc.hdeadFallbackNone
  hdeadFallbackNoCp := hc.hdeadFallbackNoCp
  hdeadCheckpointRegion := hc.hdeadCheckpointRegion
  hconsumeInv := hc.hconsumeInv
  hconsume := hc.hconsume
  hpinSkip := hc.hpinSkip

end LeanFzn.Solver.UIP
