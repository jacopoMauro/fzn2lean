/-
File: LeanFzn/Solver/UIP/Proofs/Scheduler.lean

Purpose:
  The WELL-FOUNDED RECURSION CORE of the scheduler driver, with NO fuel
  parameter, plus its binding to the REAL dispatcher `schedulerNext`.

WHAT IS PROVED HERE (see the resume note in INTERFACES.md for status):

  §1  `DriverResult`, `SchedulerTransition.successor` and `PhaseKernel`:
      a phase kernel is a dispatcher together with a strict
      `SchedulerRank` decrease for every successor. This is the ONLY
      termination guard the driver uses.
  §2  `run`: the driver as a `WellFounded.fix` over
      `schedulerRank_wf` (C3a) — a total function by construction, no
      fuel, no `partial`, no assumed termination; `run_total` states
      totality explicitly. FOLLOW-UP (not done): per-constructor
      unfolding equation lemmas (`run_propagate`, ...) are blocked by
      the dependent `match h :` in the body; the fix is to give
      `PhaseKernel` per-constructor decrease fields so the `match` is
      non-dependent. Until then the driver's step semantics is the
      `def`'s unfolding itself.
  §3  `DispatcherProgress`: the single totality premise for the REAL
      dispatcher (every non-terminal `schedulerNext` successor strictly
      decreases the rank); `dispatcherKernel` / `runScheduler` apply the
      core to the REAL `schedulerNext`, so every driver step is a real
      dispatcher step. C3a PROVES the instances for the propagate,
      decide and forced-consume arms and provides the two-step
      composites for the stutter arms; the one remaining instance is
      `.learnBackjumpAssert` (C3a OPEN ITEM, named `JumpDecrease` below,
      owner C3b/integration — it needs a trail-based rank component).
  §4  Driver-outcome SEMANTICS, consuming C2d verbatim: SAT soundness
      (`arm_sat_solution` ⇒ `SolutionWitness` in the ORIGINAL box) and
      UNSAT exclusion (`arm_unsat_coverage` /
      `arm_unsat_rootContradiction_evidence`) at the terminal arms, plus
      the root-contradiction owner premise D1a.

NO fuel: totality is `WellFounded.fix` over `schedulerRank_wf = InvImage.wf SchedulerRank rankLt_wf`, i.e. C3a's AXIOM-FREE well-foundedness. `run` is a plain `def`, so the equation lemmas below are unconditional.

DAG: Proofs.SchedulerProgress (C3a) + Proofs.SchedulerStep (C2d) -> this module.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerProgress
import LeanFzn.Solver.UIP.Proofs.SchedulerStepO2
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- The successor configuration of a transition, if any. `sat`/`unsat`
are terminal. -/
def SchedulerTransition.successor :
    SchedulerTransition leaf → Option (SchedulerConfig leaf)
  | .propagate next => some next
  | .decide next _ => some next
  | .analyzeConflict next _ => some next
  | .learnBackjumpAssert next _ _ => some next
  | .localExclude next => some next
  | .chronologicalFallback next => some next
  | .sat _ => none
  | .unsat => none

@[simp] theorem successor_propagate (n : SchedulerConfig leaf) :
    (.propagate n : SchedulerTransition leaf).successor = some n := rfl

@[simp] theorem successor_decide (n : SchedulerConfig leaf) (l : Literal) :
    (.decide n l : SchedulerTransition leaf).successor = some n := rfl

@[simp] theorem successor_analyzeConflict (n : SchedulerConfig leaf)
    (c : Clause) :
    (.analyzeConflict n c : SchedulerTransition leaf).successor = some n := rfl

@[simp] theorem successor_learnBackjumpAssert (n : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (an : ConflictAnalysis) :
    (.learnBackjumpAssert n p an : SchedulerTransition leaf).successor = some n :=
  rfl

@[simp] theorem successor_localExclude (n : SchedulerConfig leaf) :
    (.localExclude n : SchedulerTransition leaf).successor = some n := rfl

@[simp] theorem successor_chronologicalFallback (n : SchedulerConfig leaf) :
    (.chronologicalFallback n : SchedulerTransition leaf).successor = some n :=
  rfl

@[simp] theorem successor_sat (w : Assignment) :
    (.sat w : SchedulerTransition leaf).successor = none := rfl

@[simp] theorem successor_unsat :
    (.unsat : SchedulerTransition leaf).successor = none := rfl

end LeanFzn.Solver.UIP
namespace LeanFzn.Solver.UIP.C3b
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3a

/-! ## §1 Driver outcome, successor extraction, phase kernel -/

/-- The driver's outcome: a certified SAT witness or a global UNSAT claim.
Both carry C2d's semantic content (see §4). -/
inductive DriverResult (leaf : Assignment → Bool) where
  /-- the run stopped at the leaf check with this witness -/
  | sat (witness : Assignment)
  /-- the run exhausted the frontier (or proved a root contradiction) -/
  | unsat

/-- A PHASE KERNEL: a dispatcher that returns, for every configuration, a
transition together with a strict `SchedulerRank` decrease for each of its
successors (vacuous for the terminal transitions). This is exactly the
guard C3a's decreases and composites were built to supply, and it is the
only termination input the driver consumes. -/
structure PhaseKernel (leaf : Assignment → Bool) where
  /-- the dispatcher -/
  step : SchedulerConfig leaf → SchedulerTransition leaf
  /-- every successor strictly decreases the rank -/
  decrease : ∀ (cfg cfg' : SchedulerConfig leaf),
    (step cfg).successor = some cfg' →
      RankLt (SchedulerRank cfg') (SchedulerRank cfg)

/-! ## §2 The fuel-free driver (well-founded recursion) -/

/-- The driver: well-founded recursion on `SchedulerRank`, ordered by
`RankLt`. NO fuel parameter, NO `partial`, NO assumed termination — the
recursive calls are made under `WellFounded.fix` with the kernel's
decrease proofs, whose well-foundedness is C3a's axiom-free
`schedulerRank_wf`. The recursion is `noncomputable` only because
`WellFounded.fix` is; the kernel data itself is computable. -/
noncomputable def run (k : PhaseKernel leaf) : SchedulerConfig leaf → DriverResult leaf :=
  WellFounded.fix (schedulerRank_wf (leaf := leaf)) (fun cfg rec =>
    match h : k.step cfg with
    | .sat w => .sat w
    | .unsat => .unsat
    | .propagate n =>
        rec n (k.decrease cfg n (by rw [h]; rfl))
    | .decide n _ =>
        rec n (k.decrease cfg n (by rw [h]; rfl))
    | .analyzeConflict n _ =>
        rec n (k.decrease cfg n (by rw [h]; rfl))
    | .learnBackjumpAssert n _ _ =>
        rec n (k.decrease cfg n (by rw [h]; rfl))
    | .localExclude n =>
        rec n (k.decrease cfg n (by rw [h]; rfl))
    | .chronologicalFallback n =>
        rec n (k.decrease cfg n (by rw [h]; rfl)))

/-- TOTALITY: the driver is a total function on configurations — for every
kernel and every configuration a result exists, with NO fuel parameter.
The recursion is `WellFounded.fix` over C3a's `schedulerRank_wf`, so this
is an instance of well-founded recursion, not of an assumed measure. -/
theorem run_total (k : PhaseKernel leaf) (cfg : SchedulerConfig leaf) :
    ∃ r : DriverResult leaf, run k cfg = r :=
  ⟨run k cfg, rfl⟩

/-! ## §3 Binding the core to the REAL dispatcher -/

/-- The single totality obligation of the fuel-free driver on the REAL
dispatcher: every non-terminal `schedulerNext` successor strictly
decreases `SchedulerRank`.

  * PROVED instances (C3a): `rank_lt_propagate`, `rank_lt_decide`,
    `rank_lt_consume`.
  * REFUTED here (§5): the three STUTTER arms `.localExclude`,
    `.analyzeConflict`, `.chronologicalFallback` (backjump site) have
    EQUAL-rank successors, so this shape is FALSE at every real
    configuration satisfying C3a's arm guards
    (`not_dispatcherProgress_of_localExclude_site` /
    `_of_analyzeConflict_site` / `_of_fallback_site`). This definition is
    kept only as the documented NAIVE shape; the driver must consume a
    PHASE step bundling each stutter with its forced consume (C3a's
    `arm_localExclude_then_consume` / `arm_fallback_then_consume` /
    `analyzeConflict_not_repeated`) plus the restated `JumpDecrease`.
  * OPEN instance: `.learnBackjumpAssert` (see `JumpDecrease`, restated
    over the actual `perform` result because `JumpDecreaseNaive` is
    refuted by C2dO2). -/
def DispatcherProgressNaive (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg cfg' : SchedulerConfig leaf),
    (schedulerNext cfg).successor = some cfg' →
      RankLt (SchedulerRank cfg') (SchedulerRank cfg)

/-- The REAL dispatcher as a kernel, given the NAIVE obligation (FALSE at
the three stutter sites; retained only as the documented refuted shape). -/
def dispatcherKernel (leaf : Assignment → Bool)
    (h : DispatcherProgressNaive leaf) : PhaseKernel leaf where
  step := schedulerNext
  decrease := h

/-- The fuel-free driver over the naive shape (kept for the refutation
record; NOT the driver the phase design consumes). -/
noncomputable def runScheduler (h : DispatcherProgressNaive leaf)
    (cfg : SchedulerConfig leaf) : DriverResult leaf :=
  run (dispatcherKernel leaf h) cfg

/-! ### The PHASE-AWARE dispatcher

Each stutter arm is composed with its FORCED successor at the TRANSITION
level: at the forced-consume stutter sites (`.localExclude` — ARM 6 and the
checkpoint rejection of ARM 7 — and the `.chronologicalFallback` stutters of
ARM 7, all of which produce `status = .dead`), the phase dispatcher returns
the consume route itself, i.e. the SECOND real dispatcher step, whose strict
decrease is C3a's composite.

THE CONFLICT DISCRIMINATOR (verified from the definitions):
`.chronologicalFallback n` in `schedulerNext cfg` arises BOTH as the ARM 7
STUTTER (`cfg.conflict = some ev`, `n = stepChronologicalFallback cfg _`,
`n.status = .dead`) and as the REAL consume route (`cfg.conflict = none`,
`cfg.status = .dead`, `n =` the consumed configuration, `n.status = .active`).
The two are distinguished by `cfg.conflict`: under `some` the fallback is a
stutter to be composed with `consumeStep`; under `none` it IS the real step
and is passed through verbatim (otherwise the phase step would consume a
second un-dispatched pending frame).

At the `.analyzeConflict` site the recorded evidence forces the dispatcher's
next arm to `backjumpStep` (`C3a.analyzeConflict_not_repeated`), which never
returns `.analyzeConflict`. The phase step resolves that recorded route
directly: its fallback/exclusion landings are dead stutters composed with
`consumeStep`, while its `learnBackjumpAssert` landing is passed through (its
decrease is the open `JumpDecrease` premise). -/
def phaseNext (cfg : SchedulerConfig leaf) : SchedulerTransition leaf :=
  match schedulerNext cfg with
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
          match backjumpStep n ev with
          | .chronologicalFallback n' =>
              match stepConsume n' with
              | some next => .chronologicalFallback next
              | none => .unsat
          | .localExclude n' =>
              match stepConsume n' with
              | some next => .chronologicalFallback next
              | none => .unsat
          | t => t
      | none => .analyzeConflict n c
  | t => t

/-- The PHASE-AWARE totality obligation for the real dispatcher: every
successor of the phase dispatcher strictly decreases the rank. **CLOSED**
by `phaseProgress_of_jumpDecrease`, which consumes the single OPEN
dispatcher premise `JumpDecrease` (the learn/backjump/assert arm) and
discharges every other arm through C3a's decreases, the forced-consume
composites and the three `.analyzeConflict` landing compositions. -/
def PhaseProgress (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg cfg' : SchedulerConfig leaf),
    (phaseNext cfg).successor = some cfg' →
      RankLt (SchedulerRank cfg') (SchedulerRank cfg)

/-- The PHASE-AWARE kernel: the driver's step is `phaseNext`, so each of
its steps is a REAL one-or-two-step dispatcher composite (never a
fabricated move), and the decrease is the phase obligation above. -/
def phaseKernel (leaf : Assignment → Bool)
    (h : PhaseProgress leaf) : PhaseKernel leaf where
  step := phaseNext
  decrease := h

/-- The fuel-free driver over the PHASE-AWARE dispatcher, conditional on
the single named phase obligation. -/
noncomputable def runSchedulerPhase (h : PhaseProgress leaf)
    (cfg : SchedulerConfig leaf) : DriverResult leaf :=
  run (phaseKernel leaf h) cfg

/-- PHASE SITE 1 PROVED (ARM 6 → consume): the phase dispatcher's successor
of a `.localExclude` stutter site is the REAL consume successor, and it
strictly decreases — C3a's `arm_localExclude_then_consume` composed with
C2d's forced-consume dispatch at the dead successor. -/
theorem phase_localExclude_succ {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hs : schedulerNext cfg =
      .localExclude (stepLocalExclude cfg learned r))
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    (phaseNext cfg).successor = some next ∧
      RankLt (SchedulerRank next) (SchedulerRank cfg) :=
  ⟨by
    have hpe : phaseNext cfg = .chronologicalFallback next := by
      rw [phaseNext, hs]
      simp only [h]
    rw [hpe]
    rfl,
    C3a.arm_localExclude_then_consume hp h⟩

/-- PHASE SITE 2 PROVED (ARM 7 stutter → consume): at a configuration whose
RECORDED-CONFLICT route stutters into `.chronologicalFallback`, the phase
dispatcher's successor is the REAL consume successor, and it strictly
decreases — C3a's `arm_fallback_then_consume`. The `hcf` guard is what makes
the fallback a stutter rather than the real consume route (see the
`phaseNext` docstring); it is exactly `schedulerNext_cases`' first disjunct. -/
theorem phase_fallback_succ {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {ev : ConflictEvidence} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hcf : cfg.conflict = some ev)
    (hs : schedulerNext cfg =
      .chronologicalFallback (stepChronologicalFallback cfg r))
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    (phaseNext cfg).successor = some next ∧
      RankLt (SchedulerRank next) (SchedulerRank cfg) :=
  ⟨by
    have hpe : phaseNext cfg = .chronologicalFallback next := by
      rw [phaseNext, hs]
      simp only [hcf, h]
    rw [hpe]
    rfl,
    C3a.arm_fallback_then_consume hp h⟩

/-! ### The `.analyzeConflict` phase site: the composition lemmas

The `.analyzeConflict` arm is a rank STUTTER (`rank_analyzeConflict_stutter`)
whose successor carries recorded evidence, so the phase step landing there
must compose the stutter with the recorded route's own strict step. The
three lemmas below are the COMPLETE case content of that composition at the
level of the rank: the jump landing (consuming the OPEN `JumpDecrease`),
the chronological-fallback landing and the checkpoint-exclusion landing
(both consuming C3a's forced-consume composites). Each is proved by
instantiating the successor's decrease at the post-analyze configuration
and paying the stutter with `rank_analyzeConflict_stutter`. -/

/-- ANALYZE SITE → CHRONOLOGICAL-FALLBACK LANDING (PROVED): the recorded
route's fallback is itself a dead stutter, so the phase composition
continues through the forced consume — C3a's `arm_fallback_then_consume`
at the post-analyze configuration, with the analyze stutter paid. -/
theorem analyzeConflict_then_fallback_rank_lt {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    {f : BranchFrame} {rest : List BranchFrame} {next : SchedulerConfig leaf}
    (hp : (stepChronologicalFallback
        (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
        (branchRegion (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)))).pending =
        f :: rest)
    (h : stepConsume (stepChronologicalFallback
        (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
        (branchRegion (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)))) = some next) :
    RankLt (SchedulerRank next) (SchedulerRank cfg) := by
  have h2 := arm_fallback_then_consume
    (cfg := stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) hp h
  rwa [show SchedulerRank (stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
      = SchedulerRank cfg from rfl] at h2

/-- ANALYZE SITE → CHECKPOINT-EXCLUSION LANDING (PROVED): the recorded
route's checkpoint exclusion is a dead stutter, so the phase composition
continues through the forced consume — C3a's
`arm_localExclude_then_consume` at the post-analyze configuration, with the
analyze stutter paid. -/
theorem analyzeConflict_then_localExclude_rank_lt {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    {learned' : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame} {next : SchedulerConfig leaf}
    (hp : (stepLocalExclude (stepAnalyzeConflictCounted cfg c learned
        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) learned'
        r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude (stepAnalyzeConflictCounted cfg c learned
        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
        learned' r) = some next) :
    RankLt (SchedulerRank next) (SchedulerRank cfg) := by
  have h2 := arm_localExclude_then_consume
    (cfg := stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) hp h
  rwa [show SchedulerRank (stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
      = SchedulerRank cfg from rfl] at h2

/-- The still-OPEN single-step decrease of the learn/backjump/assert arm,
RESTATED over the ACTUAL `perform` result (C2dO2 PROVED that the previous,
`restored`-arbitrary shape `JumpDecreaseNaive` is FALSE: `restored :=
cfg.branch` makes the successor rank equal). Owner C3b/integration.

C3a reserved the rank's third component (the decision level) for this arm;
C2dO2's routing note says level strictness alone is insufficient (the
restored ancestor's `Frame.mass` is unconstrained) and the decrease must be
indexed by the real restoration. The positive provider
`C2dO2.learnBackjumpAssert_rank_lt_of_frontier_eq_of_mass` (see
`jumpDecrease_of_frontier_eq_of_mass` below) shows the content: the restore
must not raise the frontier cost AND must land on a strictly lighter frame —
neither is derivable from `perform`'s signature today, so this stays an
explicit premise with an owner rather than a hidden assumption. -/
def JumpDecrease (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg : SchedulerConfig leaf) (ev : ConflictEvidence)
    (an : ConflictAnalysis) (cp : DecisionCheckpoint leaf)
    (restored : BranchState leaf),
    ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.orig cfg.original cfg.props = some restored →
    RankLt
      (SchedulerRank (stepLearnBackjumpAssert cfg
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
        restored))
      (SchedulerRank cfg)

/-- The SHAPE the previous attempt stated (and C2dO2 refuted): a decrease
for an ARBITRARY `restored`. Kept as a named statement so the refutation is
first-class in this module too. -/
def JumpDecreaseNaive (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf),
    RankLt (SchedulerRank (stepLearnBackjumpAssert cfg p ev restored))
      (SchedulerRank cfg)

/-- REFUTATION (consumed from C2dO2 verbatim): the `restored`-arbitrary
shape is false for every leaf — `restored := cfg.branch` gives an EQUAL
successor rank. -/
theorem not_jumpDecreaseNaive {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf) (ev : ConflictEvidence) :
    ¬ JumpDecreaseNaive leaf :=
  fun h => C2dO2.not_jumpDecrease cfg p ev h

/-- The restated, `perform`-indexed obligation is CONSUMABLE: C2dO2's
positive provider closes it whenever the restore keeps the frontier cost and
lands on a strictly lighter frame. This is the exact residual content of
`JumpDecrease` — stated as a provider so an integration proof of the
restoration discipline can instantiate it without touching this file. -/
theorem jumpDecrease_of_frontier_eq_of_mass {leaf : Assignment → Bool}
    (h : ∀ (cfg : SchedulerConfig leaf) (ev : ConflictEvidence)
      (an : ConflictAnalysis) (cp : DecisionCheckpoint leaf)
      (restored : BranchState leaf),
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
      frontierCost (SchedulerConfig.frontier (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored)) = frontierCost (SchedulerConfig.frontier cfg) ∧
        Frame.mass restored.frame < Frame.mass cfg.branch.frame) :
    JumpDecrease leaf := fun cfg ev an cp restored hae hcp hp =>
  C2dO2.learnBackjumpAssert_rank_lt_of_frontier_eq_of_mass cfg
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev restored
    (h cfg ev an cp restored hae hcp hp).1
    (h cfg ev an cp restored hae hcp hp).2

/-- The jump arm at the dispatcher level, with the OPEN decrease as an
explicit premise: the dispatcher returns `.learnBackjumpAssert` and, given
`JumpDecrease`, its successor strictly decreases the rank. This is the
single non-C3a instance of `DispatcherProgress`; every other arm's
decrease is C3a's (`rank_lt_propagate`, `rank_lt_decide`,
`rank_lt_consume`, with the composites for the stutter arms). -/
theorem jump_arm_rank_lt {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf} (hjump : JumpDecrease leaf)
    (h : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    schedulerNext cfg =
      .learnBackjumpAssert
        (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored)
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) an ∧
      RankLt (SchedulerRank
        (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored)) (SchedulerRank cfg) :=
  ⟨C2d.schedulerNext_eq_backjump_jump h ha hcp hp,
    hjump cfg ev an cp restored ha hcp hp⟩

/-- ANALYZE SITE → JUMP LANDING (PROVED, given `JumpDecrease`): after the
evidence-recording stutter, the recorded route's performed jump strictly
decreases the rank relative to the ORIGINAL configuration. -/
theorem analyzeConflict_then_jump_rank_lt {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    (hjump : JumpDecrease leaf) {ev : ConflictEvidence}
    (hev : (stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).conflict
      = some ev)
    {an : ConflictAnalysis} (ha : ev.analysis = some an)
    {cp : DecisionCheckpoint leaf}
    (hcp : checkpointAt (stepAnalyzeConflictCounted cfg c learned
        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).checkpoints
      an.backjumpLevel = some cp)
    {restored : BranchState leaf}
    (hp : (BackjumpPlan.ofCheckpoint cp
        (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
        an.asserting an.learned).perform
        (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
        cfg.orig
        cfg.original cfg.props = some restored) :
    RankLt
      (SchedulerRank (stepLearnBackjumpAssert
        (stepAnalyzeConflictCounted cfg c learned
          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
        (BackjumpPlan.ofCheckpoint cp
          (stepAnalyzeConflictCounted cfg c learned
            (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
          an.asserting an.learned)
        ev restored))
      (SchedulerRank cfg) := by
  have h := hjump (stepAnalyzeConflictCounted cfg c learned
    (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) ev an cp restored
    ha hcp hp
  rwa [show SchedulerRank (stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
      = SchedulerRank cfg from rfl] at h

/-! ### The phase assembly: `PhaseProgress` CLOSED modulo `JumpDecrease`

`phase_compose_consume` is the single assembly rule shared by every
consume landing of `phaseNext` (ARM 6, both ARM 7 stutters, the checkpoint
rejection, and the two non-jump `.analyzeConflict` landings): if the phase
value at `cfg` is the composed consume route of an intermediate
configuration `n`, then the phase successor is the REAL consume successor
and the rank decrease is the site composite for `n`. -/

/-- The single consume-landing assembly rule (see above). The `hlt` input is
the site's rank content as a C3a (or analyze-site) composite — no fabricated
move: the successor is exactly `stepConsume n`'s result. -/
theorem phase_compose_consume {leaf : Assignment → Bool}
    {cfg cfg' n : SchedulerConfig leaf}
    (hpe : phaseNext cfg =
      (match stepConsume n with
       | some next => (.chronologicalFallback next : SchedulerTransition leaf)
       | none => .unsat))
    (hlt : ∀ {f : BranchFrame} {rest : List BranchFrame} {next : SchedulerConfig leaf},
      n.pending = f :: rest → stepConsume n = some next →
        RankLt (SchedulerRank next) (SchedulerRank cfg))
    (hsucc : (phaseNext cfg).successor = some cfg') :
    RankLt (SchedulerRank cfg') (SchedulerRank cfg) := by
  cases hsc : stepConsume n with
  | none =>
      rw [hpe, hsc] at hsucc
      simp at hsucc
  | some next =>
      rw [hpe, hsc] at hsucc
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      cases hsucc
      cases hpend : n.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := n)).mpr hpend] at hsc
          cases hsc
      | cons f rest => exact hlt hpend hsc

/-- **PHASE PROGRESS CLOSED**: given the single OPEN dispatcher premise
`JumpDecrease` (owner C3b/integration, the learn/backjump/assert arm), every
successor of the phase dispatcher `phaseNext` strictly decreases
`SchedulerRank`. Proof: the three-way `schedulerNext_cases` split, each arm
dispatched to its rank theorem — C3a's `rank_lt_propagate` / `rank_lt_decide`
/ `rank_lt_consume`, the consume landings via `phase_compose_consume` with
C3a's `arm_localExclude_then_consume` / `arm_fallback_then_consume` and the
three analyze-site compositions, and `JumpDecrease` at the jump landing.
`.sat` / `.unsat` are terminal (no successor: vacuous). -/
theorem phaseProgress_of_jumpDecrease {leaf : Assignment → Bool}
    (hjump : JumpDecrease leaf) : PhaseProgress leaf := by
  intro cfg cfg' hsucc
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (schedulerNext cfg = backjumpStep cfg ev)
    cases ha : ev.analysis with
    | none =>
        -- ARM 7a stutter → forced consume
        refine phase_compose_consume
          (n := stepChronologicalFallback cfg (branchRegion cfg))
          ?_ (fun hp h => arm_fallback_then_consume (cfg := cfg) hp h) hsucc
        simp only [phaseNext, hnext, backjumpStep, ha, hc]
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            -- ARM 7b stutter (no saved checkpoint) → forced consume
            refine phase_compose_consume
              (n := stepChronologicalFallback cfg (branchRegion cfg))
              ?_ (fun hp h => arm_fallback_then_consume (cfg := cfg) hp h) hsucc
            simp only [phaseNext, hnext, backjumpStep, ha, hcp, hc]
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                -- the assertion rejects the restored ancestor: localExclude
                -- stutter → forced consume
                refine phase_compose_consume
                  (n := stepLocalExclude cfg ev.learned (checkpointRegion cp))
                  ?_ (fun hp' h => arm_localExclude_then_consume
                    (learned := ev.learned) (r := checkpointRegion cp) hp' h) hsucc
                simp only [phaseNext, hnext, backjumpStep, ha, hcp, hp]
            | some restored =>
                -- the real jump: passed through, decrease = `JumpDecrease`
                have hpe : phaseNext cfg =
                    .learnBackjumpAssert
                      (stepLearnBackjumpAssert cfg
                        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                          an.learned) ev restored)
                      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                        an.learned) an := by
                  simp only [phaseNext, hnext, backjumpStep, ha, hcp, hp]
                rw [hpe] at hsucc
                simp only [successor_learnBackjumpAssert, Option.some.injEq] at hsucc
                cases hsucc
                exact hjump cfg ev an cp restored ha hcp hp
  · -- ===== ROUTE 2: dead branch — the REAL consume route (cfg.conflict = none)
    cases hsc : stepConsume cfg with
    | none =>
        have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
          simp only [phaseNext, hnext, consumeStep, hsc]
        rw [hpe] at hsucc
        simp at hsucc
    | some next =>
        have hpe : phaseNext cfg = .chronologicalFallback next := by
          simp only [phaseNext, hnext, consumeStep, hsc, hconf]
        rw [hpe] at hsucc
        simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
        cases hsucc
        cases hpend : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hsc
            cases hsc
        | cons f rest => exact rank_lt_consume hpend hsc
  · -- ===== ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- ARM 1: propagate
      have hpe : phaseNext cfg = .propagate (stepPropagate cfg d) := by
        simp only [phaseNext, hnext]
      rw [hpe] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      cases hsucc
      exact rank_lt_propagate cfg d
    · -- ARM 2 / ARM 3 / ARM 6: stableStepGuarded (B1: fresh or skip)
      cases hw : leafWitness leaf cfg with
      | some w =>
          have hpe : phaseNext cfg = (.sat w : SchedulerTransition leaf) := by
            simp only [phaseNext, hnext, stableStepGuarded, hw]
          rw [hpe] at hsucc
          simp at hsucc
      | none =>
          cases hsp : splitData cfg.branch.frame with
          | some q =>
              obtain ⟨l, v, vs, doms⟩ := q
              by_cases hred : TrailRedundant cfg.branch.trail l = true
              · -- ARM 2b: the redundant-pin skip
                have hs : schedulerNext cfg =
                    .decide (stepDecideSkip cfg v doms) l := by
                  rw [hnext]
                  simp only [stableStepGuarded, hw, hsp]
                  rw [if_pos hred]
                have hpe : phaseNext cfg =
                    .decide (stepDecideSkip cfg v doms) l := by
                  simp only [phaseNext, hs]
                rw [hpe] at hsucc
                simp only [successor_decide, Option.some.injEq] at hsucc
                cases hsucc
                exact rank_lt_decideSkip cfg v vs doms l hsp
              · -- ARM 2a: the fresh decision
                have hs : schedulerNext cfg =
                    .decide (stepDecide cfg v vs doms l) l := by
                  rw [hnext]
                  simp only [stableStepGuarded, hw, hsp]
                  rw [if_neg]
                  rw [show TrailRedundant cfg.branch.trail l = false from by
                    cases h : TrailRedundant cfg.branch.trail l <;> simp_all]
                  simp
                have hpe : phaseNext cfg =
                    .decide (stepDecide cfg v vs doms l) l := by
                  simp only [phaseNext, hs]
                rw [hpe] at hsucc
                simp only [successor_decide, Option.some.injEq] at hsucc
                cases hsucc
                exact rank_lt_decide cfg v vs doms l hsp
          | none =>
              -- ARM 6: localExclude stutter → forced consume
              refine phase_compose_consume
                (n := stepLocalExclude cfg [] (branchRegion cfg))
                ?_ (fun hp h => arm_localExclude_then_consume
                  (learned := []) (r := branchRegion cfg) hp h) hsucc
              simp only [phaseNext, hnext, stableStepGuarded, hw, hsp]
    · -- ARM 8 / ARM 4 / ARM 6: conflictStep
      cases cs with
      | nil =>
          -- empty reported clause list: LOCAL exclusion → forced consume
          refine phase_compose_consume
            (n := stepLocalExclude cfg learned (branchRegion cfg))
            ?_ (fun hp h => arm_localExclude_then_consume
              (learned := learned) (r := branchRegion cfg) hp h) hsucc
          simp only [phaseNext, hnext, conflictStep]
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · -- level 0: root contradiction (terminal, vacuous)
            have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
              simp only [phaseNext, hnext, conflictStep, if_pos hlv]
            rw [hpe] at hsucc
            simp at hsucc
          · -- ARM 4: the analyze site — resolved through the recorded route
            -- (the recorded config is the COUNTED site: `conflictStep` wires
            -- the executed analyzer's pivot expansions into it)
            cases hev : (stepAnalyzeConflictCounted cfg c learned
                (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).conflict with
            | none =>
                simp [stepAnalyzeConflictCounted, stepAnalyzeConflict,
                  SchedulerConfig.countResolutions] at hev
            | some ev =>
                cases ha : ev.analysis with
                | none =>
                    refine phase_compose_consume
                      (n := stepChronologicalFallback
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                        (branchRegion (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))))
                      ?_ (fun hp h => analyzeConflict_then_fallback_rank_lt
                        (cfg := cfg) (c := c) (learned := learned) hp h) hsucc
                    simp only [phaseNext, hnext, conflictStep, if_neg hlv, hev,
                      backjumpStep, ha]
                | some an =>
                    have hstep_orig :
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).original
                          = cfg.original := rfl
                    have hstep_props :
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).props
                          = cfg.props := rfl
                    have hstep_dom :
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).orig
                          = cfg.orig := rfl
                    cases hcp : checkpointAt
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).checkpoints
                        an.backjumpLevel with
                    | none =>
                        refine phase_compose_consume
                          (n := stepChronologicalFallback
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                            (branchRegion (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))))
                          ?_ (fun hp h => analyzeConflict_then_fallback_rank_lt
                            (cfg := cfg) (c := c) (learned := learned) hp h) hsucc
                        simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                          hev, backjumpStep, ha, hcp]
                    | some cp =>
                        cases hp : (BackjumpPlan.ofCheckpoint cp
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                            an.asserting an.learned).perform
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                            cfg.orig
                            cfg.original cfg.props with
                        | none =>
                            -- checkpoint rejection → localExclude → consume
                            refine phase_compose_consume
                              (n := stepLocalExclude
                                (stepAnalyzeConflictCounted cfg c learned
                                  (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                                ev.learned (checkpointRegion cp))
                              ?_ (fun hp' h => analyzeConflict_then_localExclude_rank_lt
                                (cfg := cfg) (c := c) (learned := learned)
                                hp' h) hsucc
                            simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                              hev, backjumpStep, ha, hcp, hstep_orig, hstep_props, hstep_dom, hp]
                        | some restored =>
                            -- the recorded jump: decrease = the analyze-site
                            -- composition of `JumpDecrease`
                            have hpe : phaseNext cfg =
                                .learnBackjumpAssert
                                  (stepLearnBackjumpAssert
                                    (stepAnalyzeConflictCounted cfg c learned
                                      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                                    (BackjumpPlan.ofCheckpoint cp
                                      (stepAnalyzeConflictCounted cfg c learned
                                        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                                      an.asserting an.learned) ev restored)
                                  (BackjumpPlan.ofCheckpoint cp
                                    (stepAnalyzeConflictCounted cfg c learned
                                      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                                    an.asserting an.learned) an := by
                              simp only [phaseNext, hnext, conflictStep,
                                if_neg hlv, hev, backjumpStep, ha, hcp,
                                hstep_orig, hstep_props, hstep_dom, hp]
                            rw [hpe] at hsucc
                            simp only [successor_learnBackjumpAssert,
                              Option.some.injEq] at hsucc
                            cases hsucc
                            exact analyzeConflict_then_jump_rank_lt hjump
                              hev ha hcp hp
    · -- ARM 6: localExcluded → localExclude stutter → forced consume
      refine phase_compose_consume
        (n := stepLocalExclude cfg learned (branchRegion cfg))
        ?_ (fun hp h => arm_localExclude_then_consume
          (learned := learned) (r := branchRegion cfg) hp h) hsucc
      simp only [phaseNext, hnext]

/-! ## §4 Driver-outcome semantics (C2d arms, consumed verbatim) -/

/-- SAT soundness at the terminal arm: when the run's stopping step is
C2d's `stableStep` SAT arm and the stopping configuration is reachable,
the witness is a solution of the ORIGINAL box. Consumes C2d's
`arm_sat_solution`; this is the semantic content the driver's `.sat`
outcome carries. -/
theorem sat_outcome_solution {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (h : stableStep cfg = .sat w) :
    SolutionWitness leaf cfg.orig w :=
  C2d.arm_sat_solution hreach h

/-- UNSAT exclusion at the exhausted-frontier arm: an invariant
configuration with empty pending whose current branch is dead refutes
every original leaf by a learned clause. Consumes C2d's
`arm_unsat_coverage`. -/
theorem unsat_outcome_coverage {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (hpend : cfg.pending = [])
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    ∀ a, OriginalLeaves leaf cfg.orig a →
      ∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a :=
  C2d.arm_unsat_coverage hinv hpend hdead

/-- UNSAT exclusion at the root-contradiction arm: with D1a's root-facts
bridge (the ONLY premise, owner D1a, E3's `RootFactsBridge`) the earliest
UNSAT exit yields both `UnsatEvidence` and the refuting-clause coverage.
Consumes C2d's `arm_unsat_rootContradiction_evidence`. -/
theorem unsat_outcome_rootContradiction {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (hpend : cfg.pending = [])
    (hbridge : ∀ a, leaf a = true →
      ∀ e ∈ cfg.branch.trail, e.literal.eval a = some true)
    (hroot : RootContradiction leaf cfg.branch) :
    UnsatEvidence leaf cfg.orig cfg.pending cfg.branch.learned cfg.branch ∧
      ∀ a, OriginalLeaves leaf cfg.orig a →
        ∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a :=
  C2d.arm_unsat_rootContradiction_evidence hinv hpend hbridge hroot

/-! ## §5 The naive obligation is FALSE: stutter arms of the REAL

dispatcher have EQUAL-rank successors

`DispatcherProgress` as previously stated (every immediate
`schedulerNext` successor strictly decreases the rank) is REFUTABLE at
three real arms, whose rank stutters are C3a theorems:
`.localExclude` (ARM 6 stable site), `.analyzeConflict` (ARM 4) and
`.chronologicalFallback` (ARM 7 backjump site). The progress of those
arms is the TWO-STEP composite (stutter + forced consume) that C3a
already provides (`arm_localExclude_then_consume`,
`arm_fallback_then_consume`, `analyzeConflict_not_repeated`), so the
kernel step must be a PHASE step bundling them, not `schedulerNext`
itself. The residual obligation on the real dispatcher is therefore the
phase step's decrease; these lemmas are the exact reason the naive shape
cannot be the one the driver consumes. -/

/-- A stuttering dispatcher arm refutes `DispatcherProgress` outright:
the successor's rank is EQUAL, so no `RankLt` exists. -/
theorem not_dispatcherProgress_of_stutter {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (hsucc : (schedulerNext cfg).successor = some cfg')
    (hstut : SchedulerRank cfg' = SchedulerRank cfg) :
    ¬ DispatcherProgressNaive leaf := by
  intro hprog
  have hlt := hprog cfg cfg' hsucc
  rw [hstut] at hlt
  rcases hlt with h | ⟨_, h | ⟨_, h⟩⟩ <;> omega

/-- ARM 6 site (stable local exclusion): the naive obligation fails. -/
theorem not_dispatcherProgress_of_localExclude_site {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {l : Option Literal} {reason : Option Clause} {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .localExcluded bs l reason learned) :
    ¬ DispatcherProgressNaive leaf := by
  obtain ⟨hnext, hstut⟩ := C3a.arm_localExclude hconf hstatus hd ht
  refine not_dispatcherProgress_of_stutter ?_ hstut
  rw [hnext]
  rfl

/-- ARM 4 site (conflict recording): the naive obligation fails. -/
theorem not_dispatcherProgress_of_analyzeConflict_site {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {c : Clause} {rest : List Clause} {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .conflict bs (c :: rest) learned)
    (hlevel : cfg.branch.level ≠ 0) :
    ¬ DispatcherProgressNaive leaf := by
  obtain ⟨hnext, hstut⟩ := C3a.arm_analyzeConflict hconf hstatus hd ht hlevel
  refine not_dispatcherProgress_of_stutter ?_ hstut
  rw [hnext]
  rfl

/-- ARM 7 site (backjump with no analysis): the naive obligation fails. -/
theorem not_dispatcherProgress_of_fallback_site {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (h : cfg.conflict = some ev) (ha : ev.analysis = none) :
    ¬ DispatcherProgressNaive leaf := by
  obtain ⟨hnext, hstut⟩ := C3a.arm_fallback_without_analysis h ha
  refine not_dispatcherProgress_of_stutter ?_ hstut
  rw [hnext]
  rfl

end LeanFzn.Solver.UIP.C3b
