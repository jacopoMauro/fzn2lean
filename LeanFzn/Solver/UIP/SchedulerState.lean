/-
File: LeanFzn/Solver/UIP/SchedulerState.lean

Purpose:
  The coherent scheduler configuration of the explained frontier, its
  runtime observables, and the coverage predicate the driver verdicts are
  stated over (INTERFACES §2.5–§2.7):

  * `SchedulerConfig` — the coherent configuration: original box,
    original clause database, registered propagators, the current
    `BranchState`, the actual `DecisionCheckpoint` list, the pending
    alternatives, the permanent exhaustion log, the branch status, the
    recorded conflict evidence, the runtime counters and the work
    statistics;
  * `SchedulerConfig.init` — the root configuration with the root
    checkpoint registered;
  * `SchedulerConfig.WellFormed` — the C1-expressible part of the state
    invariant C2 maintains (checkpoint identity, sub-box pending frames,
    log soundness, frontier coverage). The branch-coherence field
    `ReachableState leaf cfg.orig cfg.branch` lives in
    `LeanFzn/Solver/UIP/Proofs/BranchState.lean`, which this runtime module must
    not import (INTERFACES §3); C2 conjoins it.
  * `RuntimeEvents` — the runtime counter record of INTERFACES §2.7 with
    the increment sites `recordResolutions` (`analyzeConflict`) and
    `recordBackjump` (`learnBackjumpAssert`). NOTE: this module is the
    record's home because §2.7's suggested home (`LeanFzn/Solver/UIP/Pruned.lean`,
    next to `SearchStats`) cannot import it without a cycle — `Pruned` is
    transitively below the whole C1 chain
    (`SchedulerState -> BackjumpFrontier -> ConflictResolution ->
    ExplainedPropagation -> Pruning -> Pruned`). D1 must therefore use
    §2.7's fallback (`solveWithEvents`-style exposure) or ask for a new
    module below `Pruned.lean`; see the C1 report.
  * `OriginalLeaves` / `CoversRemainingLeaves` — the coverage predicate
    of INTERFACES §2.6. Exhaustion is deliberately NOT a disjunct: dead
    regions justify deleting alternatives at the deletion site and can
    never "cover" a surviving leaf solution.
  * `ConflictEvidence` / `ConflictAnalysis.ofUIP` — the recorded
    conflict-analysis evidence, built from the allowance entry point the
    scheduler consumes (`analyzeAtAllowance`); the classification type
    `AnalysisOutcome` is B1's and is deliberately not referenced here.

Dependencies:
  - LeanFzn.Solver.Propagation.BackjumpFrontier (C1): checkpoints, dead regions, the
    exhaustion log, the complete backjump transition.
  - LeanFzn.Solver.Chronological.Pruned: `SearchStats` (transitive through the chain
    above; imported explicitly for the record field).
  - LeanFzn.Solver.Propagation.FrameFilter: `Frame.domains` (`fullDomains`' definition).

DAG:
  BackjumpFrontier -> SchedulerState -> SchedulerStep
  -> Proofs.SchedulerStep (C2) -> Scheduler (C3) -> public driver (D1).
-/

import LeanFzn.Solver.Propagation.BackjumpFrontier
import LeanFzn.Solver.Propagation.PruningTypes
import LeanFzn.Solver.Propagation.FrameFilter

namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## Runtime events and counters (INTERFACES §2.7)

The counter record and its increment sites. A counter changes ONLY in the
two `record*` functions below, applied by the scheduler at the transition
named in the §2.7 table:

* `recordResolutions` — the `analyzeConflict` site: pivot expansions of
  the run, from B1's counted trace (`analyzeTrace`'s step count), wired
  by C3 (C1 must not fabricate the number, and its import cone has no
  counted trace — see `SchedulerConfig.countResolutions`);
* `recordBackjump` — the `learnBackjumpAssert` site:
  `backjumps += 1`, `sourceLevel := pre-jump branch.level`,
  `targetLevel := plan.target`, `assertingEnqueues += 1`.

`propagate`, `decide`, `sat`, `localExclude`, `chronologicalFallback` and
`unsat` change no counter, exactly as the §2.7 table requires. -/

/-- The runtime counters observable from a driver run (INTERFACES §2.7). -/
structure RuntimeEvents where
  /-- pivot expansions of the analyzer on the most recent analyze step -/
  reasonResolutions : Nat := 0
  /-- completed learn/backjump/assert transitions -/
  backjumps : Nat := 0
  /-- conflict level of the most recent completed backjump -/
  sourceLevel : Nat := 0
  /-- restored target level of the most recent completed backjump -/
  targetLevel : Nat := 0
  /-- asserting literals enqueued after restoration -/
  assertingEnqueues : Nat := 0
  deriving Repr, BEq, DecidableEq

/-- Accumulate two counter records: counters add, and the level fields
follow the LATER record when it completed a backjump ("most recent
completed backjump"). -/
def RuntimeEvents.add (a b : RuntimeEvents) : RuntimeEvents where
  reasonResolutions := a.reasonResolutions + b.reasonResolutions
  backjumps := a.backjumps + b.backjumps
  sourceLevel := if b.backjumps = 0 then a.sourceLevel else b.sourceLevel
  targetLevel := if b.backjumps = 0 then a.targetLevel else b.targetLevel
  assertingEnqueues := a.assertingEnqueues + b.assertingEnqueues

/-- The `analyzeConflict` increment site: add the counted pivot expansions
of the analysis run (B1's trace, wired by C3). -/
def RuntimeEvents.recordResolutions (e : RuntimeEvents) (n : Nat) :
    RuntimeEvents :=
  { e with reasonResolutions := e.reasonResolutions + n }

/-- The `learnBackjumpAssert` increment site: one completed backjump, the
pre-jump source level, the restored target level, and one asserting
enqueue. -/
def RuntimeEvents.recordBackjump (e : RuntimeEvents) (source target : Nat) :
    RuntimeEvents :=
  { e with backjumps := e.backjumps + 1,
           sourceLevel := source,
           targetLevel := target,
           assertingEnqueues := e.assertingEnqueues + 1 }

@[simp] theorem RuntimeEvents.recordResolutions_reasonResolutions
    (e : RuntimeEvents) (n : Nat) :
    (e.recordResolutions n).reasonResolutions = e.reasonResolutions + n := rfl

@[simp] theorem RuntimeEvents.recordResolutions_backjumps
    (e : RuntimeEvents) (n : Nat) : (e.recordResolutions n).backjumps = e.backjumps :=
  rfl

@[simp] theorem RuntimeEvents.recordBackjump_backjumps
    (e : RuntimeEvents) (source target : Nat) :
    (e.recordBackjump source target).backjumps = e.backjumps + 1 := rfl

@[simp] theorem RuntimeEvents.recordBackjump_sourceLevel
    (e : RuntimeEvents) (source target : Nat) :
    (e.recordBackjump source target).sourceLevel = source := rfl

@[simp] theorem RuntimeEvents.recordBackjump_targetLevel
    (e : RuntimeEvents) (source target : Nat) :
    (e.recordBackjump source target).targetLevel = target := rfl

@[simp] theorem RuntimeEvents.recordBackjump_assertingEnqueues
    (e : RuntimeEvents) (source target : Nat) :
    (e.recordBackjump source target).assertingEnqueues
      = e.assertingEnqueues + 1 := rfl

/-- The counter obligation at the analyze site (INTERFACES §2.7): the
recorded resolution count never exceeds the analysis allowance the run
consumed. C3 discharges it from B1's counted trace; C1 exports the bound
so an inflated count cannot pass it. -/
def ResolutionCountBound (trail : List TrailEntry) (c : Clause) (n : Nat) :
    Prop :=
  n ≤ analysisFuel trail c

/-! ## Coverage of the remaining search space (INTERFACES §2.6) -/

/-- The search space is the set of leaf solutions of the original box. -/
def OriginalLeaves (leaf : Assignment → Bool) (orig : List Domain)
    (a : Assignment) : Prop :=
  leaf a = true ∧ a.Fits orig

/-- All remaining original leaf solutions are enumerated by `pending` or
already excluded by the global clause database.

Two design constraints (frozen): the database disjunct is sound only
because `db` is monotone (transitions may add clauses, never remove
them); and exhaustion is NOT part of this predicate — a removed frame is
justified by dead-region evidence at the deletion site, and a `Sound`
region contains no leaf solution at all, so it must never appear as a
disjunct that could "cover" a surviving one. -/
def CoversRemainingLeaves (leaf : Assignment → Bool) (orig : List Domain)
    (pending : List BranchFrame) (db : List Clause) : Prop :=
  ∀ a, OriginalLeaves leaf orig a →
    (∃ f ∈ pending, FrameCovers f a) ∨ (∃ c ∈ db, ¬ c.SatisfiedBy a)

/-! ## Recorded conflict evidence and the UIP constructor (INTERFACES §2.5) -/

/-- `ConflictAnalysis.ofUIP`: the frozen constructor turning the
allowance entry point's `(below, uip)` pair into the analysis record —
the same construction `BranchState.analyzeWithAllowance` performs, so
the scheduler's evidence and the existing reference analysis agree
(`analyzeWithAllowance_eq_ofUIP` below). -/
def _root_.LeanFzn.Solver.Propagation.ConflictAnalysis.ofUIP (below : List (Literal × Nat)) (uip : Literal) :
    ConflictAnalysis where
  learned := uip.negate :: below.map fun p => p.1
  backjumpLevel := below.foldl (fun acc p => max acc p.2) 0
  asserting := uip.negate

@[simp] theorem _root_.LeanFzn.Solver.Propagation.ConflictAnalysis.ofUIP_learned
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofUIP below uip).learned
      = uip.negate :: below.map fun p => p.1 := rfl

@[simp] theorem _root_.LeanFzn.Solver.Propagation.ConflictAnalysis.ofUIP_asserting
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofUIP below uip).asserting = uip.negate := rfl

@[simp] theorem _root_.LeanFzn.Solver.Propagation.ConflictAnalysis.ofUIP_backjumpLevel
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofUIP below uip).backjumpLevel
      = below.foldl (fun acc p => max acc p.2) 0 := rfl

/-- A `foldl` of `max` never exceeds a bound satisfied by the initial
accumulator and every step. -/
theorem foldl_max_le {below : List (Literal × Nat)} {lvl acc : Nat}
    (hacc : acc ≤ lvl) (h : ∀ p ∈ below, p.2 ≤ lvl) :
    below.foldl (fun acc p => max acc p.2) acc ≤ lvl := by
  induction below generalizing acc with
  | nil => exact hacc
  | cons p ps ih =>
      simp only [List.foldl_cons]
      exact ih (Nat.max_le.mpr ⟨hacc, h p (List.mem_cons_self ..)⟩)
        (fun q hq => h q (List.mem_cons_of_mem _ hq))

/-- The UIP constructor's target level is legal: it never exceeds any
bound that holds for every below-level falsifier — the level law C2's
backjump legality argument consumes. -/
theorem _root_.LeanFzn.Solver.Propagation.ConflictAnalysis.ofUIP_backjumpLevel_le
    {below : List (Literal × Nat)} {uip : Literal} {lvl : Nat}
    (h : ∀ p ∈ below, p.2 ≤ lvl) :
    (ConflictAnalysis.ofUIP below uip).backjumpLevel ≤ lvl :=
  foldl_max_le (Nat.zero_le _) h

/-- The scheduler's analysis agrees with the reference
`BranchState.analyzeWithAllowance`: both are the `Option.map` of
`ConflictAnalysis.ofUIP` over the same allowance run. -/
theorem analyzeWithAllowance_eq_ofUIP (orig : List Domain) (bs : BranchState leaf) (c : Clause) :
    bs.analyzeWithAllowance orig c =
      (analyzeAtAllowance orig bs.trail bs.level c).map
        (fun p => ConflictAnalysis.ofUIP p.1 p.2) := by
  rw [BranchState.analyzeWithAllowance]
  cases h : analyzeAtAllowance orig bs.trail bs.level c with
  | none => rfl
  | some p => cases p with
    | mk below uip => rfl

/-- The recorded conflict evidence of the `analyzeConflict` transition
(INTERFACES §2.6: the successor of that transition changes only
evidence, never branch, pending or database). -/
structure ConflictEvidence where
  /-- the reported conflict clause -/
  clause : Clause
  /-- the closure's freshness-filtered new clauses (globally entailed) -/
  learned : List Clause
  /-- the recorded allowance analysis; `none` = no asserting result, the
      chronological fallback's trigger -/
  analysis : Option ConflictAnalysis
  /-- counted pivot expansions of the recorded run (B1's trace, wired by
      C3 through `SchedulerConfig.countResolutions`; `0` = uncounted) -/
  resolutions : Nat := 0
  deriving Repr

/-! ## The coherent scheduler configuration (INTERFACES §2.5) -/

/-- The current branch's work phase. C1's dispatch is phase-driven: a
branch already classified dead is not re-classified (which is what makes
`localExclude`/`chronologicalFallback` single, non-repeating steps); the
next transition consumes the following pending alternative instead. -/
inductive BranchStatus where
  /-- propagation and splitting still apply to the current branch -/
  | active
  /-- the current branch is dead (excluded/exhausted): only consumption
      of the next pending alternative applies -/
  | dead
  deriving DecidableEq, Repr

/-- The scheduler's coherent configuration: current branch, the ACTUAL
saved decision checkpoints, pending alternatives, the global learned
database (inside `branch`), and the permanent exhaustion evidence.

Field notes relative to INTERFACES §2.5 (PROPOSED field order):
`status` and `conflict` are C1 additions. `status` makes the eight frozen
transitions a non-repeating phase machine (without it a dead branch
would be re-classified forever, and `localExclude`/`chronologicalFallback`
could never be followed by consumption); `conflict` is the "evidence
recorded" payload that §2.6 REQUIRES the `analyzeConflict` successor to
carry while leaving branch/pending/DB unchanged. -/
structure SchedulerConfig (leaf : Assignment → Bool) where
  /-- the original box (fixed at the root) -/
  orig : List Domain
  /-- the problem's clause database -/
  original : List Clause
  /-- registered propagators -/
  props : List Propagator
  /-- frame + trail + level + global learned database -/
  branch : BranchState leaf
  /-- saved ancestors, newest first -/
  checkpoints : List (DecisionCheckpoint leaf)
  /-- remaining alternatives -/
  pending : List BranchFrame
  /-- permanent exhaustion evidence -/
  log : ExhaustionLog
  /-- work phase of the current branch -/
  status : BranchStatus := .active
  /-- recorded conflict evidence awaiting the learn/backjump/assert step -/
  conflict : Option ConflictEvidence := none
  /-- runtime counters (§2.7) -/
  events : RuntimeEvents := {}
  /-- existing work statistics -/
  stats : SearchStats := {}

/-- The scheduler's full work list: the current branch's frame followed by
the pending alternatives. The frozen `CoversRemainingLeaves` is stated
over an explicit frame list; the current frame is its head, which is what
makes a split/backjump coverage-preserving when it replaces the current
frame by its children or by the restored ancestor. -/
def SchedulerConfig.frontier (cfg : SchedulerConfig leaf) : List BranchFrame :=
  cfg.branch.frame :: cfg.pending

/-- The configuration's coverage obligation (INTERFACES §2.6, with the
current branch included in the frontier). C2 proves it is maintained by
every transition; the §2.6 per-transition rows are its instances. -/
def SchedulerConfig.coverage (cfg : SchedulerConfig leaf) : Prop :=
  CoversRemainingLeaves leaf cfg.orig cfg.frontier cfg.branch.learned

/-- The root configuration: the whole original box, empty trail, level
zero, the root checkpoint registered, empty pending stack and log. -/
def SchedulerConfig.init (orig : List Domain) (original : List Clause)
    (props : List Propagator) : SchedulerConfig leaf where
  orig := orig
  original := original
  props := props
  branch := { BranchState.init (leaf := leaf) (orig, []) with learned := original }
  checkpoints := [rootCheckpoint orig]
  pending := []
  log := {}
  status := .active
  conflict := none
  events := {}
  stats := {}

@[simp] theorem SchedulerConfig.init_branch (orig : List Domain)
    (original : List Clause) (props : List Propagator) :
    (SchedulerConfig.init (leaf := leaf) orig original props).branch
      = { BranchState.init (leaf := leaf) (orig, []) with learned := original } := rfl

@[simp] theorem SchedulerConfig.init_pending (orig : List Domain)
    (original : List Clause) (props : List Propagator) :
    (SchedulerConfig.init (leaf := leaf) orig original props).pending = [] := rfl

/-- The root frontier is exactly the original box with empty prefix. -/
theorem SchedulerConfig.frontier_init (orig : List Domain)
    (original : List Clause) (props : List Propagator) :
    (SchedulerConfig.init (leaf := leaf) orig original props).frontier
      = [(orig, [])] := rfl

/-- Register a sound dead region on the log (the registration site shared
by `localExclude` and `chronologicalFallback`). -/
def SchedulerConfig.registerRegion (cfg : SchedulerConfig leaf)
    (r : DeadRegion) : SchedulerConfig leaf :=
  { cfg with log := cfg.log.register r }

/-- The `analyzeConflict` counter site (INTERFACES §2.7): record B1's
counted pivot expansions and increment `events.reasonResolutions` here.
`schedulerNext` has the frozen ternary signature and cannot take the
count, and C1's import cone has no counted trace, so C3 supplies the
value through this function at the analyze site (the scheduler never
fabricates it). -/
def SchedulerConfig.countResolutions (cfg : SchedulerConfig leaf) (n : Nat) :
    SchedulerConfig leaf :=
  { cfg with
    events := cfg.events.recordResolutions n
    conflict := cfg.conflict.map fun ev => { ev with resolutions := ev.resolutions + n } }

@[simp] theorem SchedulerConfig.countResolutions_reasonResolutions
    (cfg : SchedulerConfig leaf) (n : Nat) :
    (cfg.countResolutions n).events.reasonResolutions
      = cfg.events.reasonResolutions + n := rfl

/-! ## The state invariant C1 maintains and C2 proves (INTERFACES §2.5) -/

/-- The well-formedness of a scheduler configuration that is expressible
in this runtime module: checkpoint identity, sub-box pending frames,
sound exhaustion log, and frontier coverage.

The remaining §2.5 invariant — `ReachableState leaf cfg.orig cfg.branch`,
A1's eight-field branch coherence — cannot be named here because it lives
in `LeanFzn/Solver/UIP/Proofs/BranchState.lean` and runtime modules must not
import `Proofs.*` (INTERFACES §3). C2 works with
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP

`ReachableState leaf cfg.orig cfg.branch ∧ cfg.WellFormed`; every `next`
construction site in `SchedulerStep.lean` exports the obligations for
both halves. -/
structure SchedulerConfig.WellFormed (cfg : SchedulerConfig leaf) : Prop where
  /-- every saved checkpoint identifies the current branch at its level -
      the property that lets every constructed plan carry `Identifies`
      (INTERFACES §2.4) -/
  checkpoints_identify : ∀ cp ∈ cfg.checkpoints, cp.Identifies cfg.branch cp.level
  /-- pending frames are sub-frames of the original box -/
  pending_fits : ∀ f ∈ cfg.pending, ∀ i v,
    v ∈ (Frame.domains f).getD i [] → v ∈ cfg.orig.getD i []
  /-- the current frame is a sub-frame of the original box -/
  branch_fits : ∀ i v,
    v ∈ (Frame.domains cfg.branch.frame).getD i [] → v ∈ cfg.orig.getD i []
  /-- the exhaustion log contains no leaf solution -/
  log_sound : ExhaustionLog.Sound leaf cfg.log
  /-- the frontier covers every remaining original leaf solution -/
  coverage : cfg.coverage

/-- The root configuration is well formed as far as this module can
express it (the branch half, `ReachableState leaf orig (BranchState.init
(orig, []))`, is A1's `reachable_init`; the coverage half is C2's
`covers_root_init`, INTERFACES §2.6). -/
theorem SchedulerConfig.init_wellFormed_parts (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    (∀ cp ∈ (SchedulerConfig.init (leaf := leaf) orig original props).checkpoints,
      cp.Identifies (SchedulerConfig.init (leaf := leaf) orig original props).branch
        cp.level) ∧
    ExhaustionLog.Sound leaf
      (SchedulerConfig.init (leaf := leaf) orig original props).log := by
  refine ⟨?_, ?_⟩
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    rw [hcp]
    exact rootCheckpoint_identifies_init leaf orig original
  · intro r hr
    simp only [SchedulerConfig.init, List.not_mem_nil] at hr

end LeanFzn.Solver.UIP
