/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerStep.lean

Purpose:
  THE ARM TABLE for the runtime dispatcher
  `LeanFzn/Solver/UIP/SchedulerStep.lean`'s `schedulerNext`. Every constructor the
  dispatcher can return is paired with (a) the exact guard equations that
  produce it (`schedulerNext_eq_*`), so no transition can be silently
  omitted, and (b) the field obligations of that arm, re-exported from the
  accepted C2a/C2b/C2c/E3/S0 modules with their owners named.

  Namespace: `LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C2d` — the runtime module of the same
  base name is imported, so the assembly lives in a SUB-namespace to avoid
  any short-name collision (`schedulerNext` etc. still resolve upward).

ARM TABLE (constructor -> dispatch lemma -> semantic obligation), S5:
  1. `.propagate next`            `schedulerNext_eq_deduction`
       -> C2a `stepPropagate_invariant` (`arm_propagate_invariant`)
  2. `.decide next l`             `schedulerNext_eq_stable_decide`
       -> `arm_decide_invariant_bool` (ACTIVATION route: NO pin premise;
          sole premise = the runtime `TrailRedundant ... = false` guard,
          owner integration). The old `arm_decide_invariant` is RETAGGED
          as the INT-residual route (global `hpin` refuted by S1).
  3. `.sat w`                     `schedulerNext_eq_stable_sat`
       -> C2a `stableStep_sat_solution` (`arm_sat_solution`): the witness
          is an ORIGINAL solution (`SolutionWitness`).
  4. `.analyzeConflict next c`    `schedulerNext_eq_conflict_analyze`
       -> `arm_analyzeConflict_invariant`: the pre-jump configuration is
          unchanged on every invariant-relevant projection (field-wise).
  5. `.learnBackjumpAssert ...`   `schedulerNext_eq_backjump_jump`
       -> `arm_learnBackjumpAssert_invariant` (RE-ASSEMBLED): all seven
          successor fields DERIVED (S3 `perform_reachable_of_pre`,
          S4 hpend/hbfit/hcov, L1 `jump_learned_entailed`, C2c hlog,
          `Identifies.restore_extend`). Irreducible premises:
          `RestorationPreReachable` (S5), `SurvivorRestoration` (S5 /
          S1-S4 push sites), `FalsifiedByTrail` (RecordedAnalysisFalsified,
          falsified-wiring), `LearnedEntailed ev.learned` (S4/D0).
  6. `.localExclude next`         `schedulerNext_eq_stable_localExclude`,
       `schedulerNext_eq_conflict_local`, `schedulerNext_eq_localExcluded`,
       `schedulerNext_eq_backjump_perform_none`
       -> `arm_localExclude_log_sound`/`arm_localExclude_state`
          (registration soundness at all four sites, via
          `DeadRegion.byFrame_sound`). The FULL `SchedulerInvariant` for
          this arm additionally needs the learned-clause discipline
          (owner E1/integration): NOT DONE here.
  7. `.chronologicalFallback n`   `schedulerNext_eq_consume`,
       `schedulerNext_eq_backjump_none_analysis`,
       `schedulerNext_eq_backjump_no_checkpoint`
       -> `arm_chronologicalFallback_log_sound` +
          `arm_chronologicalFallback_pending_consumed`/
          `_state` (concrete transformation). The coverage/retirement
          conjuncts are C2c's `ResumeCoherent` items (owner C2d resume
          step): NOT DONE here.
  8. `.unsat`                     `schedulerNext_eq_consume_none`,
       `arm_consume_unsat_iff` (EMPTY-FRONTIER exactness),
       `schedulerNext_eq_conflict_unsat`
       -> `arm_unsat_coverage` (exhausted frontier) and
          `arm_unsat_rootContradiction`/`_evidence` (root/level-zero
          route; bridge premise owner D1a). Both feed `S0.unsat_coverage`
          / `RootContradiction` -> `UnsatEvidence`.

Fallback wrappers: this module replaces the premise-returning
`fallback_safe`/`fallback_progress_wellFounded` shape (BackjumpFrontier
:507/:523, whose owner must delete them; NOT edited here) with concrete
per-site facts about the ACTUAL transformation: `arm_*_log_sound` are
about `stepLocalExclude`/`stepChronologicalFallback` themselves, and
`arm_chronologicalFallback_pending_consumed` is about the real
`stepConsume` successor (no premise re-statement).

DAG: SchedulerForward + SchedulerBackjump + SchedulerResume
     -> Proofs.SchedulerStep (this module; consumed by the coordinator).
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerForward
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerBackjump
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerResume
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerCoverage
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.C2d
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Dispatch equations (the arm table, machine-checked) -/

/-- ARM 5/7/8 source: a recorded conflict routes to `backjumpStep`. -/
theorem schedulerNext_eq_backjump {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (h : cfg.conflict = some ev) :
    schedulerNext cfg = backjumpStep cfg ev := by
  simp only [schedulerNext, h]

/-- ARM 7 source: a dead branch routes to the consume dispatcher. -/
theorem schedulerNext_eq_consume {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .dead) :
    schedulerNext cfg = consumeStep cfg := by
  simp only [schedulerNext, hconf, hstatus]

/-- ARM 1: an active branch with a productive deduction propagates it. -/
theorem schedulerNext_eq_deduction {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {d : ProductiveDeduction leaf cfg.branch}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    schedulerNext cfg = .propagate (stepPropagate cfg d) := by
  simp only [schedulerNext, hconf, hstatus, hd]

/-- ARM 3: a stable terminal result with a passing leaf check is `.sat`. -/
theorem schedulerNext_eq_stable_sat {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf} {w : Assignment}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs)
    (hw : leafWitness leaf cfg = some w) :
    schedulerNext cfg = .sat w := by
  simp only [schedulerNext, hconf, hstatus, hd, ht, stableStepGuarded, hw]

/-- ARM 2a: a stable terminal result with a FRESH split pin decides (the
guarded dispatcher's fresh arm; B1). -/
theorem schedulerNext_eq_stable_decide {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs)
    (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    schedulerNext cfg = .decide (stepDecide cfg k v vs l) l := by
  simp only [schedulerNext, hconf, hstatus, hd, ht, stableStepGuarded, hw,
    hsplit]
  rw [if_neg]
  rw [hred]
  simp

/-- ARM 2b (B1, skip arm): a stable terminal result whose split pin is
already recorded decides WITHOUT a trail entry (`stepDecideSkip`), pushing
no sibling. -/
theorem schedulerNext_eq_stable_decideSkip {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs)
    (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    schedulerNext cfg = .decide (stepDecideSkip cfg k v) l := by
  simp only [schedulerNext, hconf, hstatus, hd, ht, stableStepGuarded, hw,
    hsplit]
  rw [if_pos hred]

/-- ARM 6 (stable site): a stable terminal result with no split data
excludes the finished branch locally. -/
theorem schedulerNext_eq_stable_localExclude {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs)
    (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame cfg.prio = none) :
    schedulerNext cfg =
      .localExclude (stepLocalExclude cfg [] (branchRegion cfg)) := by
  simp only [schedulerNext, hconf, hstatus, hd, ht, stableStepGuarded, hw, hsplit]

/-- ARM 4: an active branch at a fixpoint with a nonempty reported clause
and a positive level records the analysis evidence. -/
theorem schedulerNext_eq_conflict_analyze {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {c : Clause} {rest : List Clause} {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .conflict bs (c :: rest) learned)
    (hlevel : cfg.branch.level ≠ 0) :
    schedulerNext cfg = .analyzeConflict (stepAnalyzeConflictCounted cfg c learned
      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) c := by
  simp only [schedulerNext, hconf, hstatus, hd, ht, conflictStep, hlevel]
  split <;> simp_all

/-- ARM 8 (level-0 site): a level-0 conflict with a nonempty reported
clause is `.unsat` — never a local exclusion. -/
theorem schedulerNext_eq_conflict_unsat {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {c : Clause} {rest : List Clause} {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .conflict bs (c :: rest) learned)
    (hlevel : cfg.branch.level = 0) :
    schedulerNext cfg = .unsat := by
  simp only [schedulerNext, hconf, hstatus, hd, ht, conflictStep, hlevel,
    if_true]

/-- ARM 6 (conflict site): an EMPTY reported clause list is a database
refutation — a LOCAL exclusion, never `.unsat`. -/
theorem schedulerNext_eq_conflict_local {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .conflict bs [] learned) :
    schedulerNext cfg =
      .localExclude (stepLocalExclude cfg learned (branchRegion cfg)) := by
  simp only [schedulerNext, hconf, hstatus, hd, ht, conflictStep]

/-- ARM 6 (closure site): a `localExcluded` terminal result excludes the
branch with the closure's freshness-filtered payload. -/
theorem schedulerNext_eq_localExcluded {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {lit : Option Literal} {reason : Option Clause} {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .localExcluded bs lit reason learned) :
    schedulerNext cfg =
      .localExclude (stepLocalExclude cfg learned (branchRegion cfg)) := by
  simp only [schedulerNext, hconf, hstatus, hd, ht]

/-- ARM 8/7 (consume site): a successful consume is the chronological
fallback successor. -/
theorem schedulerNext_eq_consume_some {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .dead)
    (h : stepConsume cfg = some next) :
    schedulerNext cfg = .chronologicalFallback next := by
  simp only [schedulerNext, hconf, hstatus, consumeStep, h]

/-- ARM 8 (consume site): an exhausted pending frontier is `.unsat`. -/
theorem schedulerNext_eq_consume_none {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .dead)
    (h : stepConsume cfg = none) :
    schedulerNext cfg = .unsat := by
  simp only [schedulerNext, hconf, hstatus, consumeStep, h]

/-- ARM 8 (consume site, EMPTY-FRONTIER EXACTNESS): the dead-branch
`.unsat` dispatch is emitted EXACTLY at the exhausted frontier — the
`iff`, not only the forward direction. The pending stack is the single
trigger: a nonempty frontier can never take the `.unsat` leaf of
`consumeStep`. -/
theorem arm_consume_unsat_iff {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .dead) :
    schedulerNext cfg = .unsat ↔ cfg.pending = [] := by
  rw [schedulerNext_eq_consume hconf hstatus, consumeStep_unsat_iff]
/-- ARM 7 (jump site, no analysis): a recorded conflict whose analysis is
`none` falls back chronologically. -/
theorem schedulerNext_eq_backjump_none_analysis {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (h : cfg.conflict = some ev) (ha : ev.analysis = none) :
    schedulerNext cfg =
      .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) := by
  simp only [schedulerNext, h, backjumpStep, ha]

/-- ARM 7 (jump site, missing checkpoint): an asserting analysis with no
saved checkpoint at the backjump level falls back chronologically. -/
theorem schedulerNext_eq_backjump_no_checkpoint {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} (h : cfg.conflict = some ev)
    (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = none) :
    schedulerNext cfg =
      .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) := by
  simp only [schedulerNext, h, backjumpStep, ha, hcp]

/-- ARM 6 (jump site): a rejected assertion excludes the CHECKPOINT's
prefix locally. -/
theorem schedulerNext_eq_backjump_perform_none {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    (h : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = none) :
    schedulerNext cfg =
      .localExclude (stepLocalExclude cfg ev.learned (checkpointRegion cp)) := by
  simp only [schedulerNext, h, backjumpStep, ha, hcp, hp]

/-- ARM 5 (jump site): a performed jump is the complete
learn/backjump/assert transition. -/
theorem schedulerNext_eq_backjump_jump {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (h : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    schedulerNext cfg =
      .learnBackjumpAssert
        (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored)
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) an := by
  simp only [schedulerNext, h, backjumpStep, ha, hcp, hp]

/-! ## §2 The three-way case split: no dispatcher leaf is omitted

Every leaf of the nested `match` in `schedulerNext` is one of: the
conflict evidence route, the dead-branch consume route, or the active
route (deduction / stable / conflict / localExcluded). The active route's
theorem is the completeness statement for the remaining leaves. -/

/-- The dispatcher's top-level split. -/
theorem schedulerNext_cases {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) :
    (∃ ev, cfg.conflict = some ev ∧ schedulerNext cfg = backjumpStep cfg ev) ∨
    (cfg.conflict = none ∧ cfg.status = .dead ∧
      schedulerNext cfg = consumeStep cfg) ∨
    (cfg.conflict = none ∧ cfg.status = .active ∧
      ((∃ d, explainedDeduction cfg.original cfg.props cfg.branch = some d ∧
        schedulerNext cfg = .propagate (stepPropagate cfg d)) ∨
      (∃ bs, terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs ∧
        schedulerNext cfg = stableStepGuarded cfg) ∨
      (∃ bs cs learned,
        terminalResult cfg.orig cfg.original cfg.props cfg.branch = .conflict bs cs learned ∧
        schedulerNext cfg = conflictStep cfg cs learned) ∨
      (∃ bs lit reason learned,
        terminalResult cfg.orig cfg.original cfg.props cfg.branch =
          .localExcluded bs lit reason learned ∧
        schedulerNext cfg =
          .localExclude (stepLocalExclude cfg learned (branchRegion cfg))))) := by
  cases hc : cfg.conflict with
  | some ev => exact Or.inl ⟨ev, rfl, schedulerNext_eq_backjump hc⟩
  | none =>
      cases hs : cfg.status with
      | dead => exact Or.inr (Or.inl ⟨rfl, rfl, schedulerNext_eq_consume hc hs⟩)
      | active =>
          cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
          | some d =>
              exact Or.inr (Or.inr ⟨rfl, rfl,
                Or.inl ⟨d, rfl, schedulerNext_eq_deduction hc hs hd⟩⟩)
          | none =>
              cases ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch with
              | stable bs =>
                  exact Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inl
                    ⟨bs, rfl, by simp only [schedulerNext, hc, hs, hd, ht]⟩)⟩)
              | conflict bs cs learned =>
                  exact Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inr (Or.inl
                    ⟨bs, cs, learned, rfl,
                      by simp only [schedulerNext, hc, hs, hd, ht]⟩))⟩)
              | localExcluded bs lit reason learned =>
                  exact Or.inr (Or.inr ⟨rfl, rfl, Or.inr (Or.inr (Or.inr
                    ⟨bs, lit, reason, learned, rfl,
                      by simp only [schedulerNext, hc, hs, hd, ht]⟩))⟩)

/-- ARM 3 (semantic): the SAT witness is an ORIGINAL leaf solution. -/
theorem arm_sat_solution {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (h : stableStep cfg = .sat w) :
    SolutionWitness leaf cfg.orig w :=
  stableStep_sat_solution hreach h

/-- The GUARDED stable dispatch's `.sat` outcome is an UNGUARDED `.sat`
outcome: the two dispatches share the leaf-witness arm, and a `.sat` outcome
forces it (both split arms are `.decide` and the exclusion arm is
`.localExclude`, so none can be `.sat`). This bridges the dispatcher's
witness route (B1) to `arm_sat_solution`. -/
theorem stableStep_sat_of_guarded {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (h : stableStepGuarded cfg = .sat w) : stableStep cfg = .sat w := by
  cases hw : leafWitness leaf cfg with
  | some w' =>
      have h1 : (SchedulerTransition.sat w' : SchedulerTransition leaf) = .sat w := by
        have h' := h
        simp only [stableStepGuarded, hw] at h'
        exact h'
      injection h1 with hw_eq
      subst hw_eq
      simp only [stableStep, hw]
  | none =>
      exfalso
      have h1 : (match splitData cfg.branch.frame cfg.prio with
          | some (l, k, v, vs) =>
              if TrailRedundant cfg.branch.trail l = true then
                (SchedulerTransition.decide (stepDecideSkip cfg k v) l :
                  SchedulerTransition leaf)
              else SchedulerTransition.decide (stepDecide cfg k v vs l) l
          | none => SchedulerTransition.localExclude
              (stepLocalExclude cfg [] (branchRegion cfg))) = .sat w := by
        have h' := h
        simp only [stableStepGuarded, hw] at h'
        exact h'
      cases hsp : splitData cfg.branch.frame cfg.prio with
      | some d =>
          obtain ⟨l, v, vs, doms⟩ := d
          rw [hsp] at h1
          simp only [] at h1
          by_cases hred : TrailRedundant cfg.branch.trail l = true
          · rw [if_pos hred] at h1
            cases h1
          · rw [if_neg hred] at h1
            cases h1
      | none =>
          rw [hsp] at h1
          cases h1

/-- ARM 1 (semantic): a productive deduction preserves the invariant.
UNIT DISCIPLINE (P1 repair): the predecessor database's `UnitDB` gates the
closure contract's learned-dependent fields. -/
theorem arm_propagate_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hinv : SchedulerInvariant cfg) (hlevel : CheckpointsBelow cfg)
    (hu : UnitDB cfg.branch.learned)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    SchedulerInvariant (stepPropagate cfg d) :=
  stepPropagate_invariant hc hinv hlevel hu hd

/-- ARM 2 (INT-RESIDUAL route, retagged): `hpin` is the GLOBAL pin iff.
S1 has REFUTED its instantiation for int splits
(`int_slot_not_typed_witness`: `.bool false` shares the integer view with
`.int 0`), so this route is a reusable component conditional on
`SlotIntTyped`-style typing hypotheses — NOT an activation ingredient. The
reachable `.bool` split sites use `arm_decide_invariant_bool` below; the
int route stays as `stepDecide_int_invariant_of_slotTyped` in S1's module.
Owner of `hpin`: C2c/D1a (see S1 handoff). -/
theorem arm_decide_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {k : Nat} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hpin : ∀ a : Assignment, a.Fits cfg.orig →
      (l.norm.eval a = some true ↔ a[k]? = some v))   -- owner: C2c/D1a (int residual)
    (hred : TrailRedundant cfg.branch.trail l = false) : -- owner: C2c/integration
    SchedulerInvariant (stepDecide cfg k v vs l) :=
  stepDecide_invariant hinv hlevel hsplit hpin hred

/-- ARM 2 (ACTIVATION ROUTE, S1 consumer patch APPLIED, expanded): a Bool
split preserves the invariant with NO pin premise — the typed pin is
discharged from the split data (`decidePinTyped_bool` inside
`stepDecide_bool_invariant`, S1). The sole premise is the runtime absence
guard `hred`, whose owner is the runtime `.decide` arm (integration):
the dispatcher must gate `.decide` on
`TrailRedundant cfg.branch.trail l = false` (S1's `not_trailRedundant_iff`
/ `stepDecide_redundant_not_distinct` is why the guard is necessary).
The composition below is S1's `stepDecide_bool_invariant` body expanded:
`SchedulerDecision` participates in an import cycle with this module
(`SchedulerDecision -> CompiledScheduler -> SchedulerConflict ->
SchedulerReachable -> SchedulerProgress -> SchedulerStep`), so the
cycle-free C2a lemmas it composes are called directly. -/
theorem arm_decide_invariant_bool {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {b : Bool} {vs : Domain}
    {k : Nat} (hinv : SchedulerInvariant cfg)
    (hlevel : CheckpointsBelow cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, .bool b, vs))
    (hred : TrailRedundant cfg.branch.trail l = false) : -- owner: integration (runtime guard)
    SchedulerInvariant (stepDecide cfg k (.bool b) vs l) :=
  ⟨stepDecide_bool_reachable hinv hsplit hred,
    stepDecide_checkpoints_identify hinv hlevel hsplit,
    stepDecide_pending_fits hinv hsplit,
    stepDecide_branch_fits hinv hsplit,
    hinv.log_sound,
    stepDecide_covers hinv hsplit,
    hinv.learned_entailed⟩

/-- ARM 4 (semantic): recording the analysis evidence touches only
`conflict`/`stats`, so every invariant-relevant projection is unchanged
(the successor's invariant is the predecessor's, field for field). -/
theorem arm_analyzeConflict_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause}
    (hinv : SchedulerInvariant cfg) :
    SchedulerInvariant (stepAnalyzeConflict cfg c learned) where
  reachable := hinv.reachable
  checkpoints_identify := hinv.checkpoints_identify
  pending_fits := hinv.pending_fits
  branch_fits := hinv.branch_fits
  log_sound := hinv.log_sound
  coverage := hinv.coverage
  learned_entailed := hinv.learned_entailed

/-- The computed region of the current branch is SOUND under the site's
deadness evidence (the Wave-E `DeadRegion.byFrame` registration). -/
theorem branchRegion_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    DeadRegion.Sound leaf (branchRegion cfg) :=
  DeadRegion.byFrame_sound hdead

/-- ARM 6 (semantic, all four sites): local exclusion's registration step
preserves the `log_sound` field. -/
theorem arm_localExclude_log_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {learned : List Clause}
    (hsound : ExhaustionLog.Sound leaf cfg.log)
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    ExhaustionLog.Sound leaf
      (stepLocalExclude cfg learned (branchRegion cfg)).log :=
  stepLocalExclude_log_sound hsound (branchRegion_sound hdead)

/-- ARM 7 (semantic): the chronological fallback's registration step
preserves `log_sound`. -/
theorem arm_chronologicalFallback_log_sound {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hsound : ExhaustionLog.Sound leaf cfg.log)
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    ExhaustionLog.Sound leaf
      (stepChronologicalFallback cfg (branchRegion cfg)).log :=
  stepChronologicalFallback_log_sound hsound (branchRegion_sound hdead)

/-- ARM 7 (concrete transformation, replacing the premise-returning
`fallback_progress_wellFounded` shape): the REAL `stepConsume` successor
consumes exactly the head alternative — the frontier strictly shrinks by
one frame, and the next consume-time UNSAT test is about the tail. -/
theorem arm_chronologicalFallback_pending_consumed {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    next.pending = rest ∧ next.status = .active ∧ next.conflict = none := by
  unfold stepConsume at h
  rw [hp] at h
  cases hc : checkpointAt cfg.checkpoints f.level with
  | some cp =>
      simp only [hc, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
  | none =>
      simp only [hc, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩

/-- ARM 6 (concrete transformation, replacing the premise-returning
`fallback_safe` shape): the REAL local exclusion marks the branch dead,
clears the recorded conflict and appends the payload to the global
database — the state facts the exemption arm is consumed through. -/
theorem arm_localExclude_state {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion} :
    (stepLocalExclude cfg learned r).status = .dead ∧
    (stepLocalExclude cfg learned r).conflict = none ∧
    (stepLocalExclude cfg learned r).branch.learned
      = learned ++ cfg.branch.learned :=
  ⟨rfl, rfl, rfl⟩

/-- ARM 6 (concrete transformation): the REAL chronological fallback marks
the branch dead and clears the recorded conflict. -/
theorem arm_chronologicalFallback_state {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {r : DeadRegion} :
    (stepChronologicalFallback cfg r).status = .dead ∧
    (stepChronologicalFallback cfg r).conflict = none :=
  ⟨rfl, rfl⟩

/-- **ARM 5 RESIDUAL (owner S5, from S3's named `RestorationPreReachable`
in `Proofs/SchedulerBackjump.lean`): the survivor restoration algebra.**
The two per-survivor inputs of `Identifies.restore_extend` that the
checkpoint chain must relate: (a) the restored frame descends from the
pre-jump branch frame (`perform`'s assertion-filter/closure narrowing
discipline, S3's `execute_represents_forward`), and (b) for every
survivor the runtime filter keeps, the restored trail extends the pre-jump
trail by entries at or above that survivor's level (`perform_trail_extends`
gives target-level extras; the chain prefix law relates each survivor's
trail to the SELECTED checkpoint's, maintained at the push sites by
S1/S2/S4). Neither is available as a theorem yet; this predicate is the
exact remaining gap, never a successor invariant field. -/
def SurvivorRestoration {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (restored : BranchState leaf) : Prop :=
  FrameDescendsFrom restored.frame cfg.branch.frame ∧
  ∀ cp ∈ cfg.checkpoints, cp.level ≤ p.target →
    ∃ extra : List TrailEntry,
      restored.trail = cfg.branch.trail ++ extra ∧
        ∀ e ∈ extra, cp.level ≤ e.level

/-- ARM 5 (semantic, RE-ASSEMBLED): the jump successor's seven field
obligations are DERIVED from predecessor facts — no successor invariant
field is a premise of this wrapper:
* `hreach`/`hbfit` — S3's `perform_reachable_of_pre` (the actual
  `perform` result) under the closure contract, with the named residual
  `RestorationPreReachable` (owner: S5 checkpoint-snapshot invariant);
* `hpend` — S4's transfer of the predecessor `pending_fits`;
* `hident` — `Identifies.restore_extend` from the predecessor's
  `checkpoints_identify` plus the named residual `SurvivorRestoration`
  (owner: S5 / push sites S1–S4);
* `hlog` — C2c's `stepLearnBackjumpAssert_log_sound`;
* `hcov` — S4's `stepLearnBackjumpAssert_coverage_of_recorded_analysis`,
  whose single residual is `FalsifiedByTrail cfg.branch an.learned`
  (`RecordedAnalysisFalsified`, owner: falsified-wiring agent: B2/A3
  producers + recorded-event wiring);
* `hlent` — L1's `jump_learned_entailed`: the payload half is the named
  `LearnedEntailed leaf ev.learned` (owner: S4/D0 via the recorded
  analysis event), the restored half comes from the successor's own
  `ReachableState.wf` — never a fresh assumption.
Irreducible premises, named with owners: `hpre` (S5/S3), `hsr` (S5/S1–S4
push sites), `hfals` (`RecordedAnalysisFalsified`, falsified-wiring),
`hent` (S4/D0), and the unit-discipline triple `hpay`/`hu`/`hplanU`
(P1 round-2 repair; supplied at the supported index from N1's run
invariant). -/
theorem arm_learnBackjumpAssert_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis}
    (hinv : SchedulerInvariant cfg)
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hpay : UnitPayload cfg.original cfg.props)
    (hu : UnitDB cfg.branch.learned) (hplanU : UnitDB [p.learned])
    (hpre : RestorationPreReachable leaf cfg.orig p cfg.branch)
    (hsr : SurvivorRestoration cfg p restored)
    (hana : ev.analysis = some an) (hplan : p.learned = an.learned)
    (hperform : p.perform cfg.branch cfg.orig cfg.original cfg.props = some restored)
    (hfals : FalsifiedByTrail cfg.branch an.learned) -- owner: falsified-wiring
    (hent : LearnedEntailed leaf ev.learned) : -- owner: S4/D0
    SchedulerInvariant (stepLearnBackjumpAssert cfg p ev restored) := by
  have hreach : ReachableState leaf cfg.orig restored :=
    perform_reachable_of_pre hc hpay hu hplanU hpre hperform
  -- The successor branch extends `restored`'s database by the conflict
  -- payload: every non-database field transfers definitionally; `wf`'s
  -- learned conjunct is `jump_learned_entailed` (L1). No successor field
  -- is Assumed — this is a DERIVED `ReachableState`.
  have hreachSucc : ReachableState leaf cfg.orig
      (stepLearnBackjumpAssert cfg p ev restored).branch :=
    { length_ok := hreach.length_ok
      full_fits := hreach.full_fits
      pins_forced := hreach.pins_forced
      agrees := hreach.agrees
      narrowing_complete := hreach.narrowing_complete
      wf := ⟨hreach.wf.1, hreach.wf.2.1, hreach.wf.2.2.1,
        hreach.wf.2.2.2.1,
        (by
          intro c hc a ha
          exact jump_learned_entailed hent hreach c hc c
            (List.mem_singleton_self c) a ha)⟩
      sorted := hreach.sorted
      distinct := hreach.distinct }
  have hident : ∀ cp ∈ (stepLearnBackjumpAssert cfg p ev restored).checkpoints,
      cp.Identifies (stepLearnBackjumpAssert cfg p ev restored).branch
        cp.level := by
    intro cp hcp
    have hmem : cp ∈ cfg.checkpoints :=
      stepLearnBackjumpAssert_checkpoints_subset hcp
    have hlev : cp.level ≤ p.target :=
      stepLearnBackjumpAssert_checkpoints_below hcp
    obtain ⟨hdesc, htrail⟩ := hsr
    exact DecisionCheckpoint.Identifies.restore_extend
      (hinv.checkpoints_identify cp hmem) hdesc (htrail cp hmem hlev)
  have hpend : ∀ f ∈ (stepLearnBackjumpAssert cfg p ev restored).pending,
      ∀ i v, v ∈ (Frame.domains f).getD i Dom.empty →
        v ∈ (stepLearnBackjumpAssert cfg p ev restored).orig.getD i Dom.empty :=
    stepLearnBackjumpAssert_pending_fits hinv.pending_fits
  have hbfit : ∀ i v,
      v ∈ (Frame.domains
        (stepLearnBackjumpAssert cfg p ev restored).branch.frame).getD i Dom.empty →
        v ∈ (stepLearnBackjumpAssert cfg p ev restored).orig.getD i Dom.empty :=
    stepLearnBackjumpAssert_branch_fits hreachSucc
  have hlog : ExhaustionLog.Sound leaf
      (stepLearnBackjumpAssert cfg p ev restored).log :=
    stepLearnBackjumpAssert_log_sound hinv.log_sound
  have hcov : (stepLearnBackjumpAssert cfg p ev restored).coverage :=
    stepLearnBackjumpAssert_coverage_of_recorded_analysis
      hinv.coverage rfl hinv.reachable hana hplan hperform hfals
  have hlent : ∀ c ∈ (stepLearnBackjumpAssert cfg p ev restored).branch.learned,
      LearnedEntailed leaf [c] :=
    jump_learned_entailed hent hreach
  exact schedulerInvariant_after_backjump hreachSucc hident hpend hbfit hlog hcov
    hlent

/-- ARM 5 (coverage route, owner-tagged): the jump's coverage obligation
`hbc` (owner C2d) plus database monotonicity `hmono` (owner C2d via E1)
conserves coverage. -/
theorem arm_learnBackjumpAssert_coverage {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    (hcov : cfg.coverage)
    (hbc : BackjumpCovers leaf cfg.orig cfg
      (stepLearnBackjumpAssert cfg p ev restored))       -- owner: C2d
    (hmono : ∀ c ∈ cfg.branch.learned,
      c ∈ (stepLearnBackjumpAssert cfg p ev restored).branch.learned) :
                                                          -- owner: C2d via E1
    (stepLearnBackjumpAssert cfg p ev restored).coverage :=
  stepLearnBackjumpAssert_coverage hcov hbc hmono

/-! ## §3 The two UNSAT justifications -/

/-- ARM 8 (exhausted frontier): the S0 `unsat_coverage` instance. The dead
branch evidence `hdead` is NOT a bare `pending = []` — it must come from
the transition that reached the verdict; this is exactly the shape the
`consumeStep` route can supply (the failed child's frame region) and the
level-0 route supplies via the root-contradiction bridge below. -/
theorem arm_unsat_coverage {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (hpend : cfg.pending = [])
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    ∀ a, OriginalLeaves leaf cfg.orig a →
      ∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a :=
  hinv.unsat_coverage hpend hdead

/-- ARM 8 (root contradiction, owner-tagged): the a-priori deadness of the
branch follows from `RootContradiction` plus the root-facts bridge — the
premise `hbridge` is the ONLY gap (owner D1a, E3's `RootFactsBridge`). -/
theorem arm_unsat_rootContradiction {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hbridge : ∀ a, leaf a = true →
      ∀ e ∈ cfg.branch.trail, e.literal.eval a = some true) -- owner: D1a
    (hroot : RootContradiction leaf cfg.branch) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False :=
  fun a ha _ => hroot a ha (hbridge a ha)

/-- ARM 8 (assembled): the level-0 `.unsat` arm's full conclusion with the
D1a-owned bridge premise: `RootContradiction` plus the bridge gives the
dead-branch evidence, and S0's `unsat_coverage` turns it into a refuting
clause of the learned database. -/
theorem arm_unsat_rootContradiction_evidence {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hinv : SchedulerInvariant cfg)
    (hpend : cfg.pending = [])
    (hbridge : ∀ a, leaf a = true →
      ∀ e ∈ cfg.branch.trail, e.literal.eval a = some true) -- owner: D1a
    (hroot : RootContradiction leaf cfg.branch) :
    UnsatEvidence leaf cfg.orig cfg.pending cfg.branch.learned cfg.branch ∧
      ∀ a, OriginalLeaves leaf cfg.orig a →
        ∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a :=
  ⟨Or.inr hroot,
    hinv.unsat_coverage hpend (arm_unsat_rootContradiction hbridge hroot)⟩

end LeanFzn.Solver.UIP.C2d
