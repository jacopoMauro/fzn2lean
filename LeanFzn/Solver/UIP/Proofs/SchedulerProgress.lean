/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerProgress.lean

Purpose:
  A well-founded measure for the runtime dispatcher
  `LeanFzn/Solver/UIP/SchedulerStep.lean`'s `schedulerNext`, with strict-decrease
  theorems bound to the ACTUAL dispatcher arms through C2d's
  `schedulerNext_eq_*` lemmas (`LeanFzn/Solver/UIP/Proofs/SchedulerStep.lean`).
  No decrease hypothesis is assumed per case: each arm's decrease is
  computed from the concrete transition.

THE MEASURE.

  `SchedulerRank cfg = (frontierCost cfg.frontier, (Frame.mass frame, level))`

  ordered lexicographically. `cfg.frontier = branch.frame :: pending`
  (the current branch IS the head of the work list, which is what makes a
  split/backjump-coverage statement true and what makes `frontierCost`
  see the whole remaining work). So:

  * FIRST component `frontierCost (frame :: pending)`: the chronological
    tree cost of the whole remaining work (`LeanFzn/Solver/UIP/Frontier.lean`).
  * SECOND component `Frame.mass` of the CURRENT frame: the total number
    of remaining domain values (`LeanFzn/Solver/UIP/FrameFilter.lean`); this is
    the component that catches PROPAGATE, whose `ProductiveDeduction`
    carries a STRICT mass decrease (`A2`'s `decreases` field).
  * THIRD component `branch.level`: retained so a future jump-component
    can use the UIP strictness fact; NOT yet load-bearing (see below).

  `frontierCost` alone is NOT a backjump proof (PLAN C3a, verbatim): a
  learn/backjump/restore can hold or increase it. The honest status of
  that arm is recorded in the CASE TABLE below.

CASE TABLE (constructor -> status), all bound to the real dispatcher:

  1. `.propagate next`            PROVED
       `arm_propagate` — C2d `schedulerNext_eq_deduction`, decrease
       `rank_lt_propagate` (mass strictly down, first component
       non-increasing by `filterFrame_cost_le`).
  2. `.decide next l`             PROVED
       `arm_decide` — C2d `schedulerNext_eq_stable_decide`, decrease
       `rank_lt_decide` (first component strictly down by
       `frontierCost_expand`; the split replaces the parent frame by its
       two children, children + 1 = parent).
  3. `.sat w`                     TERMINAL (no successor; `arm_sat`).
  4. `.analyzeConflict next c`    STUTTER + NON-REPEAT (finding)
       `arm_analyzeConflict` — `rank_analyzeConflict_stutter` (the rank
       is literally unchanged: the transition records evidence only) and
       `analyzeConflict_not_repeated` (its successor carries `conflict =
       some ev`, whose dispatcher arm is `backjumpStep`, which by
       `backjumpStep_not_analyzeConflict` can never be `.analyzeConflict`),
       so the stutter cannot repeat. A single-step strict decrease for
       this arm is IMPOSSIBLE for any `BranchState`-projection measure
       (the arm changes only `conflict`/`stats`); the phase argument is
       the correct termination content.
  5. `.learnBackjumpAssert ...`   OPEN (finding, owner C3b/integration)
       `arm_learnBackjumpAssert` — the successor restores an ANCESTOR
       frame whose `frontierCost` can exceed the conflict frame's (the
       restored frame is not a pending frame, so `frontierCost_cons`
       does not apply), and its `Frame.mass`/`level` bear no lex-relation
       to the pre-jump ones. Necessity witness (informal): jump to a
       level-0 ancestor with a wide frame after a deep narrow conflict —
       component 1 strictly increases, so no lex component can pay for
       it. The missing component is trail-based (fresh asserting entry /
       no-revisit of restored ancestors); predecessor `analyzeConflict`
       is already bounded by `analyzeConflict_not_repeated`.
  6. `.localExclude next`         STUTTER + COMPOSITE PROVED
       `arm_localExclude` — `rank_localExclude_stutter` (the rank is
       unchanged: branch/pending untouched) and
       `arm_localExclude_then_consume`: the dispatcher FORCES the next
       step to be the consume route (`conflict = none ∧ status = .dead`
       is exactly `schedulerNext_eq_consume`'s guard), and that step
       strictly decreases by `rank_lt_consume`.
  7. `.chronologicalFallback n`   STUTTER + COMPOSITE PROVED
       `arm_fallback` / `arm_fallback_without_consume` /
       `arm_fallback_composite`: same shape as arm 6 — the fallback arm is
       a rank stutter (its `learned`/`log`/`status` changes are invisible
       to the rank BY CONSTRUCTION), and the forced next consume step
       strictly decreases.
  8. `.unsat`                     TERMINAL (`arm_unsat`: pending = []).

NO-FOOLING FACTS (plan clause "explicitly prevent restarting exhausted
work"):
  * `rank_learned_congr`, `rank_log_congr`, `rank_conflict_congr`: the
    rank does not read the learned database, the exhaustion log or the
    recorded evidence, so RE-ADDING a clause already in `db`/`learned`
    or re-recording evidence cannot move (let alone reset) the measure.
  * `ExhaustionLog` registrations are permanent:
    `log_mem_localExclude` / `log_mem_chronologicalFallback` (via the
    accepted `ExhaustionLog.register_mono`) and `log_mem_learnBackjumpAssert`
    (the jump never touches the log), so a restored ancestor cannot
    un-register a dead region. Semantic soundness is the accepted
    `ExhaustionLog.Sound` (C2c/C2d owners).

DAG: Proofs.SchedulerStep (C2d arm table) -> SchedulerProgress (this
module; consumed by the C3 driver).
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerStep
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.C3a
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The measure and its well-foundedness -/

/-- The scheduler's progress measure: the chronological cost of the whole
remaining work (current frame + pending stack), then the current frame's
domain mass, then the current level — read lexicographically. -/
def SchedulerRank (cfg : SchedulerConfig leaf) : Nat × (Nat × Nat) :=
  (frontierCost cfg.frontier, (Frame.mass cfg.branch.frame, cfg.branch.level))

/-- The lexicographic order on `Nat × (Nat × Nat)` used for `SchedulerRank`.
It is the well-founded relation induced by the core product instance
(`sizeOf` on `Nat` is the identity here), so well-foundedness is
inherited, not assumed. -/
def RankLt (a b : Nat × (Nat × Nat)) : Prop :=
  a.1 < b.1 ∨ (a.1 = b.1 ∧ (a.2.1 < b.2.1 ∨ (a.2.1 = b.2.1 ∧ a.2.2 < b.2.2)))

/-- The lex order is the core product well-founded relation (definitional
identification; `Prod.Lex` is the inductive of `Prod.lex`). This is the
bridge that lets the arm proofs use plain `<`/`=` facts while
well-foundedness comes from the instance. -/
theorem rankLt_of_inst {a b : Nat × (Nat × Nat)} (h : RankLt a b) :
    (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).rel a b := by
  have hrel : (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).rel =
      Prod.Lex (sizeOfWFRel.rel (α := Nat))
        (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat))) := rfl
  rw [hrel]
  show Prod.Lex (sizeOfWFRel.rel (α := Nat))
    (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
    (a.1, a.2) (b.1, b.2)
  rcases h with h | ⟨h1, h | ⟨h2, h3⟩⟩
  · exact Prod.Lex.left (b₁ := a.2) (b₂ := b.2) h
  · rw [← h1]
    exact Prod.Lex.right (a := a.1) (Prod.Lex.left (b₁ := a.2.2) (b₂ := b.2.2) h)
  · rw [← h1]
    show Prod.Lex (sizeOfWFRel.rel (α := Nat))
      (Prod.Lex (sizeOfWFRel.rel (α := Nat)) (sizeOfWFRel.rel (α := Nat)))
      (a.1, (a.2.1, a.2.2)) (a.1, (b.2.1, b.2.2))
    rw [← h2]
    exact Prod.Lex.right (a := a.1)
      (Prod.Lex.right (a := a.2.1) h3)

/-- The measure's lex order is well-founded: it is a subrelation of the
core product well-founded relation, so an infinite strictly decreasing
chain of ranks is impossible — a repeating scheduler cycle would produce
one (each arm's decrease theorem below), hence no cycle. -/
theorem rankLt_wf : WellFounded RankLt :=
  Subrelation.wf (fun {_ _} h => rankLt_of_inst h)
    (inferInstance : WellFoundedRelation (Nat × (Nat × Nat))).wf

/-- The scheduler's step relation on configurations (successors of the
dispatcher's nonterminal arms) is well-founded when oriented by the
measure. -/
theorem schedulerRank_wf {leaf : Assignment → Bool} :
    WellFounded (fun a b : SchedulerConfig leaf =>
      RankLt (SchedulerRank a) (SchedulerRank b)) :=
  InvImage.wf SchedulerRank rankLt_wf

/-! ## §2 Rank algebra for `frontierCost` over the current frame -/

/-- Replacing the head frame by a strictly cheaper one strictly decreases
the frontier cost. -/
theorem frontierCost_frame_lt {f g : BranchFrame}
    (h : branchCost f.1 < branchCost g.1) (pending : List BranchFrame) :
    frontierCost (f :: pending) < frontierCost (g :: pending) := by
  simp only [frontierCost, List.map_cons, List.sum_cons]
  exact Nat.add_lt_add_right h _

/-- Replacing the head frame by an equally costly one keeps the frontier
cost (the first lex component is then unchanged and the second one
decides). -/
theorem frontierCost_frame_congr {f g : BranchFrame}
    (h : branchCost f.1 = branchCost g.1) (pending : List BranchFrame) :
    frontierCost (f :: pending) = frontierCost (g :: pending) := by
  simp only [frontierCost, List.map_cons, List.sum_cons]
  rw [h]

/-! ## §3 What the rank does NOT read (no reset by re-learning / re-registering)

These are the plan's "explicitly prevent repeated learned clauses or
restored ancestors from restarting exhausted work" facts, in their exact
scope: the rank is invariant under learned-database growth, exhaustion
registration, evidence recording and checkpoint retirement, so no amount
of clause re-adding or evidence re-recording can reset progress. The
only way to move the rank is to change the FRAME, the LEVEL or the
FRONTIER — which is what the decrease theorems measure. -/

/-- Re-adding clauses to the learned database cannot move the rank. -/
theorem rank_learned_congr (cfg : SchedulerConfig leaf) (ls : List Clause) :
    SchedulerRank { cfg with branch := { cfg.branch with learned := ls } } =
      SchedulerRank cfg := rfl

/-- Registering dead regions cannot move the rank. -/
theorem rank_log_congr (cfg : SchedulerConfig leaf) (l : ExhaustionLog) :
    SchedulerRank { cfg with log := l } = SchedulerRank cfg := rfl

/-- Recording conflict evidence cannot move the rank. -/
theorem rank_conflict_congr (cfg : SchedulerConfig leaf)
    (ev : Option ConflictEvidence) :
    SchedulerRank { cfg with conflict := ev } = SchedulerRank cfg := rfl

/-! ## §4 Arm table: the boxed-out transitions are rank stutters -/

/-- ARM 4 stutter: recording the analysis evidence leaves the rank exactly
unchanged (branch, pending, database and level are untouched; the rank
reads none of `conflict`, `stats`). -/
theorem rank_analyzeConflict_stutter (cfg : SchedulerConfig leaf) (c : Clause)
    (learned : List Clause) :
    SchedulerRank (stepAnalyzeConflict cfg c learned) = SchedulerRank cfg := rfl

/-- ARM 6 stutter: local exclusion leaves the rank exactly unchanged
(`learned`/`log`/`status` are invisible to the rank by construction). -/
theorem rank_localExclude_stutter (cfg : SchedulerConfig leaf)
    (learned : List Clause) (r : DeadRegion) :
    SchedulerRank (stepLocalExclude cfg learned r) = SchedulerRank cfg := rfl

/-- ARM 7 stutter: the chronological fallback leaves the rank exactly
unchanged (it registers a region and marks the branch dead). -/
theorem rank_chronologicalFallback_stutter (cfg : SchedulerConfig leaf)
    (r : DeadRegion) :
    SchedulerRank (stepChronologicalFallback cfg r) = SchedulerRank cfg := rfl

/-! ## §5 The split's frame decomposition (for the decide arm) -/

/-- `splitData` pins the head remaining value of the head remaining
domain: the frame is `(v :: vs) :: doms` with the ORIGINAL chosen
prefix. -/
theorem splitData_frame_eq {f : BranchFrame} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain} (h : splitData f = some (l, v, vs, doms)) :
    ∃ chosen, f = ((v :: vs) :: doms, chosen) := by
  obtain ⟨slots, chosen⟩ := f
  cases slots with
  | nil => simp [splitData] at h
  | cons d rest =>
      cases d with
      | nil => simp [splitData] at h
      | cons w ws =>
          cases hl : valueLiteral chosen.length w with
          | none => simp [splitData, hl] at h
          | some l' =>
              simp only [splitData, hl, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl, rfl, rfl⟩ := h
              exact ⟨chosen, rfl⟩

/-! ## §6 The proved decreases (arms 1, 2 and the forced consume) -/

/-- ARM 1 decrease: a productive deduction strictly decreases the rank.
If the narrowed frame is strictly cheaper by `branchCost`, the first
component decreases (`filterFrame_cost_le` gives the non-strict half);
otherwise the frontier cost is equal and the SECOND component wins with
the deduction's own strict mass decrease — the `Frame.mass` measure is
exactly the payload `ProductiveDeduction` carries, so no hypothesis is
assumed here. -/
theorem rank_lt_propagate (cfg : SchedulerConfig leaf)
    (d : ProductiveDeduction leaf cfg.branch) :
    RankLt (SchedulerRank (stepPropagate cfg d)) (SchedulerRank cfg) := by
  have hcost : branchCost d.frame.1 ≤ branchCost cfg.branch.frame.1 :=
    filterFrame_cost_le d.filtered
  have e1 : SchedulerRank (stepPropagate cfg d) =
      (frontierCost (d.frame :: cfg.pending),
        (Frame.mass d.frame, cfg.branch.level)) := by
    simp [SchedulerRank, SchedulerConfig.frontier, stepPropagate, narrowState]
  rw [e1]
  rcases Nat.lt_or_eq_of_le hcost with hlt | heq
  · exact Or.inl (frontierCost_frame_lt hlt cfg.pending)
  · exact Or.inr ⟨frontierCost_frame_congr heq cfg.pending, Or.inl d.decreases⟩

/-- ARM 2 decrease: the split strictly decreases the rank. The successor's
frontier is the two children followed by the old pending stack; the
parent frame is replaced (not retained), and `frontierCost_expand` gives
`children + 1 = parent`, so the FIRST component strictly decreases. -/
theorem rank_lt_decide (cfg : SchedulerConfig leaf) (v : Value)
    (vs : Domain) (doms : List Domain) (l : Literal)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    RankLt (SchedulerRank (stepDecide cfg v vs doms l)) (SchedulerRank cfg) := by
  obtain ⟨chosen, hf⟩ := splitData_frame_eq hsplit
  have hold : cfg.frontier = (((v :: vs) :: doms, chosen) :: cfg.pending) := by
    simp only [SchedulerConfig.frontier, hf]
  have hnew : (stepDecide cfg v vs doms l).frontier
      = ((doms, chosen ++ [v]) :: (vs :: doms, chosen) :: cfg.pending) := by
    simp only [SchedulerConfig.frontier, stepDecide_pending, stepDecide_frame, hf]
  refine Or.inl ?_
  show frontierCost (stepDecide cfg v vs doms l).frontier < frontierCost cfg.frontier
  rw [hnew, hold]
  have hexp := frontierCost_expand v vs doms chosen cfg.pending
  omega

/-- ARM 2b decrease (B1, the redundant-pin skip): the skip replaces the head
frame `((v :: vs) :: doms, chosen)` by the pinned child `(doms, chosen ++ [v])`
without pushing a sibling, so the frontier's cost strictly drops at the head
(the frame loses its nonempty head domain) — the FIRST component of the
historical rank decreases. -/
theorem rank_lt_decideSkip (cfg : SchedulerConfig leaf) (v : Value)
    (vs : Domain) (doms : List Domain) (l : Literal)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    RankLt (SchedulerRank (stepDecideSkip cfg v doms)) (SchedulerRank cfg) := by
  obtain ⟨chosen, hf⟩ := splitData_frame_eq hsplit
  have hold : cfg.frontier = (((v :: vs) :: doms, chosen) :: cfg.pending) := by
    simp only [SchedulerConfig.frontier, hf]
  have hnew : (stepDecideSkip cfg v doms).frontier
      = ((doms, chosen ++ [v]) :: cfg.pending) := by
    simp only [SchedulerConfig.frontier, stepDecideSkip, hf]
  refine Or.inl ?_
  show frontierCost (stepDecideSkip cfg v doms).frontier < frontierCost cfg.frontier
  rw [hnew, hold]
  have hcost : branchCost doms < branchCost ((v :: vs) :: doms) := by
    have h : branchCost ((v :: vs) :: doms)
        = 1 + (vs.length + 1) * (branchCost doms + 1) := by simp [branchCost]
    rw [h]
    have hle : branchCost doms + 1 ≤ (vs.length + 1) * (branchCost doms + 1) := by
      rw [Nat.succ_mul]
      omega
    omega
  simp only [frontierCost, List.map_cons, List.sum_cons]
  exact Nat.add_lt_add_right hcost _

/-- The consume step's resumed frame is exactly the consumed pending
alternative and its pending stack is the tail: the REAL reconstruction
(the single canonical route sets `frame := f`), no coherence assumption. -/
theorem stepConsume_frame_of_pending_cons {cfg next : SchedulerConfig leaf}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    next.branch.frame = f ∧ next.pending = rest := by
  unfold stepConsume at h
  rw [hp] at h
  simp only [Option.some.injEq] at h
  subst h
  exact ⟨resumePending_frame _ _ _, rfl⟩

/-- The consume arm's decrease: the dead current frame leaves the frontier
and the consumed pending frame becomes it — the rank's first component
drops by the dead frame's positive `branchCost` (`frontierCost_cons`). -/
theorem rank_lt_consume {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame} (hp : cfg.pending = f :: rest)
    (h : stepConsume cfg = some next) :
    RankLt (SchedulerRank next) (SchedulerRank cfg) := by
  obtain ⟨hframe, hpend⟩ := stepConsume_frame_of_pending_cons hp h
  refine Or.inl ?_
  show frontierCost (next.branch.frame :: next.pending) <
    frontierCost (cfg.branch.frame :: cfg.pending)
  rw [hframe, hpend, hp]
  exact frontierCost_cons cfg.branch.frame (f :: rest)

/-! ## §7 The dispatcher-bound arm theorems (C2d bindings) -/

/-- ARM 1 (propagate), bound to the real dispatcher: the dispatcher
returns `.propagate` and the rank strictly decreases. -/
theorem arm_propagate {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {d : ProductiveDeduction leaf cfg.branch}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    schedulerNext cfg = .propagate (stepPropagate cfg d) ∧
      RankLt (SchedulerRank (stepPropagate cfg d)) (SchedulerRank cfg) :=
  ⟨C2d.schedulerNext_eq_deduction hconf hstatus hd, rank_lt_propagate cfg d⟩

/-- ARM 2 (decide/split), bound to the real dispatcher, FRESH-pin form
(B1: the guarded dispatcher routes redundant pins to `stepDecideSkip`). -/
theorem arm_decide {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs)
    (hw : leafWitness leaf cfg = none)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    schedulerNext cfg = .decide (stepDecide cfg v vs doms l) l ∧
      RankLt (SchedulerRank (stepDecide cfg v vs doms l)) (SchedulerRank cfg) :=
  ⟨C2d.schedulerNext_eq_stable_decide hconf hstatus hd ht hw hsplit hred,
    rank_lt_decide cfg v vs doms l hsplit⟩

/-- ARM 3 (sat): terminal — no successor, no decrease obligation. -/
theorem arm_sat {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    {bs : BranchState leaf} {w : Assignment}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .stable bs)
    (hw : leafWitness leaf cfg = some w) :
    schedulerNext cfg = .sat w :=
  C2d.schedulerNext_eq_stable_sat hconf hstatus hd ht hw

/-- ARM 4 (analyzeConflict): the dispatcher records the evidence — with the
executed analyzer run's pivot expansions counted into
`events.reasonResolutions` (O1 wiring) — the rank STUTTERS, and the
successor's route is forced to `backjumpStep` — so the stutter cannot
repeat. -/
theorem arm_analyzeConflict {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {c : Clause} {rest : List Clause} {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .conflict bs (c :: rest) learned)
    (hlevel : cfg.branch.level ≠ 0) :
    schedulerNext cfg = .analyzeConflict (stepAnalyzeConflictCounted cfg c learned
        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) c ∧
      SchedulerRank (stepAnalyzeConflictCounted cfg c learned
        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
        = SchedulerRank cfg :=
  ⟨C2d.schedulerNext_eq_conflict_analyze hconf hstatus hd ht hlevel, rfl⟩

/-- ARM 5 (learn/backjump/assert): bound to the real dispatcher. The
decrease side is OPEN (see the file header): the restored ancestor's
frontier can exceed the conflict frame's, so no lex component of
`SchedulerRank` pays for the jump. -/
theorem arm_learnBackjumpAssert {leaf : Assignment → Bool}
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
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) an :=
  C2d.schedulerNext_eq_backjump_jump h ha hcp hp

/-- ARM 6 (localExclude), bound to the real dispatcher: the rank stutters.
The composite's decrease is `arm_localExclude_then_consume`. -/
theorem arm_localExclude {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {l : Option Literal} {reason : Option Clause} {learned : List Clause}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .active)
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = none)
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .localExcluded bs l
      reason learned) :
    schedulerNext cfg =
      .localExclude (stepLocalExclude cfg learned (branchRegion cfg)) ∧
      SchedulerRank (stepLocalExclude cfg learned (branchRegion cfg)) =
        SchedulerRank cfg :=
  ⟨C2d.schedulerNext_eq_localExcluded hconf hstatus hd ht,
    rank_localExclude_stutter cfg learned (branchRegion cfg)⟩

/-- ARM 7 (fallback, recorded conflict without analysis), bound to the
real dispatcher: rank stutter (the successor is dead, so the NEXT step is
the forced consume). -/
theorem arm_fallback_without_analysis {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (h : cfg.conflict = some ev) (ha : ev.analysis = none) :
    schedulerNext cfg =
      .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) ∧
      SchedulerRank (stepChronologicalFallback cfg (branchRegion cfg)) =
        SchedulerRank cfg :=
  ⟨C2d.schedulerNext_eq_backjump_none_analysis h ha,
    rank_chronologicalFallback_stutter cfg (branchRegion cfg)⟩

/-- ARM 7 (fallback, asserting analysis with no saved checkpoint), bound
to the real dispatcher: rank stutter. -/
theorem arm_fallback_without_checkpoint {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} (h : cfg.conflict = some ev)
    (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = none) :
    schedulerNext cfg =
      .chronologicalFallback (stepChronologicalFallback cfg (branchRegion cfg)) ∧
      SchedulerRank (stepChronologicalFallback cfg (branchRegion cfg)) =
        SchedulerRank cfg :=
  ⟨C2d.schedulerNext_eq_backjump_no_checkpoint h ha hcp,
    rank_chronologicalFallback_stutter cfg (branchRegion cfg)⟩

/-- ARM 7 (consume site), bound to the real dispatcher: the dead-branch
route's successors are the chronological fallback with a STRICT decrease
(finite pending — nonterminal) or `.unsat` (terminal, pending empty). -/
theorem arm_consume {leaf : Assignment → Bool} {cfg next : SchedulerConfig leaf}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .dead)
    (h : stepConsume cfg = some next) {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) :
    schedulerNext cfg = .chronologicalFallback next ∧
      RankLt (SchedulerRank next) (SchedulerRank cfg) :=
  ⟨C2d.schedulerNext_eq_consume_some hconf hstatus h, rank_lt_consume hp h⟩

/-- ARM 8 (unsat), bound to the real dispatcher: terminal, and the
pending frontier is exactly empty (the verdict's precondition). -/
theorem arm_unsat {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    (hconf : cfg.conflict = none) (hstatus : cfg.status = .dead)
    (h : stepConsume cfg = none) :
    schedulerNext cfg = .unsat ∧ cfg.pending = [] :=
  ⟨C2d.schedulerNext_eq_consume_none hconf hstatus h,
    (stepConsume_eq_none_iff (cfg := cfg)).mp h⟩

/-! ## §8 Composites: the stutters are paid by the forced next step

`stepLocalExclude` and `stepChronologicalFallback` leave `conflict = none`
and `status = .dead` — exactly `schedulerNext_eq_consume`'s guard — so
the dispatcher FORCES the consume route immediately after them and the
consumed successor's rank is strictly below the ORIGINAL configuration's
(stutter + `rank_lt_consume`). -/

/-- ARM 6 composite: local exclusion followed by the forced consume
strictly decreases the rank. -/
theorem arm_localExclude_then_consume {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    RankLt (SchedulerRank next) (SchedulerRank cfg) := by
  have hstep := rank_lt_consume hp h
  rwa [rank_localExclude_stutter] at hstep

/-- ARM 7 composite: the chronological fallback followed by the forced
consume strictly decreases the rank. -/
theorem arm_fallback_then_consume {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    RankLt (SchedulerRank next) (SchedulerRank cfg) := by
  have hstep := rank_lt_consume hp h
  rwa [rank_chronologicalFallback_stutter] at hstep

/-! ## §9 The analyze-conflict stutter cannot repeat (phase argument) -/

/-- The successor of the `analyzeConflict` arm carries recorded evidence. -/
theorem analyzeConflict_successor_conflict (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) :
    ∃ ev, (stepAnalyzeConflict cfg c learned).conflict = some ev :=
  ⟨_, rfl⟩

/-- The recorded-evidence dispatch never returns `.analyzeConflict`: every
`backjumpStep` leaf is `.chronologicalFallback`, `.localExclude` or
`.learnBackjumpAssert`. Hence the `analyzeConflict` stutter is a one-shot
phase change and the dispatcher cannot loop on it. -/
theorem backjumpStep_not_analyzeConflict (cfg : SchedulerConfig leaf)
    (ev : ConflictEvidence) :
    ¬ (∃ next c, backjumpStep cfg ev = .analyzeConflict next c) := by
  rintro ⟨next, c, hc⟩
  cases ha : ev.analysis with
  | none => simp only [backjumpStep, ha] at hc; cases hc
  | some an =>
      cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none => simp only [backjumpStep, ha, hcp] at hc; cases hc
      | some cp =>
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
              an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
          | none => simp only [backjumpStep, ha, hcp, hp] at hc; cases hc
          | some restored => simp only [backjumpStep, ha, hcp, hp] at hc; cases hc

/-- The composite non-repetition statement at the dispatcher level: after
an `analyzeConflict` arm the dispatcher's arm is `backjumpStep` and never
`.analyzeConflict` again. -/
theorem analyzeConflict_not_repeated {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {c : Clause} {learned : List Clause} :
    (stepAnalyzeConflict cfg c learned).conflict.isSome ∧
      ¬ (∃ next c', schedulerNext (stepAnalyzeConflict cfg c learned) =
        .analyzeConflict next c') := by
  obtain ⟨ev, hev⟩ := analyzeConflict_successor_conflict cfg c learned
  refine ⟨hev ▸ rfl, ?_⟩
  rintro ⟨next, c', hc⟩
  rw [C2d.schedulerNext_eq_backjump hev] at hc
  exact backjumpStep_not_analyzeConflict _ _ ⟨next, c', hc⟩

/-! ## §10 Exhausted work stays exhausted across every transition -/

/-- Local exclusion's registration is monotone. -/
theorem log_mem_localExclude {cfg : SchedulerConfig leaf} {learned : List Clause}
    {r : DeadRegion} {p : DeadRegion} (h : p ∈ cfg.log.regions) :
    p ∈ (stepLocalExclude cfg learned r).log.regions :=
  ExhaustionLog.register_mono h

/-- The chronological fallback's registration is monotone. -/
theorem log_mem_chronologicalFallback {cfg : SchedulerConfig leaf} {r : DeadRegion}
    {p : DeadRegion} (h : p ∈ cfg.log.regions) :
    p ∈ (stepChronologicalFallback cfg r).log.regions :=
  ExhaustionLog.register_mono h

/-- The jump (ancestor restoration) does NOT touch the exhaustion log: a
restored ancestor can never un-register exhausted work. -/
theorem log_mem_learnBackjumpAssert {cfg : SchedulerConfig leaf}
    {p : BackjumpPlan leaf} {ev : ConflictEvidence} {restored : BranchState leaf}
    {r : DeadRegion} (h : r ∈ cfg.log.regions) :
    r ∈ (stepLearnBackjumpAssert cfg p ev restored).log.regions := h

/-- Propagation keeps every registration. -/
theorem log_mem_propagate {cfg : SchedulerConfig leaf}
    {d : ProductiveDeduction leaf cfg.branch} {r : DeadRegion}
    (h : r ∈ cfg.log.regions) :
    r ∈ (stepPropagate cfg d).log.regions := h

/-- The split keeps every registration. -/
theorem log_mem_decide {cfg : SchedulerConfig leaf} (v : Value) (vs : Domain)
    (doms : List Domain) (l : Literal) {r : DeadRegion}
    (h : r ∈ cfg.log.regions) :
    r ∈ (stepDecide cfg v vs doms l).log.regions := h

/-- Evidence recording keeps every registration. -/
theorem log_mem_analyzeConflict {cfg : SchedulerConfig leaf} (c : Clause)
    (learned : List Clause) {r : DeadRegion} (h : r ∈ cfg.log.regions) :
    r ∈ (stepAnalyzeConflict cfg c learned).log.regions := h

end LeanFzn.Solver.UIP.C3a
