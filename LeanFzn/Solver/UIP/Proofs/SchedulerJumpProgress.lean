/-
  P4 — THE JUMP'S STRICT RANK DECREASE (`SchedulerJumpProgress`).

  Gate: "Prove jump decrease from actual reachable analysis/restore steps.
  For a novelty-first rank, use canonical database growth and handle P2's
  repeated-clause branch separately. A lower decision level alone is
  insufficient because decisions raise it again. If using exhausted-work or
  pending-supersession instead, prove its finite bound, semantic deletions
  and strict decrease; do not use fixed arithmetic slack. Export the exact
  facts consumed by P3's rank."

  DISCHARGE (new-clause route, exactly the gate's first alternative):
  (i) NOVELTY CASE: the inserted clause is `an.learned` (via
      `PlanMatchesAnalysis`), the successor database is its cons
      (`stepLearnBackjumpAssert_learned_eq`, definitional), so the canonical
      database grows by `Clause.canonicalClause an.learned`
      (`learnBackjumpAssert_records_analysis`). The component-1 countdown
      `P3.absentCount` STRICTLY decreases as soon as that canonical clause
      is one of the FIXED pool clauses (`absentCount_lt_of_mono_mem`, §1).
  (ii) REPEATED CASE: EXCLUDED, not assumed, via P2's
      `jumpNovelty_of_unfalsified`. `not_jumpRepeated_of_unfalsified`
      demands EXACTLY two premises:
        * `DatabaseUnfalsified cfg.branch`, i.e.
          `∀ c ∈ cfg.branch.learned, ¬ FalsifiedByTrailNorm cfg.branch c`
          (named missing invariant; owner S4/S5 successor-invariant
          extension), and
        * `FalsifiedByTrailNorm cfg.branch an.learned`
          (produced unconditionally at the real call site by
          `recordedAnalysis_normFalsified`, owner of
          `Proofs/SchedulerFalsified`).
  (iii) WHY NOT frontierCost / LEVEL: the F1 witness
      (`Proofs/JumpDecrease`) restores a frame whose frontier cost RISES
      1 -> 5, and `phaseRank_lt_decide` itself raises component 2; decision
      levels rise again after every jump. Neither level nor frontier cost
      can be the decreasing argument. The jump consumes COMPONENT 1 of the
      fixed-input lex rank (`PhaseLt`'s most significant position), so
      components 2–4 are irrelevant for this arm: no fixed arithmetic
      slack, no saturating subtraction — `absentCount` is a bounded count
      over the fixed pool (P3 §1).

  NAMED PREMISE (owner P2, obligation P1-a — POOL CLOSURE):
      hpool : Clause.canonicalClause an.learned ∈ clausePool orig
  This is the EXACT needed shape. P1-a as currently stated
  (`c.canonicalClause.eraseDups ∈ clausePool orig` under the literal
  vocabulary hypothesis, `SchedulerVocabulary` §P1-a) is a DIFFERENT
  statement: it erases duplicates, while `absentCount` matches the
  canonical clause itself. P2 should deliver membership of the canonical
  clause directly, or additionally a duplicate-freeness fact for the
  recorded analysis clause.

  EXPORTS CONSUMED BY P5 (jump arm of the master decrease lemma):
    * `phaseLt_stepLearnBackjumpAssert` — NO novelty assumption; carries
      `DatabaseUnfalsified` (owner S4/S5) plus the reachable-falsification
      producer inputs.
    * `phaseLt_stepLearnBackjumpAssert_of_novelty` — variant with
      `JumpNovelty` supplied directly (callers that already hold it).
    * `absentCount_stepLearnBackjumpAssert_lt` — the raw component-1
      strict decrease, no rank vocabulary.

  Dependencies: `Proofs/SchedulerRank` (P3), `Proofs/LearningNovelty` (P2),
  `Proofs/SchedulerCoverage` (S4), `Proofs/SchedulerFalsified`.
  TOOLCHAIN: no `sorry`, no custom axioms, no Mathlib (`omega` only).
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerRank
import LeanFzn.Solver.UIP.Proofs.LearningNovelty
import LeanFzn.Solver.UIP.Proofs.SchedulerCoverage
import LeanFzn.Solver.UIP.Proofs.SchedulerFalsified
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.P4
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.P3

/-! ## §1 Strict decrease of the bounded pool countdown

The only missing ingredient for novelty progress: the inserted canonical
clause is a POOL clause, so its flip from absent to present makes the
bounded count strictly smaller. All other pool clauses only flip
present-wards (`absentCount_mono`), so one strict flip suffices. -/

/-- **STRICT COUNTDOWN DECREASE**: if `db` grows into `db'` and some pool
clause `c` is absent from `canonicalDB db` but present in `canonicalDB db'`,
then the pool countdown strictly decreases. No subtraction, no slack. -/
theorem absentCount_lt_of_mono_mem {db db' pool : List Clause} {c : Clause}
    (hmono : ∀ d ∈ db, d ∈ db') (hpool : c ∈ pool)
    (hnew : c ∈ canonicalDB db') (hold : c ∉ canonicalDB db) :
    absentCount db' pool < absentCount db pool := by
  have hcanon : ∀ d, d ∈ canonicalDB db → d ∈ canonicalDB db' :=
    canonicalDB_mono hmono
  induction pool with
  | nil => simp at hpool
  | cons d ds ih =>
      rcases List.mem_cons.mp hpool with rfl | htl
      · have h1 : (if c ∈ canonicalDB db' then 0 else 1) = 0 := if_pos hnew
        have h0 : (if c ∈ canonicalDB db then 0 else 1) = 1 := if_neg hold
        have htle : absentCount db' ds ≤ absentCount db ds :=
          absentCount_mono hmono ds
        simp only [absentCount]
        rw [h1, h0]
        omega
      · have hhead : (if d ∈ canonicalDB db' then 0 else 1) ≤
            (if d ∈ canonicalDB db then 0 else 1) := by
          by_cases hd : d ∈ canonicalDB db
          · have hd' : d ∈ canonicalDB db' := hcanon d hd
            simp [hd, hd']
          · by_cases hd' : d ∈ canonicalDB db' <;> simp [hd, hd']
        have hih := ih htl
        simp only [absentCount]
        omega

/-! ## §2 The jump: component-1 strict decrease from the real steps -/

/-- **THE JUMP'S COMPONENT-1 DECREASE** (novelty supplied). Assembled from
the real ingredients only: pool membership of the inserted canonical
clause (premise, owner P2/P1-a), the real `perform` restoration
(`restorationKeepsLearned_of_perform_cfg` + `stepLearnBackjumpAssert_learned_mono`,
S4), the definitional successor shape (`stepLearnBackjumpAssert_learned_eq`
+ `learnBackjumpAssert_records_analysis`, P2), and the caller-visible
`JumpNovelty` classification case. -/
theorem absentCount_stepLearnBackjumpAssert_lt {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator}
    (hpool : Clause.canonicalClause an.learned ∈ clausePool orig)
    (hperf : p.perform cfg.branch cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an) (hn : JumpNovelty cfg.branch.learned an) :
    absentCount (stepLearnBackjumpAssert cfg p ev restored).branch.learned
        (clausePool orig)
      < absentCount cfg.branch.learned (clausePool orig) := by
  have hmem : an.learned ∈ restored.learned := by
    have h := perform_learned_mem_own hperf
    rwa [hm.1] at h
  refine absentCount_lt_of_mono_mem (pool := clausePool orig) ?_ hpool ?_ hn
  · intro c hc
    exact stepLearnBackjumpAssert_learned_mono
      (restorationKeepsLearned_of_perform_cfg hperf) c hc
  · exact learnBackjumpAssert_records_analysis hm hmem

/-! ## §3 The rank decrease: `PhaseLt` at the most significant component -/

/-- **JUMP STRICT RANK DECREASE (novelty variant)**: the jump lowers
`PhaseRank orig` lexicographically by lowering component 1 (the pool
countdown). `frontierCost` (component 2), frame mass and phase weight are
NOT used — see the file header, point (iii). -/
theorem phaseLt_stepLearnBackjumpAssert_of_novelty {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator}
    (hpool : Clause.canonicalClause an.learned ∈ clausePool orig)
    (hperf : p.perform cfg.branch cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an) (hn : JumpNovelty cfg.branch.learned an) :
    PhaseLt (PhaseRank orig (stepLearnBackjumpAssert cfg p ev restored))
      (PhaseRank orig cfg) :=
  Or.inl (absentCount_stepLearnBackjumpAssert_lt hpool hperf hm hn)

/-- **THE DELIVERABLE: `phaseLt_stepLearnBackjumpAssert`**. The repeated
case is EXCLUDED (never assumed) via `DatabaseUnfalsified` — the exact
named premise `not_jumpRepeated_of_unfalsified` demands (owner S4/S5) —
together with the norm-falsified recorded analysis (producer:
`recordedAnalysis_normFalsified`; owner `SchedulerFalsified`). No novelty
assumption reaches the caller. -/
theorem phaseLt_stepLearnBackjumpAssert {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator}
    (hpool : Clause.canonicalClause an.learned ∈ clausePool orig)
    (hperf : p.perform cfg.branch cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an)
    (hdb : DatabaseUnfalsified cfg.branch)
    (hfals : FalsifiedByTrailNorm cfg.branch an.learned) :
    PhaseLt (PhaseRank orig (stepLearnBackjumpAssert cfg p ev restored))
      (PhaseRank orig cfg) :=
  phaseLt_stepLearnBackjumpAssert_of_novelty hpool hperf hm
    (jumpNovelty_of_unfalsified hdb hfals)

/-- **REACHABLE-SITE WRAPPER** (the exact shape P5's arm-5 site has):
the falsification premise is PRODUCED, not assumed, by
`recordedAnalysis_normFalsified` from the reachable configuration and the
recorded evidence. Only `DatabaseUnfalsified` remains a named premise
(owner S4/S5). -/
theorem phaseLt_stepLearnBackjumpAssert_of_reachable {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator} {bs : BranchState leaf}
    (hpool : Clause.canonicalClause an.learned ∈ clausePool orig)
    (hperf : p.perform cfg.branch cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an)
    (hdb : DatabaseUnfalsified cfg.branch)
    (hb : cfg.branch = bs) (hreach : ReachableState leaf orig bs)
    (hcfg : SchedulerReachable cfg) (hconf : cfg.conflict = some ev)
    (hana : ev.analysis = some an) :
    PhaseLt (PhaseRank orig (stepLearnBackjumpAssert cfg p ev restored))
      (PhaseRank orig cfg) := by
  have hreach' : ReachableState leaf orig cfg.branch := by
    rw [hb]; exact hreach
  exact phaseLt_stepLearnBackjumpAssert hpool hperf hm hdb
    (recordedAnalysis_normFalsified (bs := cfg.branch) rfl hreach'
      hcfg hconf hana)

/-! ## §4 The order-insensitive (sorted-shape) jump decrease

PLAN limitation 1 (`hpool`): the P3/P4 rank's pool-membership premise is
replaced by the sorted-shape key `canonicalSorted orig`, whose pool
membership is unconditional (`canonicalSorted_mem_sortedClausePool`,
P1). The countdown follows from P3's generic `absentCountMap` lemmas at
the projection `f := canonicalSorted orig`; the only remaining premise
is sorted-shape novelty (owner P2), which is the sorted-vocabulary
restatement of `JumpNovelty`. -/

/-- Sorted-shape canonical database: P3's `canonicalDBMap` at the
    order-insensitive projection `canonicalSorted orig`. -/
def canonicalDBSorted (orig : List Domain) (db : List Clause) : List Clause :=
  canonicalDBMap (canonicalSorted orig) db

/-- Sorted-shape pool countdown over the order-insensitive pool. -/
def absentCountSorted (orig : List Domain) (db : List Clause) : Nat :=
  absentCountMap (canonicalSorted orig) db (sortedClausePool orig)

/-- Sorted-shape rank tuple: component 1 is the order-insensitive
    countdown; components 2-4 are P3's. -/
def PhaseRankSorted (orig : List Domain) (cfg : SchedulerConfig leaf) :
    Nat × Nat × Nat × Nat :=
  (absentCountSorted orig cfg.branch.learned,
   frontierCost cfg.frontier,
   Frame.mass cfg.branch.frame,
   statusWeight cfg.status)

/-- Sorted-shape novelty: the sorted canonical form of the recorded
    learned clause is absent from the sorted canonical database. -/
def SortedNovelty (orig : List Domain) (pre : List Clause)
    (an : ConflictAnalysis) : Prop :=
  canonicalSorted orig an.learned ∉ canonicalDBSorted orig pre

/-- **SORTED-CANONICAL EQUALITY TRANSFERS NORM FALSIFICATION (C1)**: when the
clause being proved falsified has pool-aligned literals, equal `canonicalSorted`
forms transfer norm-relaxed trail falsification. Order-insensitive
counterpart of `falsifiedByTrailNorm_of_canonicalClause_eq`; the refuted
sublist-ordering route is NOT used. -/
theorem falsifiedByTrailNorm_of_canonicalSorted_eq {leaf : Assignment → Bool}
    {bs : BranchState leaf} {orig : List Domain} {c d : Clause}
    (halign : ∀ q ∈ c, q.norm ∈ litPool orig)
    (heq : canonicalSorted orig c = canonicalSorted orig d)
    (h : FalsifiedByTrailNorm bs d) : FalsifiedByTrailNorm bs c := by
  intro q hq
  have hmem : q.norm ∈ canonicalSorted orig c :=
    norm_mem_canonicalSorted hq (halign q hq)
  rw [heq] at hmem
  have hmem' : q.norm ∈ d.map Literal.norm := by
    simpa using (List.mem_filter.mp hmem).2
  obtain ⟨q', hq', hq'n⟩ := List.mem_map.mp hmem'
  obtain ⟨e, he, helit⟩ := h q' hq'
  refine ⟨e, he, ?_⟩
  rw [helit]
  calc (q'.negate).norm = ((q'.norm).negate).norm :=
        (norm_negate_norm_local q').symm
    _ = ((q.norm).negate).norm := by rw [hq'n]
    _ = (q.negate).norm := norm_negate_norm_local q

/-- **THE C1 SORTED-NOVELTY PROVIDER (P4 `SortedNovelty`, discharged)**: on a
branch whose learned database is unfalsified and whose recorded analysis is
trail-falsified (producer: `recordedAnalysis_normFalsified`), the sorted key
of the learned clause is absent from the sorted canonical database — given
the DATABASE-side pool alignment (every stored clause's literals are in the
literal pool; the P2 clause-pool closure supplies it on real runs). No
`AnalysisDiffersFromConflict`, no sublist ordering, no novelty assumption. -/
theorem sortedNovelty_of_unfalsified {leaf : Assignment → Bool}
    {bs : BranchState leaf} {orig : List Domain} {an : ConflictAnalysis}
    (halignDB : ∀ c ∈ bs.learned, ∀ q ∈ c, q.norm ∈ litPool orig)
    (hdb : DatabaseUnfalsified bs) (hfals : FalsifiedByTrailNorm bs an.learned) :
    SortedNovelty orig bs.learned an := by
  intro hmem
  obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hmem
  exact hdb c hc
    (falsifiedByTrailNorm_of_canonicalSorted_eq (halignDB c hc) hceq hfals)

/-- **SORTED-SHAPE COMPONENT-1 DECREASE, NO POOL PREMISE.** The pool
    membership is a THEOREM (`canonicalSorted_mem_sortedClausePool`),
    not a hypothesis; the only countdown premise is sorted novelty. -/
theorem absentCountSorted_stepLearnBackjumpAssert_lt {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator}
    (hnov : SortedNovelty orig cfg.branch.learned an)
    (hperf : p.perform cfg.branch cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an) :
    absentCountSorted orig (stepLearnBackjumpAssert cfg p ev restored).branch.learned
      < absentCountSorted orig cfg.branch.learned := by
  have hmem : an.learned ∈ restored.learned := by
    have h := perform_learned_mem_own hperf
    rwa [hm.1] at h
  have hmono : ∀ d ∈ cfg.branch.learned,
      d ∈ (stepLearnBackjumpAssert cfg p ev restored).branch.learned := fun c hc =>
    stepLearnBackjumpAssert_learned_mono
      (restorationKeepsLearned_of_perform_cfg hperf) c hc
  have hnew : canonicalSorted orig an.learned ∈
      canonicalDBSorted orig (stepLearnBackjumpAssert cfg p ev restored).branch.learned := by
    rw [stepLearnBackjumpAssert_learned_eq]
    exact List.mem_map_of_mem (f := canonicalSorted orig)
      (List.mem_append.mpr (Or.inr hmem))
  exact absentCountMap_lt_of_mono_mem (f := canonicalSorted orig) hmono
    (canonicalSorted_mem_sortedClausePool orig an.learned) hnew hnov

/-- **SORTED-SHAPE JUMP DECREASE**: `PhaseLt` by component 1, with the
    previously-open pool-closure premise discharged internally. -/
theorem phaseLtSorted_stepLearnBackjumpAssert {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {props : List Propagator}
    (hnov : SortedNovelty orig cfg.branch.learned an)
    (hperf : p.perform cfg.branch cfg.original props = some restored)
    (hm : PlanMatchesAnalysis p an) :
    PhaseLt (PhaseRankSorted orig (stepLearnBackjumpAssert cfg p ev restored))
      (PhaseRankSorted orig cfg) :=
  Or.inl (absentCountSorted_stepLearnBackjumpAssert_lt hnov hperf hm)

/-! ## §5 Sorted-shape arm decreases (C2's per-phase obligations)

The P3 per-arm decreases re-proved at the order-insensitive component
`absentCountSorted`: database monotonicity instantiates `absentCountMap_mono`
at `f := canonicalSorted orig`, and the case analysis mirrors P3's (component
1 strict, else component 2 frontier, else component 3 mass). The jump case is
§4's `phaseLtSorted_stepLearnBackjumpAssert`. -/

/-- Sorted-shape component 1 is UNCHANGED by the counted analyze recorder
(the rank reads only learned/frontier/mass/status, all untouched). -/
theorem phaseRankSorted_analyzeConflictCounted_stutter (orig : List Domain)
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause) (n : Nat) :
    PhaseRankSorted orig (stepAnalyzeConflictCounted cfg c learned n)
      = PhaseRankSorted orig cfg := rfl

/-- **WELL-FOUNDEDNESS AT THE SORTED RANK**: the ordered step relation at
`PhaseRankSorted` is well-founded (an inverse image of P3's `phaseLt_wf`).
Any sorted-rank driver recursion can use this directly — no new
well-foundedness argument is needed. -/
theorem phaseRankSorted_wf {leaf : Assignment → Bool} (orig : List Domain) :
    WellFounded (fun a b : SchedulerConfig leaf =>
      PhaseLt (PhaseRankSorted orig a) (PhaseRankSorted orig b)) :=
  InvImage.wf (PhaseRankSorted orig) phaseLt_wf

/-- Sorted-shape component 1 never increases under a DB-changing
propagation (`stepPropagate` only PREPENDS clauses). -/
theorem absentCountSorted_propagate_le (orig : List Domain)
    (cfg : SchedulerConfig leaf) (d : ProductiveDeduction leaf cfg.branch) :
    absentCountSorted orig (stepPropagate cfg d).branch.learned ≤
      absentCountSorted orig cfg.branch.learned := by
  apply absentCountMap_mono
  intro c hc
  rw [stepPropagate_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

/-- Sorted-shape component 1 never increases under local exclusion
(`stepLocalExclude` prepends the payload). -/
theorem absentCountSorted_localExclude_le (orig : List Domain)
    (cfg : SchedulerConfig leaf) (learned : List Clause) (r : DeadRegion) :
    absentCountSorted orig (stepLocalExclude cfg learned r).branch.learned ≤
      absentCountSorted orig cfg.branch.learned := by
  apply absentCountMap_mono
  intro c hc
  rw [stepLocalExclude_learned_eq]
  exact List.mem_append.mpr (Or.inr hc)

/-- Sorted-shape PROPAGATE decrease (mirror of P3's `phaseRank_lt_propagate`). -/
theorem phaseRankSorted_lt_propagate (orig : List Domain)
    (cfg : SchedulerConfig leaf) (d : ProductiveDeduction leaf cfg.branch) :
    PhaseLt (PhaseRankSorted orig (stepPropagate cfg d)) (PhaseRankSorted orig cfg) := by
  have hrem := absentCountSorted_propagate_le orig cfg d
  rcases Nat.lt_or_eq_of_le hrem with hlt | heq
  · exact Or.inl hlt
  · refine Or.inr ⟨heq, ?_⟩
    have hcost : branchCost d.frame.1 ≤ branchCost cfg.branch.frame.1 :=
      filterFrame_cost_le d.filtered
    rcases Nat.lt_or_eq_of_le hcost with hclt | hceq
    · exact Or.inl (C3a.frontierCost_frame_lt hclt cfg.pending)
    · exact Or.inr ⟨C3a.frontierCost_frame_congr hceq cfg.pending,
        Or.inl d.decreases⟩

/-- Sorted-shape CONSUME decrease (mirror of P3's `phaseRank_lt_consume`:
the database is carried over, the frontier pops a frame). -/
theorem phaseRankSorted_lt_consume (orig : List Domain)
    {cfg next : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next) :
    PhaseLt (PhaseRankSorted orig next) (PhaseRankSorted orig cfg) := by
  have hlearn := stepConsume_learned h
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCountSorted orig next.branch.learned =
      absentCountSorted orig cfg.branch.learned
    rw [hlearn]
  · obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
    show frontierCost next.frontier < frontierCost cfg.frontier
    rw [SchedulerConfig.frontier, SchedulerConfig.frontier, hframe, hpend, hp]
    exact frontierCost_cons _ _

/-- Sorted-shape DECIDE decrease (mirror of P3's `phaseRank_lt_decide`). -/
theorem phaseRankSorted_lt_decide (orig : List Domain) (cfg : SchedulerConfig leaf)
    (v : Value) (vs : Domain) (doms : List Domain) (l : Literal)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    PhaseLt (PhaseRankSorted orig (stepDecide cfg v vs doms l))
      (PhaseRankSorted orig cfg) := by
  obtain ⟨chosen, hf⟩ := C3a.splitData_frame_eq hsplit
  have hold : cfg.frontier = (((v :: vs) :: doms, chosen) :: cfg.pending) := by
    simp only [SchedulerConfig.frontier, hf]
  have hnew : (stepDecide cfg v vs doms l).frontier
      = ((doms, chosen ++ [v]) :: (vs :: doms, chosen) :: cfg.pending) := by
    simp only [SchedulerConfig.frontier, stepDecide_pending, stepDecide_frame, hf]
  refine Or.inr ⟨rfl, Or.inl ?_⟩
  show frontierCost (stepDecide cfg v vs doms l).frontier < frontierCost cfg.frontier
  rw [hnew, hold]
  have hexp := frontierCost_expand v vs doms chosen cfg.pending
  omega

/-- Sorted-shape DECIDE-SKIP decrease (B1; the skip's frontier drop). -/
theorem phaseRankSorted_lt_decideSkip (orig : List Domain)
    (cfg : SchedulerConfig leaf) (v : Value) (vs : Domain) (doms : List Domain)
    (l : Literal)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    PhaseLt (PhaseRankSorted orig (stepDecideSkip cfg v doms))
      (PhaseRankSorted orig cfg) :=
  Or.inr ⟨rfl, Or.inl (P3.frontierCost_stepDecideSkip_lt hsplit)⟩

/-- Sorted-shape FALLBACK-then-consume composite (mirror of P5's
`fallback_then_consume_ranked` at the sorted component). -/
theorem fallback_then_consume_sorted (orig : List Domain)
    {cfg next : SchedulerConfig leaf} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    PhaseLt (PhaseRankSorted orig next) (PhaseRankSorted orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := stepConsume_learned h
  have hwork : frontierCost next.frontier
      < frontierCost (stepChronologicalFallback cfg r).frontier := by
    show frontierCost (next.branch.frame :: next.pending)
      < frontierCost ((stepChronologicalFallback cfg r).branch.frame
          :: (stepChronologicalFallback cfg r).pending)
    rw [hframe, hpend, hp]
    exact frontierCost_cons _ _
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCountSorted orig next.branch.learned =
      absentCountSorted orig cfg.branch.learned
    rw [hlearn, P3.stepChronologicalFallback_learned_eq]
  · show frontierCost next.frontier < frontierCost cfg.frontier
    rwa [show frontierCost (stepChronologicalFallback cfg r).frontier
        = frontierCost cfg.frontier from rfl] at hwork

/-- Sorted-shape localExclude-then-consume composite (mirror of P5's
`localExclude_then_consume_ranked` at the sorted component). -/
theorem localExclude_then_consume_sorted (orig : List Domain)
    {cfg next : SchedulerConfig leaf}
    {learned : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    PhaseLt (PhaseRankSorted orig next) (PhaseRankSorted orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := stepConsume_learned h
  have hrem1 := absentCountSorted_localExclude_le orig cfg learned r
  have hwork : frontierCost next.frontier
      < frontierCost (stepLocalExclude cfg learned r).frontier := by
    show frontierCost (next.branch.frame :: next.pending)
      < frontierCost ((stepLocalExclude cfg learned r).branch.frame
          :: (stepLocalExclude cfg learned r).pending)
    rw [hframe, hpend, hp]
    exact frontierCost_cons _ _
  rcases Nat.lt_or_eq_of_le hrem1 with hlt | heq
  · refine Or.inl ?_
    show absentCountSorted orig next.branch.learned
      < absentCountSorted orig cfg.branch.learned
    rw [hlearn]
    exact hlt
  · refine Or.inr ⟨?_, Or.inl ?_⟩
    · show absentCountSorted orig next.branch.learned =
        absentCountSorted orig cfg.branch.learned
      rw [hlearn]
      exact heq
    · show frontierCost next.frontier < frontierCost cfg.frontier
      rwa [show frontierCost (stepLocalExclude cfg learned r).frontier
          = frontierCost cfg.frontier from rfl] at hwork

/- The single consume-landing decomposition at the sorted rank lives in the
C2 assembly module (it needs `phaseNext`, which is outside P4's import cone). -/

end LeanFzn.Solver.UIP.P4
