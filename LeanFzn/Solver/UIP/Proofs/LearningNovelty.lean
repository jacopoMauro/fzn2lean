/-
File: LeanFzn/Solver/UIP/Proofs/LearningNovelty.lean

Purpose (PLAN.md task P2, prereq P1, S5):
  Decide whether each reachable successful jump adds a genuinely new
  canonical clause, and export an EXHAUSTIVE classification with its
  progress evidence — no novelty assumption from the caller.

  * `canonicalDB` — the canonical snapshot of a learned database
    (`Clause.canonicalClause` from P1's `Proofs/SchedulerVocabulary`).
  * `JumpNovelty` / `JumpRepeated` — the two classification cases of a
    recorded analysis `an` against the PRE-jump database.
  * `jumpNovelty_or_repeated` — PROVED unconditionally by decidable case
    analysis (`by_cases`, no `em` axiom, no caller premise): every jump
    analysis is classified, exhaustively.
  * `learnBackjumpAssert_records_analysis` / `jumpNovelty_progress` —
    PROVED from the real successor shape: the NEW case is genuine
    progress evidence against the PRE-jump database (the inserted
    canonical clause was not there), derived from the actual
    `learnGlobal` insertion chain (`plan_learned_mem_of_perform`), not
    assumed.
  * `not_jumpRepeated_of_unfalsified` — PROVED conditionally: the
    REPEATED case is refuted by the standard CDCL argument from the ONE
    named missing invariant `DatabaseUnfalsified` (see the docstring:
    no clause already in the database is trail-falsified) plus
    `FalsifiedByTrailNorm` (whose producer is `recordedAnalysis_normFalsified`,
    `Proofs/SchedulerFalsified.lean`).

HONESTY STATUS (task P2):
  * Exhaustive classification: PROVED (unconditional).
  * NEW-case progress: PROVED (unconditional, from the insertion shape).
  * REPEATED case: NOT reachable by any found witness — no `sorry`, no
    fabricated reachability; the unconditional exclusion is NOT proved
    because `DatabaseUnfalsified` is absent from `ReachableState`
    (`Proofs/BranchState.lean`) and `BranchState.WellFormed`
    (the `wf` field is `LearnedEntailed` only, no trail-satisfaction
    item). Owner to assign: S4/S5 successor-invariant extension
    (predicted successor of a BACKJUMP records DB satisfaction "at the
    moment of the last closure", not yet a field anywhere).
  * A failed proof attempt is not used as a counterexample: the repeated
    case is simply left undecided at the kernel level and excluded
    exactly when `DatabaseUnfalsified` is supplied.

Dependencies:
  - LeanFzn.Solver.UIP.Proofs.SchedulerVocabulary (P1): `Clause.canonicalClause`.
  - LeanFzn.Solver.UIP.Proofs.SchedulerFalsified: `FalsifiedByTrailNorm`,
    `recordedAnalysis_normFalsified`.
  - LeanFzn.Solver.UIP.Proofs.SchedulerStep (S5): `PlanMatchesAnalysis`,
    successor arm lemmas; `LeanFzn.Solver.UIP.SchedulerStep`: `stepLearnBackjumpAssert`.
  - LeanFzn.Solver.Propagation.BackjumpFrontier: `BackjumpPlan.perform` (`learnGlobal`).
  - LeanFzn.Solver.UIP.Proofs.SchedulerCoverage: `explainedClosure_learned_mono`.

DAG:
  Proofs.SchedulerVocabulary + Proofs.SchedulerFalsified + Proofs.SchedulerStep
    -> Proofs.LearningNovelty
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerFalsified
import LeanFzn.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Solver.UIP.Proofs.SchedulerVocabulary
import LeanFzn.Solver.UIP.Proofs.SyncVocabulary
import LeanFzn.Solver.Propagation.RestorationCertificate
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Canonical snapshot and the exhaustive classification -/

/-- Canonical snapshot of a learned database: every clause replaced by its
canonical form (P1's `Clause.canonicalClause`). Novelty and repetition are
decided against THIS image, never against raw list membership (raw
membership would be unsound under `Literal.norm` rewriting). -/
def canonicalDB (db : List Clause) : List Clause := db.map Clause.canonicalClause

/-- THE NEW CASE: the recorded analysis's canonical clause is absent from
the canonical form of the pre-jump database. This is `false` for a
re-learned (duplicate) clause. -/
def JumpNovelty (pre : List Clause) (an : ConflictAnalysis) : Prop :=
  Clause.canonicalClause an.learned ∉ canonicalDB pre

/-- THE REPEATED CASE: the recorded analysis's canonical clause already
occurs (canonically) in the pre-jump database. `JumpNovelty` and
`JumpRepeated` are exact complements. -/
def JumpRepeated (pre : List Clause) (an : ConflictAnalysis) : Prop :=
  Clause.canonicalClause an.learned ∈ canonicalDB pre

/-- **EXHAUSTIVE CLASSIFICATION, UNCONDITIONAL**: for every pre-jump
database and recorded analysis, the jump is either genuinely new or
repeated — proved by decidable case analysis, so no caller supplies a
novelty assumption and no classical axiom is invoked. -/
theorem jumpNovelty_or_repeated (pre : List Clause) (an : ConflictAnalysis) :
    JumpNovelty pre an ∨ JumpRepeated pre an := by
  by_cases h : Clause.canonicalClause an.learned ∈ canonicalDB pre
  · exact Or.inr h
  · exact Or.inl h

/-- Complementarity in the other direction (for consumers that case on the
classification). -/
theorem not_jumpRepeated_iff_jumpNovelty (pre : List Clause)
    (an : ConflictAnalysis) :
    ¬ JumpRepeated pre an ↔ JumpNovelty pre an :=
  Iff.rfl

/-- Canonical membership is preserved by raw membership — the insertion
direction the successor lemmas below consume. -/
theorem canonicalDB_mem_of_mem {db : List Clause} {c : Clause} (h : c ∈ db) :
    Clause.canonicalClause c ∈ canonicalDB db :=
  List.mem_map.mpr ⟨c, h, rfl⟩

/-! ## §2 The real insertion chain of a successful jump

`BackjumpPlan.perform` inserts `p.learned` via
`BackjumpPlan.execute (bs.learnGlobal p.learned)` (an unconditional cons,
NO dedupe), and `stepLearnBackjumpAssert` prepends the closure payload
`ev.learned`; the successor database is therefore
`ev.learned ++ restored.learned` and `p.learned ∈ restored.learned` survives
`execute` (`rfl`), `narrowFrame` (`rfl`) and the resumed closure
(`explainedClosure_learned_mono`). -/

/-- The successor database shape of the jump arm (definitional). -/
@[simp] theorem stepLearnBackjumpAssert_learned_eq {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).branch.learned
      = ev.learned ++ restored.learned := rfl

/-- The plan's learned clause survives `perform`'s `learnGlobal` insertion
into the restored branch: `p.learned ∈ restored.learned`. Proved from the
real `perform` shape (no monotonicity premise). -/
theorem plan_learned_mem_of_perform {leaf : Assignment → Bool}
    {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    {original : List Clause} {props : List Propagator}
    (h : p.perform bs orig original props = some s) :
    p.learned ∈ s.learned := by
  unfold BackjumpPlan.perform at h
  cases hr : p.restoreNarrow bs with
  | none =>
      rw [hr] at h
      cases h
  | some r =>
      rw [hr] at h
      simp only [Option.map_some, Option.some.injEq] at h
      subst h
      unfold BackjumpPlan.restoreNarrow at hr
      split at hr
      · cases hr
      · next g _ =>
          simp only [Option.some.injEq] at hr
          subst hr
          refine explainedClosure_learned_mono orig original props
            (syncAll orig ((p.execute (bs.learnGlobal p.learned)).narrowFrame g)) p.learned ?_
          rw [syncAll_learned]
          change p.learned ∈ (p.execute (bs.learnGlobal p.learned)).learned
          rw [BackjumpPlan.execute_learned]
          change p.learned ∈ p.learned :: bs.learned
          exact List.mem_cons_self ..

/-- The recorded analysis's clause is a canonical member of the jump
successor's database: the successor prepends `ev.learned` to
`restored.learned`, and `PlanMatchesAnalysis` identifies the plan's clause
with `an.learned`. This is the insertion-side half of the progress
evidence. -/
theorem learnBackjumpAssert_records_analysis {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis}
    (hm : PlanMatchesAnalysis p an) (hmem : an.learned ∈ restored.learned) :
    Clause.canonicalClause an.learned ∈
      canonicalDB (stepLearnBackjumpAssert cfg p ev restored).branch.learned :=
  canonicalDB_mem_of_mem (List.mem_append.mpr (Or.inr hmem))

/-- For a successful jump with recorded analysis `an`, the NEW case is
genuine progress evidence: the successor's canonical database contains a
clause absent from the pre-jump canonical database. Both halves are
unconditional (insertion from the real successor shape; novelty from the
caller-visible classification case, never assumed). -/
theorem jumpNovelty_progress {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis}
    (hm : PlanMatchesAnalysis p an) (hmem : an.learned ∈ restored.learned)
    (hn : JumpNovelty cfg.branch.learned an) :
    ∃ c ∈ canonicalDB (stepLearnBackjumpAssert cfg p ev restored).branch.learned,
      c ∉ canonicalDB cfg.branch.learned :=
  ⟨Clause.canonicalClause an.learned,
    learnBackjumpAssert_records_analysis hm hmem, hn⟩

/-- RECORDED-ANALYSIS VARIANT (no membership premise left to the caller):
on a successful jump through `PlanMatchesAnalysis`, the progress witness
for the NEW case follows from `perform`'s own insertion chain. -/
theorem jumpNovelty_progress_of_perform {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {p : BackjumpPlan leaf}
    {ev : ConflictEvidence} {restored : BranchState leaf}
    {an : ConflictAnalysis} {dom : List Domain} {original : List Clause}
    {props : List Propagator}
    (hm : PlanMatchesAnalysis p an)
    (hperf : p.perform cfg.branch dom original props = some restored)
    (hn : JumpNovelty cfg.branch.learned an) :
    ∃ c ∈ canonicalDB (stepLearnBackjumpAssert cfg p ev restored).branch.learned,
      c ∉ canonicalDB cfg.branch.learned :=
  jumpNovelty_progress hm (hm.1 ▸ plan_learned_mem_of_perform hperf) hn

/-! ## §3 The repeated case: exact missing invariant and conditional
exclusion

The standard CDCL argument: the freshly recorded clause is
trail-falsified (`recordedAnalysis_normFalsified`); if its canonical form
were already in the database, the OLD clause would be trail-falsified
too (canonical equality transfers falsification), contradicting the
database discipline "no stored clause is trail-falsified". That
discipline is NOT a field of `ReachableState` (`Proofs/BranchState.lean`)
or of `BranchState.WellFormed` (whose database item is `LearnedEntailed`
only) — so it is named here and the exclusion is exported CONDITIONALLY,
with the failed hypothesis precise. -/

/-- The named missing invariant: no clause already stored in the branch's
learned database is trail-falsified in the norm-relaxed sense. This is
the exact extra field the repeated-case exclusion needs; it is not
currently proved or assumed anywhere in the repository. Candidate owners:
S4/S5 successor-invariant extension (the closure saturation argument:
a stable BCP-closed state with a falsified stored clause would have
reported a conflict instead). -/
def DatabaseUnfalsified {leaf : Assignment → Bool}
    (bs : BranchState leaf) : Prop :=
  ∀ c ∈ bs.learned, ¬ FalsifiedByTrailNorm bs c

/-- Canonical equality transfers norm-relaxed trail falsification: if two
clauses have the same canonical form, a falsifier of one is a falsifier
of the other. Uses `norm_negate_norm` (negation commutes with
normalization). -/
theorem falsifiedByTrailNorm_of_canonicalClause_eq {leaf : Assignment → Bool}
    {bs : BranchState leaf} {c d : Clause}
    (heq : Clause.canonicalClause c = Clause.canonicalClause d)
    (h : FalsifiedByTrailNorm bs d) : FalsifiedByTrailNorm bs c := by
  intro q hq
  have hqn : q.norm ∈ d.canonicalClause := by
    rw [← heq]
    exact List.mem_map.mpr ⟨q, hq, rfl⟩
  obtain ⟨q', hq', hq'n⟩ := List.mem_map.mp hqn
  obtain ⟨e, he, helit⟩ := h q' hq'
  refine ⟨e, he, ?_⟩
  rw [helit]
  calc (q'.negate).norm = ((q'.norm).negate).norm :=
        (norm_negate_norm_local q').symm
    _ = ((q.norm).negate).norm := by rw [hq'n]
    _ = (q.negate).norm := norm_negate_norm_local q

/-- **REPEATED-CASE EXCLUSION (conditional, precise hypothesis)**: on a
pre-jump branch that carries `DatabaseUnfalsified` and whose recorded
analysis is trail-falsified (producer: `recordedAnalysis_normFalsified`),
the REPEATED case is impossible — the jump is genuinely new. -/
theorem not_jumpRepeated_of_unfalsified {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis}
    (hdb : DatabaseUnfalsified bs) (hfals : FalsifiedByTrailNorm bs an.learned) :
    ¬ JumpRepeated bs.learned an := by
  intro hrep
  obtain ⟨c, hc, hceq⟩ := List.mem_map.mp hrep
  exact hdb c hc (falsifiedByTrailNorm_of_canonicalClause_eq hceq hfals)

/-- **DISJUNCTION UNDER THE MISSING INVARIANT (the exact export once
S4/S5 supplies the field)**: with `DatabaseUnfalsified` and the produced
falsification, the classification collapses to the NEW case, so the
caller needs no novelty assumption — only the named invariant. -/
theorem jumpNovelty_of_unfalsified {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis}
    (hdb : DatabaseUnfalsified bs) (hfals : FalsifiedByTrailNorm bs an.learned) :
    JumpNovelty bs.learned an :=
  not_jumpRepeated_iff_jumpNovelty bs.learned an |>.mp
    (not_jumpRepeated_of_unfalsified hdb hfals)

/-! ## §4 The `hpool` producer shape: trail vocabulary and the exact
order-alignment residual

P4's `hpool : Clause.canonicalClause an.learned ∈ clausePool orig` reduces
(by P1's `canonicalClause_mem_clausePool_of_sublist`) to the sublist
`Clause.canonicalClause an.learned <+ litPool orig`. The literal half is
PROVED (`ofUIP_canonical_lits_mem` + the trail vocabulary below); the
ORDER half is irreducible from membership (P1's
`sublistsOf_reordering_witness`), since `sublistsOf` enumerates
order-preserving sublists of the pool's FIXED block order. -/

/-- The branch-level form of P1's `TrailVocabulary`: every trail literal
    of the branch normalizes into the input's literal pool. -/
def BranchTrailVocabulary {leaf : Assignment → Bool} (orig : List Domain)
    (bs : BranchState leaf) : Prop :=
  TrailVocabulary orig bs.trail

/-- The root configuration satisfies the vocabulary vacuously (empty
    trail): the invariant is non-vacuously inhabited for every input. -/
theorem branchTrailVocabulary_init {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    BranchTrailVocabulary orig
      (SchedulerConfig.init (leaf := leaf) orig original props).branch := by
  intro e he
  simp [SchedulerConfig.init, BranchState.init] at he

/-- ONE STEP, PROPAGATE ARM, PROVED: `narrowState` appends the entry
    `l.norm`, so the vocabulary is preserved as soon as the deduced
    literal is pooled. (The arm-level discharge of `hl` from
    `SchedulerReachable` is P1-c vocabulary, owner P2/S3.) -/
theorem stepPropagate_branchTrailVocabulary {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    {d : ProductiveDeduction leaf cfg.branch}
    (hv : BranchTrailVocabulary cfg.orig cfg.branch)
    (hl : d.literal.norm ∈ litPool cfg.orig) :
    BranchTrailVocabulary cfg.orig (stepPropagate cfg d).branch := by
  change TrailVocabulary cfg.orig (stepPropagate cfg d).branch.trail
  have hv' : TrailVocabulary cfg.orig cfg.branch.trail := hv
  refine syncSlot_trail_vocab (orig := cfg.orig) _ d.literal.atom.slot (P := litPool cfg.orig)
    (fun l hl => hl) ?_
  intro e he
  simp only [narrowState] at he
  rcases List.mem_append.mp he with h1 | h1
  · exact hv' e h1
  · rw [List.mem_singleton] at h1
    subst h1
    simpa [Literal.norm_idem] using hl

/-- ONE STEP, DECIDE ARM, PROVED: `BranchState.decide` appends the entry
    `l.norm`, so the vocabulary is preserved as soon as the decision
    literal is pooled. -/
theorem stepDecide_branchTrailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {v : Value}
    {vs : Domain} {doms : List Domain} {l : Literal}
    (hv : BranchTrailVocabulary orig cfg.branch)
    (hl : l.norm ∈ litPool orig) :
    BranchTrailVocabulary orig (stepDecide cfg v vs doms l).branch := by
  change TrailVocabulary orig (stepDecide cfg v vs doms l).branch.trail
  have hv' : TrailVocabulary orig cfg.branch.trail := hv
  intro e he
  simp only [stepDecide, BranchState.decide] at he
  rcases List.mem_append.mp he with h1 | h1
  · exact hv' e h1
  · rw [List.mem_singleton] at h1
    subst h1
    simpa [Literal.norm_idem] using hl

/-- THE EXACT IRREDUCIBLE RESIDUAL of P4's `hpool` (owner P4), named: the
    canonical clause must be an order-preserving sublist of the pool.
    This is strictly stronger than literal membership (kernel witness:
    `sublistsOf_reordering_witness`), so it cannot be produced by any
    vocabulary invariant; closing `hpool` genuinely requires re-keying
    the pool count by a `Perm`-insensitive membership (or sorting the
    canonical form into pool order) in `Proofs/SchedulerJumpProgress`
    and `Proofs/SchedulerRank`. -/
def AnalysisPoolAligned (orig : List Domain) (an : ConflictAnalysis) : Prop :=
  List.Sublist (Clause.canonicalClause an.learned) (litPool orig)

/-- The residual, when supplied, yields P4's `hpool` premise verbatim. -/
theorem hpool_of_aligned {orig : List Domain} {an : ConflictAnalysis}
    (h : AnalysisPoolAligned orig an) :
    Clause.canonicalClause an.learned ∈ clausePool orig :=
  canonicalClause_mem_clausePool_of_sublist h

end LeanFzn.Solver.UIP
