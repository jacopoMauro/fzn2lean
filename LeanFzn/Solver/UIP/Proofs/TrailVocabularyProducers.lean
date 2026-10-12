/-
File: LeanFzn/Solver/UIP/Proofs/TrailVocabularyProducers.lean
vocabulary producers; owner C1)

Purpose: produce `BranchTrailVocabulary` (LearningNovelty §4) at the
recorded-evidence sites of a supported run, from the landed arm laws and
the new C1 pool producers.

  * §1 the trail-UNCHANGED arm laws (`stepDecideSkip`, the counted
    analyze site, `stepLocalExclude`, `stepChronologicalFallback`):
    definitional projections of the landed branch equations.
  * §2 `stepDecide_splitLiteral_pooled`: the split literal of
    `splitData` is pooled, from `ReachableState.length_ok`/`full_fits`
    via `valueLiteral_norm_mem_litPool` (CanonicalTrailVocabulary:99).
  * §3 the substantive propagation ingredient
    `deduction_literal_pooled`: a selected deduction's literal is pooled
    — propagator-sourced events from `UnitEmissionVocabulary`, the
    DATABASE-sourced case from `DatabaseAligned` of the state's own
    learned database (the remaining literal of a learned clause is a
    literal of that clause; the landed scan facts give the shape). No
    free claim for the database case.
  * §4 closure/restoration trail facts:
    `explainedClosure_trailVocabulary` (the `Frame.mass` fuel induction
    mirroring `databaseAligned_explainedClosure`),
    `restoreLevel_trailVocabulary` (trail sublist),
    `restoreNarrow_trailVocabulary` (the jump's restored trail is the
    CHECKPOINT's trail plus the asserting entry — hence the checkpoint
    vocabulary is a real input).
  * §5 the run-level site-form producer
    `branchTrailVocabulary_supportedRun_evidenceSites`, as the
    `halignDB_of_supportedRun` sibling consumes it, plus the step law
    `stepTrailVocabulary_evidenceSites`.

HONESTY NOTE (the extra premise, why it is needed — see §5's docstring):
the requested premise set (vocabulary + branch reachability + checkpoint
trail vocabulary) does NOT suffice: the conflict-RECORDING arm of the
real dispatcher (`conflictStep` on a nonempty reported clause) records the
evidence of a configuration whose `conflict` field is `none`, so the
site-form induction hypothesis gives nothing about its branch (and
neither `ReachableState` — a semantic/level invariant — nor the
checkpoint list constrains literal forms). The only honest producers are
therefore (i) the forward-maintenance invariant — vocabulary at EVERY
state, whose jump/consume arms are the R2a/R1 canonical-resume residuals
— or (ii) the named recording-site premise `hrec` below, which states
exactly what the analyze arm consumes. This file provides the arm-table
law plus BOTH routes stated as premises; nothing is assumed about
universal conflict-state shapes.

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.TrailVocabularyProducers` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`
(coordinator).

## §6 — WHAT C2 STILL NEEDS (exact residual typing)

1. `hinhab_site` (per evidence site), in the shape the scan-stability
   ledger consumes:
   `∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ∃ a, FrameCovers cfg.branch.frame a`.
   It is NOT universally true: `not_reachableFrameInhabited_emptyDomain`
   (`Proofs/LearnedExplanation.lean:1033`) kernel-refutes the
   all-states/all-roots form at the empty-domain box `[[]]`. C2 must
   therefore classify each site: either the site's frame is inhabited
   (the premise above) or its head remaining domain is empty and the
   site goes through the PROVED local-exclusion route
   (`emptyFrame_byFrame_sound`, `DeadRegion.byFrame_sound`) — never
   through an assumed inhabitedness.
2. The `supportedPhasePremises`-style instantiation
   (`Proofs/SupportedCertifiedRun.lean` §1) needs, per field:
   * `halignDB` — `halignDB_of_supportedRun` with `hvocab` from
     `unitEmissionVocabulary_proved_of_thresholds` (needs
     `ThresholdsPooled`, `Proofs/EmissionVocabulary.lean` §2 — the
     refutable constraint-side pool residual) and the `htrail` slot from
     the site-form producer of this file;
   * `hdb` — `databaseUnfalsified_of_reachable_recorded` (ScanStability
     §4) consuming `hbr` and `hinhab_site` (1);
   * `hbr` — `supportedHbr_of_gates` (J1) / `hbr_of_reachPreserve`.
3. The forward-maintenance residual feeding (the alternative to `hrec`):
   the jump arm's restored trail (`restoreNarrow_trailVocabulary`
   consumes the CHECKPOINT trail vocabulary — landed in this file) and
   the consume arm's resumed trail (`resumePending_branchTrailVocabulary`
   landed, needs the pending-frame `PendingBacked` producer of
   `Proofs/PendingRun.lean`; `resumeSibling`'s retired entries need the
   checkpoint-side pool bridges).
-/

import LeanFzn.Solver.UIP.Proofs.EmissionVocabulary
import LeanFzn.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The trail-unchanged arm laws -/

/-- The redundant-pin skip changes only the frame: the branch trail is
the predecessor's, definitionally. -/
theorem stepDecideSkip_branchTrailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} (v : Value)
    (doms : List Domain) (hv : BranchTrailVocabulary orig cfg.branch) :
    BranchTrailVocabulary orig (stepDecideSkip cfg v doms).branch := by
  show TrailVocabulary orig cfg.branch.trail
  exact hv

/-- The counted analyze site leaves the branch unchanged
(`stepAnalyzeConflictCounted_branch`). -/
theorem stepAnalyzeConflictCounted_branchTrailVocabulary
    {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} (c : Clause) (learned : List Clause)
    (n : Nat) (hv : BranchTrailVocabulary orig cfg.branch) :
    BranchTrailVocabulary orig
      (stepAnalyzeConflictCounted cfg c learned n).branch := by
  rwa [stepAnalyzeConflictCounted_branch]

/-- Local exclusion changes only the learned database and the status: the
trail is the predecessor's. -/
theorem stepLocalExclude_branchTrailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} (learned : List Clause)
    (r : DeadRegion) (hv : BranchTrailVocabulary orig cfg.branch) :
    BranchTrailVocabulary orig (stepLocalExclude cfg learned r).branch := by
  show TrailVocabulary orig cfg.branch.trail
  exact hv

/-- The chronological fallback leaves the branch unchanged entirely. -/
theorem stepChronologicalFallback_branchTrailVocabulary
    {leaf : Assignment → Bool} {orig : List Domain}
    {cfg : SchedulerConfig leaf} (r : DeadRegion)
    (hv : BranchTrailVocabulary orig cfg.branch) :
    BranchTrailVocabulary orig (stepChronologicalFallback cfg r).branch := by
  show TrailVocabulary orig cfg.branch.trail
  exact hv

/-! ## §2 The split literal is pooled -/

/-- **THE SPLIT LITERAL PRODUCER**: the literal `splitData` pins at a
reachable branch is pooled. `splitData` reads the value at the branch's
own prefix length (`splitData_eq_some_iff`); `ReachableState.length_ok`
makes that index a real box slot and `full_fits` puts the value in the
original domain, so the `valueLiteral` bridge
(`CanonicalTrailVocabulary.valueLiteral_norm_mem_litPool`) applies. -/
theorem stepDecide_splitLiteral_pooled {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hreach : ReachableState leaf orig cfg.branch)
    (hs : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    l.norm ∈ litPool orig := by
  obtain ⟨hf, hl⟩ := splitData_eq_some_iff.mp hs
  have hs' : cfg.branch.frame.2.length < orig.length := by
    rw [← hreach.length_ok, fullDomains_length, hf]
    simp
  have hvfull : v ∈ (fullDomains cfg.branch.frame).getD
      cfg.branch.frame.2.length [] := by
    have h0 : (fullDomains cfg.branch.frame)[cfg.branch.frame.2.length]?
        = some (v :: vs) := by
      have hrem := fullDomains_remaining cfg.branch.frame 0
      rw [Nat.add_zero, hf] at hrem
      exact hrem
    rw [List.getD_eq_getElem?_getD, h0]
    exact List.mem_cons_self ..
  exact valueLiteral_norm_mem_litPool hs' (hreach.full_fits _ _ hvfull) hl

/-- The decision arm's trail vocabulary from the split data (composing
`stepDecide_branchTrailVocabulary` with §2). -/
theorem stepDecide_split_branchTrailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {v : Value} {vs : Domain} {doms : List Domain}
    (hreach : ReachableState leaf orig cfg.branch)
    (hs : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hv : BranchTrailVocabulary orig cfg.branch) :
    BranchTrailVocabulary orig (stepDecide cfg v vs doms l).branch :=
  stepDecide_branchTrailVocabulary hv
    (stepDecide_splitLiteral_pooled hreach hs)

/-! ## §3 The deduction literal is pooled -/

/-- **THE DEDUCTION-LITERAL PRODUCER.** A selected deduction's literal is
pooled. The event cases are the landed scan facts:

  * PROPAGATOR-sourced (`scanPropagators_implied_facts`): the emission
    vocabulary gives `l = q` with `q.norm ∈ litPool orig` — no database
    input;
  * DATABASE-sourced (`scanDatabase_implied_facts`): the event's literal
    is the single REMAINING literal of a learned clause `c ∈ bs.learned`
    (`clauseRemaining f c = [l]` is a filter of `c`), so the pool fact
    comes from `DatabaseAligned` of that database — a REAL premise (the
    `halignDB` chain of C1), not a free claim.

The database case is therefore NOT claimed for free: the caller threads
the alignment it has (in the supported run, `halignDB`'s own self-chain). -/
theorem deduction_literal_pooled {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {bs : BranchState leaf} {d : ProductiveDeduction leaf bs}
    (hvocab : UnitEmissionVocabulary orig props)
    (hdb : DatabaseAligned orig bs.learned)
    (hd : explainedDeduction original props bs = some d) :
    d.literal.norm ∈ litPool orig := by
  obtain ⟨c, lr, fl, hev, -, -⟩ := explainedDeduction_learned_shape hd
  rcases nextPruningEvent_implied_cases hev with hsrc | ⟨-, -, hprop⟩
  · obtain ⟨hmem, -, hrem⟩ := scanDatabase_implied_facts hsrc
    have hl : d.literal ∈ c := by
      have h1 : d.literal ∈ clauseRemaining bs.frame c := by
        rw [hrem]
        exact List.mem_singleton_self _
      exact (List.mem_filter.mp h1).1
    exact hdb c hmem d.literal hl
  · obtain ⟨p, hpm, r, hrun, hcl, -, -⟩ :=
      scanPropagators_implied_facts hprop
    obtain ⟨q, -, hlq, -, hqpool⟩ :=
      hvocab.1 p hpm (frameState bs.frame) d.literal r hrun
    rw [hlq]
    exact hqpool

/-! ## §4 Closure and restoration trail facts -/

/-- **CLOSURE TRAIL MAINTENANCE**: the explained closure keeps the trail
vocabulary (the same `Frame.mass` fuel induction as
`databaseAligned_explainedClosure`/`unitLearned_explainedClosure`). Each
`narrowState` step appends the pooled normalized deduction literal
(§3) and keeps the database aligned (`databaseAligned_deduction_learned`). -/
theorem explainedClosure_trailVocabulary {leaf : Assignment → Bool}
    (original : List Clause) (props : List Propagator) (bs : BranchState leaf)
    {orig : List Domain} (hvocab : UnitEmissionVocabulary orig props)
    (hdb : DatabaseAligned orig bs.learned)
    (hv : TrailVocabulary orig bs.trail) :
    TrailVocabulary orig (explainedClosure original props bs).trail := by
  suffices hmain : ∀ (fuel : Nat) (bs : BranchState leaf),
      Frame.mass bs.frame ≤ fuel → TrailVocabulary orig bs.trail →
      DatabaseAligned orig bs.learned →
      TrailVocabulary orig (explainedClosure original props bs).trail from
    hmain (Frame.mass bs.frame) bs (Nat.le_refl _) hv hdb
  intro fuel
  induction fuel with
  | zero =>
      intro bs hle hv hdb
      rw [explainedClosure]
      split
      · exact hv
      · rename_i d _
        exfalso
        have hdec := d.decreases
        omega
  | succ fuel ih =>
      intro bs hle hv hdb
      rw [explainedClosure]
      split
      · exact hv
      · rename_i d hd
        have hl := deduction_literal_pooled hvocab hdb hd
        have hpay := databaseAligned_deduction_learned hvocab hd
        have hv' : TrailVocabulary orig
            (narrowState bs d.frame d.literal d.reason d.learned).trail := by
          show TrailVocabulary orig (bs.trail ++
            [{ literal := d.literal.norm, level := bs.level,
               reason := some { clause := d.reason } }])
          exact trailVocabulary_append_entry hv (litPool_norm_closed hl)
        have hdb' : DatabaseAligned orig
            (narrowState bs d.frame d.literal d.reason d.learned).learned := by
          show DatabaseAligned orig (d.learned ++ bs.learned)
          exact databaseAligned_append hpay hdb
        refine ih (narrowState bs d.frame d.literal d.reason d.learned)
          ?_ hv' hdb'
        have hdec := d.decreases
        simp only [narrowState] at hdec ⊢
        omega

/-- **RESTORE-LEVEL TRAIL VOCABULARY**: `BranchState.restoreLevel` filters
the trail, so the vocabulary transfers along the sublist. -/
theorem restoreLevel_trailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} {k : Nat}
    (hv : TrailVocabulary orig bs.trail) :
    TrailVocabulary orig (bs.restoreLevel k).trail := by
  show TrailVocabulary orig (bs.trail.filter fun e => e.level ≤ k)
  intro e he
  exact hv e (List.mem_filter.mp he).1

/-- **THE JUMP'S RESTORED-TRAIL PRODUCER**: `BackjumpPlan.restoreNarrow`
restores the CHECKPOINT's trail (`p.execute`: `checkpoint.trail` plus the
single asserting entry) and narrows the frame only, so its trail
vocabulary needs the checkpoint's vocabulary and the asserting literal's
pooling. This is why `hcpTrail` (checkpoint trail vocabulary) is part of
the honest premise set. -/
theorem restoreNarrow_trailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {p : BackjumpPlan leaf} {bs s : BranchState leaf}
    (hcp : TrailVocabulary orig p.checkpoint.trail)
    (hass : p.asserting.norm ∈ litPool orig)
    (h : p.restoreNarrow bs = some s) :
    TrailVocabulary orig s.trail := by
  unfold BackjumpPlan.restoreNarrow at h
  split at h
  · cases h
  · rename_i g _
    cases h
    show TrailVocabulary orig (p.execute (bs.learnGlobal p.learned)).trail
    rw [BackjumpPlan.execute_trail]
    exact trailVocabulary_append_entry hcp (litPool_norm_closed hass)

/-- The full jump (`BackjumpPlan.perform`) trail vocabulary: restoreNarrow
followed by the closure (`explainedClosure_trailVocabulary`), with the
restored database aligned from the plan clause and the pre-jump database
(the `databaseAligned_perform` shape). -/
theorem perform_trailVocabulary {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {p : BackjumpPlan leaf} {bs restored : BranchState leaf}
    (hvocab : UnitEmissionVocabulary orig props)
    (hdb : DatabaseAligned orig bs.learned)
    (hplan : DatabaseAligned orig [p.learned])
    (hcp : TrailVocabulary orig p.checkpoint.trail)
    (hass : p.asserting.norm ∈ litPool orig)
    (hperf : p.perform bs original props = some restored) :
    TrailVocabulary orig restored.trail := by
  unfold BackjumpPlan.perform at hperf
  cases hr : p.restoreNarrow bs with
  | none =>
      simp only [hr, Option.map_none] at hperf
      cases hperf
  | some s =>
      simp only [hr, Option.map_some, Option.some.injEq] at hperf
      rw [← hperf]
      refine explainedClosure_trailVocabulary original props s hvocab ?_
        (restoreNarrow_trailVocabulary hcp hass hr)
      unfold BackjumpPlan.restoreNarrow at hr
      split at hr
      · cases hr
      · cases hr
        show DatabaseAligned orig (p.learned :: bs.learned)
        exact databaseAligned_append hplan hdb

/-! ## §5 The run-level site-form producer -/

/-- **THE ONE-STEP LAW** (the arm table of the real dispatcher): every
successor configuration's recorded-evidence site carries the trail
vocabulary, given the predecessor's site-form vocabulary and the
RECORDING-SITE premise `hrec` (see the file docstring: the recording arm
runs on a configuration with `conflict = none`, so its branch vocabulary
is not a site-form consequence). The analysis below shows every OTHER
arm's successor has `conflict = none` (cleared by its own landed
`step*_conflict` equation), so the arm table is complete and nothing
else is consumed here. -/
theorem stepTrailVocabulary_evidenceSites {leaf : Assignment → Bool}
    {orig : List Domain} {cfg cfg' : SchedulerConfig leaf}
    (htrail : ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
      BranchTrailVocabulary orig cfg.branch)
    (hrec : ∀ bs cs learned,
      terminalResult cfg.original cfg.props cfg.branch
          = .conflict bs cs learned →
        BranchTrailVocabulary orig cfg.branch)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    ∀ {ev : ConflictEvidence}, cfg'.conflict = some ev →
      BranchTrailVocabulary orig cfg'.branch := by
  -- `htrail` is the predecessor site-form input; the arm table below shows
  -- the only live successor site sits at an UNCHANGED branch (the recording
  -- arm), so `hrec` does all the work — Lean's unused-variable linter
  -- confirms `htrail` is not needed here (honesty note, file docstring).
  have _ : ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
      BranchTrailVocabulary orig cfg.branch := htrail
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1: recorded evidence resolved by `backjumpStep` (all arms clear)
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        intro ev' h
        rw [stepChronologicalFallback_conflict] at h
        cases h
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            intro ev' h
            rw [stepChronologicalFallback_conflict] at h
            cases h
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp]
                  at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                intro ev' h
                rw [stepLocalExclude_conflict] at h
                cases h
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                intro ev' h
                rw [stepLearnBackjumpAssert_conflict] at h
                cases h
  · -- ROUTE 2: dead branch consumed (`consumeStep` clears the evidence)
    rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none =>
        simp only [consumeStep, hcons] at hsucc
        cases hsucc
    | some next =>
        simp only [consumeStep, hcons] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        intro ev' h
        rw [stepConsume_conflict hcons] at h
        cases h
  · -- ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · -- propagation (clears the predecessor's none)
      rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      intro ev' h
      rw [stepPropagate_conflict, hconf] at h
      cases h
    · -- guarded stable dispatch
      rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hl : leafWitness leaf cfg with
      | some w =>
          simp only [hl, successor_sat] at hsucc
          cases hsucc
      | none =>
          cases hs : splitData cfg.branch.frame with
          | some p =>
              obtain ⟨l, v, vs, doms⟩ := p
              simp only [hl, hs] at hsucc
              split at hsucc
              · rw [successor_decide] at hsucc
                cases hsucc
                intro ev' h
                rw [stepDecideSkip_conflict, hconf] at h
                cases h
              · rw [successor_decide] at hsucc
                cases hsucc
                intro ev' h
                rw [stepDecide_conflict, hconf] at h
                cases h
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              intro ev' h
              rw [stepLocalExclude_conflict] at h
              cases h
    · -- recorded conflict dispatch
      rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          intro ev' h
          rw [stepLocalExclude_conflict] at h
          cases h
      | cons c0 rest =>
          intro ev' h
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            -- THE ONLY LIVE SITE: the branch is unchanged and the recording
            -- premise supplies its vocabulary
            rw [stepAnalyzeConflictCounted_branch]
            exact hrec bs (c0 :: rest) learned ht
    · -- the local-exclusion terminal result
      rw [hsj] at hsucc
      rw [successor_localExclude] at hsucc
      cases hsucc
      intro ev' h
      rw [stepLocalExclude_conflict] at h
      cases h

/-- **THE C1 RUN-LEVEL SITE-FORM PRODUCER** (the shape
`halignDB_of_supportedRun` / `databaseAlignedAndEvidence_of_supportedRun`
consume as their `htrail` slot): along a supported run, every
recorded-evidence configuration's branch carries the trail vocabulary.

Premises: the kit's emission vocabulary (`hvocab`), branch reachability
(`hbr`) and checkpoint trail vocabulary (`hcpTrail`) — the requested
inputs — PLUS the recording-site premise `hrec` (§5's honesty note: the
recording arm's branch is a `conflict = none` configuration, so the
stated set is insufficient; `hvocab`/`hbr`/`hcpTrail` are the inputs the
DOWNSTREAM producers need for that premise, and the canonical-resume
route is already landed as `resumePending_branchTrailVocabulary`). -/
theorem branchTrailVocabulary_supportedRun_evidenceSites
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hvocab : UnitEmissionVocabulary orig props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hcpTrail : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cp ∈ cfg.checkpoints →
        TrailVocabulary orig cp.trail)
    (hrec : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∀ (bs : BranchState leaf) (cs learned : List Clause),
          terminalResult cfg.original cfg.props cfg.branch = .conflict bs cs learned →
            BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          BranchTrailVocabulary orig cfg.branch := by
  -- `hvocab`/`hbr`/`hcpTrail` are the downstream inputs of the recording
  -- premise `hrec` (file docstring); they are not consumed by this theorem.
  have _ : UnitEmissionVocabulary orig props := hvocab
  have _ : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch := hbr
  have _ : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cp ∈ cfg.checkpoints →
        TrailVocabulary orig cp.trail := hcpTrail
  intro cfg hreach
  induction hreach with
  | init =>
      intro ev h
      simp [SchedulerConfig.init] at h
  | step hpre hsucc ih =>
      intro ev' h'
      exact stepTrailVocabulary_evidenceSites ih (hrec hpre) hsucc h'

/-! ## §7 C1 update (session 11, task C1 worker D): `hrec` DISCHARGED

The recording-site premise `hrec` of §5 is no longer needed on any completed
C1 path. Route (i) of the C1 task — the run-wide forward maintenance — is
implemented in the new module `Proofs/ExtendedPoolProducers.lean`
(owner C1):

  * `ExtendedPoolProducers.TrailInvWith` is the joint per-state invariant
    (branch vocabulary ∧ database alignment ∧ checkpoint-trail vocabulary ∧
    recorded-evidence payload alignment) at an arbitrary extended pool
    `litPoolWith extra orig`;
  * `ExtendedPoolProducers.trailInvWith_step` is the full dispatcher arm
    table (the recording arm's successor inherits the predecessor's branch
    vocabulary — that is exactly what the site-form induction of §5 could
    not see);
  * `ExtendedPoolProducers.trailInvWith_of_supportedRun` maintains it along
    the whole supported run, so
    `branchTrailVocabulary_evidenceSites_litPoolExt_of_supportedRun` and
    `branchTrailVocabulary_supportedRun_evidenceSites_allStates` state the
    §5 conclusion WITHOUT `hrec` (the `litPool`-keyed one from `hvocab`
    + branch reachability + box typing; the unit-route one at
    `litPoolExt orig dcs` from `hprops` + `hSupp` + the same two inputs).

The canonical-resume trail membership this file's §6 mentions is landed as
`ExtendedPoolProducers.resumePending_branchTrailVocabulary_at` (used by the
consume arm of the step law), and the resumed-site recorded-analysis
alignment as
`ExtendedPoolProducers.recordedAnalysis_learned_poolAligned_at_resumePending`.
The `PendingBacked` head input comes from
`PendingRun.pendingSideInv_of_premises` (run-level, unconditional). No
declaration of this file changed; the §5 law and its `hrec` premise are
retained as the honest site-form statement and as the historical record. -/

end LeanFzn.Solver.UIP
