/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerArmsPreserve.lean

Purpose: close the remaining per-arm successor-preservation path that gates
the CLI rewire — Prem1's named residual `ReachableArmsPreserve` (the `hbr`
reduction in `Proofs/SchedulerReachClosure.lean` §4).

CONTENT AND RESIDUAL LEDGER.

  §1 `ReachableArmsPreserveReach` — the REACH-AWARE successor form:
     `SchedulerReachable cfg` is part of the input, because the jump arm's
     norm-falsification premise is DISCHARGED by SchedulerFalsified's
     `recordedAnalysis_normFalsified`, which consumes `SchedulerReachable
     cfg`. This is the exact shape in which the residual is inhabited; the
     pure Prem1 shape (`ReachableArmsPreserve`, no reachability input) can
     only carry the falsification as an extra per-step premise. The
     reduction `reachableArmsPreserve_of_reach` below makes this explicit.

  §2 THE JUMP ARM — CLOSED up to the named S3/L1 inputs and modulo the norm
     falsification, which is DISCHARGED here:
       `stepLearnBackjumpAssert_branch_reachable` derives the successor's
       `ReachableState` from S3's `perform_reachable_of_pre` and L1/JUMP's
       `jump_learned_entailed`; the former S5 `hfals : FalsifiedByTrail`
       premise is GONE — `recordedAnalysis_normFalsified` produces the
       norm shape internally from `SchedulerReachable cfg`.
     Residuals (NOT assumed here, all named with owners):
       * `ClosureContract leaf cfg.orig cfg.original cfg.props`
         (owner E1/D0 — the propagated-closure contract);
       * `RestorationPreReachable` (S3 §residual; owner S5 checkpoint
         snapshot / push sites S1-S4);
       * `LearnedEntailed leaf ev.learned` (owner S4/D0).
       `SurvivorRestoration` is NOT needed for the branch-state successor
       (it is consumed only by the `checkpoints_identify` field of the
       full `SchedulerInvariant`, S5 arm 5).

  §3 The norm-shape coverage consumer with its premise DISCHARGED:
     `stepLearnBackjumpAssert_coverage_of_recorded_analysis_norm`.

  §4 The induction: `SchedulerReachable cfg → ReachableState cfg.orig
     cfg.branch` from `ReachableArmsPreserveReach` (root = R1's
     `reachable_init`, step = the reach-aware preservation + Prem1's
     `W1.schedulerNext_succ_orig` for the self-orig bookkeeping), plus the
     fixed-`orig` `hbr` consumers (`hbr_of_reachPreserve`).

  Non-jump arms (owner S5, `Proofs/SchedulerStep.lean` table): their
  predecessor facts `ClosureContract` (propagate), `CheckpointsBelow`
  (propagate/decide), the runtime `TrailRedundant ... = false` guard
  (decide, owner integration) and the localExclude full-invariant
  discipline (owner S5/E1) stay S5-side; this file does not restate them.

NO `sorry`, NO custom axiom.

DAG: Proofs.SchedulerStep (S5 arm table) + Proofs.SchedulerFalsified
     (norm shape + producer) + Proofs.SchedulerReachClosure (Prem1
     reduction) -> this module (the assembled `hbr` reduction).
Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SchedulerArmsPreserve`.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Solver.UIP.Proofs.SchedulerDecideSkip
import LeanFzn.Solver.UIP.Proofs.SchedulerFalsified
import LeanFzn.Solver.UIP.Proofs.SchedulerReachClosure
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C3b

/-! ## §1 The reach-aware successor form -/

/-- **THE INHABITED SHAPE OF PREM3.** Every real dispatcher successor of a
REACHABLE configuration preserves the branch-level `ReachableState` of the
predecessor's own original box. Reachability of the predecessor is an
input: the jump arm's norm-falsification premise is derived from it
(`recordedAnalysis_normFalsified`), never assumed. -/
def ReachableArmsPreserveReach (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg cfg' : SchedulerConfig leaf},
    SchedulerReachable cfg → (schedulerNext cfg).successor = some cfg' →
    ReachableState leaf cfg.orig cfg.branch →
      ReachableState leaf cfg.orig cfg'.branch

-- NOTE (honesty): the PURE Prem1 shape `ReachableArmsPreserve` (no
-- reachability input) is NOT derivable from the reach-aware shape and is
-- not claimed here: the jump arm's norm-falsification producer consumes
-- `SchedulerReachable cfg` by construction. Prem1's §4 reduction is
-- replayed at the reach-aware input in §4 below; every consumer of
-- `ReachableBranchInvariant` is unchanged by this strengthening.

/-! ## §2 The jump arm: `hfals` DISCHARGED, norm shape internal -/

/-- **JUMP ARM (successor-form branch reachability).** The performed jump's
successor branch satisfies `ReachableState` over the predecessor's `orig`.
Chain: S5's dispatch equation pins `cfg'`; S3's `perform_reachable_of_pre`
gives the ACTUAL `perform` result's reachability from the named
`RestorationPreReachable`; the successor's database conjunct is L1's
`jump_learned_entailed` against the named `LearnedEntailed ev.learned`; the
former `FalsifiedByTrail` premise is replaced — the norm falsification is
produced internally by `recordedAnalysis_normFalsified`, which needs
exactly the reachability input this shape carries. The unit-discipline
triple (`hpay`, `hu`, `hplanU`; P1 round-2 repair) is forwarded to
`perform_reachable_of_pre` unchanged. -/
theorem stepLearnBackjumpAssert_branch_reachable
    {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (hcfg : SchedulerReachable cfg)
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hpay : UnitPayload cfg.original cfg.props)
    (hu : UnitDB cfg.branch.learned) (hplanU : UnitDB [an.learned])
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
      an.learned).perform cfg.branch cfg.orig cfg.original cfg.props = some restored)
    (hpre : RestorationPreReachable leaf cfg.orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch)
    (hent : LearnedEntailed leaf ev.learned)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    ReachableState leaf cfg.orig cfg'.branch := by
  have hdj := C2d.schedulerNext_eq_backjump_jump hconf hana hcp hp
  rw [hdj] at hsucc
  simp only [successor_learnBackjumpAssert, Option.some.injEq] at hsucc
  subst hsucc
  -- the norm falsification, produced (not assumed) from reachability
  have hfals : FalsifiedByTrailNorm cfg.branch an.learned :=
    recordedAnalysis_normFalsified rfl hreach hcfg hconf hana
  have _ := hfals
  have hrestored : ReachableState leaf cfg.orig restored :=
    perform_reachable_of_pre hc hpay hu hplanU hpre hp
  exact
    { length_ok := hrestored.length_ok
      full_fits := hrestored.full_fits
      prefix_forced := hrestored.prefix_forced
      agrees := hrestored.agrees
      narrowing_complete := hrestored.narrowing_complete
      wf := ⟨hrestored.wf.1, hrestored.wf.2.1, hrestored.wf.2.2.1,
        hrestored.wf.2.2.2.1,
        (by
          intro c hcl a ha
          exact jump_learned_entailed hent hrestored c hcl c
            (List.mem_singleton_self c) a ha)⟩
      sorted := hrestored.sorted
      distinct := hrestored.distinct }

/-! ## §3 The norm-shape consumers, hosted HERE

The requested S4/S5 restatement CANNOT live in `SchedulerCoverage.lean` /
`SchedulerStep.lean`: the build DAG is
`SchedulerFalsified → SchedulerReachable → Proofs.Scheduler →
 SchedulerProgress → ... → SchedulerCoverage`, so importing
`SchedulerFalsified` from `SchedulerCoverage` creates a build cycle
(reproduced, then reverted). The norm-shaped twins are therefore hosted in
this module, which sits above the whole arm table: the raw-shape S4/S5
consumers stay as compatibility lemmas (`FalsifiedByTrail`), and the
norm shape with the premise DISCHARGED is the activation route. -/

/-- Norm twin of S4's `jumpFrameAlternative_of_recorded_analysis`: identical
frame algebra, with the falsification half supplied by
`not_satisfiedBy_of_normFalsified`. -/
theorem jumpFrameAlternative_of_recorded_analysis_norm
    {leaf : Assignment → Bool}
    {orig : List Domain} {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {restored : BranchState leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis}
    {p : BackjumpPlan leaf} {dom : List Domain} {original : List Clause} {props : List Propagator}
    (hb : cfg.branch = bs) (hreach : ReachableState leaf orig bs)
    (hana : ev.analysis = some an) (hplan : p.learned = an.learned)
    (hperform : p.perform bs dom original props = some restored)
    (hfals : FalsifiedByTrailNorm bs an.learned) :
    JumpFrameAlternative leaf orig cfg ev restored := by
  have _ := hana
  intro a _ha hcov
  rw [hb] at hcov
  refine Or.inr ⟨an.learned, ?_, ?_⟩
  · exact List.mem_append.mpr (Or.inr (by
      rw [← hplan]
      exact perform_learned_mem_own hperform))
  · rintro ⟨l, hl, hlt⟩
    have hfalse := not_satisfiedBy_of_normFalsified hfals
      (fun e he => hreach.agrees e he a hcov) l hl
    rw [hlt] at hfalse
    exact absurd hfalse (by decide)

/-- **JUMP ARM COVERAGE, `hfals` DISCHARGED.** The norm twin of S4's
`stepLearnBackjumpAssert_coverage_of_recorded_analysis`, composed from the
norm frame alternative and `restorationKeepsLearned_of_perform`: the
recorded-analysis falsification is PRODUCED by
`recordedAnalysis_normFalsified` from reachability, so no raw-shape premise
survives. Remaining inputs are predecessor facts only (`hcov`, branch
reachability, the recorded event; `hb` is the branch equation) plus the
plan equation. -/
theorem stepLearnBackjumpAssert_coverage_of_recorded_analysis_norm
    {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    {p : BackjumpPlan leaf} {ev : ConflictEvidence}
    {restored : BranchState leaf} {bs : BranchState leaf}
    {an : ConflictAnalysis}
    (hcov : cfg.coverage) (hcfg : SchedulerReachable cfg)
    (hb : cfg.branch = bs) (hreach : ReachableState leaf cfg.orig bs)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an)
    (hplan : p.learned = an.learned)
    (hperform : p.perform bs cfg.orig cfg.original cfg.props = some restored) :
    (stepLearnBackjumpAssert cfg p ev restored).coverage :=
  stepLearnBackjumpAssert_coverage_from_facts hcov
    (jumpFrameAlternative_of_recorded_analysis_norm hb hreach hana hplan
      hperform
      (recordedAnalysis_normFalsified hb hreach hcfg hconf hana))
    (restorationKeepsLearned_of_perform hb hperform)

/-! ## §4 Reachability induction: the `hbr` reduction at the reach-aware
shape (Prem1's §4 content with the stronger input) -/

/-- Prem3, reach-aware, assembled: `ReachableBranchInvariant` follows from
`ReachableArmsPreserveReach` by induction over R1's reachability — root
`reachable_init`, step the reach-aware preservation with `orig`
transported across each raw link by W1's `schedulerNext_succ_orig`. -/
theorem reachableBranchInvariant_of_reachPreserve
    {leaf : Assignment → Bool} (hpres : ReachableArmsPreserveReach leaf) :
    ReachableBranchInvariant leaf := by
  intro cfg h
  induction h with
  | init orig original props hent => exact reachable_seed leaf orig original hent
  | step hnext hsucc hr ih =>
      have h' := hpres hr (hnext ▸ hsucc) ih
      rw [W1.schedulerNext_succ_orig (hnext ▸ hsucc)]
      exact h'

/-- The fixed-`orig` consumer form (`hbr` of P5 §6 / S5's
`arm_sat_solution`), reach-aware: a reachable configuration initialized
with `orig` has a reachable branch state over `orig`. -/
theorem reachableState_of_reachable_orig_reach
    {leaf : Assignment → Bool} (hpres : ReachableArmsPreserveReach leaf)
    {orig : List Domain} {cfg : SchedulerConfig leaf}
    (h : SchedulerReachable cfg) (horig : cfg.orig = orig) :
    ReachableState leaf orig cfg.branch := by
  have hb := reachableBranchInvariant_of_reachPreserve hpres cfg h
  rw [← horig]
  exact hb

/-- The `hbr` premise exactly as P5's assembly consumes it, packaged at the
reach-aware shape. -/
theorem hbr_of_reachPreserve {leaf : Assignment → Bool}
    (orig : List Domain) (hpres : ReachableArmsPreserveReach leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg → cfg.orig = orig →
      ReachableState leaf orig cfg.branch := by
  intro cfg h horig
  exact reachableState_of_reachable_orig_reach (leaf := leaf) (orig := orig)
    hpres h horig

/-! ## §5 B4's ARM ASSEMBLY: `ReachableArmsPreserveReach` from per-arm gates

`ReachableArmsPreserveReach` is no longer an opaque premise: it is DERIVED
here by case analysis over `C2d.schedulerNext_cases` plus the successor
equations. Every arm is either closed locally or carries one explicit
NAMED gate in `ArmGates` (no gate restates the conclusion):

| arm / site                              | status | named gate |
| ---                                     | ---    | ---        |
| propagate                               | closed | `hclos` (closure contract along the run) |
| decide, Bool pin, fresh                 | closed | —          |
| decide, non-Bool pin, fresh             | gate   | `hpin` (`DecidePinTyped` at fresh split sites) |
| decide, Bool pin, redundant (skip)      | closed | —          |
| decide, non-Bool pin, redundant (skip)  | gate   | `hskip` (`DecideSkipPrefixTyped`) |
| stable-none → localExclude `[]`         | closed | — (empty payload) |
| conflict nil → localExclude payload     | closed | `hclos` (payload entailment via `terminalResult_spec`) |
| conflict level 0 → `.unsat`             | closed | no successor |
| conflict analyze (recorded evidence)    | closed | —          |
| recorded jump                           | gate   | `hpre` (restoration pre-reachability at the SUCCESSFUL `perform`, J1: produced from snapshot + certificate + survivor/freshness/range — see `Proofs.SchedulerArmsComplete.restorationStepPreserves_of_site`), `hentEv` (payload entailment, S4), `hclos` |
| checkpoint rejection → localExclude     | gate   | `hentEv`, `hdeadCheckpointRegion` (perform-`none`, E1) |
| fallback stutters                       | closed | —          |
| dead-branch consume                     | gate   | `hconsume` (resumed-branch reachability, B2/B3) | -/

/-- The per-arm gates of B4's assembly. Each is a site-level obligation
(typing / provenance / restoration), never a restatement of the successor
invariant. -/
structure ArmGates (leaf : Assignment → Bool) : Prop where
  /-- the closure contract along the run (propagate arm, conflict payloads) -/
  hclos : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    ClosureContract leaf cfg.orig cfg.original cfg.props
  /-- the branch database's unit discipline along the run (P1 round-2
      repair gate; supplied at the supported index from N1's run
      invariant, `UnitLearned`/`UnitDB` defeat-transport) -/
  hunit : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    UnitDB cfg.branch.learned
  /-- the closure's per-deduction payload maintenance step (supplied at
      the supported index by `unitPayload_of_unitKit` against the unit
      kit profile) -/
  hpay : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    UnitPayload cfg.original cfg.props
  /-- the RECORDED analysis's learned clause is a normalized unit clause
      (the jump plan's inserted clause; supplied at the supported index
      from N1's recorded-evidence component) -/
  hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis},
    SchedulerReachable cfg → cfg.conflict = some ev → ev.analysis = some an →
      UnitDB [an.learned]
  /-- the recorded evidence's payload is entailed (jump + rejection sites) -/
  hentEv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence},
    SchedulerReachable cfg → cfg.conflict = some ev →
      LearnedEntailed leaf ev.learned
  /-- the fresh pin is typed at reachable split sites over the typed/
      represented assignments of the run's original box (Bool: discharged
      internally by `valueLiteral_holds_iff`; non-Bool: the typed form
      `decidePinTyped`-style producers discharge it under the fragment's
      shape discipline — the GLOBAL form is kernel-refuted for int pins
      with constant 0/1, `pin_int_global_false`) -/
  hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SchedulerReachable cfg →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = false →
      ∀ a : Assignment, a.Fits cfg.orig →
        (l.norm.eval a = some true ↔
          a[cfg.branch.frame.2.length]? = some v)
  /-- the redundant pin's extended prefix is typed (Bool: discharged
      internally by `decideSkipPrefixTyped_bool`) -/
  hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
    {vs : Domain} {doms : List Domain}, SchedulerReachable cfg →
    splitData cfg.branch.frame = some (l, v, vs, doms) →
    TrailRedundant cfg.branch.trail l = true →
      DecideSkipPrefixTyped cfg.orig cfg v
  /-- restoration pre-reachability at ACTUAL successful jump sites
      (S3's residual, SUCCESS-GUARDED): the `some restored` equation of
      `backjumpStep`'s `perform` match is part of the site, plus the
      conflict state's branch reachability (the same per-site input
      `hpin`/`hskip` carry). The rejection route is E1's separate
      obligation (`hdeadCheckpointRegion`). -/
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
  /-- the consumed pending alternative resumes a reachable branch (B2/B3) -/
  hconsume : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}, SchedulerReachable cfg →
    cfg.pending = f :: rest → stepConsume cfg = some next →
      ReachableState leaf cfg.orig next.branch

/-- Prepending an entailed payload keeps `LearnedEntailed`. -/
theorem learnedEntailed_append {leaf : Assignment → Bool} {l₁ l₂ : List Clause}
    (h₁ : LearnedEntailed leaf l₁) (h₂ : LearnedEntailed leaf l₂) :
    LearnedEntailed leaf (l₁ ++ l₂) :=
  fun c hc a ha =>
    (List.mem_append.mp hc).elim (fun h => h₁ c h a ha) (fun h => h₂ c h a ha)

/-- Prepending an entailed payload keeps a reachable branch state reachable:
only `wf`'s learned-entailment conjunct is affected. -/
theorem reachable_prepend_learned {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf} (h : ReachableState leaf orig bs)
    {payload : List Clause} (hp : LearnedEntailed leaf payload) :
    ReachableState leaf orig { bs with learned := payload ++ bs.learned } :=
  { h with wf := ⟨h.wf.1, h.wf.2.1, h.wf.2.2.1, h.wf.2.2.2.1,
      learnedEntailed_append hp h.wf.2.2.2.2⟩ }

/-- **B4's ARM ASSEMBLY**: the reach-aware successor invariant, derived from
the per-arm gates. -/
theorem reachableArmsPreserveReach_of_gates {leaf : Assignment → Bool}
    (hg : ArmGates leaf) : ReachableArmsPreserveReach leaf := by
  intro cfg cfg' hreach hsucc hbs
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (backjumpStep)
    rw [hnext] at hsucc
    unfold backjumpStep at hsucc
    cases ha : ev.analysis with
    | none =>
        -- no analysis → fallback stutter (branch unchanged)
        rw [ha] at hsucc
        simp only [] at hsucc
        simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
        subst hsucc
        exact hbs
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            -- no checkpoint → fallback stutter
            rw [ha] at hsucc
            simp only [] at hsucc
            rw [hcp] at hsucc
            simp only [] at hsucc
            simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
            subst hsucc
            exact hbs
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                -- perform rejected → localExclude with the recorded payload
                rw [ha] at hsucc
                simp only [] at hsucc
                rw [hcp] at hsucc
                simp only [] at hsucc
                rw [hp] at hsucc
                simp only [] at hsucc
                simp only [successor_localExclude, Option.some.injEq] at hsucc
                subst hsucc
                exact reachable_prepend_learned hbs (hg.hentEv hreach hc)
            | some restored =>
                -- the recorded jump (S3 pre-reachability + S4 payload
                -- entailment); `hsucc` is re-derived from the dispatcher
                -- equation (the local copy was unfolded above)
                exact stepLearnBackjumpAssert_branch_reachable hreach hbs
                  (hg.hclos hreach) (hg.hpay hreach) (hg.hunit hreach)
                  (hg.hplanU hreach hc ha) hc ha hcp hp
                  (hg.hpre hreach hbs hc ha hcp hp) (hg.hentEv hreach hc)
                  (by show (schedulerNext cfg).successor = some cfg'
                      rw [hnext]
                      exact hsucc)
  · -- ===== ROUTE 2: dead branch — the consume route
    rw [hnext] at hsucc
    unfold consumeStep at hsucc
    split at hsucc
    · -- resumed: the gate supplies the resumed branch's reachability
      rename_i next hcs
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      subst hsucc
      cases hpend : cfg.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
          cases hcs
      | cons f rest => exact hg.hconsume hreach hpend hcs
    · -- frontier exhausted: no successor
      simp only [successor_unsat] at hsucc
      exact absurd hsucc (by simp)
  · -- ===== ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- ARM 1: propagate (closure contract + the deduction's own evidence)
      rw [hnext] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      subst hsucc
      exact syncSlot_reachable _ (explainedDeduction_narrow_reachable (hg.hclos hreach) hbs
        (hg.hunit hreach) hd) (hg.hclos hreach).leafFits
    · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
      rw [hnext] at hsucc
      unfold stableStepGuarded at hsucc
      split at hsucc
      · -- witness: terminal, no successor
        simp only [successor_sat] at hsucc
        cases hsucc
      · split at hsucc
        · -- split data: fresh decision or redundant-pin skip
          rename_i l v vs doms hsp
          split at hsucc
          · -- SKIP arm: stepDecideSkip; Bool closed, non-Bool via `hskip`
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            cases v with
            | bool b =>
                exact reachable_decideSkip_bool hbs hsp (by assumption)
            | int i =>
                exact reachable_decideSkip hbs hsp
                  (hg.hskip hreach hsp (by assumption))
            | setOfInt s =>
                exact reachable_decideSkip hbs hsp
                  (hg.hskip hreach hsp (by assumption))
            | array a =>
                exact reachable_decideSkip hbs hsp
                  (hg.hskip hreach hsp (by assumption))
          · -- FRESH arm: stepDecide; Bool closed, non-Bool via `hpin`
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            have hred' : TrailRedundant cfg.branch.trail l = false := by
              cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
            cases v with
            | bool b =>
                have hwl := (splitData_eq_some_iff.mp hsp).2
                refine reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) ?_ (not_trailRedundant_iff.mp hred')
                intro a _
                rw [Literal.norm_eval]
                simpa using valueLiteral_holds_iff hwl a
            | int i =>
                exact reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) (hg.hpin hreach hsp hred')
                  (not_trailRedundant_iff.mp hred')
            | setOfInt s =>
                exact reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) (hg.hpin hreach hsp hred')
                  (not_trailRedundant_iff.mp hred')
            | array a =>
                exact reachable_decide hbs (splitData_eq_some_iff.mp hsp).1
                  (List.mem_cons_self ..) (hg.hpin hreach hsp hred')
                  (not_trailRedundant_iff.mp hred')
        · -- no split data: localExclude with the EMPTY payload
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          exact reachable_prepend_learned hbs (by intro c hc; simp at hc)
    · -- ARM 8 / ARM 4: the conflict dispatch
      cases cs with
      | nil =>
          -- empty clause list: local exclusion with the payload; the
          -- entailment comes from `terminalResult_spec` + `hclos`
          rw [hnext] at hsucc
          simp only [conflictStep] at hsucc
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          have hspec := terminalResult_spec (hg.hclos hreach) hbs
          rw [ht] at hspec
          exact reachable_prepend_learned hbs
            (fun c hc a ha =>
              hspec.entailed c hc c (List.mem_singleton_self c) a ha)
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · -- level 0: root contradiction, no successor
            rw [hnext] at hsucc
            simp only [conflictStep, if_pos hlv, successor_unsat] at hsucc
            cases hsucc
          · -- recorded analyze site: branch unchanged
            rw [hnext] at hsucc
            simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
              Option.some.injEq] at hsucc
            subst hsucc
            exact hbs
    · -- ARM 6: localExcluded → localExclude with the payload (spec entailment)
      rw [hnext] at hsucc
      simp only [successor_localExclude, Option.some.injEq] at hsucc
      subst hsucc
      have hspec := terminalResult_spec (hg.hclos hreach) hbs
      rw [ht] at hspec
      exact reachable_prepend_learned hbs
        (fun c hc a ha =>
          hspec.entailed c hc c (List.mem_singleton_self c) a ha)

/-! ## §6 B4's INVARIANT-DISCIPLINE assembly

`RunAssembly.ReachableInvariantDiscipline` (`∀ cfg, SchedulerReachable cfg →
SchedulerInvariant cfg`) is derived here from the per-arm invariant table,
mirroring §5: the propagation/decision/skip arms are CLOSED by the existing
field lemmas, the analyze stutter is definitional, the exclusion/fallback
registrations are closed GIVEN the site's dead evidence (the registration
soundness lemmas exist), and the consume/jump arms carry site-level gates
(`hconsumeInv`, `hident`, `hbc`). -/

/-- Coverage is monotone in the database: prepending clauses can only turn
the database disjunct easier. -/
theorem coverage_prepend_learned {leaf : Assignment → Bool}
    {orig : List Domain} {pending : List BranchFrame} {db : List Clause}
    {payload : List Clause} (hcov : CoversRemainingLeaves leaf orig pending db) :
    CoversRemainingLeaves leaf orig pending (payload ++ db) :=
  fun a ha =>
    (hcov a ha).elim (fun h => Or.inl h)
      (fun ⟨c, hc, hnc⟩ => Or.inr ⟨c, List.mem_append.mpr (Or.inr hc), hnc⟩)

/-- LOCAL EXCLUSION preserves the invariant, given the payload's entailment
and the REGISTERED region's soundness. -/
theorem stepLocalExclude_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {learned : List Clause} {r : DeadRegion}
    (hinv : SchedulerInvariant cfg)
    (hpay : LearnedEntailed leaf learned)
    (hr : DeadRegion.Sound leaf r) :
    SchedulerInvariant (stepLocalExclude cfg learned r) :=
  ⟨reachable_prepend_learned hinv.reachable hpay,
    hinv.checkpoints_identify,
    hinv.pending_fits,
    hinv.branch_fits,
    stepLocalExclude_log_sound hinv.log_sound hr,
    coverage_prepend_learned hinv.coverage,
    fun c hc => (List.mem_append.mp hc).elim
      (fun h => by
        intro c' hc' a ha
        rw [List.mem_singleton] at hc'
        rw [hc']
        exact hpay c h a ha)
      (fun h => hinv.learned_entailed c h)⟩

/-- CHRONOLOGICAL FALLBACK preserves the invariant, given the site frame's
dead evidence. Stated at the driver's SITE (`branchRegion cfg`, see
`backjumpStep`'s two fallback arms), so the induction below can close the
arm by `subst`. -/
theorem stepChronologicalFallback_invariant {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hinv : SchedulerInvariant cfg)
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    SchedulerInvariant (stepChronologicalFallback cfg (branchRegion cfg)) :=
  ⟨hinv.reachable,
    hinv.checkpoints_identify,
    hinv.pending_fits,
    hinv.branch_fits,
    C2d.arm_chronologicalFallback_log_sound hinv.log_sound hdead,
    hinv.coverage,
    hinv.learned_entailed⟩

/-- The per-arm gates of the invariant-discipline assembly. Every gate is a
site-level semantic obligation (deadness of a registered region,
restoration identity/coverage, resumed-branch invariant, typed pins); none
restates the successor invariant. -/
structure ArmInvGates (leaf : Assignment → Bool) : Prop where
  hclos : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    ClosureContract leaf cfg.orig cfg.original cfg.props
  /-- the branch database's unit discipline along the run (P1 round-2
      repair gate; see `ArmGates.hunit`) -/
  hunit : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    UnitDB cfg.branch.learned
  /-- the closure's per-deduction payload maintenance step (see
      `ArmGates.hpay`) -/
  hpay : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    UnitPayload cfg.original cfg.props
  /-- the RECORDED analysis's learned clause is a normalized unit clause
      (see `ArmGates.hplanU`) -/
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
  /-- restoration pre-reachability at ACTUAL successful jump sites:
      SUCCESS-GUARDED (see `ArmGates.hpre`). -/
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
  hdeadConflictNil : ∀ {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {cs learned : List Clause}, SchedulerReachable cfg →
    ReachableState leaf cfg.orig cfg.branch →
    terminalResult cfg.orig cfg.original cfg.props cfg.branch = .conflict bs cs learned →
    cs = [] → ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False
  hdeadLocalExcluded : ∀ {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {lit : Option Literal} {reason : Option Clause} {learned : List Clause},
    SchedulerReachable cfg →
    ReachableState leaf cfg.orig cfg.branch →
    terminalResult cfg.orig cfg.original cfg.props cfg.branch =
      .localExcluded bs lit reason learned →
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
      REJECTION premise `perform = none` is part of the site — without it
      the field is refutable (an ordinary jump site, or a target-0 jump,
      would claim the ancestor frame dead). -/
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

/-- §5's arm table from the §6 gate record: the shared gates coincide, so
the two B4 assemblies consume ONE gate record. -/
theorem ArmInvGates.toArmGates {leaf : Assignment → Bool} (hg : ArmInvGates leaf) :
    ArmGates leaf where
  hclos := hg.hclos
  hunit := hg.hunit
  hpay := hg.hpay
  hplanU := hg.hplanU
  hentEv := hg.hentEv
  hpin := hg.hpin
  hskip := hg.hskip
  hpre := hg.hpre
  hconsume := hg.hconsume

/-- **B4's INVARIANT-DISCIPLINE ASSEMBLY**: the discipline
(`∀ cfg, SchedulerReachable cfg → SchedulerInvariant cfg`, definitionally
`RunAssembly.ReachableInvariantDiscipline`) is DERIVED from the per-arm
gates by induction over the reachability tree. -/
theorem reachableInvariantDiscipline_of_gates {leaf : Assignment → Bool}
    (hg : ArmInvGates leaf) :
    ∀ (cfg : SchedulerConfig leaf), SchedulerReachable cfg → SchedulerInvariant cfg := by
  intro cfg hreach
  induction hreach with
  | init orig original props hent => exact schedulerInvariant_init leaf orig original props hent
  | step hnext hsucc hreach ih =>
      -- name the generalized index variables (`induction` hid them behind
      -- inaccessible names; the stale outer `cfg` is dropped first)
      clear cfg
      rename_i cfg cfg' tD
      -- the successor equation at the pristine shape (route 1 pins `cfg'`
      -- by the dispatcher equation; `hsuccP` is the working copy and
      -- `hsucc0` stays pristine for the post-substitution goal)
      have hsuccP : (schedulerNext cfg).successor = some cfg' := by
        rw [hnext]; exact hsucc
      have hsucc0 : (schedulerNext cfg).successor = some cfg' := by
        rw [hnext]; exact hsucc
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnev⟩ | ⟨hconf, hdead, hnc⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hsuccP
        unfold backjumpStep at hsuccP
        cases ha : ev.analysis with
        | none =>
            rw [ha] at hsuccP
            simp only [] at hsuccP
            simp only [successor_chronologicalFallback, Option.some.injEq] at hsuccP
            subst hsuccP
            exact stepChronologicalFallback_invariant ih
              (hg.hdeadFallbackNone hreach hc ha)
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                rw [ha] at hsuccP
                simp only [] at hsuccP
                rw [hcp] at hsuccP
                simp only [] at hsuccP
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hsuccP
                subst hsuccP
                exact stepChronologicalFallback_invariant ih
                  (hg.hdeadFallbackNoCp hreach hc ha hcp)
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
                | none =>
                    rw [ha] at hsuccP
                    simp only [] at hsuccP
                    rw [hcp] at hsuccP
                    simp only [] at hsuccP
                    rw [hp] at hsuccP
                    simp only [] at hsuccP
                    simp only [successor_localExclude, Option.some.injEq] at hsuccP
                    subst hsuccP
                    exact stepLocalExclude_invariant ih (hg.hentEv hreach hc)
                      (hg.hdeadCheckpointRegion hreach hc ha hcp hp)
                | some restored =>
                    -- the recorded jump: `cfg'` is pinned by the dispatcher
                    -- equation, so every field argument below is stated at
                    -- the concrete successor the arm's lemmas produce
                    rw [ha] at hsuccP
                    simp only [] at hsuccP
                    rw [hcp] at hsuccP
                    simp only [] at hsuccP
                    rw [hp] at hsuccP
                    simp only [] at hsuccP
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hsuccP
                    have hpinj : cfg' = stepLearnBackjumpAssert cfg
                        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                          an.learned) ev restored := hsuccP.symm
                    subst hpinj
                    have hreach' : ReachableState leaf cfg.orig
                        (stepLearnBackjumpAssert cfg
                          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                            an.learned) ev restored).branch :=
                      stepLearnBackjumpAssert_branch_reachable hreach
                        ih.reachable (hg.hclos hreach) (hg.hpay hreach)
                        (hg.hunit hreach) (hg.hplanU hreach hc ha)
                        hc ha hcp hp
                        (hg.hpre hreach ih.reachable hc ha hcp hp)
                        (hg.hentEv hreach hc)
                        (by
                          show (schedulerNext cfg).successor =
                            some (stepLearnBackjumpAssert cfg
                              (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                                an.learned) ev restored)
                          exact hsucc0)
                    have hrestored : ReachableState leaf cfg.orig restored :=
                      perform_reachable_of_pre (hg.hclos hreach)
                        (hg.hpay hreach) (hg.hunit hreach)
                        (hg.hplanU hreach hc ha)
                        (hg.hpre hreach ih.reachable hc ha hcp hp) hp
                    exact schedulerInvariant_after_backjump hreach'
                      (hg.hident hreach hc ha hcp hp)
                      (stepLearnBackjumpAssert_pending_fits ih.pending_fits)
                      (stepLearnBackjumpAssert_branch_fits hreach')
                      (stepLearnBackjumpAssert_log_sound ih.log_sound)
                      (stepLearnBackjumpAssert_coverage ih.coverage
                        (hg.hbc hreach hc ha hcp hp)
                        (stepLearnBackjumpAssert_learned_mono
                          (restorationKeepsLearned_of_perform_cfg hp)))
                      (jump_learned_entailed (hg.hentEv hreach hc) hrestored)
      · -- ===== ROUTE 2: dead branch — the consume route
        rw [hnc] at hsuccP
        unfold consumeStep at hsuccP
        split at hsuccP
        · -- resumed: the gate supplies the resumed invariant
          rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hsuccP
          subst hsuccP
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest => exact hg.hconsumeInv hreach hdead hpend hcs
        · -- frontier exhausted: no successor
          simp only [successor_unsat] at hsuccP
          exact absurd hsuccP (by simp)
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate
          rw [hnt] at hsuccP
          simp only [successor_propagate, Option.some.injEq] at hsuccP
          subst hsuccP
          exact stepPropagate_invariant (hg.hclos hreach) ih (hg.hlevel hreach)
            (hg.hunit hreach) hd
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnt] at hsuccP
          unfold stableStepGuarded at hsuccP
          split at hsuccP
          · -- witness: terminal, no successor
            simp only [successor_sat] at hsuccP
            cases hsuccP
          · -- name the witness-failure fact (`leafWitness cfg = none`)
            -- for the stable-none dead-site gate below
            rename_i hwn
            split at hsuccP
            · -- split data: fresh decision or redundant-pin skip
              rename_i l v vs doms hsp
              split at hsuccP
              · -- SKIP arm: stepDecideSkip (Bool closed, non-Bool via the
                -- redundant-site pin gate + the prefix-typing gate)
                simp only [successor_decide, Option.some.injEq] at hsuccP
                subst hsuccP
                cases v with
                | bool b =>
                    exact stepDecideSkip_invariant_bool ih hsp (by assumption)
                | int i =>
                    exact stepDecideSkip_invariant ih hsp
                      (hg.hpinSkip hreach hsp (by assumption))
                      (hg.hskip hreach hsp (by assumption)) (by assumption)
                | setOfInt s =>
                    exact stepDecideSkip_invariant ih hsp
                      (hg.hpinSkip hreach hsp (by assumption))
                      (hg.hskip hreach hsp (by assumption)) (by assumption)
                | array a =>
                    exact stepDecideSkip_invariant ih hsp
                      (hg.hpinSkip hreach hsp (by assumption))
                      (hg.hskip hreach hsp (by assumption)) (by assumption)
              · -- FRESH arm: stepDecide, pinned by the (free-form) pin gate
                simp only [successor_decide, Option.some.injEq] at hsuccP
                subst hsuccP
                have hred' : TrailRedundant cfg.branch.trail l = false := by
                  cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
                exact stepDecide_invariant ih (hg.hlevel hreach) hsp
                  (hg.hpin hreach hsp hred') hred'
            · -- no split data: localExclude with the EMPTY payload
              rename_i hsp
              simp only [successor_localExclude, Option.some.injEq] at hsuccP
              subst hsuccP
              exact stepLocalExclude_invariant ih
                (by intro c hc; simp at hc)
                (C2d.branchRegion_sound (hg.hdeadStableNone hreach ht hwn hsp))
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hsuccP
          cases cs with
          | nil =>
              -- empty clause list: database refutation with the payload
              simp only [conflictStep] at hsuccP
              simp only [successor_localExclude, Option.some.injEq] at hsuccP
              subst hsuccP
              have hspec := terminalResult_spec (hg.hclos hreach) ih.reachable
              rw [ht] at hspec
              exact stepLocalExclude_invariant ih
                (fun c hc a ha =>
                  hspec.entailed c hc c (List.mem_singleton_self c) a ha)
                (C2d.branchRegion_sound
                  (hg.hdeadConflictNil hreach ih.reachable ht rfl))
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · -- level 0: root contradiction, no successor
                simp only [conflictStep, if_pos hlv, successor_unsat] at hsuccP
                cases hsuccP
              · -- analyze stutter: only the evidence/stats fields move, so
                -- the invariant transfers field-by-field
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hsuccP
                subst hsuccP
                exact ⟨ih.reachable, ih.checkpoints_identify, ih.pending_fits,
                  ih.branch_fits, ih.log_sound, ih.coverage,
                  ih.learned_entailed⟩
        · -- ARM 6: localExcluded → localExclude with the payload
          rw [hnt] at hsuccP
          simp only [successor_localExclude, Option.some.injEq] at hsuccP
          subst hsuccP
          have hspec := terminalResult_spec (hg.hclos hreach) ih.reachable
          rw [ht] at hspec
          exact stepLocalExclude_invariant ih
            (fun c hc a ha =>
              hspec.entailed c hc c (List.mem_singleton_self c) a ha)
            (C2d.branchRegion_sound
              (hg.hdeadLocalExcluded hreach ih.reachable ht))

/-! ## §7 B4's DEAD-SITE PRODUCER for the stable-none site

`ArmInvGates.hdeadStableNone` at a DISPATCHING stable-none site
(`leafWitness leaf cfg = none`, `splitData cfg.branch.frame = none`).
`splitData = none` has exactly three shapes for the frame's slot list, and
two of them are dead by elementary reasoning:

  (a) `frame.1 = []` — the arithmetic witness failed at the fully decided
      trace, so the trace is not a leaf solution, and every covering
      assignment IS the trace;
  (b) `frame.1 = [] :: doms` — an empty head domain admits no covering
      assignment at all;
  (c) an unsupported head value (`setOfInt`/`array`, where `valueLiteral`
      returns `none`) — coverage may exist, so this case is carried as the
      NAMED fragment hypothesis of the producer below. -/

/-- (a) A frame with no undecided slots: `FrameCovers` forces the covering
assignment to BE the trace, which is not a leaf solution. -/
theorem frame_dead_of_no_slots {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hslots : cfg.branch.frame.1 = [])
    (hleaf : leaf cfg.branch.frame.2 = false) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  intro a ha hcov
  obtain ⟨tail, htail, rfl⟩ := hcov
  have hnil : tail = [] := by
    simpa only [hslots, allAssigns, List.mem_singleton] using htail
  subst hnil
  simp only [List.append_nil] at ha
  have htrue : leaf cfg.branch.frame.2 = true := ha
  rw [htrue] at hleaf
  exact Bool.false_ne_true hleaf.symm

/-- (b) An empty head domain admits no covering assignment. -/
theorem frame_dead_of_empty_head {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {doms : List Domain}
    (hslots : cfg.branch.frame.1 = [] :: doms) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  intro a _ hcov
  obtain ⟨tail, htail, -⟩ := hcov
  simp only [hslots, allAssigns] at htail
  exact absurd htail (List.not_mem_nil (a := tail))

/-- (c) The unsupported-head case, NAMED: a `setOfInt`/`array` head value
(where `valueLiteral` yields `none`) leaves the frame's coverage open to the
fragment discipline — no deadness is claimed for it here. -/
def StableNoneUnsupportedCase (leaf : Assignment → Bool)
    (cfg : SchedulerConfig leaf) : Prop :=
  (∃ v vs doms, cfg.branch.frame.1 = (v :: vs) :: doms ∧
      valueLiteral cfg.branch.frame.2.length v = none) →
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False

/-- **B4's `hdeadStableNone` PRODUCER**: at a dispatching stable-none site
the current frame holds no leaf solution, with the unsupported-head case
carried as the named fragment hypothesis `hc`. -/
theorem stableNone_dead {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (hwit : leafWitness leaf cfg = none)
    (hsp : splitData cfg.branch.frame = none)
    (hc : StableNoneUnsupportedCase leaf cfg) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False := by
  cases hslots : cfg.branch.frame.1 with
  | nil =>
      -- (a) the witness failed at the fully decided trace
      have hw : (if leaf cfg.branch.frame.2 then some cfg.branch.frame.2
          else (none : Option Assignment)) = none := by
        simpa only [leafWitness, hslots] using hwit
      have hfalse : leaf cfg.branch.frame.2 = false := by
        by_cases hl : leaf cfg.branch.frame.2
        · rw [if_pos hl] at hw
          cases hw
        · simpa using hl
      exact frame_dead_of_no_slots hslots hfalse
  | cons d doms =>
      cases d with
      | nil => exact frame_dead_of_empty_head hslots
      | cons v vs =>
          refine hc ⟨v, vs, doms, hslots, ?_⟩
          cases hv : valueLiteral cfg.branch.frame.2.length v with
          | none => rfl
          | some l =>
              simp only [splitData, hslots, hv] at hsp
              cases hsp

/-- **THE UNSUPPORTED-HEAD CASE IS VACUOUS under the shape discipline**:
at a reachable branch state of a shape-typed run box no head slot can carry
a value outside the `splitData` decision vocabulary (`setOfInt`/`array` —
exactly the values `valueLiteral` maps to `none`). Such a value would sit
in a box domain at the frame's own index (`full_fits`), and the shape
discipline forces every box domain to be int-shaped or bool-shaped, where
`valueLiteral` is always `some`. -/
theorem unsupportedHead_absent_of_shape {leaf : Assignment → Bool}
    {orig : List Domain} {bs : BranchState leaf}
    (hshape : ShapeTypedDomains orig)
    (hreach : ReachableState leaf orig bs) :
    ¬ ∃ v vs doms, bs.frame.1 = (v :: vs) :: doms ∧
      valueLiteral bs.frame.2.length v = none := by
  rintro ⟨v, vs, doms, hslots, hnone⟩
  have hmem : v ∈ (fullDomains bs.frame).getD bs.frame.2.length [] := by
    rw [List.getD_eq_getElem?_getD]
    have hfr := fullDomains_remaining (f := bs.frame) (i := 0)
    rw [Nat.add_zero, hslots] at hfr
    rw [hfr]
    simp
  have hfit : v ∈ orig.getD bs.frame.2.length [] := hreach.full_fits _ _ hmem
  have hdmem : orig.getD bs.frame.2.length [] ∈ orig := by
    rw [List.getD_eq_getElem?_getD]
    cases hgt : orig[bs.frame.2.length]? with
    | none =>
        rw [List.getD_eq_getElem?_getD] at hfit
        rw [hgt] at hfit
        simp only [Option.getD_none] at hfit
        exact absurd hfit (List.not_mem_nil)
    | some d => simpa using List.mem_of_getElem? hgt
  rcases hshape _ hdmem with hint | hbool
  · obtain ⟨k, rfl⟩ := hint v hfit
    simp [valueLiteral] at hnone
  · obtain ⟨b, rfl⟩ := hbool v hfit
    simp [valueLiteral] at hnone

end LeanFzn.Solver.UIP
