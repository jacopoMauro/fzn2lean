/-
File: LeanFzn/Solver/UIP/Proofs/ConsumeRun.lean

Purpose: the supported-run producer for the consume successor's
`SchedulerInvariant` — the `hconsumeInv` input of the supported gate
records (`SupportedGates.lean` §core, `SchedulerArmsPreserve.lean` §6,
`SchedulerArmGatesProduced.lean`, `SupportedDead.lean` §5). The
field-by-field assembly is REUSED verbatim from
`stepConsume_invariant_of_components` (`Proofs/ConsumeInvariant.lean`);
this file only produces its inputs from the landed run-level producers and
never re-proves a successor field:

  * predecessor branch reachability and `PendingSideInv` — the TRIPLE joint
    induction `supportedReachAndEvidence_of_premises`
    (`Proofs/SupportedArms.lean` §0), called here, not redone;
  * predecessor log soundness — L1's run producer
    `supportedLogSound_of_newRegions` (`Proofs/SupportedLog.lean`) fed with
    the run-level registration dispatcher `SupportedNewRegionsSound` (the
    explicit L1 residual, owned by the L1 worker);
  * predecessor coverage — DISCHARGED here by the coverage-only run
    induction `supportedCoverage_of_premises` (§2-bis): the dispatcher walk
    of the invariant discipline maintaining the single `coverage` conjunct
    (identity on the log/evidence-only arms, `coverage_prepend_learned` on
    the database-growing arms, the landed jump/consume/decide/propagate
    combinators on the semantic arms; registered-region witnesses are
    eliminated by L1's log soundness). §2 takes it as the premise
    `hcov : cfg.coverage` for callers that already have it;
    `supportedHconsumeInv_of_coverage` (§2-ter) produces it internally;
  * exhausted-frame dead evidence at the consume site — DERIVED here from
    the run-level dead-site producer `supportedDeadEvidence_of_premises`
    (`Proofs/SupportedDead.lean` §4) plus the site fact
    `cfg.status = .dead` (the dispatcher's consume route,
    `C2d.schedulerNext_cases` route 2). No successor invariant is assumed;
    no predecessor `SchedulerInvariant` is assumed either.

Field-to-producer table (`SchedulerInvariant next` field → producer →
residual owner):

| field                | producer                                          | residual |
|----------------------|---------------------------------------------------|----------|
| `reachable`          | `stepConsume_reachable_of_inv` inside the         | none — from the joint induction `J` |
|                      | component lemma ← `J`'s reachability half         |          |
| `checkpoints_identify`| vacuous: `stepConsume` empties the list          | none |
| `pending_fits`       | `PendingSideInv` component of `J`                 | none — `J` |
| `branch_fits`        | `J`'s `ReachableState` full-fit conjunct          | none — `J` |
| `log_sound`          | `supportedLogSound_of_newRegions`                 | `hnew` — L1 (SupportedLogSites) |
| `coverage`           | `stepConsume_coverage` + consume-site dead evidence; | none — produced in §2-bis |
|                      | input `hcov` covered by `supportedCoverage_of_premises` |          |
| `learned_entailed`   | `J`'s `ReachableState` `WellFormed` conjunct      | none — `J` |

STATEMENT-FIDELITY NOTE (R2 report). The shared field
`... hconsumeInv : SupportedReach … cfg → cfg.pending = f :: rest →
stepConsume cfg = some next → SchedulerInvariant next` is stated WITHOUT
`cfg.status = .dead`. That exact shape is NOT provable (and is in fact
refutable): a supported ACTIVE configuration with a nonempty pending stack
(e.g. the fresh child of a real split) satisfies the premises, and
`stepConsume` there deletes a LIVE current frame from the frontier, so the
successor's `coverage` field fails whenever the learned database does not
already exclude that frame's leaves. The honest field must carry the
site's dead status:

  hconsumeInv := fun hreach hstatus hpend hcs =>
    supportedHconsumeInv_of_coverage <gates> <hnew> hreach hstatus hpend hcs

(no `hcov` argument: this file produces the predecessor coverage). The
only consumer of the full successor invariant, the route-2 arm of the two
invariant-discipline assemblies, has `hdead : cfg.status = .dead` in the
route-2 pattern. The third consumer, the `hident` chain induction, reads
only the vacuous `checkpoints_identify` and can drop the parameter
entirely (its CpChain half already unfolds `stepConsume`). The exact diff
is in §3.

No `sorry`, no custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.ConsumeRun` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (integration owner).
-/

import LeanFzn.Solver.UIP.Proofs.ConsumeInvariant
import LeanFzn.Solver.UIP.Proofs.SupportedLog
import LeanFzn.Solver.UIP.Proofs.SupportedDead
import LeanFzn.Solver.UIP.Proofs.SchedulerForward
import LeanFzn.Solver.UIP.Proofs.SchedulerBackjump
import LeanFzn.Solver.UIP.Proofs.SchedulerDecideSkip
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 Consume-site dead evidence -/

/-- **CONSUME-SITE DEAD EVIDENCE** (in the exact `hdead` shape the
component lemma consumes): at a supported dead configuration the current
frame holds no leaf solution — the run-level dead-site producer
`SupportedDeadEvidence` at the site's `status = .dead` — so the
registered-region/learned-clause witness disjunction is vacuous. This is
the "supply consume-site dead evidence for coverage" item: derived, never
assumed. -/
theorem consumeHdead_of_deadStatus {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hdeadEv : SupportedDeadEvidence orig original props leaf)
    {cfg : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (hstatus : cfg.status = .dead) :
    ∀ a, leaf a = true → FrameCovers cfg.branch.frame a →
      (∃ r ∈ cfg.log.regions, r.mem a = true) ∨
      (∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a) :=
  fun a ha hc => False.elim (hdeadEv hreach hstatus a ha hc)

/-! ## §2 The supported consume-invariant producer -/

/-- **THE SUPPORTED `hconsumeInv` PRODUCER (minimized-premise form)**: the
consume successor's `SchedulerInvariant` at every configuration of one
supported run, by reuse of `stepConsume_invariant_of_components`. The
external premises are exactly: the run's gate package for the joint
induction (same shapes as `SupportedDead.lean` §5, with `hpin`/`hskip`
derived from `hshape` by `supportedPinGates_of_shape`), L1's
registration dispatcher `hnew`, the site's `cfg.status = .dead`, and the
predecessor's coverage `hcov`. Nothing about the successor is assumed and
no predecessor invariant package is assumed. -/
theorem supportedHconsumeInv_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props)
    (hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned)
    (hpay : UnitPayload original props)
    (hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned])
    (hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch)
    (hnew : SupportedNewRegionsSound orig original props leaf)
    {cfg next : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (hreach : SupportedReach orig original props cfg)
    (hstatus : cfg.status = .dead)
    (hcov : cfg.coverage)
    (hp : cfg.pending = f :: rest) (hs : stepConsume cfg = some next) :
    SchedulerInvariant next := by
  have J : ∀ {d : SchedulerConfig leaf}, SupportedReach orig original props d →
      ReachableState leaf orig d.branch ∧
        (∀ {ev : ConflictEvidence}, d.conflict = some ev →
          LearnedEntailed leaf ev.learned) ∧
        PendingSideInv orig d :=
    supportedReachAndEvidence_of_premises hclos hunit hpay hplanU
      (supportedPinGates_of_shape hshape).hpin
      (supportedPinGates_of_shape hshape).hskip hpre hshape
  have hbr : ∀ {d : SchedulerConfig leaf},
      SupportedReach orig original props d → ReachableState leaf orig d.branch :=
    fun hd => (J hd).1
  -- the dead-site producer takes the per-configuration triple form
  have hclosC : ∀ {d : SchedulerConfig leaf}, SupportedReach orig original props d →
      ClosureContract leaf orig d.original d.props :=
    fun {d} hd => by
      rw [SupportedReach.original_eq hd, SupportedReach.props_eq hd]
      exact hclos hd
  have hdeadEv : SupportedDeadEvidence orig original props leaf :=
    supportedDeadEvidence_of_premises hclosC hbr hshape
  have hbrG : ReachableState leaf cfg.orig cfg.branch := by
    rw [SupportedReach.orig_eq hreach]
    exact (J hreach).1
  have hpendG : PendingSideInv cfg.orig cfg := by
    rw [SupportedReach.orig_eq hreach]
    exact (J hreach).2.2
  exact stepConsume_invariant_of_components hp hs hbrG hpendG
    (supportedLogSound_of_newRegions hnew hreach) hcov
    (consumeHdead_of_deadStatus hdeadEv hreach hstatus)
    (by rw [SupportedReach.orig_eq hreach]; exact (hclos hreach).leafFits)

/-! ## §2-bis The supported coverage producer (discharging the `hcov`
residual)

A coverage-only induction over the supported run. It mirrors the
dispatcher walk of the two invariant-discipline assemblies but maintains
the SINGLE `coverage` conjunct, so it never assembles or assumes a
`SchedulerInvariant`. Most arms are coverage-neutral (frontier and
database carried) or monotone (`coverage_prepend_learned`); the three
nontrivial arms reuse the landed coverage combinators, with the
reachability conjunct split out of the full-invariant restatements. -/

/-- Coverage of `stepPropagate`: the landed `stepPropagate_covers` with its
`SchedulerInvariant` input split into the two conjuncts it actually
consumes (coverage + branch reachability). Body verbatim. -/
theorem stepPropagate_coverage_of_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hc : ClosureContract leaf cfg.orig cfg.original cfg.props)
    (hcov : cfg.coverage)
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    (stepPropagate cfg d).coverage := by
  intro a hleaf
  rcases hcov a hleaf with ⟨f, hf, hcv⟩ | hdb
  · rcases List.mem_cons.mp hf with rfl | hf
    · left
      have hleafl : leaf a = true := hleaf.1
      have hrep := hreach.represents_of_frame hleafl hcv
      obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
      have hlit := hc.literalSound cfg.branch hreach d.literal d.reason
        lr fl hev a hleafl hrep
      have hlit' : d.literal.eval a = some true := by
        rwa [Literal.norm_eval] at hlit
      obtain ⟨g, hg, hcv'⟩ := filterFrame_preserves hcv hlit'
      have hg' : g = d.frame := Option.some.inj (hg.symm.trans d.filtered)
      subst hg'
      exact ⟨d.frame, by simp [SchedulerConfig.frontier, stepPropagate, narrowState], hcv'⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ hf, hcv⟩
  · right
    rcases hdb with ⟨c, hc', hnc⟩
    exact ⟨c, by simpa [stepPropagate, narrowState] using Or.inr hc', hnc⟩

/-- Coverage of the redundant-pin skip: `stepDecideSkip_covers` with its
`SchedulerInvariant` input split into coverage + branch reachability.
Body verbatim. -/
theorem stepDecideSkip_coverage_of_reachable {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hcov : cfg.coverage)
    (hreach : ReachableState leaf cfg.orig cfg.branch)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hpin : DecidePinTyped cfg l v)
    (hred : TrailRedundant cfg.branch.trail l = true) :
    (stepDecideSkip cfg v doms).coverage := by
  intro a hleaf
  rcases hcov a hleaf with ⟨f, hf, hcv⟩ | hdb
  · have hf' : f = cfg.branch.frame ∨ f ∈ cfg.pending := by
      simpa [SchedulerConfig.frontier] using hf
    rcases hf' with rfl | hf
    · left
      exact ⟨(doms, cfg.branch.frame.2 ++ [v]), List.mem_cons_self ..,
        stepDecide_redundant_no_alternative hreach hsplit hpin hred a hcv⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ (by simpa [stepDecideSkip] using hf), hcv⟩
  · right
    exact hdb

/-- Coverage of the fresh split: `stepDecide_covers` with the coverage
conjunct alone (the landed proof consumes nothing else). Body verbatim. -/
theorem stepDecide_coverage_of_coverage {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {l : Literal} {v : Value} {vs : Domain}
    {doms : List Domain}
    (hcov : cfg.coverage)
    (hsplit : splitData cfg.branch.frame = some (l, v, vs, doms)) :
    (stepDecide cfg v vs doms l).coverage := by
  have hdom := (splitData_eq_some_iff.mp hsplit).1
  intro a hleaf
  rcases hcov a hleaf with ⟨f, hf, hcv⟩ | hdb
  · rcases List.mem_cons.mp hf with rfl | hf
    · left
      have hsplitcov := (covers_split v vs doms cfg.branch.frame.2 a).mp (by
        rw [show cfg.branch.frame = (((v :: vs) :: doms), cfg.branch.frame.2)
          from Prod.ext hdom rfl] at hcv
        exact hcv)
      rcases hsplitcov with hchild | hsib
      · exact ⟨(doms, cfg.branch.frame.2 ++ [v]),
          List.mem_cons_self .., hchild⟩
      · exact ⟨(vs :: doms, cfg.branch.frame.2),
          List.mem_cons_of_mem _ (List.mem_cons_self ..), hsib⟩
    · left
      exact ⟨f, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hf), hcv⟩
  · right
    exact hdb

/-- **THE SUPPORTED COVERAGE PRODUCER**: coverage at every configuration
of one supported run. Premises: the run's shape/closure gates, the run's
branch reachability (the joint induction's first component — consumers
pass it as a function), the jump site's `BackjumpCovers` gate, the
run-level dead-site evidence (consume arm) and L1's log-soundness producer
(the consume arm's registered-region disjunct is eliminated by log
soundness, exactly as in the component lemma). -/
theorem supportedCoverage_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props)
    (hbc : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis} {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
        BackjumpCovers leaf orig cfg
          (stepLearnBackjumpAssert cfg
            (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
            restored))
    (hdeadEv : SupportedDeadEvidence orig original props leaf)
    (hnew : SupportedNewRegionsSound orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      cfg.coverage := by
  intro cfg hreach
  induction hreach with
  | init _ => exact covers_root_init leaf orig original
  | step hrec hs ih =>
      clear cfg
      rename_i cfg cfg'
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnev⟩ | ⟨hconf, hdead, hnc⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnev] at hs
        unfold backjumpStep at hs
        cases ha : ev.analysis with
        | none =>
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            simpa [stepChronologicalFallback, SchedulerConfig.coverage,
              SchedulerConfig.frontier] using ih
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                rw [ha] at hs
                simp only [] at hs
                rw [hcp] at hs
                simp only [] at hs
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hs
                subst hs
                simpa [stepChronologicalFallback, SchedulerConfig.coverage,
                  SchedulerConfig.frontier] using ih
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
                | none =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_localExclude, Option.some.injEq] at hs
                    subst hs
                    exact coverage_prepend_learned ih
                | some restored =>
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hs
                    subst hs
                    exact stepLearnBackjumpAssert_coverage ih
                      (by rw [SupportedReach.orig_eq hrec]
                          exact hbc hrec hc ha hcp hp)
                      (stepLearnBackjumpAssert_learned_mono
                        (restorationKeepsLearned_of_perform_cfg hp))
      · -- ===== ROUTE 2: dead branch — the consume route
        rw [hnc] at hs
        unfold consumeStep at hs
        split at hs
        · rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hs
          subst hs
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest =>
              obtain ⟨-, -, hlog', hlearn', horig'⟩ :=
                stepConsume_some_shape hpend hcs
              intro a ha
              have ha0 : OriginalLeaves leaf cfg.orig a := by
                simpa [horig'] using ha
              rcases ih a ha0 with hfront | hcl
              · rcases stepConsume_coverage hpend hcs
                  (consumeHdead_of_deadStatus hdeadEv hrec hdead)
                  a ha.1 hfront with hfr | hreg | hcl
                · exact Or.inl hfr
                · obtain ⟨r, hrmem, hrval⟩ := hreg
                  exact False.elim (supportedLogSound_of_newRegions hnew hrec r
                    (by simpa [hlog'] using hrmem) a ha.1 hrval)
                · exact Or.inr hcl
              · exact Or.inr (by simpa [hlearn'] using hcl)
        · simp only [successor_unsat] at hs
          cases hs
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnt⟩ | ⟨bs, ht, hnt⟩ | ⟨bs, cs, learned, ht, hnt⟩ |
            ⟨bs, lit, reason, learned, ht, hnt⟩
        · -- ARM 1: propagate
          rw [hnt] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          refine stepPropagate_coverage_of_reachable ?_ ih ?_ hd
          · rw [SupportedReach.orig_eq hrec, SupportedReach.original_eq hrec,
              SupportedReach.props_eq hrec]
            exact hclos hrec
          · rw [SupportedReach.orig_eq hrec]
            exact hbr hrec
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnt] at hs
          unfold stableStepGuarded at hs
          split at hs
          · -- witness: terminal, no successor
            simp only [successor_sat] at hs
            cases hs
          · split at hs
            · -- split data: fresh decision or redundant-pin skip
              rename_i l v vs doms hsp
              split at hs
              · -- SKIP arm: coverage-neutral frame move (typed pin)
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                refine stepDecideSkip_coverage_of_reachable ih
                  (by rw [SupportedReach.orig_eq hrec]; exact hbr hrec) hsp
                  ((supportedPinGates_of_shape hshape).hpinSkip hrec
                    (hbr hrec) hsp (by assumption)) (by assumption)
              · -- FRESH arm: the split covers the parent frame
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                exact stepDecide_coverage_of_coverage ih hsp
            · -- no split data: localExclude with the EMPTY payload
              rename_i hsp
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              simpa [stepLocalExclude, SchedulerConfig.coverage,
                SchedulerConfig.frontier] using ih
        · -- ARM 8 / ARM 4: the conflict dispatch
          rw [hnt] at hs
          cases cs with
          | nil =>
              -- empty clause list: the payload grows the database
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact coverage_prepend_learned ih
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- the recording site: only evidence/stat fields move
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                exact ih
        · -- ARM 6: localExcluded → localExclude with the payload
          rw [hnt] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          exact coverage_prepend_learned ih

/-! ## §2-ter The field-shaped producer with `hcov` DISCHARGED

The consume-invariant producer with the predecessor coverage produced from
`supportedCoverage_of_premises` (which in turn consumes an explicit
`hbr`, here the joint induction's projection). The remaining premises are
exactly: the gate package for the joint induction (P1/J1-owned), the jump
site's `hbc` gate (J1-owned), L1's `hnew`, and the site's
`cfg.status = .dead`. This is the producer the corrected field interface
(§3) instantiates. -/

/-- **SUPPORTED `hconsumeInv`, COVERAGE DISCHARGED**: the same producer as
§2 with `hcov` proven from the run instead of assumed. -/
theorem supportedHconsumeInv_of_coverage {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props)
    (hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned)
    (hpay : UnitPayload original props)
    (hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned])
    (hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch)
    (hbc : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis} {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.orig cfg.original cfg.props = some restored →
        BackjumpCovers leaf orig cfg
          (stepLearnBackjumpAssert cfg
            (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
            restored))
    (hnew : SupportedNewRegionsSound orig original props leaf)
    {cfg next : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame}
    (hreach : SupportedReach orig original props cfg)
    (hstatus : cfg.status = .dead)
    (hp : cfg.pending = f :: rest) (hs : stepConsume cfg = some next) :
    SchedulerInvariant next := by
  have J : ∀ {d : SchedulerConfig leaf}, SupportedReach orig original props d →
      ReachableState leaf orig d.branch ∧
        (∀ {ev : ConflictEvidence}, d.conflict = some ev →
          LearnedEntailed leaf ev.learned) ∧
        PendingSideInv orig d :=
    supportedReachAndEvidence_of_premises hclos hunit hpay hplanU
      (supportedPinGates_of_shape hshape).hpin
      (supportedPinGates_of_shape hshape).hskip hpre hshape
  have hbr : ∀ {d : SchedulerConfig leaf},
      SupportedReach orig original props d → ReachableState leaf orig d.branch :=
    fun hd => (J hd).1
  have hclosC : ∀ {d : SchedulerConfig leaf}, SupportedReach orig original props d →
      ClosureContract leaf orig d.original d.props :=
    fun {d} hd => by
      rw [SupportedReach.original_eq hd, SupportedReach.props_eq hd]
      exact hclos hd
  have hdeadEv : SupportedDeadEvidence orig original props leaf :=
    supportedDeadEvidence_of_premises hclosC hbr hshape
  exact supportedHconsumeInv_of_premises hshape hclos hunit hpay hplanU hpre
    hnew hreach hstatus (supportedCoverage_of_premises hshape hbr hclos hbc
      hdeadEv hnew hreach) hp hs

/-! ## §3 The shared-interface fidelity diff (report only; NOT applied here)

The field `hconsumeInv` must carry the one honest site fact. Recommended
minimal diff (integration owner; `hdead : cfg.status = .dead` is already
in scope at the route-2 use sites):

1. `Proofs/SupportedGates.lean` (≈ l.253), field of
   `SupportedArmInvGatesCore`:

     hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
       {rest : List BranchFrame}, SupportedReach orig original props cfg →
       cfg.pending = f :: rest → stepConsume cfg = some next →
         SchedulerInvariant next

   becomes

     hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
       {rest : List BranchFrame}, SupportedReach orig original props cfg →
       cfg.status = .dead →
       cfg.pending = f :: rest → stepConsume cfg = some next →
         SchedulerInvariant next

   (and the same restatement of the copies at
   `Proofs/SchedulerArmsPreserve.lean` ≈ l.706,
   `Proofs/SchedulerArmGatesProduced.lean` ≈ l.148, and the premise of
   `Proofs/SupportedDead.lean` ≈ l.501, which are pass-throughs;
   `cfg.coverage` is NOT added — §2-bis produces predecessor coverage).

2. Use sites pass the site fact:
   * `Proofs/SupportedArms.lean` ≈ l.824 (`supportedInvariantDiscipline_of_gates`,
     route 2):
       `exact hg.core.hconsumeInv hrec hpend hcs` →
       `exact hg.core.hconsumeInv hrec hdead hpend hcs`
     (`hdead : cfg.status = .dead` from the route-2 pattern);
   * `Proofs/SchedulerArmsPreserve.lean` ≈ l.857
     (`reachableInvariantDiscipline_of_gates`, route 2): the same edit.

3. `Proofs/SupportedProviders.lean` ≈ l.551/745: the only non-discipline
   consumer reads the successor's vacuous `checkpoints_identify`; drop the
   `hconsumeInv` parameter of `supportedIdentifiesChain_of_premises` /
   `supportedHident_of_premises` and inline the trivial witness at
   ≈ l.648 (as the CpChain half already does), then
   `Proofs/SupportedDead.lean` ≈ l.558 changes
   `hident := supportedHident_of_premises hconsumeInv` →
   `hident := supportedHident_of_premises`.

With (1)–(2), the discipline instantiations provide
`hconsumeInv := fun hreach hstatus hpend hcs =>
supportedHconsumeInv_of_coverage … hreach hstatus hpend hcs`.

Residual assessment after §2-bis: the consume producer's remaining
residuals are L1's `hnew : SupportedNewRegionsSound` and the P1/J1-owned
gate package (`hshape`, `hclos`, `hunit`, `hpay`, `hplanU`, `hpre`; the
`hbc` gate has producer `supportedHbc_of_recorded_analysis hbr` —
SupportedProviders §6 — with `hbr` the joint induction's projection, so it
is not a new residual). No successor invariant and no predecessor
invariant package is assumed anywhere in this file. -/

end LeanFzn.Solver.UIP
