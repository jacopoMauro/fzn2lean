/-
File: LeanFzn/Solver/UIP/Proofs/SupportedInstance.lean
compiled unit-kit instance of the supported core gates)

Purpose: the CONCRETE INSTANTIATION of the eight-input core assembly
`SupportedDead.supportedCoreGates_of_producers` for the unit kit
(`props = dcs.filterMap propagatorOfProved` with every
`unitFamilyB dc = true`), wiring every landed producer and exporting the
derived run-level instances for C2/W1.

## Field-to-producer table (`SupportedArmInvGatesCore` field → producer →
residual, with OWNER)

| field                   | producer                                                      | residual (owner) |
|-------------------------|---------------------------------------------------------------|------------------|
| `hclos`                 | `supportedHclos_of_contract` (P1)                             | `hcontract` — P1/D1 compiled route `supportedHclos_of_compiled` |
| `hunit`                 | `supportedHunit_of_unitRun` (SupportedDead §6, N1)            | none (unit kit) |
| `hpay`                  | `supportedHpay_of_unitRun` (SupportedDead §6, N1)             | none (unit kit) |
| `hplanU`                | `supportedHplanU_of_unitRun` (SupportedDead §6, N1)           | none (unit kit) |
| `hlevel`                | `supportedHlevel_of_reach` (SupportedProviders §5)            | none |
| `hpin`/`hskip`/`hpinSkip`| `supportedPinGates_of_shape` (SupportedProviders §1; inside the assembly) | `hshape` — F1 compiled shape (`shapeTypedDomains_of_compileModel_toLCG`) |
| `hpre`                  | `supportedHpre_of_unitRun_site_or_coverless` (HdeadCkpt §11)  | `hAnalysisEntail` (I1-B), `hinhabOr` (C2a, PREMISE-FREE), `hsepF` (C2c), `hv` (C1) |
| (joint `hbr`)           | §0 `supportedReachEvidenceChain_of_premises` (this file)      | NONE — the four-component induction |
| (site snapshots)        | §0 chain component `(J hreach).2.2.2`                         | NONE |
| (joint `hentEv`)        | §0 entailment component `(J hreach).2.1`                      | NONE |
| `hident`                | `supportedHident_of_premises` (SupportedProviders §5)         | none |
| `hbc`                   | `supportedHbc_of_recorded_analysis hbrF` (SupportedProviders §6) | none |
| `hdeadStableNone`       | `supportedHdeadStableNone_of_shape` (SupportedDead §2)        | `hshape` only |
| `hdeadFallbackNone`     | `supportedFrameDead_of_recordedEvidence` (SupportedDead §1)   | `hclos` only |
| `hdeadFallbackNoCp`     | same producer as `hdeadFallbackNone`                          | `hclos` only |
| `hdeadCheckpointRegion` | `supportedHdeadCheckpointRegion_of_reach` (HdeadCkpt §9, E1)  | `hAnalysisEntail` (I1-B) only — `hbr` is the §0 component |
| `hconsumeInv`           | `supportedHconsumeInv_of_coverage` (ConsumeRun §2-ter, R2)    | `hnew` (below), `hbc`, + the same core package |
| `hconsume`              | `supportedHconsume_of_premises` (inside the assembly, PendingRun §5) | none |

## The `hpre ↔ hbr/hent` circularity: RESOLVED in this file

`SupportedArms.supportedReachAndEvidence_of_premises` calls its `hpre`
parameter at each jump site with only the site's `ReachableState`, while
the site-level `hpre` producer needs the selected checkpoint's
`CheckpointSnapshot` — and the snapshot family's only producer
(`supportedReachableCpSnapshots_of_premises`) consumes the very `hbr` that
this induction produces. §0 below breaks the cycle WITHOUT touching the
shared file: the SAME induction is re-run at the extended motive
(reachability, evidence entailment, `PendingSideInv`, and the chain
component `ReachableCpSnapshots`), with the one extra `hpre` argument
`CheckpointSnapshot leaf orig cp` supplied at the call site from the
PREVIOUS state's chain component (`ih.2.2.2 cp (checkpointAt_mem hcp)`).
Everything in §2 is then built from `(J ·).1` / `(J ·).2.2.2` / the site
twins; no `hbr` premise remains.

OPTIONAL CONSOLIDATION (for the integration owner, NOT required for
closure): fold §0 into `Proofs/SupportedArms.lean` so the shared induction
carries the chain component, i.e. (i) + the 4th conjunct
`ReachableCpSnapshots leaf orig cfg` in the motive of
`supportedStepReachAndEvidence_of_premises` and
`supportedReachAndEvidence_of_premises` (SupportedArms.lean ≈ l.47/≈ l.60/≈ l.355),
(ii) + `(hsnap : CheckpointSnapshot leaf orig cp)` as the third argument of
the `hpre` parameter of both, (iii) the call site ≈ l.172 becomes
`hpre hreach ih.1 (ih.2.2.2 cp (checkpointAt_mem hcp)) hc ha hcp hp`, and
(iv) each arm's conclusion gains the chain component exactly as §0 does
(sublists for the filters/stutters, `checkpointSnapshot_ofBranch ih.1` for
the fresh-decide push). Then `SupportedDead.supportedCoreGates_of_producers`
(§5) and `ConsumeRun` §2/§2-ter take the EXTENDED-typed `hpre` and fill the
record field with the lambda
`fun hreach hbs hc ha hcp hp => hpre hreach hbs (hsnapF hreach cp (checkpointAt_mem hcp)) hc ha hcp hp`
(their pass-through call sites are otherwise unchanged). Until then, §0's
copy is the authoritative induction and the assembled record is identical.

Derived producers exported here (`SupportedUnitKit`):
  * `hnew : SupportedNewRegionsSound` — L1's
    `supportedNewRegionsSound_of_premises` (`hp`/`hshape`/`hclos`/`hdeadCkpt`);
  * the run-level log soundness — L1's `supportedLogSound_of_newRegions`;
  * `hdeadEv : SupportedDeadEvidence` — E1's `supportedDeadEvidence_of_premises`;
  * `hbc` — J2's `supportedHbc_of_recorded_analysis`;
  * `hconsumeInv` — R2's `supportedHconsumeInv_of_coverage`
    (with R2 §2-bis's predecessor coverage produced internally);
  * `core : SupportedArmInvGatesCore` — the eight-input assembly.

RESIDUAL HYPOTHESES (verbatim, the honest list — the entry points that
consume it are the `_or_coverless` variants; there is no circularity
marker):

  hshape :
    ShapeTypedDomains orig
  hcontract :
    ClosureContract leaf orig original props
  hAnalysisEntail :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned]
  hinhabOr :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
        (∃ d ∈ cfg.branch.frame.1, d = [])
  hsepF :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm
  hv :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch

(plus the unit-kit equations `hprops : props = dcs.filterMap
propagatorOfProved` and `hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true`).

`hinhabOr` is itself PREMISE-FREE (`SiteInhabited.supportedInhabited_or_coverless`,
`Proofs/SiteInhabited.lean`, kernel-checked), so the honest list has
exactly ONE genuine residual: `hsepF` — the level separation at COVERLESS
sites (C2c). At unit-kit recorded sites the target is pinned to `0`
(`FreshCoverless.unitKit_backjumpLevel_eq_zero`) and every pure
canonical-resume site is discharged by
`FreshCoverless.canonicalTrail_levelSeparated`; the remaining, NOT yet
formalized sub-case is an EMPTY-prefix `stepConsume` followed by level-0
propagations and a decide pushing a level-0 checkpoint (owner C2 — see
`FreshCoverless` §4/§5).

The ALL-SITES inhabitedness family `hinhab`
(`∀ cfg, SupportedReach … cfg → ∃ a, FrameCovers cfg.branch.frame a`) is
KERNEL-REFUTED (`SiteInhabited.cexNotAllSites`; its recorded-site form by
`SiteLiveness.recordedInhabited_false`), so the theorems below that still
carry it are LEGACY entry points, each marked with the docstring line
"REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless`
variant". The supported interfaces are the variants:
`supportedHpre_unitKit_of_site_or_coverless` (§1),
`supportedUnitKit_of_premises_or_coverless` (§2),
`supportedCoreGates_unitKit_or_coverless` /
`supportedCoreGates_unitKit_of_supportedInput_or_coverless` (§2), the four
`*_unitKit_or_coverless` §3 exports, and the §4
`*_discharged_or_coverless` wrappers.

Owners: `hshape`/`hcontract` — P1/D1 (landed compiled producers, wired in
`supportedCoreGates_unitKit_of_supportedInput_or_coverless`);
`hAnalysisEntail` — I1-B (`Proofs/AnalysisEntail.lean`, the resolution
bridge from the terminal conflict clause + trail reasons to the analysis's
learned clause; the site-shaped form is the one the extended induction
consumes — the run-indexed form would itself need `hbr`); `hinhabOr` —
C2a (PREMISE-FREE: `Proofs/SiteInhabited.lean`,
`supportedInhabited_or_coverless`; it is an explicit argument here only
because this file does not import `SiteInhabited`); `hsepF` — C2c
(`Proofs/FreshCoverless.lean` §4/§5 + `HdeadCkpt` §11; the one genuine
residual, exact sub-case documented above); `hv` — C1 (the landed-pool
trail vocabulary; the unit kit's premise-free emission vocabulary is only
the EXTENDED-pool one, `unitEmissionVocabulary_proved_litPoolExt`, so the
landed-pool `hv` route needs the pool extension re-keyed into `hrange`,
or a slot-range lemma at `litPoolExt`).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedInstance` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Solver.UIP.Proofs.SupportedDead
import LeanFzn.Solver.UIP.Proofs.HdeadCkpt
import LeanFzn.Solver.UIP.Proofs.SupportedLogSites
import LeanFzn.Solver.UIP.Proofs.ConsumeRun
import LeanFzn.Solver.UIP.Proofs.AnalysisEntail
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §0 The four-component joint induction (the circularity break)

`SupportedArms.supportedReachAndEvidence_of_premises` produces the triple
(branch reachability, evidence entailment, `PendingSideInv`) with an `hpre`
that is called at each jump site with only the site's `ReachableState` —
while the site-level `hpre` producer (`HdeadCkpt` §10) additionally needs
the selected checkpoint's `CheckpointSnapshot`. The two lemmas below add
the CHAIN COMPONENT (`ReachableCpSnapshots` of the configuration, the
`hbr`-free snapshot family) to the same induction, so the site snapshot is
`(the previous state's chain component) cp (checkpointAt_mem hcp)` — an
available site fact — and the `hpre` argument gains exactly ONE extra
argument (`CheckpointSnapshot leaf orig cp` between the site's
`ReachableState` and the conflict facts). Bodies are the landed
`SupportedArms` §0 proofs with the chain component maintained per arm
(the jump filter and the consume filter are sublists, the fresh decide
pushes the parent snapshot `checkpointSnapshot_ofBranch ih.1`, every
other arm keeps the checkpoint list). Nothing here modifies the shared
file: this is the same induction at the extended motive, owned by I1. -/

/-- **THE EXTENDED JOINT STEP**: one dispatcher step preserves
(reachability, recorded-evidence entailment, `PendingSideInv`, checkpoint
snapshots) jointly. The `hpre` argument carries the site snapshot. -/
theorem supportedStepReachEvidenceChain_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props)
    (hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned)
    (hpay : UnitPayload original props)
    (hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned])
    (hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = false →
        ∀ a : Assignment, Assignment.Fits orig a →
          (l.norm.eval a = some true ↔
            a[cfg.branch.frame.2.length]? = some v))
    (hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = true →
        DecideSkipPrefixTyped orig cfg v)
    (hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      CheckpointSnapshot leaf orig cp →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch)
    (hshape : ShapeTypedDomains orig)
    {cfg cfg' : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg')
    (ih : ReachableState leaf orig cfg.branch ∧
      (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
        LearnedEntailed leaf ev.learned) ∧
      PendingSideInv orig cfg ∧
      ReachableCpSnapshots leaf orig cfg) :
    ReachableState leaf orig cfg'.branch ∧
      (∀ {ev : ConflictEvidence}, cfg'.conflict = some ev →
        LearnedEntailed leaf ev.learned) ∧
      PendingSideInv orig cfg' ∧
      ReachableCpSnapshots leaf orig cfg' := by
  have hs' : (schedulerNext cfg).successor = some cfg' := hsucc
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
        refine ⟨ih.1, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
          ReachableCpSnapshots.of_sublist ih.2.2.2
            (by simpa only [stepChronologicalFallback]
              using List.Sublist.refl cfg.checkpoints)⟩
        intro ev' hconf'
        rw [stepChronologicalFallback_conflict] at hconf'
        cases hconf'
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            -- no checkpoint → fallback stutter
            rw [ha] at hsucc
            simp only [] at hsucc
            rw [hcp] at hsucc
            simp only [] at hsucc
            simp only [successor_chronologicalFallback, Option.some.injEq]
              at hsucc
            subst hsucc
            refine ⟨ih.1, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
              ReachableCpSnapshots.of_sublist ih.2.2.2
                (by simpa only [stepChronologicalFallback]
                  using List.Sublist.refl cfg.checkpoints)⟩
            intro ev' hconf'
            rw [stepChronologicalFallback_conflict] at hconf'
            cases hconf'
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.original cfg.props with
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
                refine ⟨reachable_prepend_learned ih.1 (ih.2.1 hc), ?_,
                  pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
                  ReachableCpSnapshots.of_sublist ih.2.2.2
                    (by simpa only [stepLocalExclude]
                      using List.Sublist.refl cfg.checkpoints)⟩
                intro ev' hconf'
                rw [stepLocalExclude_conflict] at hconf'
                cases hconf'
            | some restored =>
                -- the recorded jump (S3 pre-reachability + S4 payload
                -- entailment); the site snapshot is the chain component
                rw [ha] at hsucc
                simp only [] at hsucc
                rw [hcp] at hsucc
                simp only [] at hsucc
                rw [hp] at hsucc
                simp only [] at hsucc
                simp only [successor_learnBackjumpAssert, Option.some.injEq]
                  at hsucc
                subst hsucc
                have hres := stepLearnBackjumpAssert_branch_reachable hreach.reachable
                  (by rw [SupportedReach.orig_eq hreach]; exact ih.1)
                  (by rw [SupportedReach.orig_eq hreach,
                          SupportedReach.original_eq hreach,
                          SupportedReach.props_eq hreach]
                      exact hclos hreach)
                  (by rw [SupportedReach.original_eq hreach,
                          SupportedReach.props_eq hreach]
                      exact hpay)
                  (hunit hreach) (hplanU hreach hc ha)
                  hc ha hcp hp
                  (by rw [SupportedReach.orig_eq hreach]
                      exact hpre hreach ih.1 (ih.2.2.2 cp (checkpointAt_mem hcp))
                        hc ha hcp hp)
                  (ih.2.1 hc)
                  (by show (schedulerNext cfg).successor = some
                        (stepLearnBackjumpAssert cfg
                          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                            an.learned) ev restored)
                      rw [hnext]
                      unfold backjumpStep
                      rw [ha]
                      simp only []
                      rw [hcp]
                      simp only []
                      rw [hp]
                      simp only []
                      simp only [successor_learnBackjumpAssert])
                rw [SupportedReach.orig_eq hreach] at hres
                refine ⟨hres, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
                  ReachableCpSnapshots.of_sublist ih.2.2.2
                    (checkpoints_sublist_stepLearnBackjumpAssert cfg
                      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                        an.learned) ev restored)⟩
                intro ev' hconf'
                rw [stepLearnBackjumpAssert_conflict] at hconf'
                cases hconf'
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
      | cons f rest =>
          have hres := stepConsume_reachable_of_inv hpend hcs ih.1 ih.2.2.1
            (SupportedReach.orig_eq hreach)
          refine ⟨hres, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
            ReachableCpSnapshots.of_sublist ih.2.2.2
              (stepConsume_checkpoints_sublist hpend hcs)⟩
          intro ev' hconf'
          rw [stepConsume_conflict hcs] at hconf'
          cases hconf'
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
      have hd' : explainedDeduction original props cfg.branch = some d := by
        rw [← SupportedReach.original_eq hreach, ← SupportedReach.props_eq hreach]
        exact hd
      refine ⟨explainedDeduction_narrow_reachable (hclos hreach) ih.1
        (hunit hreach) hd', ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
        ReachableCpSnapshots.of_sublist ih.2.2.2
          (by simpa only [stepPropagate]
            using List.Sublist.refl cfg.checkpoints)⟩
      intro ev' hconf'
      rw [stepPropagate_conflict] at hconf'
      exact ih.2.1 hconf'
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
            refine ⟨?_, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
              ReachableCpSnapshots.of_sublist ih.2.2.2
                (by simpa only [stepDecideSkip]
                  using List.Sublist.refl cfg.checkpoints)⟩
            · cases v with
              | bool b =>
                  exact reachable_decideSkip_bool ih.1 hsp (by assumption)
              | int i =>
                  exact reachable_decideSkip ih.1 hsp
                    (hskip hreach ih.1 hsp (by assumption))
              | setOfInt s =>
                  exact reachable_decideSkip ih.1 hsp
                    (hskip hreach ih.1 hsp (by assumption))
              | array a =>
                  exact reachable_decideSkip ih.1 hsp
                    (hskip hreach ih.1 hsp (by assumption))
            · intro ev' hconf'
              rw [stepDecideSkip_conflict] at hconf'
              exact ih.2.1 hconf'
          · -- FRESH arm: stepDecide; Bool closed, non-Bool via `hpin`
            simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            have hred' : TrailRedundant cfg.branch.trail l = false := by
              cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
            refine ⟨?_, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1, ?_⟩
            · cases v with
              | bool b =>
                  have hwl := (splitData_eq_some_iff.mp hsp).2
                  refine reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) ?_ (not_trailRedundant_iff.mp hred')
                  intro a _
                  rw [Literal.norm_eval]
                  simpa using valueLiteral_holds_iff hwl a
              | int i =>
                  exact reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) (hpin hreach ih.1 hsp hred')
                    (not_trailRedundant_iff.mp hred')
              | setOfInt s =>
                  exact reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) (hpin hreach ih.1 hsp hred')
                    (not_trailRedundant_iff.mp hred')
              | array a =>
                  exact reachable_decide ih.1 (splitData_eq_some_iff.mp hsp).1
                    (List.mem_cons_self ..) (hpin hreach ih.1 hsp hred')
                    (not_trailRedundant_iff.mp hred')
            · intro ev' hconf'
              rw [stepDecide_conflict] at hconf'
              exact ih.2.1 hconf'
            · -- the pushed checkpoint is the parent's own snapshot
              intro c hc
              rw [show (stepDecide cfg v vs doms l).checkpoints =
                DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints
                from rfl] at hc
              rcases List.mem_cons.mp hc with rfl | hc
              · exact checkpointSnapshot_ofBranch (leaf := leaf) ih.1
              · exact ih.2.2.2 c hc
        · -- no split data: localExclude with the EMPTY payload
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          refine ⟨reachable_prepend_learned ih.1 (by intro c hc'; simp at hc'), ?_,
            pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
            ReachableCpSnapshots.of_sublist ih.2.2.2
              (by simpa only [stepLocalExclude]
                using List.Sublist.refl cfg.checkpoints)⟩
          intro ev' hconf'
          rw [stepLocalExclude_conflict] at hconf'
          cases hconf'
    · -- ARM 8 / ARM 4: the conflict dispatch
      cases cs with
      | nil =>
          -- empty clause list: local exclusion with the payload; the
          -- entailment comes from `terminalResult_spec` + `hclos`
          rw [hnext] at hsucc
          simp only [conflictStep] at hsucc
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          have hspec := terminalResult_spec (hclos hreach) ih.1
          rw [SupportedReach.original_eq hreach,
            SupportedReach.props_eq hreach] at ht
          rw [ht] at hspec
          refine ⟨reachable_prepend_learned ih.1
            (fun c hc' a ha =>
              hspec.entailed c hc' c (List.mem_singleton_self c) a ha), ?_,
            pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
            ReachableCpSnapshots.of_sublist ih.2.2.2
              (by simpa only [stepLocalExclude]
                using List.Sublist.refl cfg.checkpoints)⟩
          intro ev' hconf'
          rw [stepLocalExclude_conflict] at hconf'
          cases hconf'
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
            refine ⟨ih.1, ?_, pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
              ReachableCpSnapshots.of_sublist ih.2.2.2
                (by simpa only [stepAnalyzeConflictCounted, stepAnalyzeConflict,
                  SchedulerConfig.countResolutions]
                  using List.Sublist.refl cfg.checkpoints)⟩
            intro ev' hconf'
            rw [stepAnalyzeConflictCounted_conflict] at hconf'
            injection hconf' with hev
            subst hev
            have hspec := terminalResult_spec (hclos hreach) ih.1
            rw [SupportedReach.original_eq hreach,
              SupportedReach.props_eq hreach] at ht
            rw [ht] at hspec
            exact fun c' hc' a ha =>
              hspec.entailed c' hc' c' (List.mem_singleton_self c') a ha
    · -- ARM 6: localExcluded → localExclude with the payload (spec entailment)
      rw [hnext] at hsucc
      simp only [successor_localExclude, Option.some.injEq] at hsucc
      subst hsucc
      have hspec := terminalResult_spec (hclos hreach) ih.1
      rw [SupportedReach.original_eq hreach,
        SupportedReach.props_eq hreach] at ht
      rw [ht] at hspec
      refine ⟨reachable_prepend_learned ih.1
        (fun c hc' a ha =>
          hspec.entailed c hc' c (List.mem_singleton_self c) a ha), ?_,
        pendingSideInv_supportedStep hshape ih.1 hs' ih.2.2.1,
        ReachableCpSnapshots.of_sublist ih.2.2.2
          (by simpa only [stepLocalExclude]
            using List.Sublist.refl cfg.checkpoints)⟩
      intro ev' hconf'
      rw [stepLocalExclude_conflict] at hconf'
      cases hconf'

/-- **THE FOUR-COMPONENT JOINT INVARIANT PRODUCER (I1)**: one induction over
the supported run yields branch reachability, recorded-evidence
entailment, `PendingSideInv` AND the checkpoint-snapshot chain — the
`hbr`-free replacement whose `hpre` argument receives the site's snapshot
`CheckpointSnapshot leaf orig cp`. -/
theorem supportedReachEvidenceChain_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props)
    (hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned)
    (hpay : UnitPayload original props)
    (hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned])
    (hpin : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = false →
        ∀ a : Assignment, Assignment.Fits orig a →
          (l.norm.eval a = some true ↔
            a[cfg.branch.frame.2.length]? = some v))
    (hskip : ∀ {cfg : SchedulerConfig leaf} {l : Literal} {v : Value}
      {vs : Domain} {doms : List Domain}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      splitData cfg.branch.frame = some (l, v, vs, doms) →
      TrailRedundant cfg.branch.trail l = true →
        DecideSkipPrefixTyped orig cfg v)
    (hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      CheckpointSnapshot leaf orig cp →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch ∧
        (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          LearnedEntailed leaf ev.learned) ∧
        PendingSideInv orig cfg ∧
        ReachableCpSnapshots leaf orig cfg := by
  intro cfg hreach
  induction hreach with
  | init =>
      exact ⟨reachable_init leaf orig,
        (fun {ev} hconf => absurd hconf (by simp [SchedulerConfig.init])),
        PendingSideInv.init orig original props,
        reachableCpSnapshots_init orig original props⟩
  | step hrec hs ih =>
      exact supportedStepReachEvidenceChain_of_premises hclos hunit hpay hplanU
        hpin hskip hpre hshape hrec hs ih

/-! ## §1 The `hpre` field from the site-level twins

The core assembly's `hpre` premise (exact `SupportedArmInvGatesCore.hpre`
field shape) is built from `HdeadCkpt` §10's SITE-LEVEL twins, so the only
run-level inputs it consumes are exactly the site facts the joint
induction supplies: the selected checkpoint's snapshot (the §0 chain
component `(J hreach).2.2.2`, passed here as the `hsnapF` family) and the
site entailment (I1-B's bridge at the site's own `ReachableState`). -/

/-- **THE UNIT-KIT `hpre` FIELD FROM SITE INGREDIENTS**: the field-typed
restoration pre-reachability producer of the joint induction, assembled
from the site-level twins.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedHpre_unitKit_of_site {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hsnapF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableCpSnapshots leaf orig cfg)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch :=
  fun {_cfg} {cp} {_ev} {_an} {_restored} hreach hbs hconf hana hcp hp =>
    supportedHpre_of_unitRun_site hprops hSupp hreach hbs
      (hsnapF hreach cp (checkpointAt_mem hcp))
      (fun hc' ha' => hAnalysisEntail hreach hcontract hbs hc' ha')
      (hinhab hreach) (hv hreach) hconf hana hcp hp

/-- **THE UNIT-KIT `hpre` FIELD FROM SITE INGREDIENTS, HONEST FORM (I1)**:
the `_or_coverless` twin of `supportedHpre_unitKit_of_site` — the refuted
site inhabitedness is replaced by C2a's PREMISE-FREE classification family
`hinhabOr` and C2c's coverless-site level separation `hsepF`, wired through
`HdeadCkpt.supportedHpre_of_unitRun_site_or_coverless` (§11). Every other
site ingredient is unchanged: `hsnapF` supplies the site's checkpoint
snapshot via `checkpointAt_mem`, `hAnalysisEntail` the site entailment,
`hv` the site trail vocabulary. -/
theorem supportedHpre_unitKit_of_site_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hsnapF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableCpSnapshots leaf orig cfg)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch :=
  fun {_cfg} {_cp} {_ev} {_an} {_restored} hreach hbs hconf hana hcp hp =>
    supportedHpre_of_unitRun_site_or_coverless hprops hSupp hreach hbs
      (fun {_ev'} {_an'} {cp'} _hc' _ha' hcp' =>
        hsnapF hreach cp' (checkpointAt_mem hcp'))
      (fun hc' ha' => hAnalysisEntail hreach hcontract hbs hc' ha')
      hinhabOr hsepF (hv hreach) hconf hana hcp hp

/-! ## §2 The wired unit-kit instance -/

/-- **THE WIRED UNIT-KIT INSTANCE**: everything
`supportedCoreGates_of_producers` consumes, wired from the landed
producers (see the module table). Every field is a derived run-level fact
of the one supported run; no successor invariant, no region soundness, no
log soundness and no restoration conclusion is assumed. -/
structure SupportedUnitKit (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop where
  /-- the joint induction's branch-reachability family -/
  hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch
  /-- the chain component (checkpoint snapshots), here from
      `supportedReachableCpSnapshots_of_premises` -/
  hsnapF : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ReachableCpSnapshots leaf orig cfg
  /-- the D1/I1-B analysis entailment at the recorded sites -/
  hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    {an : ConflictAnalysis}, SupportedReach orig original props cfg →
    cfg.conflict = some ev → ev.analysis = some an →
      LearnedEntailed leaf [an.learned]
  /-- the E1 checkpoint-rejection region soundness -/
  hdeadCkpt : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
    ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = none →
      DeadRegion.Sound leaf (checkpointRegion cp)
  /-- the jump successor's coverage gate (J2) -/
  hbc : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf},
    SupportedReach orig original props cfg → cfg.conflict = some ev →
    ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = some restored →
      BackjumpCovers leaf orig cfg
        (stepLearnBackjumpAssert cfg
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
          restored)
  /-- L1's registration-site dispatcher -/
  hnew : SupportedNewRegionsSound orig original props leaf
  /-- the run-level exhaustion-log soundness (L1) -/
  hlog : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ExhaustionLog.Sound leaf cfg.log
  /-- the run-level dead-site evidence (E1) -/
  hdeadEv : SupportedDeadEvidence orig original props leaf
  /-- the consume successor's invariant (R2) -/
  hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}, SupportedReach orig original props cfg →
    cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
      SchedulerInvariant next
  /-- the eight-input core-gate assembly -/
  core : SupportedArmInvGatesCore orig original props leaf

/-- **THE WIRED UNIT-KIT BUILDER (I1)**: the unit kit plus the residual
hypotheses (the module docstring's verbatim list) produce the whole
instance: the unit-discipline trio from N1, the `hpre` field from the
site-level twins, the E1/L1/J2/R2 run-level producers, the eight-input
assembly and the derived log/dead/consume exports.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedUnitKit_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedUnitKit orig original props leaf := by
  -- the closure contract at the two spellings the producers take
  have hclosF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig original props :=
    fun _ => hcontract
  have hclosC : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props :=
    fun hreach => by
      rw [SupportedReach.original_eq hreach, SupportedReach.props_eq hreach]
      exact hcontract
  -- N1's unit-discipline trio (SupportedDead §6)
  have hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned :=
    supportedHunit_of_unitRun hprops hSupp
  have hpay : UnitPayload original props :=
    supportedHpay_of_unitRun hprops hSupp
  have hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned] :=
    supportedHplanU_of_unitRun hprops hSupp
  -- the extended-`hpre` site producer: the four-component induction below
  -- supplies the site's snapshot (`ih.2.2.2`) and the site entailment is
  -- I1-B's bridge at the site's own ReachableState
  have hpreJ : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      CheckpointSnapshot leaf orig cp →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch :=
    fun hreach hbs hsnapS hc ha hcp hp =>
      supportedHpre_of_unitRun_site hprops hSupp hreach hbs hsnapS
        (fun hc' ha' => hAnalysisEntail hreach hcontract hbs hc' ha')
        (hinhab hreach) (hv hreach) hc ha hcp hp
  -- THE FOUR-COMPONENT JOINT INDUCTION (I1): reachability, evidence
  -- entailment, PendingSideInv AND the checkpoint-snapshot chain
  have J : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch ∧
        (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          LearnedEntailed leaf ev.learned) ∧
        PendingSideInv orig cfg ∧
        ReachableCpSnapshots leaf orig cfg :=
    supportedReachEvidenceChain_of_premises hclosF hunit hpay hplanU
      (supportedPinGates_of_shape hshape).hpin
      (supportedPinGates_of_shape hshape).hskip hpreJ hshape
  have hbrF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch :=
    fun hreach => (J hreach).1
  -- the chain component (no longer an external family)
  have hsnapF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableCpSnapshots leaf orig cfg :=
    fun hreach => (J hreach).2.2.2
  -- the site entailment family (I1-B's bridge at the site's ReachableState)
  have hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned] :=
    fun hreach hconf hana => hAnalysisEntail hreach hcontract (hbrF hreach) hconf hana
  -- the `hpre` FIELD of the record (the joint induction consumed `hpreJ`)
  have hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch :=
    supportedHpre_unitKit_of_site hcontract hprops hSupp hsnapF
      hAnalysisEntail hinhab hv
  -- E1 (HdeadCkpt §9) and its L1 dispatcher consumption
  have hdeadCkpt : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp) :=
    supportedHdeadCheckpointRegion_of_reach hbrF hent
  have hnew : SupportedNewRegionsSound orig original props leaf :=
    supportedNewRegionsSound_of_premises hshape hclosC hbrF hdeadCkpt
  have hlog : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
    supportedLogSound_of_newRegions hnew
  -- E1's run-level dead evidence, J2's coverage gate, R2's consume gate
  have hdeadEv : SupportedDeadEvidence orig original props leaf :=
    supportedDeadEvidence_of_premises hclosC hbrF hshape
  have hbc : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        BackjumpCovers leaf orig cfg
          (stepLearnBackjumpAssert cfg
            (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
            restored) :=
    supportedHbc_of_recorded_analysis hbrF
  have hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame}, SupportedReach orig original props cfg →
      cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
        SchedulerInvariant next :=
    fun hreach hstatus hp hs =>
      supportedHconsumeInv_of_coverage hshape hclosF hunit hpay hplanU hpre hbc
        hnew hreach hstatus hp hs
  -- the eight-input core assembly
  have core : SupportedArmInvGatesCore orig original props leaf :=
    supportedCoreGates_of_producers hshape hclosC hunit hpay hplanU
      hpre hdeadCkpt hconsumeInv
  exact
  { hbr := hbrF
    hsnapF := hsnapF
    hent := hent
    hdeadCkpt := hdeadCkpt
    hbc := hbc
    hnew := hnew
    hlog := hlog
    hdeadEv := hdeadEv
    hconsumeInv := hconsumeInv
    core := core }

/-- **THE WIRED UNIT-KIT BUILDER, HONEST FORM (I1)**: the `_or_coverless`
twin of `supportedUnitKit_of_premises` — the refuted all-sites
inhabitedness family `hinhab` is replaced by C2a's PREMISE-FREE
classification family `hinhabOr` and C2c's coverless-site level separation
`hsepF`, wired through `HdeadCkpt.supportedHpre_of_unitRun_site_or_coverless`
(§11) at the site and through `supportedHpre_unitKit_of_site_or_coverless`
(§1) for the record's `hpre` field. Everything else is the old builder:
the unit-discipline trio from N1, the four-component joint induction (§0),
E1/L1/J2/R2's run-level producers and the eight-input assembly. -/
theorem supportedUnitKit_of_premises_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedUnitKit orig original props leaf := by
  -- the closure contract at the two spellings the producers take
  have hclosF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig original props :=
    fun _ => hcontract
  have hclosC : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props :=
    fun hreach => by
      rw [SupportedReach.original_eq hreach, SupportedReach.props_eq hreach]
      exact hcontract
  -- N1's unit-discipline trio (SupportedDead §6)
  have hunit : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → UnitDB cfg.branch.learned :=
    supportedHunit_of_unitRun hprops hSupp
  have hpay : UnitPayload original props :=
    supportedHpay_of_unitRun hprops hSupp
  have hplanU : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an → UnitDB [an.learned] :=
    supportedHplanU_of_unitRun hprops hSupp
  -- the extended-`hpre` site producer: the site's checkpoint-at family is
  -- the single site snapshot transported along conflict/analysis/checkpoint
  -- single-valuedness; the site entailment is I1-B's bridge
  have hpreJ : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      CheckpointSnapshot leaf orig cp →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch :=
    fun hreach hbs hsnapS hc ha hcp hp =>
      supportedHpre_of_unitRun_site_or_coverless hprops hSupp hreach hbs
        (fun {_ev'} {_an'} {_cp'} _hc' _ha' hcp' => by
          have hev := Option.some.inj (_hc'.symm.trans hc)
          rw [hev] at _ha'
          have han := Option.some.inj (_ha'.symm.trans ha)
          rw [han] at hcp'
          have hck := Option.some.inj (hcp'.symm.trans hcp)
          rw [hck]
          exact hsnapS)
        (fun hc' ha' => hAnalysisEntail hreach hcontract hbs hc' ha')
        hinhabOr hsepF (hv hreach) hc ha hcp hp
  -- THE FOUR-COMPONENT JOINT INDUCTION (I1): reachability, evidence
  -- entailment, PendingSideInv AND the checkpoint-snapshot chain
  have J : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch ∧
        (∀ {ev : ConflictEvidence}, cfg.conflict = some ev →
          LearnedEntailed leaf ev.learned) ∧
        PendingSideInv orig cfg ∧
        ReachableCpSnapshots leaf orig cfg :=
    supportedReachEvidenceChain_of_premises hclosF hunit hpay hplanU
      (supportedPinGates_of_shape hshape).hpin
      (supportedPinGates_of_shape hshape).hskip hpreJ hshape
  have hbrF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch :=
    fun hreach => (J hreach).1
  -- the chain component (no longer an external family)
  have hsnapF : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableCpSnapshots leaf orig cfg :=
    fun hreach => (J hreach).2.2.2
  -- the site entailment family (I1-B's bridge at the site's ReachableState)
  have hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned] :=
    fun hreach hconf hana => hAnalysisEntail hreach hcontract (hbrF hreach) hconf hana
  -- the `hpre` FIELD of the record (the joint induction consumed `hpreJ`)
  have hpre : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch :=
    supportedHpre_unitKit_of_site_or_coverless hcontract hprops hSupp hsnapF
      hAnalysisEntail hinhabOr hsepF hv
  -- E1 (HdeadCkpt §9) and its L1 dispatcher consumption
  have hdeadCkpt : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp) :=
    supportedHdeadCheckpointRegion_of_reach hbrF hent
  have hnew : SupportedNewRegionsSound orig original props leaf :=
    supportedNewRegionsSound_of_premises hshape hclosC hbrF hdeadCkpt
  have hlog : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
    supportedLogSound_of_newRegions hnew
  -- E1's run-level dead evidence, J2's coverage gate, R2's consume gate
  have hdeadEv : SupportedDeadEvidence orig original props leaf :=
    supportedDeadEvidence_of_premises hclosC hbrF hshape
  have hbc : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis}
      {restored : BranchState leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        BackjumpCovers leaf orig cfg
          (stepLearnBackjumpAssert cfg
            (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
            restored) :=
    supportedHbc_of_recorded_analysis hbrF
  have hconsumeInv : ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame}, SupportedReach orig original props cfg →
      cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
        SchedulerInvariant next :=
    fun hreach hstatus hp hs =>
      supportedHconsumeInv_of_coverage hshape hclosF hunit hpay hplanU hpre hbc
        hnew hreach hstatus hp hs
  -- the eight-input core assembly
  have core : SupportedArmInvGatesCore orig original props leaf :=
    supportedCoreGates_of_producers hshape hclosC hunit hpay hplanU
      hpre hdeadCkpt hconsumeInv
  exact
  { hbr := hbrF
    hsnapF := hsnapF
    hent := hent
    hdeadCkpt := hdeadCkpt
    hbc := hbc
    hnew := hnew
    hlog := hlog
    hdeadEv := hdeadEv
    hconsumeInv := hconsumeInv
    core := core }

/-- **THE CONCRETE CORE-GATE INSTANTIATION (I1 acceptance)**: the
`SupportedArmInvGatesCore` record of the unit kit, every field produced by
a landed producer (module table), from the unit kit and the residual
hypotheses only.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedCoreGates_unitKit {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedArmInvGatesCore orig original props leaf :=
  (supportedUnitKit_of_premises hshape hcontract hprops hSupp hAnalysisEntail
    hinhab hv).core

/-- **THE CONCRETE CORE-GATE INSTANTIATION, HONEST FORM (I1 acceptance)**:
the `_or_coverless` twin of `supportedCoreGates_unitKit` — C2a's
PREMISE-FREE classification family `hinhabOr` plus C2c's coverless-site
level separation `hsepF` replace the refuted `hinhab`, every other
premise unchanged. -/
theorem supportedCoreGates_unitKit_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedArmInvGatesCore orig original props leaf :=
  (supportedUnitKit_of_premises_or_coverless hshape hcontract hprops hSupp
    hAnalysisEntail hinhabOr hsepF hv).core

/-- The shape-typed variant: `SupportedInput` (F1's compiled-input record)
supplies the shape discipline; the closure contract is still P1's
`CompiledInput.closureContract_of_provenance` output.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedCoreGates_unitKit_of_supportedInput {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hin : SupportedInput leaf orig original props)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedArmInvGatesCore orig original props leaf :=
  supportedCoreGates_unitKit hin.shape hcontract hprops hSupp hAnalysisEntail
    hinhab hv

/-- The shape-typed variant, honest form: `SupportedInput` supplies the
shape discipline, C2a's `hinhabOr` + C2c's `hsepF` replace the refuted
`hinhab`. -/
theorem supportedCoreGates_unitKit_of_supportedInput_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hin : SupportedInput leaf orig original props)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedArmInvGatesCore orig original props leaf :=
  supportedCoreGates_unitKit_or_coverless hin.shape hcontract hprops hSupp
    hAnalysisEntail hinhabOr hsepF hv

/-! ## §3 The derived run-level exports (for C2/W1)

The instance's derived producers, exported individually so downstream
tasks (C2's phase Premises, W1's compiled entry) consume them directly
without rebuilding the package. -/

/-- The unit kit's registration-site dispatcher (L1).

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedNewRegionsSound_unitKit {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedNewRegionsSound orig original props leaf :=
  (supportedUnitKit_of_premises hshape hcontract hprops hSupp hAnalysisEntail
    hinhab hv).hnew

/-- The registration-site dispatcher (L1), honest form: C2a's `hinhabOr`
plus C2c's `hsepF` in place of the refuted `hinhab`. -/
theorem supportedNewRegionsSound_unitKit_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedNewRegionsSound orig original props leaf :=
  (supportedUnitKit_of_premises_or_coverless hshape hcontract hprops hSupp
    hAnalysisEntail hinhabOr hsepF hv).hnew

/-- The unit kit's run-level exhaustion-log soundness (L1 × the run
induction `supportedLogSound_of_newRegions`).

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedLogSound_unitKit {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
  (supportedUnitKit_of_premises hshape hcontract hprops hSupp hAnalysisEntail
    hinhab hv).hlog

/-- The run-level exhaustion-log soundness, honest form. -/
theorem supportedLogSound_unitKit_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
  (supportedUnitKit_of_premises_or_coverless hshape hcontract hprops hSupp
    hAnalysisEntail hinhabOr hsepF hv).hlog

/-- The unit kit's run-level dead-site evidence (E1 §4).

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedDeadEvidence_unitKit {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedDeadEvidence orig original props leaf :=
  (supportedUnitKit_of_premises hshape hcontract hprops hSupp hAnalysisEntail
    hinhab hv).hdeadEv

/-- The run-level dead-site evidence (E1 §4), honest form. -/
theorem supportedDeadEvidence_unitKit_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedDeadEvidence orig original props leaf :=
  (supportedUnitKit_of_premises_or_coverless hshape hcontract hprops hSupp
    hAnalysisEntail hinhabOr hsepF hv).hdeadEv

/-- The unit kit's consume-successor invariant (R2 §2-ter, `hcov`
discharged internally).

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedHconsumeInv_unitKit {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame}, SupportedReach orig original props cfg →
      cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
        SchedulerInvariant next :=
  (supportedUnitKit_of_premises hshape hcontract hprops hSupp hAnalysisEntail
    hinhab hv).hconsumeInv

/-- The consume-successor invariant (R2 §2-ter), honest form. -/
theorem supportedHconsumeInv_unitKit_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hAnalysisEntail : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame}, SupportedReach orig original props cfg →
      cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
        SchedulerInvariant next :=
  (supportedUnitKit_of_premises_or_coverless hshape hcontract hprops hSupp
    hAnalysisEntail hinhabOr hsepF hv).hconsumeInv

/-! ## §4 Integration (coordinator): the I1-B entailment bridge plugged in

The residual `hAnalysisEntail` of §1–§3 is DISCHARGED by
`AnalysisEntail.hAnalysisEntail_unitKit` (I1-B), whose premises are the
unit kit equations alone. The wrappers below restate the §2/§3 exports
with the bridge already applied, so downstream consumers (W1) need only
`hshape`/`hcontract`/`hprops`/`hSupp` plus the residual premises. The
originating signatures of §2/§3 are kept intact for consumers that carry
their own entailment derivation.

The `*_discharged` wrappers still carry the REFUTED `hinhab`; the
supported interfaces are the `*_discharged_or_coverless` twins, whose
residuals are exactly `hinhabOr` (PREMISE-FREE — pass
`fun _ => SiteInhabited.supportedInhabited_or_coverless`), `hsepF` (C2)
and `hv` (C1). -/

/-- The `hAnalysisEntail` premise of §1–§3, discharged from the unit kit
by I1-B's bridge (`Proofs/AnalysisEntail.lean`). -/
theorem hAnalysisEntail_unitKit_of {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      ClosureContract leaf orig original props →
      ReachableState leaf orig cfg.branch → cfg.conflict = some ev →
      ev.analysis = some an → LearnedEntailed leaf [an.learned] :=
  fun hreach hcontract hbs hc ha =>
    hAnalysisEntail_unitKit hprops hSupp hreach hcontract hbs hc ha

/-- **THE UNIT-KIT INSTANCE, ENTAILMENT DISCHARGED**: `SupportedUnitKit`
from the kit equations, the compiled shape/closure inputs and the named
residuals (`hinhab` — C2; `hv` — C1) only.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedUnitKit_unitKit_discharged {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedUnitKit orig original props leaf :=
  supportedUnitKit_of_premises hshape hcontract hprops hSupp
    (hAnalysisEntail_unitKit_of hprops hSupp) hinhab hv

/-- **THE UNIT-KIT INSTANCE, ENTAILMENT DISCHARGED, HONEST FORM**: the
residuals are `hinhabOr` (PREMISE-FREE) + `hsepF` (C2) + `hv` (C1). -/
theorem supportedUnitKit_unitKit_discharged_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedUnitKit orig original props leaf :=
  supportedUnitKit_of_premises_or_coverless hshape hcontract hprops hSupp
    (hAnalysisEntail_unitKit_of hprops hSupp) hinhabOr hsepF hv

/-- **THE CONCRETE CORE-GATE INSTANTIATION, ENTAILMENT DISCHARGED**
(I1 acceptance): the eight-input assembly's record with I1-B's bridge
applied, from the kit equations, the compiled inputs and the C2/C1
residuals only.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedCoreGates_unitKit_discharged {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedArmInvGatesCore orig original props leaf :=
  supportedCoreGates_unitKit hshape hcontract hprops hSupp
    (hAnalysisEntail_unitKit_of hprops hSupp) hinhab hv

/-- The eight-input assembly's record, entailment discharged, honest form. -/
theorem supportedCoreGates_unitKit_discharged_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedArmInvGatesCore orig original props leaf :=
  supportedCoreGates_unitKit_or_coverless hshape hcontract hprops hSupp
    (hAnalysisEntail_unitKit_of hprops hSupp) hinhabOr hsepF hv

/-- The registration-site dispatcher, entailment discharged.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedNewRegionsSound_unitKit_discharged {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedNewRegionsSound orig original props leaf :=
  (supportedUnitKit_unitKit_discharged hshape hcontract hprops hSupp
    hinhab hv).hnew

/-- The registration-site dispatcher, entailment discharged, honest form. -/
theorem supportedNewRegionsSound_unitKit_discharged_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedNewRegionsSound orig original props leaf :=
  (supportedUnitKit_unitKit_discharged_or_coverless hshape hcontract hprops
    hSupp hinhabOr hsepF hv).hnew

/-- The run-level exhaustion-log soundness, entailment discharged.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedLogSound_unitKit_discharged {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
  (supportedUnitKit_unitKit_discharged hshape hcontract hprops hSupp
    hinhab hv).hlog

/-- The run-level exhaustion-log soundness, entailment discharged, honest
form. -/
theorem supportedLogSound_unitKit_discharged_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
  (supportedUnitKit_unitKit_discharged_or_coverless hshape hcontract hprops
    hSupp hinhabOr hsepF hv).hlog

/-- The run-level dead-site evidence, entailment discharged.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedDeadEvidence_unitKit_discharged {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedDeadEvidence orig original props leaf :=
  (supportedUnitKit_unitKit_discharged hshape hcontract hprops hSupp
    hinhab hv).hdeadEv

/-- The run-level dead-site evidence, entailment discharged, honest form. -/
theorem supportedDeadEvidence_unitKit_discharged_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    SupportedDeadEvidence orig original props leaf :=
  (supportedUnitKit_unitKit_discharged_or_coverless hshape hcontract hprops
    hSupp hinhabOr hsepF hv).hdeadEv

/-- The consume-successor invariant, entailment discharged.

REFUTED premise (`SiteInhabited.cexNotAllSites`); use the `_or_coverless` variant. -/
theorem supportedHconsumeInv_unitKit_discharged {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhab : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame}, SupportedReach orig original props cfg →
      cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
        SchedulerInvariant next :=
  (supportedUnitKit_unitKit_discharged hshape hcontract hprops hSupp
    hinhab hv).hconsumeInv

/-- The consume-successor invariant, entailment discharged, honest form. -/
theorem supportedHconsumeInv_unitKit_discharged_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hshape : ShapeTypedDomains orig)
    (hcontract : ClosureContract leaf orig original props)
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hinhabOr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        (∃ a : Assignment, FrameCovers cfg.branch.frame a) ∨
          (∃ d ∈ cfg.branch.frame.1, d = []))
    (hsepF : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → (∃ d ∈ cfg.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hv : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      BranchTrailVocabulary orig cfg.branch) :
    ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame}, SupportedReach orig original props cfg →
      cfg.status = .dead → cfg.pending = f :: rest → stepConsume cfg = some next →
        SchedulerInvariant next :=
  (supportedUnitKit_unitKit_discharged_or_coverless hshape hcontract hprops
    hSupp hinhabOr hsepF hv).hconsumeInv

end LeanFzn.Solver.UIP
