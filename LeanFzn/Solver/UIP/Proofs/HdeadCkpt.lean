/-
File: LeanFzn/Solver/UIP/Proofs/HdeadCkpt.lean

Purpose: the E1 `hdeadCheckpointRegion` producer and the index-correct J1
premise producers, at the frozen gate shapes of `SupportedGates` /
`SupportedArmInvGatesCore`.

  §1 `supportedHdeadCheckpointRegion_of_snapshots` (E1): when the runtime
     REJECTS the selected checkpoint (`perform = none`), the selected
     checkpoint's computable frame region `checkpointRegion cp` is SOUND.
     The rejection is characterized exactly by
     `perform_eq_none_iff_filterFrame_eq_none` (a filter failure on the
     checkpoint frame); soundness then follows from the site certificate,
     the checkpoint's reachable snapshot and the surviving-trail premise
     via `restoreAssert_filterFrame_none_excludes`. A failed descendant
     alone does NOT exclude the ancestor region — the certificate + the
     snapshot carry the semantic content, never a raw deadness premise.

  §2 `supportedHpre_of_snapshots` (J1): the index-correct variant of
     `supportedHpre_of_premises` (SupportedProviders.lean): the chain
     premise is consumed as the `ReachableCpSnapshots` bundle
     (`supportedReachableCpSnapshots_of_premises`' conclusion) instead of
     the raw `SchedulerReachable`-indexed `hpush` bundle, so J1/I1 can
     feed a supported-index producer without an index mismatch.

  §3 `supportedHstable_of_reach` (J1): the `hstable` family
     (`an.asserting.norm = an.asserting`) is DERIVED from reachability
     (`reachable_analysis_success` makes the recorded analysis the
     canonical `normalized` record; `normalized_asserting_norm` makes its
     asserting literal stable).

  §4 The `hneg` probe (J1 retained evidence) and the APPLIED restatement:
     `¬ NegStable [posBool 0 true]` is KERNEL-CHECKED, so the whole-clause
     `hneg` family of `supportedHpre_of_premises` is REFUTABLE as stated;
     the honest family `NegStableAvoiding an.asserting an.learned` is what
     the restoration chain consumes and what `supportedHpre_of_snapshots`
     and the `LearnedExplanation` consumers now take
     (`RestorationCertificate.lean` carries the restatement; the legacy
     `NegStable`-typed entry points remain only for the out-of-scope
     callers `Proofs/ConflictResolution.lean` and
     `SupportedProviders.lean`).

NO `sorry`, NO custom axiom.

Registration owes the umbrella import line `LeanFzn.Solver.UIP.Proofs.HdeadCkpt`
in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (owned by the coordinator; not edited here).
-/

import LeanFzn.Solver.UIP.Proofs.SupportedProviders
import LeanFzn.Solver.UIP.Proofs.CheckpointPrefix
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 E1: sound checkpoint-region exclusion at the rejection site -/

/-- **THE `hdeadCheckpointRegion` PRODUCER (E1)**: at every supported
configuration with recorded evidence whose selected checkpoint the runtime
REJECTS (`perform = none`), the computable region `checkpointRegion cp` is
sound — no leaf solution lies in it.

The proof consumes the ACTUAL site pieces, not a deadness premise:

  * `hnone` — the rejection IS a filter failure
    (`perform_eq_none_iff_filterFrame_eq_none`);
  * `hcert` — the restoration certificate at the recording site;
  * `hsnap` — the selected checkpoint is a reachable snapshot (the chain
    bundle of `supportedReachableCpSnapshots_of_premises`);
  * `hsurv` — the surviving-trail premise of the site (entries at or below
    the target level survive into the checkpoint trail).

The semantic content: a leaf solution covered by the checkpoint frame
satisfies every surviving trail entry (snapshot `agrees` transported
across the frame/trail equalities), hence by the certificate's UNIT
property it satisfies the asserting literal; but the failed filter
refuses every covered assignment (its unit property makes
`filterFrame_none_excludes` apply). Contradiction. In particular the
region is excluded by the LEARNED ANALYSIS's semantic content, not by the
descendant's failure. -/
theorem supportedHdeadCheckpointRegion_of_snapshots {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hsnaps : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableCpSnapshots leaf orig cfg)
    (hcert : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp) := by
  intro cfg cp ev an hreach hconf hana hcp hp
  -- the rejection IS a filter failure on the checkpoint frame
  have hnone : filterFrame an.asserting cp.frame = none :=
    perform_eq_none_iff_filterFrame_eq_none.mp hp
  -- the selected checkpoint is a reachable snapshot of this run's box
  have hsnap : CheckpointSnapshot leaf orig cp :=
    hsnaps hreach cp (checkpointAt_mem hcp)
  have hcert' : RestorationCertificate leaf cfg.branch an :=
    hcert hreach hconf hana
  have hsv : ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel →
      e ∈ cp.trail := hsurv hreach hconf hana hcp
  show DeadRegion.Sound leaf (DeadRegion.byFrame cp.frame)
  refine DeadRegion.byFrame_sound (fun a hleaf hcov => ?_)
  -- the certificate's unit property + the failed filter exclude `a`
  refine restoreAssert_filterFrame_none_excludes hcert' hnone a hleaf ?_ hcov
  intro e he hlev
  obtain ⟨bs', hbs', hf, ht, _⟩ := hsnap
  have hecp : e ∈ cp.trail := hsv e he hlev
  have he' : e ∈ bs'.trail := by rw [ht]; exact hecp
  have hcov' : FrameCovers bs'.frame a := by rw [hf]; exact hcov
  exact hbs'.agrees e he' a hcov'

/-! ## §2 J1: the index-correct `hpre` producer -/

/-- **THE INDEX-CORRECT `hpre` PRODUCER**: `supportedHpre_of_premises`
(SupportedProviders §3-bis) consumes the raw `SchedulerReachable`-indexed
push bundle `hpush`; at supported sites the chain is available as the
`ReachableCpSnapshots` bundle instead
(`supportedReachableCpSnapshots_of_premises`'s conclusion with the joint
induction's branch-reachability component). This variant takes that bundle
DIRECTLY, so J1/I1 can instantiate it from a supported-index producer with
no `SchedulerReachable` index mismatch and no snapshot transport (the
bundle is already stated at the run's fixed box `orig`).

The six site-premise families (`hcert`, `hstable`, `hneg`, `hsurv`,
`hfresh`, `hrange`) are copied verbatim from
`supportedHpre_of_premises`; the successful-perform equation is the
runtime's own `some restored` branch, and `hbs` is the per-site branch
reachability the restored database's entailment needs. -/
theorem supportedHpre_of_snapshots {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hsnaps : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableCpSnapshots leaf orig cfg)
    (hcert : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hstable : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.norm = an.asserting)
    (hneg : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        NegStableAvoiding an.asserting an.learned)
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hfresh : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm)
    (hrange : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.atom.slot < orig.length) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis} {restored : BranchState leaf},
      SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = some restored →
        RestorationPreReachable leaf orig
          (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
          cfg.branch := by
  intro cfg cp ev an restored hreach hbs hconf hana hcp hp
  have hsnap : CheckpointSnapshot leaf orig cp :=
    hsnaps hreach cp (checkpointAt_mem hcp)
  exact restorationPreReachable_of_success_avoiding hsnap hbs
    (hcert hreach hconf hana)
    (hstable hreach hconf hana) (hneg hreach hconf hana)
    (hsurv hreach hconf hana hcp) (hfresh hreach hconf hana hcp)
    (hrange hreach hconf hana) hp

/-! ## §3 J1: the `hstable` producer from reachability -/

/-- **THE `hstable` PRODUCER**: at every supported configuration with
recorded evidence, the recorded analysis's asserting literal is
normalization-stable. N1's provenance makes the record CANONICAL
(`reachable_analysis_success`: the recorded `an` is
`(ofUIP below uip).normalized`), and
`ConflictAnalysis.normalized_asserting_norm` shows the canonical record's
asserting literal is its own normal form. No premise remains: this
discharges the `hstable` family of `supportedHpre_of_premises`. -/
theorem supportedHstable_of_reach {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool} :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → an.asserting.norm = an.asserting := by
  intro cfg ev an hreach hconf hana
  obtain ⟨below, uip, -, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  rw [hcanon]
  exact ConflictAnalysis.normalized_asserting_norm _

/-! ## §4 The `hneg` probe and the RESTATEMENT (J1 round 2) -/

/-- RETAINED EVIDENCE (J1): the whole-clause `hneg` family is REFUTABLE as
stated. `posBool s b` is a normal form whose negation is not: its negate
is the negative literal `¬(b = s)`, which normalizes to `s = !b`. So
`NegStable [posBool 0 true]` is FALSE, kernel-checked below. (The dual
instance `boolUip_norm_gap` in `RestorationCertificate.lean` records the
same gap for `posBool 0 false`.)

THE REPAIR (APPLIED in `RestorationCertificate.lean`, this round): the
restoration chain only ever consumes the guard on NON-ASSERTING learned
literals — `restore_chronology_of_certificate` derives `q ≠ an.asserting`
from the `q ≠ an.asserting.norm` its conclusion carries before applying
it. The honest family is

  `NegStableAvoiding an.asserting an.learned`,
  i.e. `∀ q ∈ an.learned, q ≠ an.asserting → (q.negate).norm = q.negate`,

which `restore_chronology_of_certificate` /
`restore_filter_chronology_of_certificate` and all three
`LearnedExplanation` consumers now take (`restore_chronology_of_NegStable`
/ `restore_filter_chronology_of_NegStable` remain as documented thin
wrappers for the out-of-scope `Proofs/ConflictResolution.lean` caller and
`supportedHpre_of_premises` in the not-yet-released
`SupportedProviders.lean`). For the UNIT fragment the restated family is
discharged with NO premise: the recorded analysis's learned clause IS the
singleton of its asserting literal, so the non-asserting part is empty —
see §6 `supportedHnegAvoiding_of_unitRun` below. -/
theorem negStable_posBool_refuted : ¬ NegStable [posBool 0 true] := by
  intro h
  have h0 := h (posBool 0 true) (List.mem_singleton_self _)
  exact absurd h0 (by decide)

/-! ## §5 STRETCH: the `hcert` producer from reachability + entailment -/

/-- Entailment transfers back across literal normalization: a clause
satisfied by every leaf solution in normalized form is satisfied in
original form (`Literal.norm_eval`), so the canonical record's
`learnedEntailed` lifts to the raw analyzer record. -/
theorem learnedEntailed_of_map_norm {leaf : Assignment → Bool} {c : Clause}
    (h : LearnedEntailed leaf [c.map Literal.norm]) :
    LearnedEntailed leaf [c] := by
  intro c' hc' a hleaf
  rw [List.mem_singleton] at hc'
  rw [← hc'] at h
  obtain ⟨l, hl, hev⟩ :=
    h (c'.map Literal.norm) (List.mem_singleton_self _) a hleaf
  rw [List.mem_map] at hl
  obtain ⟨q, hq, rfl⟩ := hl
  exact ⟨q, hq, by rw [← Literal.norm_eval]; exact hev⟩

/-- **THE `hcert` PRODUCER (stretch)**: from the joint supported
induction's branch-reachability component and the named leaf-level
entailment premise of the recorded analysis, the restoration certificate
at every supported recorded-evidence site. No certificate content is
assumed: the record is canonicalized by provenance
(`reachable_analysis_success`), the raw certificate is built by the
landed computed-allowance constructor
(`analyzeAtAllowance_certificate`, whose `hanL`/`hanA`/`hanB` are `rfl`
for `ConflictAnalysis.ofUIP`), the positive-level ingredient is
`recorded_conflict_level_pos`, and the canonical transfer is
`RestorationCertificate.normalized`. The only semantic premise is `hent`
— the named D1a-style leaf entailment of the analysis's learned clause. -/
theorem supportedHcert_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned]) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → RestorationCertificate leaf cfg.branch an := by
  intro cfg ev an hreach hconf hana
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  have hmap : LearnedEntailed leaf
      [((ConflictAnalysis.ofUIP below uip).learned).map Literal.norm] := by
    have h := hent hreach hconf hana
    rwa [hcanon, ConflictAnalysis.normalized_learned] at h
  have hent0 : LearnedEntailed leaf
      [(ConflictAnalysis.ofUIP below uip).learned] :=
    learnedEntailed_of_map_norm hmap
  have hcert0 : RestorationCertificate leaf cfg.branch
      (ConflictAnalysis.ofUIP below uip) :=
    analyzeAtAllowance_certificate (hbr hreach)
      (recorded_conflict_level_pos hreach.reachable ev hconf) hrun
      rfl rfl rfl hent0
  rw [hcanon]
  exact RestorationCertificate.normalized hcert0

/-! ## §6 J1: the unit-fragment producers and the maximal instantiation

The unit fragment's SUPPLY of the `hpre` families. Under the supported kit
(`props = dcs.filterMap propagatorOfProved`, every `unitFamilyB dc = true`)
the recorded event's clause is a normalized singleton, so:

  * `supportedLearned_eq_asserting_of_unitRun` — the recorded analysis's
    learned clause IS `[an.asserting]` (the N1 singleton-analysis shape);
  * `supportedHneg_of_unitRun` — the `hneg` family of
    `supportedHpre_of_snapshots` is DISCHARGED with no premise (the
    non-asserting part is empty);
  * `supportedHstable_of_reach` — the `hstable` family is DISCHARGED
    (landed in §3).

`supportedHpre_of_unitRun` assembles the maximal instantiation: the two
discharged families plus the four honest residual families (`hcert` via
`supportedHcert_of_premises`, whose `hent` is the D1 entailment premise;
`hsurv`/`hfresh`/`hrange`). No restoration conclusion is assumed and
`RestorationPreReachable` is unchanged. -/

/-- **UNIT-FRAGMENT LEARNED SHAPE (J1)**: under the supported kit, the
recorded analysis's learned clause is EXACTLY the singleton of its
asserting literal. The proof is the N1 chain: the event's clause is a
normalized singleton (`.recorded`), the recorded analysis is the
canonical `(ofUIP below uip).normalized` (`reachable_analysis_success`),
`analyzeAtAllowance_singleton_below` empties the below list, and the
canonical record's learned clause is `[(uip.negate).norm]` — while its
asserting literal is `(uip.negate).norm` as well. -/
theorem supportedLearned_eq_asserting_of_unitRun {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → an.learned = [an.asserting] := by
  intro cfg ev an hreach hc ha
  obtain ⟨q, hq, -⟩ :=
    (unitRunInvariant_of_reachable (leaf := leaf) hSupp hreach.reachable
      (by rw [SupportedReach.props_eq hreach, hprops])).recorded ev hc |>.1
  obtain ⟨below, uip, hrun, heq⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hc ha
  rw [hq] at hrun
  obtain ⟨q', hq', -⟩ := unitLearned_ofUIP_normalized_of_singleton hrun
  have hass : an.asserting = (uip.negate).norm := by
    rw [heq, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting]
  have hq'e : q' = (uip.negate).norm := by
    have hmem : (uip.negate).norm ∈
        (ConflictAnalysis.ofUIP below uip).normalized.learned := by
      rw [ConflictAnalysis.normalized_learned, ConflictAnalysis.ofUIP_learned]
      simp
    rw [hq'] at hmem
    exact (by simpa using hmem : (uip.negate).norm = q').symm
  have hl' : an.learned = [q'] := by rw [heq, hq']
  have has' : an.asserting = q' := by rw [hass, ← hq'e]
  rw [hl', has']

/-- **THE `hneg` FAMILY OF THE UNIT FRAGMENT (J1, NO PREMISE)**: the
restated negation-stability condition holds vacuously — the learned
clause is the singleton of the asserting literal, so it has no
non-asserting member. -/
theorem supportedHneg_of_unitRun {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an →
        NegStableAvoiding an.asserting an.learned := by
  intro cfg ev an hreach hc ha
  exact negStableAvoiding_of_learned_eq_singleton
    (supportedLearned_eq_asserting_of_unitRun hprops hSupp hreach hc ha)

/-- **THE MAXIMAL UNIT-FRAGMENT INSTANTIATION OF `supportedHpre_of_snapshots`
(J1 acceptance).** At the supported index of the unit kit the `hstable`
family is discharged (`supportedHstable_of_reach`) and the `hneg` family is
discharged from the unit-run shape (`supportedHneg_of_unitRun`); the
`hcert` family is produced from the branch-reachability family plus the
named D1 entailment premise (`supportedHcert_of_premises`). The remaining
three families are explicit, honestly named premises of THIS theorem:

  * `hsurv` — the surviving-trail (checkpoint identity) family. NOT
    derivable from the site's `checkpointAt` data: see §7's finding — the
    non-strict level bound is exactly the boundary that `Identifies`
    leaves open (mid entries AT the target level);
  * `hfresh` — the enqueue absence check (S5/E3; the certificate's
    `assertingSurvives` speaks about the NEGATION, so it cannot supply it,
    `restore_filter_enqueue_distinct`);
  * `hrange` — the asserting literal's in-range slot; the unit fragment
    reaches it from the UIP trail entry once a trail-literal slot-range
    invariant is available (named residual, see the §6 docstring of
    `supportedHpre_of_unitRun`'s report).

Everything else is constructed: the snapshot bundle via `hsnaps`, the
success guard via the runtime's own `some restored` equation. No
restoration conclusion is assumed and `RestorationPreReachable` is not
weakened. -/
theorem supportedHpre_of_unitRun {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hsnaps : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableCpSnapshots leaf orig cfg)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned])
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hfresh : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm)
    (hrange : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.atom.slot < orig.length) :
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
  supportedHpre_of_snapshots hsnaps
    (supportedHcert_of_premises hbr hent)
    (fun hreach hconf hana =>
      supportedHstable_of_reach hreach hconf hana)
    (fun hreach hconf hana =>
      supportedHneg_of_unitRun hprops hSupp hreach hconf hana)
    hsurv hfresh hrange

/-! ## §7 J1: the `hsurv` target-level boundary (finding + kernel witnesses)

The site family `hsurv` is stated with the NON-STRICT level bound. This
section determines exactly what the boundary case costs:

  * `identifies_survives_strict` — the checkpoint identity data
    (`DecisionCheckpoint.Identifies`) gives the STRICT half for free;
  * `othersBelow_falsifier_at_target` — the CERTIFICATE itself guarantees,
    at every positive target level, a NON-asserting learned literal whose
    falsifier sits at EXACTLY the target level (`targetAttained` +
    `assertingSurvives`). The level-`target` case is therefore
    LOAD-BEARING: the chronology's falsifier set cannot be covered by a
    strict bound;
  * `strict_hsurv_insufficient_for_chronology` — the kernel-checked
    witness: all the non-`hsurv` site data (a genuine certificate, stable
    asserting normalization, the honest `NegStableAvoiding` family) PLUS
    the strict bound are consistent with the chronology conclusion FAILING.
    So `restore_chronology_of_certificate` cannot consume a strict `hsurv`,
    and the non-strict family cannot be weakened.

HONEST RESTATEMENT PROPOSAL (for the coordinator; no file outside J1's
scope is edited): the non-strict `hsurv` is specifiable only where the
checkpoint trail contains every level-`target` entry of the branch trail,
i.e. where `Identifies`'s `mid` sits STRICTLY above the target. The two
kernel-checked repairs are (a) strengthen the runtime's checkpoint
identification to the strict-mid form (`mid` entries at `> target`, not
`≥ target`) and keep the non-strict family, or (b) restore through the
LEVEL FILTER (`BranchState.restoredTrail`, `restoreLevel`), where the
chronology is `hsurv`-FREE
(`restore_filter_chronology_of_certificate_avoiding`). Route (b) is the
standard CDCL backjump semantics and is consonant with the pending R2
resume repair (frame/orig-derived falsifiers, `PendingRun.lean` §4). -/

/-- STRICT SURVIVAL FROM CHECKPOINT IDENTITY: `Identifies` gives the
STRICT half of the surviving-trail family for free — every entry strictly
below the target is a checkpoint entry, because mid entries sit at or
above the target. -/
theorem identifies_survives_strict {leaf : Assignment → Bool}
    {cp : DecisionCheckpoint leaf} {bs : BranchState leaf} {target : Nat}
    (hident : cp.Identifies bs target) :
    ∀ e ∈ bs.trail, e.level < target → e ∈ cp.trail := by
  obtain ⟨-, ⟨mid, htrail, hmid⟩, -⟩ := hident
  intro e he hlt
  rw [htrail] at he
  rcases List.mem_append.mp he with h | h
  · exact h
  · exact absurd (hmid e h) (by omega)

/-- NECESSITY OF THE BOUNDARY (J1): at every POSITIVE target level the
certificate itself names a NON-ASSERTING learned literal falsified at
EXACTLY the target level. (`targetAttained` gives an entry at the target
level falsifying a learned literal; `assertingSurvives` forbids that
literal to be the asserting one, since the target is a surviving level.)
Hence no strict bound `e.level < target → e ∈ cpTrail` can cover every
falsifier the chronology needs. -/
theorem othersBelow_falsifier_at_target {leaf : Assignment → Bool}
    {bs : BranchState leaf} {an : ConflictAnalysis}
    (hcert : RestorationCertificate leaf bs an)
    (hpos : 0 < an.backjumpLevel) :
    ∃ q ∈ an.learned, q ≠ an.asserting ∧
      ∃ e ∈ bs.trail, e.level = an.backjumpLevel ∧
        e.literal = (q.negate).norm := by
  rcases hcert.targetAttained with h0 | ⟨e, he, hlev, q, hq, hlit⟩
  · omega
  · refine ⟨q, hq, ?_, e, he, hlev, hlit⟩
    intro hqa
    rw [hqa] at hlit
    exact hcert.assertingSurvives e he (hlev ▸ Nat.le_refl _) hlit

private def hsurvLeaf : Assignment → Bool := fun _ => false

private def hsurvQ : Literal := posLe 0 3

private def hsurvA : Literal := posBool 1 true

private def hsurvEq : TrailEntry :=
  { literal := (hsurvQ.negate).norm, level := 1, reason := none }

private def hsurvEa : TrailEntry :=
  { literal := (hsurvA.negate).norm, level := 2, reason := none }

private def hsurvBs : BranchState hsurvLeaf :=
  { frame := ([[Value.bool true]], []), trail := [hsurvEq, hsurvEa],
    level := 2, learned := [] }

private def hsurvAn : ConflictAnalysis :=
  { learned := [hsurvQ, hsurvA], backjumpLevel := 1, asserting := hsurvA }

private theorem hsurvQ_lit_ne_a :
    (hsurvQ.negate).norm ≠ (hsurvA.negate).norm := by
  show (negLe 0 3) ≠ (posBool 1 false)
  decide

private theorem hsurvQ_ne_a : hsurvQ ≠ hsurvAn.asserting.norm := by
  show (posLe 0 3) ≠ (posBool 1 true)
  decide

/-- THE WITNESS CERTIFICATE: every field of `RestorationCertificate` holds
for the concrete boundary data — the `leaf` is constantly false, so the
three semantic fields are vacuous; the two trail entries falsify `hsurvQ`
(level 1 = the target) and the asserting `hsurvA` (level 2 = the conflict
level) respectively. -/
private theorem hsurvCertificate :
    RestorationCertificate hsurvLeaf hsurvBs hsurvAn where
  assertingMem := List.mem_cons_of_mem _ (List.mem_singleton_self _)
  learnedEntailed := by
    intro c' _ a hleaf
    simp [hsurvLeaf] at hleaf
  learnedFalsified := by
    intro p hp
    rw [show hsurvAn.learned = [hsurvQ, hsurvA] from rfl] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · exact ⟨hsurvEq, by simp [hsurvBs], rfl⟩
    · rw [List.mem_singleton] at hp
      subst hp
      exact ⟨hsurvEa, by simp [hsurvBs], rfl⟩
  assertingAtConflict :=
    ⟨hsurvEa, by simp [hsurvBs], rfl, rfl⟩
  othersBelow := by
    intro p hp hne
    rw [show hsurvAn.learned = [hsurvQ, hsurvA] from rfl] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · refine ⟨⟨hsurvEq, by simp [hsurvBs], ?_, rfl⟩, ?_⟩
      · show (1 : Nat) ≤ 1
        omega
      · intro e he hlev
        rw [show hsurvBs.trail = [hsurvEq, hsurvEa] from rfl] at he
        rcases List.mem_cons.mp he with rfl | he
        · rw [show hsurvEq.level = 1 from rfl,
            show hsurvBs.level = 2 from rfl] at hlev
          omega
        · rw [List.mem_singleton] at he
          subst he
          exact fun h => hsurvQ_lit_ne_a h.symm
    · rw [List.mem_singleton] at hp
      subst hp
      exact absurd rfl hne
  targetLegal := by
    show (1 : Nat) ≤ 2
    omega
  targetDescends := by
    right
    show (1 : Nat) < 2
    omega
  targetMaximal := by
    intro p hp hne e he hlit
    rw [show hsurvAn.learned = [hsurvQ, hsurvA] from rfl] at hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rw [show hsurvBs.trail = [hsurvEq, hsurvEa] from rfl] at he
      rcases List.mem_cons.mp he with rfl | he
      · show (1 : Nat) ≤ 1
        omega
      · rw [List.mem_singleton] at he
        subst he
        exact absurd hlit (fun h => hsurvQ_lit_ne_a h.symm)
    · rw [List.mem_singleton] at hp
      subst hp
      exact absurd rfl hne
  assertingSurvives := by
    intro e he hlev hlit
    rw [show hsurvBs.trail = [hsurvEq, hsurvEa] from rfl] at he
    rcases List.mem_cons.mp he with rfl | he
    · exact hsurvQ_lit_ne_a hlit
    · rw [List.mem_singleton] at he
      subst he
      rw [show hsurvEa.level = 2 from rfl,
        show hsurvAn.backjumpLevel = 1 from rfl] at hlev
      omega
  unitAfterRestore := by
    intro a hleaf
    simp [hsurvLeaf] at hleaf
  conservation := by
    intro a hleaf
    simp [hsurvLeaf] at hleaf
  targetAttained :=
    Or.inr ⟨hsurvEq, by simp [hsurvBs], rfl, hsurvQ,
      List.mem_cons_self .., rfl⟩

/-- **STRICT `hsurv` IS INSUFFICIENT (J1, kernel-checked)**: there is a
genuine certificate + stable asserting normalization + the honest
`NegStableAvoiding` family + the STRICT surviving bound, at which the
chronology conclusion of `restore_chronology_of_certificate` is FALSE
(its only needed falsifier sits at the target level, and the checkpoint
trail is empty). Consequence: the strict form cannot replace the
non-strict family; the boundary content must be carried by the site
(restatement proposal in the §7 header). -/
theorem strict_hsurv_insufficient_for_chronology :
    ∃ (bs : BranchState hsurvLeaf) (an : ConflictAnalysis)
      (cpTrail : List TrailEntry),
      RestorationCertificate hsurvLeaf bs an ∧
      an.asserting.norm = an.asserting ∧
      NegStableAvoiding an.asserting an.learned ∧
      (∀ e ∈ bs.trail, e.level < an.backjumpLevel → e ∈ cpTrail) ∧
      ¬ (∀ q ∈ an.learned, q ≠ an.asserting.norm →
          ∃ e' ∈ cpTrail, e'.literal = q.negate) := by
  refine ⟨hsurvBs, hsurvAn, [], hsurvCertificate, ?_, ?_, ?_, ?_⟩
  · show (posBool 1 true).norm = posBool 1 true
    rfl
  · intro q hq hne
    rw [show hsurvAn.learned = [hsurvQ, hsurvA] from rfl] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · show ((posLe 0 3).negate).norm = (posLe 0 3).negate
      rfl
    · rw [List.mem_singleton] at hq
      exact absurd hq hne
  · intro e he hlt
    rw [show hsurvBs.trail = [hsurvEq, hsurvEa] from rfl] at he
    rcases List.mem_cons.mp he with rfl | he
    · rw [show hsurvEq.level = 1 from rfl,
        show hsurvAn.backjumpLevel = 1 from rfl] at hlt
      omega
    · rw [List.mem_singleton] at he
      subst he
      rw [show hsurvEa.level = 2 from rfl,
        show hsurvAn.backjumpLevel = 1 from rfl] at hlt
      omega
  · intro h
    obtain ⟨e', he', -⟩ := h hsurvQ (List.mem_cons_self ..) hsurvQ_ne_a
    cases he'

/-! ## §8 E1: the concrete failed-checkpoint exclusion producer

`supportedHdeadCheckpointRegion_of_snapshots`'s certificate and snapshot
premises are now DISCHARGED from the run's branch-reachability component
(`supportedReachableCpSnapshots_of_premises` for the snapshot bundle,
`supportedHcert_of_premises` for the certificate), leaving the
survivor family `hsurv` as the single named premise — the honest residual
per the §7 finding (the chronology genuinely needs the LOOSE bound;
a strict-bound restatement is provably insufficient). -/
theorem supportedHdeadCheckpointRegion_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned])
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp) :=
  supportedHdeadCheckpointRegion_of_snapshots
    (supportedReachableCpSnapshots_of_premises hbr)
    (supportedHcert_of_premises hbr hent) hsurv

/-! ## §9 J1 round 3: the DERIVED survivors and the E1 acceptance wiring

`CheckpointPrefix.lean` (J1 round 3) proves the run-level STRICT
checkpoint-prefix invariant (`checkpointsStrictPrefix_of_reach`) and the
three producers:

  * `supportedHsurv_of_cert` — the loose-bound survivor family from the
    site certificate (strict-mid from the invariant, `targetDescends`
    from the certificate; entries exactly at the target level included);
  * `supportedHfresh_of_reach` — the enqueue absence check from the UIP
    witness (`analyzeStep_uip_on_trail`) plus the single premise
    `hinhab` = RECORDED-SITE INHABITEDNESS of the branch frame (C2's
    owed obligation, PLAN.md C2);
  * `supportedHrange_of_premises` — the asserting slot range from C1's
    run-wide trail vocabulary (`BranchTrailVocabulary`) plus the new
    pool slot-range lemma (`litPool_slot_lt`).

This section exports at the CONSUMER index:

  * `supportedHsurv_of_reach` — the `hsurv` family from `hbr` + `hent`
    (the certificate is `supportedHcert_of_premises`' own output), so the
    E1 acceptance shape carries exactly the landed consumers' premises;
  * `supportedHdeadCheckpointRegion_of_reach` — E1 ACCEPTANCE: the
    failed-checkpoint exclusion at the supported index with NO survivor
    premise and NO assumed region deadness;
  * `supportedHpre_of_unitRun_reach` — the maximal derived `hpre`
    instantiation: the snapshot bundle and the `hcert`/`hstable`/`hneg`/
    `hsurv`/`hfresh`/`hrange` families all DERIVED, leaving only the unit
    kit (`hprops`/`hSupp`), the branch-reachability family, the D1
    entailment `hent`, the inhabitedness `hinhab` and the C1 vocabulary
    `hv`. `supportedHpre_of_unitRun` (§6) is retained unchanged as the
    named-premise reference instantiation. -/

/-- **THE `hsurv` FAMILY FROM `hbr` + `hent`** (J1 round 3 acceptance):
the loose-bound survivor condition at every supported recorded-evidence
site, with the certificate produced by `supportedHcert_of_premises`
(`supportedHcert_of_premises hbr hent`) and the strict invariant of
`checkpointsStrictPrefix_of_reach` doing the survivor work. No strict
restatement: entries exactly at the target level are covered. -/
theorem supportedHsurv_of_reach {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned]) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail :=
  supportedHsurv_of_cert (supportedHcert_of_premises hbr hent)

/-- **E1 ACCEPTANCE (J1 round 3)**: the concrete failed-checkpoint
exclusion at the supported index. Premises: exactly the joint
induction's branch-reachability family `hbr` and the D1 entailment
`hent` — the restoration certificate, the snapshot bundle and the
survivor family are all DERIVED (`supportedHcert_of_premises`,
`supportedReachableCpSnapshots_of_premises`, `supportedHsurv_of_reach`).
No region deadness and no survivor premise is assumed. -/
theorem supportedHdeadCheckpointRegion_of_reach {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned]) :
    ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp) :=
  supportedHdeadCheckpointRegion_of_premises hbr hent
    (supportedHsurv_of_reach hbr hent)

/-- **THE MAXIMAL DERIVED `hpre` INSTANTIATION (J1 round 3)**: the unit
fragment's restoration pre-reachability with every family of
`supportedHpre_of_snapshots` DERIVED except the two named honest
prerequisites of this round:

  * `hinhab` — recorded-site inhabitedness of the branch frame (C2's
    obligation; consumed by `supportedHfresh_of_reach`);
  * `hv` — C1's run-wide trail vocabulary (consumed by
    `supportedHrange_of_premises`);

plus the joint induction's `hbr`, the D1 entailment `hent` and the unit
kit (`hprops`/`hSupp`, which discharges `hneg` via
`supportedHneg_of_unitRun`). The snapshot bundle
(`supportedReachableCpSnapshots_of_premises`), `hcert`
(`supportedHcert_of_premises`), `hstable` (`supportedHstable_of_reach`),
`hsurv` (`supportedHsurv_of_reach`) and `hrange`
(`supportedHrange_of_premises`) are produced here. -/
theorem supportedHpre_of_unitRun_reach {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned])
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
  supportedHpre_of_snapshots
    (supportedReachableCpSnapshots_of_premises hbr)
    (supportedHcert_of_premises hbr hent)
    (fun hreach hconf hana => supportedHstable_of_reach hreach hconf hana)
    (fun hreach hconf hana =>
      supportedHneg_of_unitRun hprops hSupp hreach hconf hana)
    (supportedHsurv_of_reach hbr hent)
    (supportedHfresh_of_reach hbr hinhab)
    (supportedHrange_of_premises hbr hv)

/-! ## §10 I1: the SITE-LEVEL twins (circularity breakers)

The §5/§9 producers take their `hbr`/`hent` inputs as RUN FAMILIES
(`∀ {cfg}, SupportedReach … cfg → …`), so none of them can be applied
INSIDE the joint reachability/evidence induction
(`SupportedArms.supportedReachAndEvidence_of_premises` §0), whose per-step
context supplies only the site's own facts: `hreach : SupportedReach … cfg`
(the pre-state), `hbs` (its `ReachableState`, the triple's first component)
and — once the induction carries the chain component — the selected
checkpoint's `CheckpointSnapshot`. The twins below are the SAME proofs with
every family argument replaced by the site fact, so an `hpre` producer of
the joint induction's site shape is built from exactly:

  * the site's `SupportedReach` (run-level strict-prefix/provenance lemmas);
  * the site's `ReachableState` (the triple's first component);
  * the selected checkpoint's `CheckpointSnapshot` (chain component);
  * the site entailment `LearnedEntailed leaf [an.learned]` (D1/I1-B
    analysis-entailment bridge at the site);
  * the site frame inhabitedness (C2's `hinhab` at the site);
  * the site trail vocabulary (C1's `hv` at the site).

No family input remains. The twins are verbatim specializations of the
landed family producers (`supportedHcert_of_premises`,
`supportedHsurv_of_cert`, `supportedHfresh_of_reach`,
`supportedHrange_of_premises`, `supportedHdeadCheckpointRegion_of_snapshots`,
`supportedHpre_of_snapshots`); no statement is weakened and no proof step
is new. -/

/-- **THE `hcert` PRODUCER, SITE FORM**: the restoration certificate at ONE
supported recorded-evidence site from the site's branch reachability and
the site entailment (the family producer's proof applied at the site). -/
theorem supportedHcert_of_site {orig : List Domain} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    (hb : cfg.branch = bs) (hbs : ReachableState leaf orig bs)
    (hreach : SchedulerReachable cfg)
    (hentSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned]) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an := by
  intro ev an hconf hana
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach hconf hana
  have hmap : LearnedEntailed leaf
      [((ConflictAnalysis.ofUIP below uip).learned).map Literal.norm] := by
    have h := hentSite hconf hana
    rwa [hcanon, ConflictAnalysis.normalized_learned] at h
  have hent0 : LearnedEntailed leaf
      [(ConflictAnalysis.ofUIP below uip).learned] :=
    learnedEntailed_of_map_norm hmap
  have hcert0 : RestorationCertificate leaf cfg.branch
      (ConflictAnalysis.ofUIP below uip) :=
    analyzeAtAllowance_certificate (show ReachableState leaf orig cfg.branch from
        hb ▸ hbs)
      (recorded_conflict_level_pos hreach ev hconf) hrun rfl rfl rfl hent0
  rw [hcanon]
  exact RestorationCertificate.normalized hcert0

/-- **THE `hsurv` PRODUCER, SITE FORM**: the loose-bound survivor condition
at ONE supported recorded-evidence site from the site certificate (the
`supportedHsurv_of_cert` proof applied at the site; the strict-prefix
invariant is run-level). -/
theorem supportedHsurv_of_site {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (hcertSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis}
      {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail := by
  intro ev an cp hconf hana hcp e he hle
  have hlt : an.backjumpLevel < cfg.branch.level := by
    have hd := (hcertSite hconf hana).targetDescends
    have hp := recorded_conflict_level_pos hreach.reachable ev hconf
    rcases hd with h0 | h
    · omega
    · exact h
  obtain ⟨mid, hmid, hmidlev⟩ := checkpointsStrictPrefix_of_reach hreach hcp hlt
  rw [hmid] at he
  rcases List.mem_append.mp he with h | h
  · exact h
  · exact absurd (hmidlev e h) (by omega)

/-- **THE `hfresh` PRODUCER, SITE FORM**: the enqueue absence check at ONE
supported recorded-evidence site from the site's branch reachability and
the site frame inhabitedness (C2's obligation at the site). -/
theorem supportedHfresh_of_site {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    (hb : cfg.branch = bs) (hbs : ReachableState leaf orig bs)
    (hreach : SupportedReach orig original props cfg)
    (hinhabSite : ∃ a : Assignment, FrameCovers bs.frame a) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis}
      {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  intro ev an cp hconf hana hcp e he hcon
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  have hass : an.asserting.norm = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting, norm_norm]
  have hel : e.literal = (uip.negate).norm := by rw [hcon, hass]
  obtain ⟨hident, -⟩ := identifiesChain_of_reach hreach
  obtain ⟨mid, hmid, -⟩ := (hident cp (checkpointAt_mem hcp)).2.1
  have he' : e ∈ bs.trail := by
    rw [← hb, hmid]
    exact List.mem_append.mpr (Or.inl he)
  have hrun' := hrun
  unfold analyzeAtAllowance at hrun'
  obtain ⟨m, hm, hmlit, -⟩ :=
    analyzeStep_uip_on_trail cfg.branch.trail cfg.branch.level
      (analysisFuel cfg.branch.trail ev.clause) [ev.clause] none [] []
      (analyzerInvariant_init cfg.branch.trail cfg.branch.level) below uip hrun'
  have hm' : m ∈ bs.trail := by rw [← hb]; exact hm
  obtain ⟨a, hcov⟩ := hinhabSite
  have h1 : (uip.negate).eval a = some true := by
    have h := hbs.agrees e he' a hcov
    rw [hel, Literal.norm_eval] at h
    exact h
  have h2 : uip.eval a = some false :=
    (Literal.eval_negate_false_iff uip a).mp h1
  have h3 : uip.eval a = some true := by
    have h := hbs.agrees m hm' a hcov
    rwa [hmlit] at h
  rw [h2] at h3
  cases h3

/-- **THE `hrange` PRODUCER, SITE FORM**: the recorded asserting literal's
slot range at ONE supported recorded-evidence site from the site's branch
reachability and the site trail vocabulary (C1's `hv` at the site). -/
theorem supportedHrange_of_site {orig : List Domain} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    (hb : cfg.branch = bs) (hbs : ReachableState leaf orig bs)
    (hreach : SchedulerReachable cfg)
    (hvSite : BranchTrailVocabulary orig bs) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        an.asserting.atom.slot < orig.length := by
  intro ev an hconf hana
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach hconf hana
  have hmem : an.asserting ∈ an.learned := by
    rw [hcanon]
    simp only [ConflictAnalysis.normalized_learned,
      ConflictAnalysis.normalized_asserting, ConflictAnalysis.ofUIP_learned,
      ConflictAnalysis.ofUIP_asserting]
    exact List.mem_map_of_mem (f := Literal.norm) (List.mem_cons_self ..)
  have halign := recordedAnalysis_learned_poolAligned (leaf := leaf)
    (orig := orig) (cfg := cfg) (bs := bs) (ev := ev) (an := an)
    hb hbs hreach hconf hana hvSite
  have hpool : an.asserting.norm ∈ litPool orig :=
    halign an.asserting hmem
  have hlt := litPool_slot_lt hpool
  rwa [norm_atom_slot] at hlt

/-- **THE E1 REGION PRODUCER, SITE FORM**: the failed-checkpoint region
exclusion at ONE supported rejection site from the site certificate, the
site survivor family and the selected checkpoint's snapshot (the
`supportedHdeadCheckpointRegion_of_snapshots` proof applied at the site).
The rejection premise is the runtime's own `perform = none` value. -/
theorem supportedHdeadCheckpointRegion_of_site {orig : List Domain}
    {leaf : Assignment → Bool} {cfg : SchedulerConfig leaf}
    {cp : DecisionCheckpoint leaf}
    (hcertSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hsurvSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail)
    (hsnap : CheckpointSnapshot leaf orig cp) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp) := by
  intro ev an hconf hana hp
  have hnone : filterFrame an.asserting cp.frame = none :=
    perform_eq_none_iff_filterFrame_eq_none.mp hp
  have hcert' : RestorationCertificate leaf cfg.branch an :=
    hcertSite hconf hana
  have hsv : ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel →
      e ∈ cp.trail := hsurvSite hconf hana
  show DeadRegion.Sound leaf (DeadRegion.byFrame cp.frame)
  refine DeadRegion.byFrame_sound (fun a hleaf hcov => ?_)
  refine restoreAssert_filterFrame_none_excludes hcert' hnone a hleaf ?_ hcov
  intro e he hlev
  obtain ⟨bs', hbs', hf, ht, _⟩ := hsnap
  have hecp : e ∈ cp.trail := hsv e he hlev
  have he' : e ∈ bs'.trail := by rw [ht]; exact hecp
  have hcov' : FrameCovers bs'.frame a := by rw [hf]; exact hcov
  exact hbs'.agrees e he' a hcov'

/-- **THE UNIT-FRAGMENT `hpre` PRODUCER, SITE FORM (the circularity
breaker)**: `RestorationPreReachable` at ONE successful supported jump
site, with EVERY family input of `supportedHpre_of_unitRun_reach` replaced
by its site fact: the site's `SupportedReach` (strict-prefix/provenance),
the site's `ReachableState`, the selected checkpoint's snapshot (the chain
component of the joint induction), the site entailment, the site frame
inhabitedness and the site trail vocabulary. Its argument list is exactly
the current `hpre` site context plus the three run-level site facts the
joint induction must supply (`hsnap`, `hentSite` via the D1/I1-B bridge,
`hinhabSite`/`hvSite` via the C2/C1 families at the site). -/
theorem supportedHpre_of_unitRun_site {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hreach : SupportedReach orig original props cfg)
    (hbs : ReachableState leaf orig cfg.branch)
    (hsnap : CheckpointSnapshot leaf orig cp)
    (hentSite : ∀ {ev' : ConflictEvidence} {an' : ConflictAnalysis},
      cfg.conflict = some ev' → ev'.analysis = some an' →
        LearnedEntailed leaf [an'.learned])
    (hinhabSite : ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    (hvSite : BranchTrailVocabulary orig cfg.branch)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = some restored) :
    RestorationPreReachable leaf orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch :=
  restorationPreReachable_of_success_avoiding hsnap hbs
    (supportedHcert_of_site rfl hbs hreach.reachable hentSite hconf hana)
    (supportedHstable_of_reach hreach hconf hana)
    (supportedHneg_of_unitRun hprops hSupp hreach hconf hana)
    (supportedHsurv_of_site hreach
      (supportedHcert_of_site rfl hbs hreach.reachable hentSite)
      hconf hana hcp)
    (supportedHfresh_of_site rfl hbs hreach hinhabSite hconf hana hcp)
    (supportedHrange_of_site rfl hbs hreach.reachable hvSite hconf hana)
    hp

/-! ## §11 C2c: the `hfresh` producer WITHOUT inhabitedness (C2 completion)

The inhabitedness premises `hinhab`/`hinhabSite` of §9/§10 are
KERNEL-REFUTED (`SiteInhabited.cexNotAllSites` for the all-sites family,
`SiteLiveness.recordedInhabited_false` for the unit kit's recorded sites),
so no entry point may keep them. This section exports the honest
replacement — proved in the companion file `Proofs/FreshCoverless.lean`
(worker C2c), and RE-PROVED here in the self-contained raw-formula
spelling so this file needs no new import (the two spellings are the same
reduction; the coordinator may collapse this section to thin wrappers once
`LeanFzn.Solver.UIP.Proofs.FreshCoverless` is registered in the umbrella):

  * the `hfresh` CONCLUSION follows from the LEVEL SEPARATION

      ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
      ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
        e₀.literal ≠ e.literal.negate.norm

    (no entry at level ≤ target is the normalized negation of an entry
    strictly above the target) — no coverage, no inhabitedness, no frame
    content. The proof consumes the UIP witness
    (`analyzeStep_uip_on_trail`: the entry `m` on the trail with
    `m.literal = uip` at `m.level = cfg.branch.level`), the checkpoint's
    snapshot (`CheckpointSnapshot`'s `ReachableState.wf.1` bounds the
    checkpoint's trail levels by `cp.level = an.backjumpLevel`) and
    `targetDescends` + `recorded_conflict_level_pos` (the target strictly
    descends). `FreshCoverless.TrailLevelSeparated` names the predicate,
    `FreshCoverless.supportedHfresh_of_site_separated` is the same
    reduction under the def;
  * the LIVE case keeps the landed semantic route
    (`supportedHfresh_of_site`), so the classification
    `inhabited ∨ coverless` (C2a's `frameCovers_or_coverless`, supplied
    per site or per family) is all the coverage that remains;
  * `supportedHfresh_of_site_levelSeparated` (§11 site form) — the exact
    §10 `hfresh` site twin with the inhabitedness argument replaced by the
    level separation;
  * `supportedHfresh_of_reach_or_coverless` (family form) — the §9 `hfresh`
    family with the inhabitedness family replaced by C2a's disjunction
    family `hinhabOr` and the separation family `hsepF` AT COVERLESS
    SITES;
  * `supportedHpre_of_unitRun_reach_or_coverless` — THE RE-POINTED §9
    ACCEPTANCE PRODUCER: `supportedHpre_of_unitRun_reach` with `hinhab`
    replaced by `hinhabOr` + `hsepF`, every other family unchanged.

`FreshCoverless.canonicalTrail_levelSeparated` discharges the separation
for every canonical resume trail (`stepConsume` installs
`canonicalTrail`; empty prefix: all entries at level 0, nonempty prefix:
no entry at level 0), and
`FreshCoverless.plainConsistent_canonicalTrail_refuted` shows the
level-SYMMETRIC "no complementary pair" discipline is FALSE (the canonical
resume of a coverless bool slot emits both retirements at the same level),
which is why the separation is stated in the level-strict form. The
remaining residual (sites whose canonical resume is followed by level-0
propagations, i.e. after an EMPTY-prefix resume) is documented in
`FreshCoverless` §4/§5; the C2a-2 counterexample site itself satisfies the
separation and carries no checkpoint at its target
(`FreshCoverless.cx5_trail_levelSeparated`,
`FreshCoverless.cx5_hfresh_vacuous`). -/

/-- **THE `hfresh` SITE PRODUCER FROM THE LEVEL SEPARATION (C2c)**: the
coverless-case twin of `supportedHfresh_of_site` (§10) — the site's level
separation replaces the site's frame inhabitedness. -/
theorem supportedHfresh_of_site_levelSeparated {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (hcertSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hsnapSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis}
      {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        CheckpointSnapshot leaf orig cp)
    (hsepSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  intro ev an cp hconf hana hcp e he
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  have hass : an.asserting.norm = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting, norm_norm]
  have hrun' := hrun
  unfold analyzeAtAllowance at hrun'
  obtain ⟨m, hm, hmlit, hmlev⟩ :=
    analyzeStep_uip_on_trail cfg.branch.trail cfg.branch.level
      (analysisFuel cfg.branch.trail ev.clause) [ev.clause] none [] []
      (analyzerInvariant_init cfg.branch.trail cfg.branch.level) below uip hrun'
  obtain ⟨hident, -⟩ := identifiesChain_of_reach hreach
  obtain ⟨mid, hmid, -⟩ := hident cp (checkpointAt_mem hcp) |>.2.1
  have he' : e ∈ cfg.branch.trail := by
    rw [hmid]; exact List.mem_append.mpr (Or.inl he)
  obtain ⟨bs', hbs', -, ht, hl⟩ := hsnapSite hconf hana hcp
  have hlevE : e.level ≤ an.backjumpLevel := by
    have h1 : e.level ≤ bs'.level := hbs'.wf.1 e (by rw [ht]; exact he)
    rw [hl, checkpointAt_level hcp] at h1
    exact h1
  have hlt : an.backjumpLevel < cfg.branch.level := by
    have hd := (hcertSite hconf hana).targetDescends
    have hp := recorded_conflict_level_pos hreach.reachable ev hconf
    rcases hd with h0 | h
    · omega
    · exact h
  have hmgt : an.backjumpLevel < m.level := by
    rw [hmlev]; exact hlt
  intro hcon
  exact (hsepSite hconf hana e he' hlevE m hm hmgt)
    (hcon.trans (by rw [hass, ← hmlit]))

/-- **THE `hfresh` FAMILY FROM `hinhabOr` + THE COVERLESS-SITE SEPARATION
(C2c)**: the §9/§10 `hfresh` family with the refuted inhabitedness family
replaced by C2a's classification family `hinhabOr` and the level-separation
family `hsepF` at coverless sites. The live case is the landed semantic
producer `supportedHfresh_of_site` (§10). -/
theorem supportedHfresh_of_reach_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hcert : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an → RestorationCertificate leaf cfg.branch an)
    (hsnaps : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableCpSnapshots leaf orig cfg)
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
            e₀.literal ≠ e.literal.negate.norm) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  intro cfg ev an cp hreach hconf hana hcp
  rcases hinhabOr hreach with h | h
  · exact supportedHfresh_of_site rfl (hbr hreach) hreach h hconf hana hcp
  · refine supportedHfresh_of_site_levelSeparated hreach ?_ ?_ ?_ hconf hana hcp
    · intro ev0 an0 hc ha
      exact hcert hreach hc ha
    · intro ev0 an0 cp0 hc ha hcp0
      exact hsnaps hreach cp0 (checkpointAt_mem hcp0)
    · intro ev0 an0 hc ha
      exact hsepF hreach hc ha h

/-- **THE RE-POINTED §9 ACCEPTANCE PRODUCER (C2c)**: identical to
`supportedHpre_of_unitRun_reach` except that the `hfresh` family is fed by
`supportedHfresh_of_reach_or_coverless` — so the refuted `hinhab` family is
replaced by C2a's classification `hinhabOr` plus the coverless-site
separation `hsepF`, with every other producer family unchanged. -/
theorem supportedHpre_of_unitRun_reach_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned])
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
  supportedHpre_of_snapshots
    (supportedReachableCpSnapshots_of_premises hbr)
    (supportedHcert_of_premises hbr hent)
    (fun hreach hconf hana => supportedHstable_of_reach hreach hconf hana)
    (fun hreach hconf hana =>
      supportedHneg_of_unitRun hprops hSupp hreach hconf hana)
    (supportedHsurv_of_reach hbr hent)
    (supportedHfresh_of_reach_or_coverless hbr
      (supportedHcert_of_premises hbr hent)
      (supportedReachableCpSnapshots_of_premises hbr) hinhabOr hsepF)
    (supportedHrange_of_premises hbr hv)

/-- **THE `hfresh` SITE PRODUCER FROM THE SITE DISJUNCTION + THE SITE LEVEL
SEPARATION (C2c)**: the combined §10 `hfresh` twin — the drop-in for
`supportedHfresh_of_site`'s inhabitedness argument, taking the site's
disjunction (C2a), the site's separation (coverless case), the site
certificate family and the checkpoint-snapshot family. -/
theorem supportedHfresh_of_site_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    (hb : cfg.branch = bs) (hbs : ReachableState leaf orig bs)
    (hreach : SupportedReach orig original props cfg)
    (hinhabOrSite : (∃ a : Assignment, FrameCovers bs.frame a) ∨
      (∃ d ∈ bs.frame.1, d = []))
    (hcertSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        RestorationCertificate leaf cfg.branch an)
    (hsnapSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis}
      {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        CheckpointSnapshot leaf orig cp)
    (hsepSite : ∀ {ev : ConflictEvidence} {an : ConflictAnalysis},
      cfg.conflict = some ev → ev.analysis = some an →
        ∀ e₀ ∈ cfg.branch.trail, e₀.level ≤ an.backjumpLevel →
          ∀ e ∈ cfg.branch.trail, an.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm) :
    ∀ {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  rcases hinhabOrSite with h | h
  · exact supportedHfresh_of_site hb hbs hreach h
  · exact supportedHfresh_of_site_levelSeparated hreach hcertSite hsnapSite hsepSite

/-- **THE RE-POINTED §10 SITE PRODUCER (C2c)**:
`supportedHpre_of_unitRun_site` with the site inhabitedness `hinhabSite`
replaced by C2a's classification family `hinhabOr` and the coverless-site
level-separation family `hsepF` — the interface to use in place of
`SupportedInstance.supportedHpre_unitKit_of_site`'s `hinhab` argument. The
site's checkpoint snapshot enters in the `checkpointAt`-indexed family form
(derivable from the joint induction's `ReachableCpSnapshots` chain
component via `checkpointAt_mem`); the site's own recorded facts
(`hreach`, `hconf`, `hana`, `hcp`) stay pinned, so the coverless branch
consumes `hsepF` at the site's own analysis. -/
theorem supportedHpre_of_unitRun_site_or_coverless {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} {dcs : List DomConstraint}
    {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    {restored : BranchState leaf}
    (hprops : props = dcs.filterMap propagatorOfProved)
    (hSupp : ∀ dc ∈ dcs, unitFamilyB dc = true)
    (hreach : SupportedReach orig original props cfg)
    (hbs : ReachableState leaf orig cfg.branch)
    (hsnapSite : ∀ {ev' : ConflictEvidence} {an' : ConflictAnalysis}
      {cp' : DecisionCheckpoint leaf},
      cfg.conflict = some ev' → ev'.analysis = some an' →
      checkpointAt cfg.checkpoints an'.backjumpLevel = some cp' →
        CheckpointSnapshot leaf orig cp')
    (hentSite : ∀ {ev' : ConflictEvidence} {an' : ConflictAnalysis},
      cfg.conflict = some ev' → ev'.analysis = some an' →
        LearnedEntailed leaf [an'.learned])
    (hinhabOr : ∀ {cfg' : SchedulerConfig leaf},
      SupportedReach orig original props cfg' →
        (∃ a : Assignment, FrameCovers cfg'.branch.frame a) ∨
          (∃ d ∈ cfg'.branch.frame.1, d = []))
    (hsepF : ∀ {cfg' : SchedulerConfig leaf} {ev' : ConflictEvidence}
      {an' : ConflictAnalysis},
      SupportedReach orig original props cfg' → cfg'.conflict = some ev' →
      ev'.analysis = some an' → (∃ d ∈ cfg'.branch.frame.1, d = []) →
        ∀ e₀ ∈ cfg'.branch.trail, e₀.level ≤ an'.backjumpLevel →
          ∀ e ∈ cfg'.branch.trail, an'.backjumpLevel < e.level →
            e₀.literal ≠ e.literal.negate.norm)
    (hvSite : BranchTrailVocabulary orig cfg.branch)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
        cfg.branch cfg.original cfg.props = some restored) :
    RestorationPreReachable leaf orig
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      cfg.branch := by
  rcases hinhabOr hreach with hinhab | hcov
  · exact restorationPreReachable_of_success_avoiding
      (hsnapSite hconf hana hcp) hbs
      (supportedHcert_of_site rfl hbs hreach.reachable hentSite hconf hana)
      (supportedHstable_of_reach hreach hconf hana)
      (supportedHneg_of_unitRun hprops hSupp hreach hconf hana)
      (supportedHsurv_of_site hreach
        (supportedHcert_of_site rfl hbs hreach.reachable hentSite)
        hconf hana hcp)
      (supportedHfresh_of_site rfl hbs hreach hinhab hconf hana hcp)
      (supportedHrange_of_site rfl hbs hreach.reachable hvSite hconf hana)
      hp
  · exact restorationPreReachable_of_success_avoiding
      (hsnapSite hconf hana hcp) hbs
      (supportedHcert_of_site rfl hbs hreach.reachable hentSite hconf hana)
      (supportedHstable_of_reach hreach hconf hana)
      (supportedHneg_of_unitRun hprops hSupp hreach hconf hana)
      (supportedHsurv_of_site hreach
        (supportedHcert_of_site rfl hbs hreach.reachable hentSite)
        hconf hana hcp)
      (supportedHfresh_of_site_levelSeparated hreach
        (fun hc ha => supportedHcert_of_site rfl hbs hreach.reachable hentSite hc ha)
        hsnapSite
        (fun hc ha => hsepF hreach hc ha hcov)
        hconf hana hcp)
      (supportedHrange_of_site rfl hbs hreach.reachable hvSite hconf hana)
      hp

end LeanFzn.Solver.UIP
