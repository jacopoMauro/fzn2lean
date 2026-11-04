/-
File: LeanFzn/Solver/UIP/Proofs/LcgAsserting.lean

The semantic jump premise `AssertingSem` (LcgRunInvariantTrailStep.lean) derived from the
checkpoint-prefix invariant and the restoration certificate, instead of assumed.

* Lemma A (`checkpoint_covers_of_supportedRun`): at a recorded conflict whose analysis jumps to
  target `t`, every branch-trail entry at level `≤ t` lies in the selected checkpoint's trail.
  Proved from the strict-prefix invariant (`checkpointsStrictPrefix_of_reach`) through
  `supportedHsurv_of_cert`; the certificate is `supportedHcert_of_premises`.
* Lemma B (`semFalsifiedBefore_of_others`): every non-asserting learned literal `q` is falsified
  by a trail entry at level `≤ t` (certificate field `othersBelow`), hence by the checkpoint trail.
* `assertingSem_of_supportedRun`: `AssertingSem` at every supported configuration.
* `lcgRunInvCond_of_residual_noAss`: the conditional run invariant without the `AssertingSem`
  premise. Its remaining premises are the D1 entailment of the analysis learned clause
  (`hcertEnt`, the premise of `supportedHcert_of_premises`) and the reachability premise `hbr`.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEntailed
import LeanFzn.Legacy.Solver.UIP.Proofs.HdeadCkpt

namespace LeanFzn.Solver.UIP.LcgAsserting

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-- **Lemma A.** At a recorded conflict whose analysis target has a checkpoint, every branch-trail
entry at level `≤ an.backjumpLevel` is an entry of that checkpoint's trail. -/
theorem checkpoint_covers_of_supportedRun {orig : List Domain} {original : List Clause}
    {props : List Propagator}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hcertEnt : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → LearnedEntailed leaf [an.learned])
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis}
    {cp : DecisionCheckpoint leaf}
    (hreach : SupportedReach orig original props cfg) (hconf : cfg.conflict = some ev)
    (hana : ev.analysis = some an) (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp) :
    ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail :=
  supportedHsurv_of_cert
    (fun hr hc ha => supportedHcert_of_premises hbr hcertEnt hr hc ha) hreach hconf hana hcp

/-- **Lemma B.** A non-asserting learned literal of a certificate is semantically falsified by any
trail that contains the trail entries at level `≤ an.backjumpLevel`. -/
theorem semFalsifiedBefore_of_others {bs : BranchState leaf} {an : ConflictAnalysis}
    {orig : List Domain} {pre : List TrailEntry}
    (hcert : RestorationCertificate leaf bs an)
    (hcov : ∀ e ∈ bs.trail, e.level ≤ an.backjumpLevel → e ∈ pre)
    {q : Literal} (hq : q ∈ an.learned) (hqa : q ≠ an.asserting) :
    SemFalsifiedBefore orig pre q := by
  obtain ⟨⟨e, he, hle, hlit⟩, -⟩ := hcert.othersBelow q hq hqa
  exact semFalsified_of_trail_negate (hcov e he hle) hlit

/-- **The jump premise, derived.** `AssertingSem` holds at every supported configuration, from
branch reachability, the D1 entailment of the analysis learned clause, and the checkpoint-prefix
invariant. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem assertingSem_of_supportedRun {orig : List Domain} {original : List Clause}
    {props : List Propagator}
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hcertEnt : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → LearnedEntailed leaf [an.learned]) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → AssertingSem cfg := by
  intro cfg hreach ev an cp hconf hana hcp
  have hcert : RestorationCertificate leaf cfg.branch an :=
    supportedHcert_of_premises hbr hcertEnt hreach hconf hana
  have hcov := checkpoint_covers_of_supportedRun hbr hcertEnt hreach hconf hana hcp
  obtain ⟨below, uip, -, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hconf hana
  have hstable : an.asserting.norm = an.asserting := by
    rw [hcanon]
    exact ConflictAnalysis.normalized_asserting_norm _
  have hmem : an.asserting.norm ∈ an.learned :=
    of_eq_true (hcert.asserting_norm_mem_of_stable hstable)
  refine ⟨by rw [norm_norm]; exact hmem, ?_⟩
  intro q hq hne
  have hqa : q ≠ an.asserting := by
    intro h
    rw [h, norm_norm] at hne
    have htrue : litEqB an.asserting.norm an.asserting.norm = true := litEqB_iff.mpr rfl
    rw [htrue] at hne
    exact Bool.noConfusion hne
  exact semFalsifiedBefore_of_others hcert hcov hq hqa

/-- **The conditional run invariant without the `AssertingSem` premise.** Same as
`lcgRunInvCond_of_residual_noEnt`, with the jump premise derived by `assertingSem_of_supportedRun`;
the premise `hcertEnt` is the D1 entailment of the analysis learned clause. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem lcgRunInvCond_of_residual_noAss {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw)
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, (Dom.enum d).Nodup)
    (htyped : ClampPool.EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hfit : ∀ a, leaf a = true → a.Fits orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hcertEnt : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → LearnedEntailed leaf [an.learned])
    (hlive : DecideLive orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      LeanFzn.Solver.UIP.LcgEvidence.LcgRunInv' cfg :=
  LeanFzn.Solver.UIP.LcgEvidence.lcgRunInvCond_of_residual hraw hprops hfam hint hnd htyped horig hfit
    hbr (fun hr => assertingSem_of_supportedRun hbr hcertEnt hr)
    (LeanFzn.Solver.UIP.LcgEntailed.entailedRun_of_supportedRun hbr) hlive

end LeanFzn.Solver.UIP.LcgAsserting
