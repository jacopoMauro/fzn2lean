/-
File: LeanFzn/Solver/UIP/Proofs/LcgMixedJump.lean
A2b: the mixed analyze/jump (perform) arm — shape-typed twins of the four
jump lemmas of `LcgRunStep`:
  * `cert_of_state_shape`  (cert_of_state)
  * `jump_good0_shape`     (jump_good0)
  * `core_jump_shape`      (core_jump)
  * `jump_frameSnd_shape`  (jump_frameSnd)
Every statement is the integer twin with `MixedLcgKit` in place of `LcgKit`,
`LcgMixedRunState` in place of `LcgRunState` and `MixedLcgGood` in place of
`LcgGood`; the hypotheses (SupportedReach, root truth, recorded analysis,
checkpoint selection and the successful perform) are unchanged. The frame/pin
producers are the shape-typed ones (`frameJ_perform_aux_shape`,
`boolPinsOn_syncAll`, `boolPinsOn_restoreNarrow`); the closure coverage is
`LcgMixedRunDrop.closure_frameSnd_shape`; the canonical database of the
synchronised restoration is the run invariant's `CanonicalCfg` evidence (the
level-0 `syncAll` never changes `learned`).
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunStep
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunState
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunDrop
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgAsserting LeanFzn.Solver.UIP.LcgRunConflict LeanFzn.Solver.UIP.LcgRunArms
open LeanFzn.Solver.UIP.LcgRunJump LeanFzn.Solver.UIP.LcgRunCert LeanFzn.Solver.UIP.LcgRunPending
open LeanFzn.Solver.UIP.LcgRunState LeanFzn.Solver.UIP.LcgRootTrue LeanFzn.Solver.UIP.LcgRootBase
open LeanFzn.Solver.UIP.LcgRunDrop LeanFzn.Solver.UIP.LcgRunStep
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedRunState
open LeanFzn.Solver.UIP.LcgMixedRunDrop LeanFzn.Solver.UIP.LcgCanonicalClauses
open LeanFzn.Solver.UIP.LcgCanonicalRun LeanFzn.Solver.UIP.LcgCanonicalScheduler

namespace LeanFzn.Solver.UIP.LcgMixedJump

variable {leaf : Assignment → Bool}

/-! ## The certificate of the recorded analysis -/

/-- The restoration certificate of the recorded analysis, from the mixed run
invariant. Identical body to `cert_of_state`: every ingredient is
sort-agnostic and `h.core` is a `LcgCore`. -/
theorem cert_of_state_shape {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : MixedLcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgMixedRunState leaf cfg.orig cfg)
    (hroot : ∀ e ∈ cfg.branch.trail, e.level = 0 → ∀ a, leaf a = true →
      e.literal.eval a = some true)
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an) :
    RestorationCertificate leaf cfg.branch an := by
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hc ha
  have hconf := (h.core.ev ev hc).1
  have hent0 := analyzeAtAllowance_learnedEntailed K.fits hconf
    (fun e he r hr => (h.core.reach.reason_ent e he r hr).1) hroot hrun
  have hcert0 : RestorationCertificate leaf cfg.branch (ConflictAnalysis.ofUIP below uip) :=
    lcg_certificate (orig := cfg.orig) h.core.reach.distinct h.core.reach.norm
      (recorded_conflict_level_pos hreach.reachable ev hc) hrun rfl rfl rfl hent0
  rw [hcanon]
  exact RestorationCertificate.normalized hcert0

/-! ## The jump arm -/

/-- The synchronised restoration state of a successful jump is
`MixedLcgGood`: reachability and vocabulary are reused, the frame comes from
the shape-typed performed-restoration producer, the Boolean prefix pins from
the checkpoint pins through restoration and level-0 sync, and the canonical
database from the run invariant's `CanonicalCfg` (the sync never changes
`learned`). -/
theorem jump_good0_shape {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : MixedLcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgMixedRunState leaf cfg.orig cfg)
    (hroot : ∀ e ∈ cfg.branch.trail, e.level = 0 → ∀ a, leaf a = true →
      e.literal.eval a = some true)
    {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    ∃ g, filterFrame an.asserting cp.frame = some g ∧
      restored = explainedClosure cfg.orig cfg.original cfg.props
        (syncAll cfg.orig (restorationState cp cfg.branch an g)) ∧
      MixedLcgGood leaf cfg.orig (syncAll cfg.orig (restorationState cp cfg.branch an g)) := by
  have hco := h.core
  have hcert := cert_of_state_shape K hreach h hroot hc ha
  have hstable : an.asserting.norm = an.asserting := supportedHstable_of_reach hreach hc ha
  have hcpmem : cp ∈ cfg.checkpoints := checkpointAt_mem hcp
  have hsurv : ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail :=
    surv_of_cert hreach hc hcp hcert
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hc ha
  -- the asserting literal is pooled, hence in range
  have hfals := lcg_normFalsified (cfg := cfg) (bs := cfg.branch) rfl hco.reach hreach.reachable hc ha
  have halignAn : ∀ q ∈ an.learned, q.norm ∈ litPool cfg.orig := by
    have := normFalsified_learned_poolAligned_at (pool := litPool cfg.orig)
      (fun l hl => litPool_negate_norm_mem hl) hco.voc hfals
    exact this
  have hassP : an.asserting.norm ∈ litPool cfg.orig :=
    recordedAnalysis_asserting_poolAligned_at hreach.reachable hc ha halignAn
  have hrange : an.asserting.atom.slot < cfg.orig.length := by
    have := litPool_slot_lt hassP
    rwa [norm_atom_slot] at this
  -- the successful perform
  obtain ⟨g, hg, hres⟩ := perform_eq_some_iff.mp hp
  have hpre : LcgReachableState leaf cfg.orig (restorationState cp cfg.branch an g) :=
    lcgRestorationState_reachable (hco.snaps cp hcpmem) hco.reach hcert hstable hsurv
      hrange hg
  -- the MixedLcgGood bundle of the synchronised restoration state
  have hJcp : FrameJ cfg.orig cp.trail cp.frame := h.frameRun.cps cp hcpmem
  have hShcp : FrameShape cfg.orig cp.frame := h.frameRun.cpShape cp hcpmem
  have hBpins : BoolPinsOn cp.trail cp.frame.2 := h.frameRun.checkpointBoolPins cp hcpmem
  have hplan : DatabaseAlignedAt (litPool cfg.orig) [an.learned] :=
    databaseAlignedAt_singleton_of_clause halignAn
  have hs : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).restoreNarrow
      cfg.branch = some (restorationState cp cfg.branch an g) :=
    restoreNarrow_eq_some_iff.mpr ⟨g, hg, rfl⟩
  have hgood0 : MixedLcgGood leaf cfg.orig
      (syncAll cfg.orig (restorationState cp cfg.branch an g)) := by
    have hsf : (restorationState cp cfg.branch an g).frame = g := rfl
    refine ⟨syncAll_lcgReachable hpre K.fits, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := frameJ_perform_aux_shape K.shape
        (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
        hJcp hBpins hg (restorationState cp cfg.branch an g) rfl rfl
      rw [syncAll_frame, hsf]
      exact this
    · rw [syncAll_frame, hsf]
      exact frameShape_filter hg hShcp
    · refine syncAll_trail_vocab (orig := cfg.orig) _ (fun l hl => hl) ?_
      rcases restorationState_trail_cases cp cfg.branch an g with ⟨ht, -⟩ | ⟨ht, -⟩
      · rw [ht]; exact h.core.cpVoc cp hcpmem
      · rw [ht]
        exact trailVocabularyAt_append_entry (h.core.cpVoc cp hcpmem)
          (by rw [norm_norm]; exact hassP)
    · rw [syncAll_learned, restorationState_learned]
      exact databaseAlignedAt_append hplan hco.db
    · exact boolPinsOn_syncAll (boolPinsOn_restoreNarrow hBpins hs)
    · rw [syncAll_learned]
      exact restoreNarrow_canonical h.canonical.db
        ((h.canonical.evidence ev hc).2 an ha) hs
  exact ⟨g, hg, hres, hgood0⟩

/-- The mixed core of the jump arm: the same seven-part `LcgCore` assembly as
`core_jump`, over the closure of the shape-typed jump-good state. -/
theorem core_jump_shape {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : MixedLcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgMixedRunState leaf cfg.orig cfg)
    (hroot : ∀ e ∈ cfg.branch.trail, e.level = 0 → ∀ a, leaf a = true →
      e.literal.eval a = some true)
    {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    LcgCore leaf cfg.orig
      (stepLearnBackjumpAssert cfg
        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev restored) := by
  have hco := h.core
  obtain ⟨g, hg, hres, hgood0⟩ := jump_good0_shape K hreach h hroot hc ha hcp hp
  have hgood : MixedLcgGood leaf cfg.orig restored := by
    rw [hres]
    exact hgood0.closure K
  obtain ⟨hevc, hevl, hevd⟩ := hco.ev ev hc
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact lcgReachable_prepend_learned hgood.reach hevl
  · exact hgood.voc
  · exact databaseAlignedAt_append hevd hgood.db
  · intro cp' hcp'
    rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
      (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      (ev := ev) (restored := restored)] at hcp'
    exact hco.snaps cp' (List.mem_filter.mp hcp').1
  · intro cp' hcp'
    rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
      (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
      (ev := ev) (restored := restored)] at hcp'
    exact hco.cpVoc cp' (List.mem_filter.mp hcp').1
  · intro ev' h'
    rw [stepLearnBackjumpAssert_conflict] at h'
    cases h'

/-- The restored frame of a mixed jump holds every leaf solution of its pin
prefix: the shape-typed closure coverage over the synchronised restoration. -/
theorem jump_frameSnd_shape {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : MixedLcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgMixedRunState leaf cfg.orig cfg)
    (hroot : ∀ e ∈ cfg.branch.trail, e.level = 0 → ∀ a, leaf a = true →
      e.literal.eval a = some true)
    {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    FrameSnd leaf restored.frame := by
  obtain ⟨g, hg, hres, hgood0⟩ := jump_good0_shape K hreach h hroot hc ha hcp hp
  have hcert := cert_of_state_shape K hreach h hroot hc ha
  have hstable : an.asserting.norm = an.asserting := supportedHstable_of_reach hreach hc ha
  have hsurv : ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail :=
    surv_of_cert hreach hc hcp hcert
  have hmem : an.asserting.norm ∈ an.learned :=
    of_eq_true (hcert.asserting_norm_mem_of_stable hstable)
  have hsem : SemReasonOK cfg.orig cp.trail an.asserting.norm an.learned := by
    refine ⟨by rw [norm_norm]; exact hmem, ?_⟩
    intro q hq hne
    have hqa : q ≠ an.asserting := by
      intro h'
      rw [h', norm_norm] at hne
      have htrue : litEqB an.asserting.norm an.asserting.norm = true := litEqB_iff.mpr rfl
      rw [htrue] at hne
      exact Bool.noConfusion hne
    exact semFalsifiedBefore_of_others hcert hsurv hq hqa
  have hcpmem : cp ∈ cfg.checkpoints := checkpointAt_mem hcp
  obtain ⟨bs, hbs, hbf, hbt, -⟩ := h.core.snaps cp hcpmem
  have hFg : FrameSnd leaf g := by
    intro a ha' hpre
    have hpre' : g.2 = cp.frame.2 := filterFrame_prefix hg
    have hcv : FrameCovers cp.frame a := h.cpSnd cp hcpmem a ha' (by rw [← hpre']; exact hpre)
    have hsat := hcert.learnedEntailed an.learned (List.mem_singleton_self _) a ha'
    have h1 := pivot_true hsem (K.fits a ha') (fun e he => by
      have := hbs.agrees e (by rw [hbt]; exact he) a (by rw [hbf]; exact hcv)
      exact this) hsat
    rw [norm_norm, Literal.norm_eval] at h1
    obtain ⟨g', hg', hcv'⟩ := filterFrame_preserves hcv h1
    have : g' = g := Option.some.inj (hg'.symm.trans hg)
    rw [← this]; exact hcv'
  rw [hres]
  refine closure_frameSnd_shape K hgood0 ?_
  rw [syncAll_frame]
  exact hFg

end LeanFzn.Solver.UIP.LcgMixedJump
