/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunStep.lean
H2c (part 8): the one-step law `lcgRunState_step` of `LcgRunState` along real dispatcher
successors, arm by arm.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunState
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunDrop
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgAsserting LeanFzn.Solver.UIP.LcgRunConflict LeanFzn.Solver.UIP.LcgRunArms
open LeanFzn.Solver.UIP.LcgRunJump LeanFzn.Solver.UIP.LcgRunCert LeanFzn.Solver.UIP.LcgRunPending
open LeanFzn.Solver.UIP.LcgRunState LeanFzn.Solver.UIP.LcgRootTrue LeanFzn.Solver.UIP.LcgRootBase
open LeanFzn.Solver.UIP.LcgRunDrop

namespace LeanFzn.Solver.UIP.LcgRunStep

variable {leaf : Assignment → Bool}

/-! ## Core helpers for the non-moving arms -/

theorem core_same {orig : List Domain} {cfg cfg' : SchedulerConfig leaf}
    (h : LcgCore leaf orig cfg) (ho : cfg'.orig = cfg.orig)
    (hb : cfg'.branch = cfg.branch) (hc : cfg'.checkpoints = cfg.checkpoints)
    (hn : cfg'.conflict = none) : LcgCore leaf orig cfg' where
  orig_eq := ho.trans h.orig_eq
  reach := by rw [hb]; exact h.reach
  voc := by rw [hb]; exact h.voc
  db := by rw [hb]; exact h.db
  snaps := by intro cp hcp; rw [hc] at hcp; exact h.snaps cp hcp
  cpVoc := by intro cp hcp; rw [hc] at hcp; exact h.cpVoc cp hcp
  ev := by intro ev hev; rw [hn] at hev; cases hev

theorem core_localExclude {orig : List Domain} {cfg cfg' : SchedulerConfig leaf}
    (h : LcgCore leaf orig cfg) (ho : cfg'.orig = cfg.orig)
    (payload : List Clause) (hent : LearnedEntailed leaf payload)
    (halign : DatabaseAlignedAt (litPool orig) payload)
    (hb : cfg'.branch = { cfg.branch with learned := payload ++ cfg.branch.learned })
    (hc : cfg'.checkpoints = cfg.checkpoints)
    (hn : cfg'.conflict = none) : LcgCore leaf orig cfg' where
  orig_eq := ho.trans h.orig_eq
  reach := by rw [hb]; exact lcgReachable_prepend_learned h.reach hent
  voc := by rw [hb]; exact h.voc
  db := by rw [hb]; exact databaseAlignedAt_append halign h.db
  snaps := by intro cp hcp; rw [hc] at hcp; exact h.snaps cp hcp
  cpVoc := by intro cp hcp; rw [hc] at hcp; exact h.cpVoc cp hcp
  ev := by intro ev hev; rw [hn] at hev; cases hev

theorem core_analyze {orig : List Domain} {cfg cfg' : SchedulerConfig leaf}
    (h : LcgCore leaf orig cfg) (ho : cfg'.orig = cfg.orig)
    (hb : cfg'.branch = cfg.branch) (hc : cfg'.checkpoints = cfg.checkpoints)
    (hev : ∀ ev, cfg'.conflict = some ev →
      LearnedEntailed leaf [ev.clause] ∧ LearnedEntailed leaf ev.learned ∧
        DatabaseAlignedAt (litPool orig) ev.learned) : LcgCore leaf orig cfg' where
  orig_eq := ho.trans h.orig_eq
  reach := by rw [hb]; exact h.reach
  voc := by rw [hb]; exact h.voc
  db := by rw [hb]; exact h.db
  snaps := by intro cp hcp; rw [hc] at hcp; exact h.snaps cp hcp
  cpVoc := by intro cp hcp; rw [hc] at hcp; exact h.cpVoc cp hcp
  ev := hev


theorem core_move {orig : List Domain} {cfg cfg' : SchedulerConfig leaf}
    (h : LcgCore leaf orig cfg) (ho : cfg'.orig = cfg.orig)
    (hr : LcgReachableState leaf orig cfg'.branch)
    (hv : TrailVocabularyAt (litPool orig) cfg'.branch.trail)
    (hd : DatabaseAlignedAt (litPool orig) cfg'.branch.learned)
    (hc : cfg'.checkpoints = cfg.checkpoints)
    (hn : cfg'.conflict = none) : LcgCore leaf orig cfg' where
  orig_eq := ho.trans h.orig_eq
  reach := hr
  voc := hv
  db := hd
  snaps := by intro cp hcp; rw [hc] at hcp; exact h.snaps cp hcp
  cpVoc := by intro cp hcp; rw [hc] at hcp; exact h.cpVoc cp hcp
  ev := by intro ev hev; rw [hn] at hev; cases hev

/-! ## Propagation -/

theorem core_propagate {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (h : LcgRunState leaf cfg.orig cfg) (hconf : cfg.conflict = none)
    {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    LcgCore leaf cfg.orig (stepPropagate cfg d) := by
  have hg := h.good.stepNarrowSync K hd
  exact core_move h.core rfl hg.reach hg.voc hg.db rfl (by rw [stepPropagate_conflict, hconf])


/-! ## Decide / skip -/

theorem lcg_splitLiteral_pooled {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hreach : LcgReachableState leaf orig cfg.branch)
    (hs : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs)) :
    l.norm ∈ litPool orig := by
  obtain ⟨hspec, hl⟩ := splitData_spec hs
  obtain ⟨dk, hdk, -⟩ := exists_dom_of_enum_cons hspec
  have hklt : k < orig.length := by
    rw [← hreach.length_ok, fullDomains_length]
    exact (List.getElem?_eq_some_iff.mp hdk).1
  have hmem : v ∈ (fullDomains cfg.branch.frame).getD k Dom.empty := by
    show v ∈ (cfg.branch.frame.doms.getD k Dom.empty)
    exact (DomainLike.mem_iff _ v).mpr (by
      rw [domElems_eq_enum, enum_getD_of_enum_cons hspec]
      exact List.mem_cons_self)
  exact valueLiteral_norm_mem_litPool hklt (hreach.full_fits _ _ hmem) hl

theorem core_decide {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (h : LcgRunState leaf cfg.orig cfg) (hconf : cfg.conflict = none)
    {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (hs : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    LcgCore leaf cfg.orig (stepDecide cfg k v vs l) := by
  have hc := h.core
  obtain ⟨i, rfl, -, hpin⟩ := lcgPinFits_int hs hc.reach K.int
  have hdom := (splitData_eq_some_iff.mp hs).2.1
  obtain ⟨dk, hdk, hdke⟩ := exists_dom_of_enum_cons hdom
  have hvk : Value.int i ∈ dk :=
    (DomainLike.mem_iff dk _).mpr (by
      rw [domElems_eq_enum, hdke]
      exact List.mem_cons_self)
  have hr : LcgReachableState leaf cfg.orig (stepDecide cfg k (Value.int i) vs l).branch :=
    lcgReachable_decide hc.reach hdk hvk hpin (not_trailRedundant_iff.mp hred)
  have hck : (stepDecide cfg k (Value.int i) vs l).checkpoints
      = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
  refine ⟨rfl, hr, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepDecide_branchTrailVocabulary_at (cfg := cfg) hc.voc (lcg_splitLiteral_pooled hc.reach hs)
  · exact stepDecide_halignDBAt k (Value.int i) vs l hc.db
  · intro cp hcp
    rw [hck] at hcp
    rcases List.mem_cons.mp hcp with rfl | hcp
    · exact lcgSnapshot_ofBranch hc.reach
    · exact hc.snaps cp hcp
  · intro cp hcp
    rw [hck] at hcp
    rcases List.mem_cons.mp hcp with rfl | hcp
    · exact hc.voc
    · exact hc.cpVoc cp hcp
  · intro ev hev
    rw [stepDecide_conflict, hconf] at hev
    cases hev

theorem core_skip {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (h : LcgRunState leaf cfg.orig cfg) (hconf : cfg.conflict = none)
    {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (hs : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    LcgCore leaf cfg.orig (stepDecideSkip cfg k v) := by
  have hc := h.core
  refine core_move hc rfl (lcgReachable_decideSkip hc.reach hs (lcgSkipTyped hs hc.reach K.int hred))
    hc.voc hc.db rfl (by rw [stepDecideSkip_conflict, hconf])

/-! ## Consume -/

theorem core_consume {cfg next : SchedulerConfig leaf} {orig : List Domain}
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (h : LcgRunState leaf orig cfg) {f : BranchFrame} {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (hcons : stepConsume cfg = some next) :
    LcgCore leaf orig next := by
  have hc := h.core
  have hpb : PendingBacked orig f := h.pend.pending f (by rw [hp]; exact List.mem_cons_self ..)
  have hbr : next.branch = resumePending cfg.orig cfg.branch f := stepConsume_branch hp hcons
  have hck : next.checkpoints = [] := by
    unfold stepConsume at hcons
    rw [hp] at hcons
    simp only [Option.some.injEq] at hcons
    subst hcons
    rfl
  have hn : next.conflict = none := stepConsume_conflict hcons
  have hno : next.orig = cfg.orig := by
    unfold stepConsume at hcons
    rw [hp] at hcons
    simp only [Option.some.injEq] at hcons
    subst hcons
    rfl
  refine ⟨hno.trans hc.orig_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hbr, hc.orig_eq]
    exact lcgResume_reachable hc.reach.learned_ent hpb hfits
  · rw [hbr, hc.orig_eq]
    exact fun e he => resumePending_branchTrailVocabulary (bs := cfg.branch) hpb e he
  · rw [hbr, resumePending_learned]; exact hc.db
  · intro cp hcp; rw [hck] at hcp; cases hcp
  · intro cp hcp; rw [hck] at hcp; cases hcp
  · intro ev hev; rw [hn] at hev; cases hev


/-! ## The jump arm -/

/-- The restoration certificate of the recorded analysis, from the Lcg invariant. -/
theorem cert_of_state {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgRunState leaf cfg.orig cfg)
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

/-- The surviving prefix: every branch-trail entry at level `≤ an.backjumpLevel` lies in the
selected checkpoint's trail (strict-prefix invariant + the certificate's `targetDescends`). -/
theorem surv_of_cert {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg)
    {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    (hc : cfg.conflict = some ev)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hcert : RestorationCertificate leaf cfg.branch an) :
    ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail := by
  intro e he hle
  have hlt : an.backjumpLevel < cfg.branch.level := by
    have hd := hcert.targetDescends
    have hpos := recorded_conflict_level_pos hreach.reachable ev hc
    rcases hd with h0 | h1
    · omega
    · exact h1
  obtain ⟨mid, hmid, hmidlev⟩ := checkpointsStrictPrefix_of_reach hreach hcp hlt
  rw [hmid] at he
  rcases List.mem_append.mp he with h1 | h1
  · exact h1
  · exact absurd (hmidlev e h1) (by omega)

/-- The enqueue absence check from recorded-site inhabitedness of the branch frame (a
SUFFICIENT route only: a wipe-out conflict is recorded on an uncovered frame). -/
theorem fresh_of_inhab {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg)
    (hreachS : LcgReachableState leaf orig cfg.branch)
    (hinhab : ∃ a : Assignment, FrameCovers cfg.branch.frame a)
    {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp) :
    ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm := by
  have hcpmem : cp ∈ cfg.checkpoints := checkpointAt_mem hcp
  obtain ⟨below, uip, hrun, hcanon⟩ :=
    reachable_analysis_success leaf cfg ev an hreach.reachable hc ha
  intro e he hcon
  have hass : an.asserting.norm = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting,
      ConflictAnalysis.ofUIP_asserting, norm_norm]
  have hel : e.literal = (uip.negate).norm := by rw [hcon, hass]
  obtain ⟨hident, -⟩ := identifiesChain_of_reach hreach
  obtain ⟨mid, hmid, -⟩ := (hident cp hcpmem).2.1
  have he' : e ∈ cfg.branch.trail := by
    rw [hmid]
    exact List.mem_append.mpr (Or.inl he)
  obtain ⟨m, hm, hmlit, -⟩ := analyzeAtAllowance_uip_on_trail hrun
  obtain ⟨a, hcov⟩ := hinhab
  have h1 : (uip.negate).eval a = some true := by
    have h' := hreachS.agrees e he' a hcov
    rw [hel, Literal.norm_eval] at h'
    exact h'
  have h2 : uip.eval a = some false := (Literal.eval_negate_false_iff uip a).mp h1
  have h3 : uip.eval a = some true := by
    have h' := hreachS.agrees m hm a hcov
    rwa [hmlit] at h'
  rw [h2] at h3
  cases h3

theorem jump_good0 {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgRunState leaf cfg.orig cfg)
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
      LcgGood leaf cfg.orig (syncAll cfg.orig (restorationState cp cfg.branch an g)) := by
  have hco := h.core
  have hcert := cert_of_state K hreach h hroot hc ha
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
  -- the Good bundle of the synchronised restoration state
  have hJcp : FrameJ cfg.orig cp.trail cp.frame := h.frameRun.cps cp hcpmem
  have hShcp : FrameShape cfg.orig cp.frame := h.frameRun.cpShape cp hcpmem
  have hplan : DatabaseAlignedAt (litPool cfg.orig) [an.learned] :=
    databaseAlignedAt_singleton_of_clause halignAn
  have hgood0 : LcgGood leaf cfg.orig (syncAll cfg.orig (restorationState cp cfg.branch an g)) := by
    have hsf : (restorationState cp cfg.branch an g).frame = g := rfl
    refine ⟨syncAll_lcgReachable hpre K.fits, ?_, ?_, ?_, ?_⟩
    · have := frameJ_perform_aux K.int
        (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) hJcp hg
        (restorationState cp cfg.branch an g) rfl rfl
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
  exact ⟨g, hg, hres, hgood0⟩

theorem core_jump {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgRunState leaf cfg.orig cfg)
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
  obtain ⟨g, hg, hres, hgood0⟩ := jump_good0 K hreach h hroot hc ha hcp hp
  have hgood : LcgGood leaf cfg.orig restored := by
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


/-- The restored frame of a jump holds every leaf solution of its pin prefix: the checkpoint
frame does, the learned clause (entailed) makes the asserting literal true at solutions
agreeing with the checkpoint trail, and the closure preserves coverage. -/
theorem jump_frameSnd {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgRunState leaf cfg.orig cfg)
    (hroot : ∀ e ∈ cfg.branch.trail, e.level = 0 → ∀ a, leaf a = true →
      e.literal.eval a = some true)
    {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    FrameSndOrder leaf restored.frame := by
  obtain ⟨g, hg, hres, hgood0⟩ := jump_good0 K hreach h hroot hc ha hcp hp
  have hcert := cert_of_state K hreach h hroot hc ha
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
  have hFg : FrameSndOrder leaf g := by
    intro a ha' hpre
    have hpreCP : Frame.PinsOnOrder cp.frame a := by
      intro j hj w hjw
      have hjg : j ∈ g.order := by
        rw [Frame.filterFrame_order hg]
        exact hj
      exact hpre j hjg w (filterFrame_singleton hg hjw)
    have hcv : FrameCovers cp.frame a := h.cpSnd cp hcpmem a ha' hpreCP
    have hsat := hcert.learnedEntailed an.learned (List.mem_singleton_self _) a ha'
    have h1 := pivot_true hsem (K.fits a ha') (fun e he => by
      have := hbs.agrees e (by rw [hbt]; exact he) a (by rw [hbf]; exact hcv)
      exact this) hsat
    rw [norm_norm, Literal.norm_eval] at h1
    obtain ⟨g', hg', hcv'⟩ := filterFrame_preserves hcv h1
    have : g' = g := Option.some.inj (hg'.symm.trans hg)
    rw [← this]; exact hcv'
  rw [hres]
  refine closure_frameSnd K hgood0 ?_
  rw [syncAll_frame]
  exact hFg

/-! ## Root base along the arms (H2e-2) -/

theorem stepConsume_checkpoints_nil {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame} (hp : cfg.pending = f :: rest)
    (hcons : stepConsume cfg = some next) : next.checkpoints = [] := by
  unfold stepConsume at hcons
  rw [hp] at hcons
  simp only [Option.some.injEq] at hcons
  subst hcons
  rfl

/-- The root-base clause of `LcgRunState`, as a predicate on a configuration. -/
def RootBaseCfg (cfg : SchedulerConfig leaf) : Prop :=
  RootBase leaf cfg.branch.trail ∧ ∀ cp ∈ cfg.checkpoints, RootBase leaf cp.trail

theorem rootBase_jump {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cp : DecisionCheckpoint leaf} {bs : BranchState leaf} {an : ConflictAnalysis}
    {restored : BranchState leaf}
    (hcp : RootBase leaf cp.trail)
    (hp : (BackjumpPlan.ofCheckpoint cp bs an.asserting an.learned).perform bs orig original
      props = some restored) :
    RootBase leaf restored.trail := by
  obtain ⟨g, -, hres⟩ := perform_eq_some_iff.mp hp
  rw [hres]
  refine explainedClosure_rootBase _ _ _ (syncAll_rootBase _ ?_)
  show RootBase leaf (restorationState cp bs an g).trail
  rcases restorationState_trail_cases cp bs an g with ⟨ht, -⟩ | ⟨ht, -⟩
  · rw [ht]; exact hcp
  · rw [ht]; exact rootBase_snoc_reasoned hcp _ (by simp)

/-! ## The one-step law -/

/-- The canonical level-0 falsifiers of a consumed (resumed) pending frame -- the dropped
sibling values recorded as reason-less entries at level `|pre|` (level 0 exactly when `pre = []`)
-- hold at every leaf solution, at every dead supported configuration. DERIVED (H2f) from the
stack-soundness invariant: `consumeRootRun_of_kit`. -/
def ConsumeRootRun (orig : List Domain) (original : List Clause) (props : List Propagator)
    (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf} {f : BranchFrame} {rest : List BranchFrame},
    SupportedReach orig original props cfg → cfg.status = .dead → cfg.pending = f :: rest →
      ∀ e ∈ canonicalFalsifiers cfg.orig f, e.level = 0 →
        ∀ a, leaf a = true → e.literal.eval a = some true

theorem rootBase_consume {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (h : ∀ e ∈ canonicalFalsifiers orig f, e.level = 0 →
      ∀ a, leaf a = true → e.literal.eval a = some true) :
    RootBase leaf (resumePending orig bs f).trail := by
  unfold resumePending
  refine syncAll_rootBase _ ?_
  intro e he hl hr
  change e ∈ canonicalTrail orig f at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨p, -, v, l, -, -, heq⟩ := mem_canonicalPins.mp he
    subst e
    exact absurd hl (Nat.succ_ne_zero p.2)
  · exact h e he hl

/-- UNUSED since H2e-1 (kept for reference): the asserting enqueue of a jump is fresh in the
selected checkpoint's trail. `BackjumpPlan.execute` now skips the append when the literal is
already on the restored trail, so no run premise is needed for `distinct`. -/
def FreshRun (orig : List Domain) (original : List Clause) (props : List Propagator)
    (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ∀ (ev : ConflictEvidence) (an : ConflictAnalysis) (cp : DecisionCheckpoint leaf),
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      ∀ e ∈ cp.trail, e.literal ≠ an.asserting.norm

theorem lcgRunState_step {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {cfg cfg' : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (h : LcgRunState leaf orig cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    LcgRunState leaf orig cfg' := by
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hreach
  subst hor hon hpr
  have hFR : FrameRun cfg' :=
    frameRun_step K.int h.frameRun h.pend.pending hsucc
  have hPS : PendingSideInv cfg.orig cfg' :=
    lcgPendingSideInv_step (shape_of_allInt K.int) h.core.reach hsucc h.pend
  suffices hboth : LcgCore leaf cfg.orig cfg' ∧ RootBaseCfg cfg' ∧ DropInv cfg' from
    ⟨hboth.1, hFR, hPS, hboth.2.1, hboth.2.2.1, hboth.2.2.2.1, hboth.2.2.2.2⟩
  have hRB : RootBaseCfg cfg := h.rootBase
  have hD : DropInv cfg := ⟨h.stack, h.dead, h.cpSnd⟩
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1: recorded evidence
    have hdc : ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a :=
      h.dead (Or.inr (by rw [hc]; exact Option.some_ne_none _))
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact ⟨core_same h.core rfl rfl rfl rfl, hRB, dropInv_stay hD rfl rfl rfl hdc⟩
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact ⟨core_same h.core rfl rfl rfl rfl, hRB, dropInv_stay hD rfl rfl rfl hdc⟩
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact ⟨core_localExclude h.core rfl ev.learned (h.core.ev ev hc).2.1
                  (h.core.ev ev hc).2.2 rfl rfl rfl, hRB, dropInv_stay hD rfl rfl rfl hdc⟩
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                have hck : ∀ cp' ∈ (stepLearnBackjumpAssert cfg
                    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned) ev
                    restored).checkpoints, cp' ∈ cfg.checkpoints := by
                  intro cp' hcp'
                  rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
                    (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                    (ev := ev) (restored := restored)] at hcp'
                  exact (List.mem_filter.mp hcp').1
                refine ⟨core_jump K hreach h (h.rootTrue K.fits) hc ha hcp hp, ⟨?_, ?_⟩, ?_⟩
                · have hj : RootBase leaf restored.trail :=
                    rootBase_jump (hRB.2 cp (checkpointAt_mem hcp)) hp
                  exact hj
                · intro cp' hcp'
                  exact hRB.2 cp' (hck cp' hcp')
                · have hB' : FrameSndOrder leaf restored.frame :=
                    jump_frameSnd K hreach h (h.rootTrue K.fits) hc ha hcp hp
                  exact dropInv_replace hD rfl hck hB'
                    (fun a ha' hcv => absurd hcv (hdc a ha')) rfl rfl
  · -- ROUTE 2: dead branch consumed
    rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none =>
        simp only [consumeStep, hcons] at hsucc
        cases hsucc
    | some next =>
        simp only [consumeStep, hcons] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        cases hp : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hp] at hcons
            cases hcons
        | cons f rest =>
            have hdc : ∀ a, leaf a = true → ¬ FrameCovers cfg.branch.frame a :=
              h.dead (Or.inl hdead)
            have hst : StackSoundFrom leaf (fun _ => False) (cfg.branch.frame :: f :: rest) := by
              have := h.stack
              unfold StackSound at this
              rw [hp] at this
              exact this
            have hpb : PendingBacked cfg.orig f :=
              h.pend.pending f (by rw [hp]; exact List.mem_cons_self ..)
            refine ⟨core_consume K.fits h hp hcons, ⟨?_, ?_⟩, ?_⟩
            · rw [stepConsume_branch hp hcons]
              exact rootBase_consume (consume_falsifiers hst hdc hpb)
            · intro cp hcp
              have hck := stepConsume_checkpoints_nil hp hcons
              simp only [hck] at hcp
              cases hcp
            · unfold stepConsume at hcons
              rw [hp] at hcons
              simp only [Option.some.injEq] at hcons
              subst hcons
              exact dropInv_consume hD hp hdc (by simp [resumePending_frame]) rfl rfl rfl rfl
  · -- ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      have hfr := stepPropagate_branch_frame cfg d
      have hB' : FrameSndOrder leaf (stepPropagate cfg d).branch.frame := by
        rw [hfr]
        intro a ha hp
        have hp' : Frame.PinsOnOrder cfg.branch.frame a := by
          intro j hj w hjw
          have hjd : j ∈ d.frame.order := by
            rw [Frame.filterFrame_order d.filtered]
            exact hj
          exact hp j hjd w (filterFrame_singleton d.filtered hjw)
        exact propagate_covers K h.good hd a ha (frameSnd_of_head h.stack a ha hp')
      refine ⟨core_propagate K h hconf hd, ⟨?_, hRB.2⟩, ?_⟩
      · exact syncSlot_rootBase _ (narrowState_rootBase hRB.1 _ _ _ _) _
      · refine dropInv_replace hD rfl (fun cp hcp => hcp) hB' ?_ rfl
          (by rw [stepPropagate_conflict, hconf])
        rw [hfr]
        exact propagate_covers K h.good hd
    · rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hl : leafWitness leaf cfg with
      | some w =>
          simp only [hl, successor_sat] at hsucc
          cases hsucc
      | none =>
          cases hs : splitData cfg.branch.frame cfg.prio with
          | some p =>
              obtain ⟨l, k, v, vs⟩ := p
              simp only [hl, hs] at hsucc
              split at hsucc
              · rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                exact ⟨core_skip K h hconf hs hred, hRB,
                  dropInv_skip hD (splitData_eq_some_iff.mp hs).2.1
                    (skip_covers h.core.reach K.int K.fits hs hred) hconf⟩
              · rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                have hred' : TrailRedundant cfg.branch.trail l = false := by
                  cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
                refine ⟨core_decide K h hconf hs hred', ⟨decide_rootBase hRB.1 _, ?_⟩,
                  dropInv_decide hD (splitData_eq_some_iff.mp hs).2.1
                    (SparseRun.Frame.splitData_sibling_ne_nil hs) hconf⟩
                intro cp hcp
                change cp ∈ DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints at hcp
                rcases List.mem_cons.mp hcp with rfl | hcp
                · exact hRB.1
                · exact hRB.2 cp hcp
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact ⟨core_localExclude h.core rfl [] (by intro c hc; simp at hc)
                (databaseAlignedAt_nil _) rfl rfl rfl, hRB,
                dropInv_stay hD rfl rfl rfl (stableNone_dead_lcg K.int h.core.reach hl hs)⟩
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          obtain ⟨hcsE, hlsub⟩ := terminal_conflict_entailed K h.core.reach ht
          exact ⟨core_localExclude h.core rfl learned
            (fun c hc => by have := hlsub c hc; simp at this)
            (databaseAlignedAt_terminalResult_conflict K.vocab ht) rfl rfl rfl, hRB,
            dropInv_stay hD rfl rfl rfl (terminal_conflict_dead K h.good ht)⟩
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            obtain ⟨hcsE, hlsub⟩ := terminal_conflict_entailed K h.core.reach ht
            refine ⟨core_analyze h.core rfl rfl
              (by rw [stepAnalyzeConflictCounted_checkpoints]) ?_,
              ⟨hRB.1, by rw [stepAnalyzeConflictCounted_checkpoints]; exact hRB.2⟩,
              dropInv_stay hD rfl rfl (by rw [stepAnalyzeConflictCounted_checkpoints])
                (terminal_conflict_dead K h.good ht)⟩
            intro ev' h'
            obtain ⟨hcl, hlearned, -⟩ :=
              stepAnalyzeConflictCounted_evidence (cfg := cfg) (c := c0) (learned := learned) h'
            refine ⟨?_, ?_, ?_⟩
            · rw [hcl]
              intro c hc a ha
              rw [List.mem_singleton] at hc
              subst hc
              exact hcsE _ (List.mem_cons_self ..) a ha
            · rw [hlearned]
              intro c hc a ha
              exact hcsE c (hlsub c hc) a ha
            · rw [hlearned]
              exact databaseAlignedAt_terminalResult_conflict K.vocab ht
    · exact absurd ht terminalResult_ne_localExcluded

/-- **THE RUN INVARIANT ALONG A SUPPORTED RUN (no `hbr`).** -/
theorem lcgRunState_of_supportedRun {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      LcgRunState leaf orig cfg := by
  intro cfg hreach
  induction hreach with
  | init hent => exact lcgRunState_init K hent
  | step hpre hsucc ih =>
      exact lcgRunState_step K hpre ih hsucc

/-- **`ConsumeRootRun`, DERIVED (H2f)**: the canonical level-0 falsifiers of a resumed pending
frame hold at every leaf solution, from the stack/dead soundness of the Lcg run state. -/
theorem consumeRootRun_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    ConsumeRootRun orig original props leaf := by
  intro cfg f rest hreach hdead hp
  have h := lcgRunState_of_supportedRun K hreach
  have hdc := h.dead (Or.inl hdead)
  have hst : StackSoundFrom leaf (fun _ => False) (cfg.branch.frame :: f :: rest) := by
    have := h.stack
    unfold StackSound at this
    rw [hp] at this
    exact this
  have hpb : PendingBacked orig f := h.pend.pending f (by rw [hp]; exact List.mem_cons_self ..)
  rw [h.core.orig_eq]
  exact consume_falsifiers hst hdc hpb

/-- **`lcgReach_of_kit`**: branch reachability along a supported run, without `hbr`. -/
theorem lcgReach_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    LcgReachableState leaf orig cfg.branch :=
  (lcgRunState_of_supportedRun K hreach).core.reach


/-- `EntailedRun` along a supported run of the kit (no `hbr`). -/
theorem entailedRun_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    EntailedRun orig original props leaf := by
  intro cfg hreach
  exact (lcgRunState_of_supportedRun K hreach).core.reach.learned_ent

/-- **`hcertEnt` of `LcgAsserting`, derived** (no `hbr`): the learned clause of a recorded
analysis is entailed, from the restoration certificate of the Lcg run state. -/
theorem hcertEnt_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → LearnedEntailed leaf [an.learned] := by
  intro cfg ev an hreach hc ha
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hreach
  subst hor hon hpr
  have h := lcgRunState_of_supportedRun K hreach
  exact (cert_of_state K hreach h (h.rootTrue K.fits) hc ha).learnedEntailed

/-- The restoration certificate at every recorded analysis of a supported run (no `hbr`). -/
theorem cert_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → RestorationCertificate leaf cfg.branch an := by
  intro cfg ev an hreach hc ha
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hreach
  subst hor hon hpr
  have h := lcgRunState_of_supportedRun K hreach
  exact cert_of_state K hreach h (h.rootTrue K.fits) hc ha

/-- **The jump premise `AssertingSem`, derived** (no `hbr`, no `hcertEnt`). -/
theorem assertingSem_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      AssertingSem cfg := by
  intro cfg hreach ev an cp hconf hana hcp
  have hcert := cert_of_kit K hreach hconf hana
  have hcov := surv_of_cert hreach hconf hcp hcert
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

end LeanFzn.Solver.UIP.LcgRunStep
