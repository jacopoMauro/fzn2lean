/-
File: LeanFzn/Solver/UIP/Proofs/LcgMixedRunStep.lean
A3: the mixed joint one-step law `lcgMixedRunState_step` of `LcgMixedRunState` along
real dispatcher successors, arm by arm, and the mixed run induction plus the mixed
kit projections (`lcgMixedRunState_of_supportedRun`, `lcgMixedReach_of_kit`,
`entailedRun_of_kit_mixed`, `hcertEnt_of_kit_mixed`, `cert_of_kit_mixed`,
`assertingSem_of_kit_mixed`, `consumeRootRun_of_kit_mixed`).
Every statement is the direct twin of the integer declaration of `LcgRunStep`
(`LcgKit` -> `MixedLcgKit`, `LcgRunState` -> `LcgMixedRunState`, `LcgGood` ->
`MixedLcgGood`, `AllIntBox` -> `ShapeTypedDomains`). The body is the integer proof
with the mixed arms substituted (`mixedFrameRun_step`, `lcgPendingSideInv_step`,
`core_*_shape`, `jump_*_shape`, `*_covers_shape`, `*_dead_*_shape`) and the new
`canonical` field supplied by `canonicalCfg_step` with `EmissionCanonical` derived
from the kit's family gate. The pin premises are consumed inside
`mixedFrameRun_step`/`jump_frameSnd_shape`, so no extra premise is needed here.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedCore
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedJump
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedRunDrop
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedConflict
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedFrameRun
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalScheduler
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgCanonicalFamilies
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunStep
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgAsserting LeanFzn.Solver.UIP.LcgRunConflict LeanFzn.Solver.UIP.LcgRunArms
open LeanFzn.Solver.UIP.LcgRunJump LeanFzn.Solver.UIP.LcgRunCert LeanFzn.Solver.UIP.LcgRunPending
open LeanFzn.Solver.UIP.LcgRunState LeanFzn.Solver.UIP.LcgRootTrue LeanFzn.Solver.UIP.LcgRootBase
open LeanFzn.Solver.UIP.LcgRunDrop
open LeanFzn.Solver.UIP.LcgRunStep (core_same core_localExclude core_analyze core_move
  rootBase_jump rootBase_consume surv_of_cert stepConsume_checkpoints_nil RootBaseCfg ConsumeRootRun)
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedRunState
open LeanFzn.Solver.UIP.LcgMixedCore (core_decide core_skip core_propagate_shape core_consume_shape)
open LeanFzn.Solver.UIP.LcgMixedJump LeanFzn.Solver.UIP.LcgMixedRunDrop
open LeanFzn.Solver.UIP.LcgMixedConflict
open LeanFzn.Solver.UIP.LcgCanonicalScheduler LeanFzn.Solver.UIP.LcgCanonicalClauses
open LeanFzn.Solver.UIP.LcgCanonicalFamilies

namespace LeanFzn.Solver.UIP.LcgMixedRunStep

variable {leaf : Assignment → Bool}

/-! ## The one-step law -/

/-- **THE MIXED ONE-STEP LAW**: a `MixedLcgKit` carries the combined mixed run
invariant along every real dispatcher successor, without any additional premise
beyond the mixed run state. The `canonical` field is the new mixed component
(integer `LcgRunState` has no analogue): `canonicalCfg_step` over the kit's
`EmissionCanonical` from the family gate. -/
theorem lcgMixedRunState_step {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg cfg' : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (h : LcgMixedRunState leaf orig cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    LcgMixedRunState leaf orig cfg' := by
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hreach
  subst hor hon hpr
  have hFR : MixedFrameRun cfg' :=
    mixedFrameRun_step K.shape h.frameRun h.pend.pending hsucc
  have hPS : PendingSideInv cfg.orig cfg' :=
    lcgPendingSideInv_step K.shape h.core.reach hsucc h.pend
  have hCanon : CanonicalCfg cfg' :=
    canonicalCfg_step h.canonical
      (by rw [K.props_eq, K.raw_eq]
          exact clampProps_canonical cfg.orig (emissionCanonical_of_families K.fam))
      hsucc
  suffices hboth : LcgCore leaf cfg.orig cfg' ∧ RootBaseCfg cfg' ∧ DropInv cfg' from
    ⟨hboth.1, hFR, hCanon, hPS, hboth.2.1, hboth.2.2.1, hboth.2.2.2.1, hboth.2.2.2.2⟩
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
                refine ⟨core_jump_shape K hreach h (h.rootTrue K.fits) hc ha hcp hp,
                  ⟨?_, ?_⟩, ?_⟩
                · have hj : RootBase leaf restored.trail :=
                    rootBase_jump (hRB.2 cp (checkpointAt_mem hcp)) hp
                  exact hj
                · intro cp' hcp'
                  exact hRB.2 cp' (hck cp' hcp')
                · have hB' : FrameSndOrder leaf restored.frame :=
                    jump_frameSnd_shape K hreach h (h.rootTrue K.fits) hc ha hcp hp
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
            refine ⟨core_consume_shape K.fits h hp hcons, ⟨?_, ?_⟩, ?_⟩
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
        exact propagate_covers_shape K h.good hd a ha (frameSnd_of_head h.stack a ha hp')
      refine ⟨core_propagate_shape K h.core h.good hconf hd, ⟨?_, hRB.2⟩, ?_⟩
      · exact syncSlot_rootBase _ (narrowState_rootBase hRB.1 _ _ _ _) _
      · refine dropInv_replace hD rfl (fun cp hcp => hcp) hB' ?_ rfl
          (by rw [stepPropagate_conflict, hconf])
        rw [hfr]
        exact propagate_covers_shape K h.good hd
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
                exact ⟨core_skip K h.core hconf hs hred, hRB,
                  dropInv_skip hD (splitData_eq_some_iff.mp hs).2.1
                    (skip_covers_shape h.core.reach K.shape K.fits hs hred) hconf⟩
              · rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                have hred' : TrailRedundant cfg.branch.trail l = false := by
                  cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
                refine ⟨core_decide K h.core hconf hs hred', ⟨decide_rootBase hRB.1 _, ?_⟩,
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
                dropInv_stay hD rfl rfl rfl (stableNone_dead_lcg_shape K.shape h.core.reach hl hs)⟩
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          obtain ⟨hcsE, hlsub⟩ :=
            LeanFzn.Solver.UIP.LcgMixedConflict.terminal_conflict_entailed K h.core.reach ht
          exact ⟨core_localExclude h.core rfl learned
            (fun c hc => by have := hlsub c hc; simp at this)
            (databaseAlignedAt_terminalResult_conflict K.vocab ht) rfl rfl rfl, hRB,
            dropInv_stay hD rfl rfl rfl (terminal_conflict_dead_shape K h.good ht)⟩
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            obtain ⟨hcsE, hlsub⟩ :=
              LeanFzn.Solver.UIP.LcgMixedConflict.terminal_conflict_entailed K h.core.reach ht
            refine ⟨core_analyze h.core rfl rfl
              (by rw [stepAnalyzeConflictCounted_checkpoints]) ?_,
              ⟨hRB.1, by rw [stepAnalyzeConflictCounted_checkpoints]; exact hRB.2⟩,
              dropInv_stay hD rfl rfl (by rw [stepAnalyzeConflictCounted_checkpoints])
                (terminal_conflict_dead_shape K h.good ht)⟩
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

/-- **THE MIXED RUN INVARIANT ALONG A SUPPORTED RUN.** -/
theorem lcgMixedRunState_of_supportedRun {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      LcgMixedRunState leaf orig cfg := by
  intro cfg hreach
  induction hreach with
  | init hent => exact lcgMixedRunState_init K hent
  | step hpre hsucc ih =>
      exact lcgMixedRunState_step K hpre ih hsucc

/-! ## The mixed kit projections -/

/-- **`ConsumeRootRun`, DERIVED (mixed)**: the canonical level-0 falsifiers of a resumed
pending frame hold at every leaf solution, from the stack/dead soundness of the mixed
run state. -/
theorem consumeRootRun_of_kit_mixed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) :
    ConsumeRootRun orig original props leaf := by
  intro cfg f rest hreach hdead hp
  have h := lcgMixedRunState_of_supportedRun K hreach
  have hdc := h.dead (Or.inl hdead)
  have hst : StackSoundFrom leaf (fun _ => False) (cfg.branch.frame :: f :: rest) := by
    have := h.stack
    unfold StackSound at this
    rw [hp] at this
    exact this
  have hpb : PendingBacked orig f := h.pend.pending f (by rw [hp]; exact List.mem_cons_self ..)
  rw [h.core.orig_eq]
  exact consume_falsifiers hst hdc hpb

/-- **`lcgMixedReach_of_kit`**: branch reachability along a supported run of the mixed kit. -/
theorem lcgMixedReach_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    LcgReachableState leaf orig cfg.branch :=
  (lcgMixedRunState_of_supportedRun K hreach).core.reach

/-- `EntailedRun` along a supported run of the mixed kit. -/
theorem entailedRun_of_kit_mixed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) :
    EntailedRun orig original props leaf := by
  intro cfg hreach
  exact (lcgMixedRunState_of_supportedRun K hreach).core.reach.learned_ent

/-- **`hcertEnt` of `LcgAsserting`, derived (mixed)**: the learned clause of a recorded
analysis is entailed, from the restoration certificate of the mixed run state. -/
theorem hcertEnt_of_kit_mixed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → LearnedEntailed leaf [an.learned] := by
  intro cfg ev an hreach hc ha
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hreach
  subst hor hon hpr
  have h := lcgMixedRunState_of_supportedRun K hreach
  exact (cert_of_state_shape K hreach h (h.rootTrue K.fits) hc ha).learnedEntailed

/-- The restoration certificate at every recorded analysis of a supported run of the
mixed kit. -/
theorem cert_of_kit_mixed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
        ev.analysis = some an → RestorationCertificate leaf cfg.branch an := by
  intro cfg ev an hreach hc ha
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hreach
  subst hor hon hpr
  have h := lcgMixedRunState_of_supportedRun K hreach
  exact cert_of_state_shape K hreach h (h.rootTrue K.fits) hc ha

/-- **The jump premise `AssertingSem`, derived (mixed)**: no `hbr`, no `hcertEnt`. -/
theorem assertingSem_of_kit_mixed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      AssertingSem cfg := by
  intro cfg hreach ev an cp hconf hana hcp
  have hcert := cert_of_kit_mixed K hreach hconf hana
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

end LeanFzn.Solver.UIP.LcgMixedRunStep
