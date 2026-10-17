/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantTrailStep.lean
U1c (3): the semantic reason contract `TrailSem` is preserved by every scheduler arm.
Named premise (U1d): the asserting entry of a jump is semantically justified by the checkpoint
prefix (`AssertingSem`).
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunInvariantReasons
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

structure TrailRun (cfg : SchedulerConfig leaf) : Prop where
  branch : TrailSem cfg.orig cfg.branch.trail
  cps : ∀ cp ∈ cfg.checkpoints, TrailSem cfg.orig cp.trail

/-- **`AssertingSem`** (named premise, U1d): at a jump site the learned clause is a semantic
reason for the asserting literal at the checkpoint prefix. -/
def AssertingSem (cfg : SchedulerConfig leaf) : Prop :=
  ∀ ev an cp, cfg.conflict = some ev → ev.analysis = some an →
    checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
    SemReasonOK cfg.orig cp.trail an.asserting.norm an.learned

theorem trailRun_same {cfg cfg' : SchedulerConfig leaf} (hinv : TrailRun cfg)
    (ho : cfg'.orig = cfg.orig) (ht : cfg'.branch.trail = cfg.branch.trail)
    (hc : cfg'.checkpoints = cfg.checkpoints) : TrailRun cfg' where
  branch := by rw [ho, ht]; exact hinv.branch
  cps := by intro cp hcp; rw [hc] at hcp; rw [ho]; exact hinv.cps cp hcp

/-- **THE ONE-STEP LAW of `TrailSem`**. -/
theorem trailRun_step {cfg cfg' : SchedulerConfig leaf}
    (hint : AllIntBox cfg.orig) (hF : FrameRun cfg)
    (hT : TrailRun cfg)
    (hP : ∀ (bs : BranchState leaf), FrameExplainedFull cfg.orig bs →
      TrailSnapFixed cfg.orig bs.trail → ∀ p ∈ cfg.props, PropSemContract cfg.orig p bs)
    (hsn : TrailSnapFixed cfg.orig cfg.branch.trail)
    (hsn' : TrailSnapFixed cfg.orig cfg'.branch.trail) (hA : AssertingSem cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg') : TrailRun cfg' := by
  have hor : cfg'.orig = cfg.orig := W1.schedulerNext_succ_orig hsucc
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact trailRun_same hT rfl rfl rfl
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact trailRun_same hT rfl rfl rfl
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact trailRun_same hT rfl rfl rfl
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                have hmem := checkpointAt_mem hcp
                refine ⟨?_, ?_⟩
                · exact trailSem_perform (original := cfg.original) (props := cfg.props) (restored := restored)
                    hint hP
                    (hF.cps cp hmem) (hF.cpShape cp hmem) (hT.cps cp hmem)
                    (hA ev an cp hc ha hcp) hp hsn'
                · intro cp' hcp'
                  rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
                    (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                    (ev := ev) (restored := restored)] at hcp'
                  exact hT.cps cp' (List.mem_filter.mp hcp').1
  · -- ROUTE 2: consume
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
            have hck : cfg'.checkpoints = [] := by
              unfold LeanFzn.Solver.UIP.stepConsume at hcons
              rw [hp] at hcons
              simp only [Option.some.injEq] at hcons
              subst hcons
              rfl
            refine ⟨?_, ?_⟩
            · rw [stepConsume_branch hp hcons, hor]
              show TrailSem cfg.orig (resumePending cfg.orig cfg.branch f).trail
              unfold resumePending
              apply syncAll_trailSem
              intro i e hi
              have hmem : e ∈ canonicalTrail cfg.orig f := List.mem_of_getElem? hi
              intro r hr
              rw [canonicalTrail_reason_none hmem] at hr
              cases hr
            · intro cp hcp'
              rw [hck] at hcp'
              cases hcp'
  · -- ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · -- propagation
      rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      obtain ⟨lr, fl, hev⟩ := explainedDeduction_event hd
      have hFull := frameExplainedFull_of_explDoms hint hF.branch.expl
      have hsem := nextPruningEvent_implied_sem (original := cfg.original) hint hF.branch
        hF.shape (hP cfg.branch hFull hsn) hev
      exact ⟨stepNarrowSync_trailSem cfg.branch d hT.branch hsem, hT.cps⟩
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
                exact trailRun_same hT rfl rfl rfl
              · rw [successor_decide] at hsucc
                cases hsucc
                refine ⟨?_, ?_⟩
                · show TrailSem cfg.orig (cfg.branch.trail ++ [⟨l.norm, cfg.branch.level + 1, none⟩])
                  exact hT.branch.snoc_decision
                · intro cp hcp'
                  have hck : (stepDecide cfg v vs doms l).checkpoints
                      = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
                  rw [hck] at hcp'
                  rcases List.mem_cons.mp hcp' with rfl | hcp'
                  · exact hT.branch
                  · exact hT.cps cp hcp'
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact trailRun_same hT rfl rfl rfl
    · -- recorded conflict dispatch
      rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          exact trailRun_same hT rfl rfl rfl
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            exact trailRun_same hT rfl rfl rfl
    · exact absurd ht terminalResult_ne_localExcluded

/-- **(3a) `TrailSem` ALONG A CLAMPED SUPPORTED RUN of an integer box.** Premises: compiled-problem
facts (int box, duplicate-free domains, typed emissions, aligned original clauses, family gate),
the branch reachability `hbr`, and the named U1d premise `AssertingSem` at every jump site. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem trailRun_of_supportedRun {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (hraw : raw = dcs.filterMap propagatorOfProved)
    (hprops : props = clampProps orig raw)
    (hfam : ∀ dc ∈ dcs, lcgFamB dc = true)
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, d.Nodup)
    (htyped : ClampPool.EmissionTyped orig raw)
    (horig : DatabaseAligned orig original)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch)
    (hA : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → AssertingSem cfg) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → TrailRun cfg := by
  intro cfg hreach
  induction hreach with
  | init hent =>
      refine ⟨TrailSem.nil _, ?_⟩
      intro cp hcp
      simp only [SchedulerConfig.init, List.mem_singleton] at hcp
      subst hcp
      exact TrailSem.nil _
  | step hpre hsucc ih =>
      rename_i cfg0 cfg1
      have hor : cfg0.orig = orig := SupportedReach.orig_eq hpre
      have hpr : cfg0.props = props := SupportedReach.props_eq hpre
      have hF := frameRun_of_supportedRun hint hnd (shape_of_allInt hint) hbr hpre
      have hsn0 := trailSnapFixed_of_clampedRun hprops htyped horig hbr (shape_of_allInt hint) hpre
      have hsn1 := trailSnapFixed_of_clampedRun hprops htyped horig hbr (shape_of_allInt hint)
        (SupportedReach.step hpre hsucc)
      refine trailRun_step (by rw [hor]; exact hint) hF ih ?_ (by rw [hor]; exact hsn0)
        (by rw [hor]; exact hsn1)
        (hA hpre) hsucc
      intro bs hFull hsnap p hp
      rw [hor] at hFull hsnap ⊢
      rw [hpr] at hp
      exact propSem_of_state hraw hprops hfam hFull hsnap p hp

end LeanFzn.Solver.UIP.LcgRunInv
