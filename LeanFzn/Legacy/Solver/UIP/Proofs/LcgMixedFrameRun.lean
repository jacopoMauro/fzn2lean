/-
Purpose: mixed integer/Boolean configuration frames, initialization, and one-step preservation.
Dependencies: LcgBooleanPins supplies shape-aware frame/pin operations;
LcgRunInvariantStep supplies existing frame shape and checkpoint bundles;
LcgRunInvariantAbsentShape derives the full semantic frame contract.
DAG: structural Boolean preservation -> this stronger run bundle -> mixed LCG kit.
Boolean pins hold on every supported run. Joint semantic induction supplies pending provenance.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgBooleanPins
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantAbsentShape

namespace LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgFamilies

/-- The existing frame bundle strengthened with Boolean prefix pins on the
current branch and every saved checkpoint. No correctness conclusion is assumed. -/
structure MixedFrameRun {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop
    extends FrameRun cfg where
  branchBoolPins : BoolPinsOn cfg.branch.trail cfg.branch.frame
  checkpointBoolPins : ∀ cp ∈ cfg.checkpoints, BoolPinsOn cp.trail cp.frame

theorem mixedFrameRun_init {prio : List Nat} {actBump : Bool} {leaf : Assignment → Bool} {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    (hshape : ShapeTypedDomains orig) (hnd : ∀ d ∈ orig, (Dom.enum d).Nodup) :
    MixedFrameRun (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) where
  toFrameRun :=
    { branch := frameJ_root_shape hshape
      cps := by
        intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst cp
        exact frameJ_root_shape hshape
      shape := frameShape_root hnd
      cpShape := by
        intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst cp
        exact frameShape_root hnd
      pendNodup := by intro f hf; cases hf }
  branchBoolPins := boolPinsOn_nil _ rfl
  checkpointBoolPins := by
    intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst cp
    exact boolPinsOn_nil _ rfl

/-- The stronger bundle derives the full frame contract for the current
branch from the problem's legitimate shape hypothesis. -/
theorem MixedFrameRun.frameExplained {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (h : MixedFrameRun cfg)
    (hshape : ShapeTypedDomains cfg.orig) : FrameExplainedFull cfg.orig cfg.branch :=
  frameExplainedFull_of_frameJ_shape hshape h.branch h.branchBoolPins

/-- Shape-aware preservation of the frame component across every real dispatcher arm.
Checkpoint Boolean pins are used only for restored-prefix explanations. -/
theorem frameRun_step_shape {cfg cfg' : SchedulerConfig leaf}
    (hint : ShapeTypedDomains cfg.orig) (hinv : FrameRun cfg)
    (hcpPins : ∀ cp ∈ cfg.checkpoints, BoolPinsOn cp.trail cp.frame)
    (hpend : ∀ f ∈ cfg.pending, PendingBacked cfg.orig f)
    (hsucc : (schedulerNext cfg).successor = some cfg') : FrameRun cfg' := by
  have hor : cfg'.orig = cfg.orig := W1.schedulerNext_succ_orig hsucc
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1: recorded evidence
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact frameRun_same hinv rfl rfl rfl rfl rfl
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact frameRun_same hinv rfl rfl rfl rfl rfl
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact frameRun_same hinv rfl rfl rfl rfl rfl
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                have hJcp : FrameJ cfg.orig
                    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).checkpoint.trail
                    (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).checkpoint.frame :=
                  hinv.cps cp (checkpointAt_mem hcp)
                have hJ := (frameJ_perform_shape (original := cfg.original) (props := cfg.props) hint hJcp
                  hp).1
                have hSh := frameShape_perform (original := cfg.original) (props := cfg.props)
                  (hinv.cpShape cp (checkpointAt_mem hcp)) hp
                refine ⟨hJ, ?_, hSh, ?_, hinv.pendNodup⟩
                · intro cp' hcp'
                  rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
                    (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                    (ev := ev) (restored := restored)] at hcp'
                  exact hinv.cps cp' (List.mem_filter.mp hcp').1
                · intro cp' hcp'
                  rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
                    (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                    (ev := ev) (restored := restored)] at hcp'
                  exact hinv.cpShape cp' (List.mem_filter.mp hcp').1
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
            have hpb : PendingBacked cfg.orig f :=
              hpend f (by rw [hp]; exact List.mem_cons_self ..)
            have hck : cfg'.checkpoints = [] := by
              unfold LeanFzn.Solver.UIP.stepConsume at hcons
              rw [hp] at hcons
              simp only [Option.some.injEq] at hcons
              subst hcons
              rfl
            have hpd : cfg'.pending = rest := by
              unfold LeanFzn.Solver.UIP.stepConsume at hcons
              rw [hp] at hcons
              simp only [Option.some.injEq] at hcons
              subst hcons
              rfl
            refine ⟨?_, ?_, ?_, ?_, ?_⟩
            · rw [stepConsume_branch hp hcons, hor]
              show FrameJ cfg.orig (resumePending cfg.orig cfg.branch f).trail
                (resumePending cfg.orig cfg.branch f).frame
              rw [resumePending_frame]
              exact frameJ_resume_shape hint cfg.branch hpb
            · intro cp hcp'
              rw [hck] at hcp'
              cases hcp'
            · rw [stepConsume_branch hp hcons, hor]
              show FrameShape cfg.orig (resumePending cfg.orig cfg.branch f).frame
              rw [resumePending_frame]
              refine ⟨?_, hinv.pendNodup f (by rw [hp]; exact List.mem_cons_self ..)⟩
              exact hpb.full_len
            · intro cp hcp'
              rw [hck] at hcp'
              cases hcp'
            · rw [hpd]
              intro g hg
              exact hinv.pendNodup g (by rw [hp]; exact List.mem_cons_of_mem _ hg)
  · -- ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · -- propagation
      rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      exact ⟨frameJ_stepNarrowSync_shape hint cfg.branch d hinv.branch, hinv.cps,
        (by rw [stepPropagate_branch_frame]; exact frameShape_filter d.filtered hinv.shape),
        hinv.cpShape, hinv.pendNodup⟩
    · -- guarded stable dispatch
      rw [hsj] at hsucc
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
              have hparts := splitData_eq_some_iff.mp hs
              have hd : cfg.branch.frame.doms[k]?.map Dom.enum =
                  some (v :: vs.enum) := hparts.2.1
              have hval : valueLiteral k v = some l := hparts.2.2.1
              have hJp : FrameJ cfg.orig cfg.branch.trail cfg.branch.frame := hinv.branch
              have hShp : FrameShape cfg.orig cfg.branch.frame := hinv.shape
              have hkfresh : k ∉ cfg.branch.frame.order := by
                intro hkord
                obtain ⟨v', -, hv', -, -⟩ := hJp.pins k hkord
                obtain ⟨v2, vs2, hlive, hne⟩ := SparseRun.Frame.splitData_live hs
                rw [hv'] at hlive
                have hEq : [v'] = v2 :: vs2.enum := Option.some.inj hlive
                injection hEq with _ h2
                exact hne h2.symm
              split at hsucc
              · -- redundant-pin skip
                rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                obtain ⟨e, he, hel⟩ := trailRedundant_iff.mp hred
                refine ⟨?_, hinv.cps, (frameShape_split hShp hd).1, hinv.cpShape,
                  hinv.pendNodup⟩
                exact frameJ_split_value_shape hint hJp hd hval hkfresh
                  (fun x hx => hx) he hel (split_agree_skip hd hJp.agree)
              · -- fresh split
                rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                refine ⟨?_, ?_, (frameShape_split hShp hd).1, ?_, ?_⟩
                · show FrameJ cfg.orig
                    (cfg.branch.trail ++ [⟨l.norm, cfg.branch.level + 1, none⟩])
                    (cfg.branch.frame.pin k v)
                  exact frameJ_split_value_shape hint hJp hd hval hkfresh
                    (fun x hx => List.mem_append_left _ hx)
                    (List.mem_append_right _ (List.mem_singleton_self _)) rfl
                    (split_agree_push_value hJp.agree hd hval)
                · intro cp hcp'
                  have hck : (stepDecide cfg k v vs l).checkpoints
                      = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
                  rw [hck] at hcp'
                  rcases List.mem_cons.mp hcp' with rfl | hcp'
                  · exact hinv.branch
                  · exact hinv.cps cp hcp'
                · intro cp hcp'
                  have hck : (stepDecide cfg k v vs l).checkpoints
                      = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
                  rw [hck] at hcp'
                  rcases List.mem_cons.mp hcp' with rfl | hcp'
                  · exact hinv.shape
                  · exact hinv.cpShape cp hcp'
                · intro g hg
                  have hpd : (stepDecide cfg k v vs l).pending
                      = cfg.branch.frame.retire k vs :: cfg.pending := rfl
                  rw [hpd] at hg
                  rcases List.mem_cons.mp hg with rfl | hg
                  · intro d hdd
                    rw [BranchFrame.retire_doms] at hdd
                    rcases List.mem_or_eq_of_mem_set hdd with hmem | heq
                    · exact hShp.2 d hmem
                    · subst heq
                      exact (frameShape_split hShp hd).2
                  · exact hinv.pendNodup g hg
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact frameRun_same hinv rfl rfl rfl rfl rfl
    · -- recorded conflict dispatch
      rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          exact frameRun_same hinv rfl rfl rfl rfl rfl
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            exact frameRun_same hinv rfl rfl rfl rfl rfl
    · exact absurd ht terminalResult_ne_localExcluded


/-- Boolean pins on the branch and all saved checkpoints. -/
def BooleanPinRun {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) : Prop :=
  BoolPinsOn cfg.branch.trail cfg.branch.frame ∧
    ∀ cp ∈ cfg.checkpoints, BoolPinsOn cp.trail cp.frame

theorem booleanPinRun_same {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    (h : BooleanPinRun cfg) (hf : cfg'.branch.frame = cfg.branch.frame)
    (ht : cfg'.branch.trail = cfg.branch.trail) (hc : cfg'.checkpoints = cfg.checkpoints) :
    BooleanPinRun cfg' := by
  constructor
  · rw [hf, ht]; exact h.1
  · intro cp hcp
    rw [hc] at hcp
    exact h.2 cp hcp

/-- Boolean pins are preserved by every actual scheduler successor. No sort,
reachability or semantic correctness assumption is needed for this structural fact. -/
theorem booleanPinRun_step {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    (h : BooleanPinRun cfg)
    (hpend : ∀ f ∈ cfg.pending, PendingBacked cfg.orig f) (hsucc : (schedulerNext cfg).successor = some cfg') :
    BooleanPinRun cfg' := by
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha,
          successor_chronologicalFallback] at hsucc
        cases hsucc
        exact booleanPinRun_same h rfl rfl rfl
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp,
              successor_chronologicalFallback] at hsucc
            cases hsucc
            exact booleanPinRun_same h rfl rfl rfl
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
                cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp,
                  successor_localExclude] at hsucc
                cases hsucc
                exact booleanPinRun_same h rfl rfl rfl
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp,
                  successor_learnBackjumpAssert] at hsucc
                cases hsucc
                constructor
                · change BoolPinsOn restored.trail restored.frame
                  exact boolPinsOn_perform (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                    (h.2 cp (checkpointAt_mem hcp)) hp
                · intro cp' hcp'
                  rw [stepLearnBackjumpAssert_checkpoints] at hcp'
                  exact h.2 cp' (List.mem_filter.mp hcp').1
  · rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none => simp [consumeStep, hcons] at hsucc
    | some next =>
        simp only [consumeStep, hcons, successor_chronologicalFallback] at hsucc
        cases hsucc
        cases hp : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hp] at hcons
            cases hcons
        | cons f rest =>
            have hck : cfg'.checkpoints = [] := by
              unfold stepConsume at hcons
              rw [hp] at hcons
              simp only [Option.some.injEq] at hcons
              subst cfg'
              rfl
            constructor
            · rw [stepConsume_branch hp hcons, resumePending_frame]
              exact boolPinsOn_resume cfg.orig cfg.branch f
                (hpend f (by rw [hp]; exact List.mem_cons_self ..))
            · intro cp hcp
              rw [hck] at hcp
              cases hcp
  · rcases hrest with ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ |
      ⟨bs, cs, learned, ht, hsj⟩ | ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj, successor_propagate] at hsucc
      cases hsucc
      exact ⟨boolPinsOn_stepNarrowSync cfg.branch d h.1, h.2⟩
    · rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hl : leafWitness leaf cfg with
      | some w => simp [hl] at hsucc
      | none =>
          cases hs : splitData cfg.branch.frame cfg.prio with
          | none =>
              simp only [hl, hs, successor_localExclude] at hsucc
              cases hsucc
              exact booleanPinRun_same h rfl rfl rfl
          | some p =>
              obtain ⟨l, k, v, vs⟩ := p
              simp only [hl, hs] at hsucc
              have hparts := splitData_eq_some_iff.mp hs
              have hd : cfg.branch.frame.doms[k]?.map Dom.enum =
                  some (v :: vs.enum) := hparts.2.1
              have hval : valueLiteral k v = some l := hparts.2.2.1
              have hkfresh : k ∉ cfg.branch.frame.order := by
                intro hkord
                obtain ⟨v', hv'⟩ := h.1.1 k hkord
                obtain ⟨v2, vs2, hlive, hne⟩ := SparseRun.Frame.splitData_live hs
                rw [hv'] at hlive
                have hEq : [v'] = v2 :: vs2.enum := Option.some.inj hlive
                injection hEq with _ h2
                exact hne h2.symm
              split at hsucc
              · rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                obtain ⟨e, he, hel⟩ := trailRedundant_iff.mp hred
                exact ⟨boolPinsOn_append_value h.1 hd hval hkfresh
                  (fun _ hx => hx) he hel, h.2⟩
              · rw [successor_decide] at hsucc
                cases hsucc
                constructor
                · exact boolPinsOn_append_value h.1 hd hval hkfresh
                    (fun _ hx => List.mem_append_left _ hx)
                    (List.mem_append_right _ (List.mem_singleton_self _)) rfl
                · intro cp hcp
                  change cp ∈ DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints at hcp
                  rcases List.mem_cons.mp hcp with rfl | hcp
                  · exact h.1
                  · exact h.2 cp hcp
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep, successor_localExclude] at hsucc
          cases hsucc
          exact booleanPinRun_same h rfl rfl rfl
      | cons c rest =>
          by_cases hz : cfg.branch.level = 0
          · simp [conflictStep, hz] at hsucc
          · simp only [conflictStep, if_neg hz, successor_analyzeConflict] at hsucc
            cases hsucc
            exact booleanPinRun_same h rfl rfl rfl
    · exact absurd ht terminalResult_ne_localExcluded

/-- Boolean pins hold on every supported run, without any caller premise. -/
theorem booleanPinRun_of_supportedRun {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → BooleanPinRun cfg := by
  intro cfg hr
  induction hr with
  | init hent =>
      constructor
      · exact boolPinsOn_nil _ rfl
      · intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst cp
        exact boolPinsOn_nil _ rfl
  | step hpre hsucc ih =>
      rename_i cfg0 cfg1
      have hor : cfg0.orig = orig := SupportedReach.orig_eq hpre
      have hpend := (pendingSideInv_of_premises hshape hbr hpre).pending
      exact booleanPinRun_step ih (by rw [hor]; exact hpend) hsucc

/-- The mixed bundle is preserved by each actual successor. Pending-frame
provenance is supplied by the joint semantic run invariant, as for the existing integer proof. -/
theorem mixedFrameRun_step {leaf : Assignment → Bool} {cfg cfg' : SchedulerConfig leaf}
    (hshape : ShapeTypedDomains cfg.orig) (h : MixedFrameRun cfg)
    (hpend : ∀ f ∈ cfg.pending, PendingBacked cfg.orig f)
    (hs : (schedulerNext cfg).successor = some cfg') : MixedFrameRun cfg' where
  toFrameRun := frameRun_step_shape hshape h.toFrameRun h.checkpointBoolPins hpend hs
  branchBoolPins := (booleanPinRun_step ⟨h.branchBoolPins, h.checkpointBoolPins⟩ hpend hs).1
  checkpointBoolPins := (booleanPinRun_step ⟨h.branchBoolPins, h.checkpointBoolPins⟩ hpend hs).2

end LeanFzn.Solver.UIP.LcgRunInv
