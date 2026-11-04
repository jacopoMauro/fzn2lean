/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunInvariantStep.lean
U1c (2): the frame invariant of an integer box holds at every configuration of every
supported run (one-step law `frameRun_step` + init + induction).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantFrame
import LeanFzn.Legacy.Solver.UIP.Proofs.ExtendedPoolProducers
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunInv

variable {leaf : Assignment → Bool}

/-- The frame-explanation bundle of a configuration: current branch + saved checkpoints. -/
structure FrameRun (cfg : SchedulerConfig leaf) : Prop where
  branch : FrameJ cfg.orig cfg.branch.trail cfg.branch.frame
  cps : ∀ cp ∈ cfg.checkpoints, FrameJ cfg.orig cp.trail cp.frame
  shape : FrameShape cfg.orig cfg.branch.frame
  cpShape : ∀ cp ∈ cfg.checkpoints, FrameShape cfg.orig cp.frame
  pendNodup : ∀ f ∈ cfg.pending, ∀ d ∈ f.1, (Dom.enum d).Nodup

theorem explDoms_root {orig : List Domain} (hint : AllIntBox orig) :
    ExplDoms orig [] orig := by
  intro s
  refine ⟨⟨fun mx h => ?_, fun mn h => ?_⟩, fun c h => ?_, fun k h1 h2 h3 => ?_⟩
  · obtain ⟨-, hall⟩ := domMaxI_spec h
    refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    have hvD : v ∈ orig.getD s Dom.empty :=
      (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
    obtain ⟨k, rfl⟩ := allInt_getD hint s v hv
    have := hall _ hvD k rfl
    simp [Literal.valueHolds, negLe, Value.intView]
    omega
  · obtain ⟨-, hall⟩ := domMinI_spec h
    refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    have hvD : v ∈ orig.getD s Dom.empty :=
      (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
    obtain ⟨k, rfl⟩ := allInt_getD hint s v hv
    have := hall _ hvD k rfl
    simp [Literal.valueHolds, posLe, Value.intView]
    omega
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    change v ∈ Dom.enum (orig.getD s Dom.empty) at hv
    rw [h] at hv
    have : v = Value.int c := List.mem_singleton.mp hv
    subst this
    simp [Literal.valueHolds, posNe, Value.intView]
  · refine Or.inl ((litFalseAtRoot_iff orig _).mpr ?_)
    intro v hv
    have hvD : v ∈ orig.getD s Dom.empty :=
      (DomainLike.mem_iff _ v).mpr (by rw [domElems_eq_enum]; exact hv)
    obtain ⟨k, rfl⟩ := allInt_getD hint s v hv
    have := h3 _ hvD
    simp [Literal.valueHolds, negNe, Value.intView] at this ⊢
    exact this

theorem frameShape_root {orig : List Domain} (hnd : ∀ d ∈ orig, (Dom.enum d).Nodup) :
    FrameShape orig { doms := orig, order := [] } :=
  ⟨by simp [Frame.domains], fun d hd => hnd d hd⟩

theorem frameJ_root {orig : List Domain} (hint : AllIntBox orig) :
    FrameJ orig [] { doms := orig, order := [] } where
  expl := by
    simpa [Frame.domains] using explDoms_root hint
  pins := fun s hs => by simp at hs
  nc := fun i _ w hw hn => absurd (by simpa [Frame.domains] using hw) hn
  fits := fun s v hv => by simpa [Frame.domains] using hv
  agree := fun s e he => by cases he

/-- A step that keeps branch frame/trail and the checkpoint list. -/
theorem frameRun_same {cfg cfg' : SchedulerConfig leaf} (hinv : FrameRun cfg)
    (ho : cfg'.orig = cfg.orig) (hf : cfg'.branch.frame = cfg.branch.frame)
    (ht : cfg'.branch.trail = cfg.branch.trail) (hc : cfg'.checkpoints = cfg.checkpoints)
    (hp : cfg'.pending = cfg.pending) :
    FrameRun cfg' where
  branch := by rw [ho, hf, ht]; exact hinv.branch
  cps := by intro cp hcp; rw [hc] at hcp; rw [ho]; exact hinv.cps cp hcp
  shape := by rw [ho, hf]; exact hinv.shape
  cpShape := by intro cp hcp; rw [hc] at hcp; rw [ho]; exact hinv.cpShape cp hcp
  pendNodup := by rw [hp]; exact hinv.pendNodup

/-- **THE ONE-STEP LAW of the frame invariant** (arm table of the real dispatcher). -/
theorem frameRun_step {cfg cfg' : SchedulerConfig leaf}
    (hint : AllIntBox cfg.orig) (hinv : FrameRun cfg)
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
                have hJ := frameJ_perform (original := cfg.original) (props := cfg.props) hint hJcp hp
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
              exact frameJ_resume hint cfg.branch hpb
            · intro cp hcp'
              rw [hck] at hcp'
              cases hcp'
            · rw [stepConsume_branch hp hcons, hor]
              show FrameShape cfg.orig (resumePending cfg.orig cfg.branch f).frame
              rw [resumePending_frame]
              exact ⟨by simpa [FrameShape, fullDomains, Frame.domains] using hpb.full_len,
                hinv.pendNodup f (by rw [hp]; exact List.mem_cons_self ..)⟩
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
      exact ⟨frameJ_stepNarrowSync hint cfg.branch d hinv.branch, hinv.cps,
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
              have hd : cfg.branch.frame.doms[k]?.map Dom.enum = some (v :: vs.enum) :=
                hparts.2.1
              have hlit : valueLiteral k v = some l := hparts.2.2.1
              have hvs : vs = Dom.ofList vs.enum := hparts.2.2.2
              have hJp : FrameJ cfg.orig cfg.branch.trail cfg.branch.frame := hinv.branch
              have hShp : FrameShape cfg.orig cfg.branch.frame := hinv.shape
              have hvmemD : v ∈ (Frame.domains cfg.branch.frame).getD k Dom.empty :=
                (DomainLike.mem_iff _ v).mpr (by
                  rw [domElems_eq_enum, split_domains_parent hd]
                  exact List.mem_cons_self)
              have hvmem : v ∈ cfg.orig.getD k Dom.empty := hJp.fits k v hvmemD
              obtain ⟨i, hi⟩ := allInt_getD hint k v
                (by rw [← domElems_eq_enum]; exact (DomainLike.mem_iff _ v).mp hvmem)
              have hl' : l = negNe k i := by
                rw [hi] at hlit
                have h := hlit
                simp only [valueLiteral, Option.some.injEq] at h
                exact h.symm
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
                have hel' : e.literal = negNe k i := by rw [hel, hl']; rfl
                refine ⟨?_, hinv.cps, (frameShape_split hShp hd).1, hinv.cpShape, hinv.pendNodup⟩
                exact frameJ_split (fun w hw => allInt_getD hint k w
                  (by rw [← domElems_eq_enum]; exact (DomainLike.mem_iff _ w).mp hw)) hJp hd hi hkfresh
                  (fun x hx => hx) he hel'
                  (split_agree_skip hd hJp.agree)
              · -- fresh split
                rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                refine ⟨?_, ?_, (frameShape_split hShp hd).1, ?_, ?_⟩
                · show FrameJ cfg.orig
                    (cfg.branch.trail ++ [⟨l.norm, cfg.branch.level + 1, none⟩])
                    (cfg.branch.frame.pin k v)
                  have hn : l.norm = negNe k i := by rw [hl']; rfl
                  rw [hn]
                  exact frameJ_split (fun w hw => allInt_getD hint k w
                  (by rw [← domElems_eq_enum]; exact (DomainLike.mem_iff _ w).mp hw)) hJp hd hi hkfresh
                    (fun x hx => List.mem_append_left _ hx)
                    (List.mem_append_right _ (List.mem_singleton_self _)) rfl
                    (split_agree_push hJp.agree hd hi)
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

theorem shape_of_allInt {orig : List Domain} (h : AllIntBox orig) : ShapeTypedDomains orig :=
  fun d hd => Or.inl (h d hd)

/-- **(2) THE FRAME INVARIANT ALONG A SUPPORTED RUN** of an integer box. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem frameRun_of_supportedRun {orig : List Domain} {original : List Clause}
    {props : List Propagator} (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, (Dom.enum d).Nodup)
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → FrameRun cfg := by
  intro cfg hreach
  induction hreach with
  | init hent =>
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact frameJ_root hint
      · intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst hcp
        exact frameJ_root hint
      · exact frameShape_root hnd
      · intro cp hcp
        simp only [SchedulerConfig.init, List.mem_singleton] at hcp
        subst hcp
        exact frameShape_root hnd
      · intro f hf; cases hf
  | step hpre hsucc ih =>
      rename_i cfg0 cfg1
      have hor : cfg0.orig = orig := SupportedReach.orig_eq hpre
      have hpend := (pendingSideInv_of_premises hshape hbr hpre).pending
      exact frameRun_step (by rw [hor]; exact hint) ih
        (by rw [hor]; exact hpend) hsucc

/-- The stated `FrameExplainedFull` of an integer box, along a supported run. 
VACUOUS on non-unit LCG instances (hbr_refuted); use *_of_kit (LcgKitFinal). -/
theorem frameExplainedFull_of_supportedRun {orig : List Domain} {original : List Clause}
    {props : List Propagator} (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, (Dom.enum d).Nodup)
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      FrameExplainedFull orig cfg.branch := by
  intro cfg hreach
  have h := (frameRun_of_supportedRun hint hnd hshape hbr hreach).branch
  rw [SupportedReach.orig_eq hreach] at h
  exact frameExplainedFull_of_explDoms hint h.expl

end LeanFzn.Solver.UIP.LcgRunInv
