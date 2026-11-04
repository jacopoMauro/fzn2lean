/-
File: LeanFzn/Solver/UIP/Proofs/LcgNoBoolRun.lean

DL (decide-site liveness), part 3: along every supported run of the kit, no trail literal (of the
branch or of any saved checkpoint) is a Boolean-atom literal.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgNoBoolTrail
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgAsserting LeanFzn.Solver.UIP.LcgRunConflict LeanFzn.Solver.UIP.LcgRunArms
open LeanFzn.Solver.UIP.LcgRunJump LeanFzn.Solver.UIP.LcgRunCert LeanFzn.Solver.UIP.LcgRunPending
open LeanFzn.Solver.UIP.LcgRunState LeanFzn.Solver.UIP.LcgRootTrue LeanFzn.Solver.UIP.LcgRootBase
open LeanFzn.Solver.UIP.LcgRunDrop LeanFzn.Solver.UIP.LcgRunStep LeanFzn.Solver.UIP.LcgNoBool
open LeanFzn.Solver.UIP.LcgNoBoolTrail

namespace LeanFzn.Solver.UIP.LcgNoBoolRun

variable {leaf : Assignment → Bool}

/-- The no-Boolean-atom invariant of a configuration. -/
def NBCfg (cfg : SchedulerConfig leaf) : Prop :=
  NBTrail cfg.branch.trail ∧ ∀ cp ∈ cfg.checkpoints, NBTrail cp.trail

theorem valueLiteral_nb {s : Nat} {v : Value} {l : Literal}
    (hv : ∃ k : Int, v = Value.int k) (hl : valueLiteral s v = some l) : NoBoolAtom l := by
  obtain ⟨k, rfl⟩ := hv
  have : l = negNe s k := by simpa [valueLiteral] using hl.symm
  subst this
  exact noBoolAtom_negNe _ _

/-! ## The canonical resume -/

theorem canonicalTrail_nb {orig : List Domain} {f : BranchFrame} (hint : AllIntBox orig)
    (hb : PendingBacked orig f) : NBTrail (canonicalTrail orig f) := by
  intro e he
  rw [canonicalTrail] at he
  rcases List.mem_append.mp he with he | he
  · obtain ⟨p, hp, v, l, hv, hl, heq⟩ := mem_canonicalPins.mp he
    subst e
    have hmem : v ∈ orig.getD p.1 Dom.empty := hb.fit p.1 v (by
      show v ∈ (fullDomains f).getD p.1 Dom.empty
      exact (DomainLike.mem_iff _ v).mpr (by
        rw [domElems_eq_enum]
        show v ∈ Dom.enum (f.doms.getD p.1 Dom.empty)
        rw [enum_getD_of_enum_singleton hv]
        simp))
    exact (noBoolAtom_norm _).mpr
      (valueLiteral_nb (allInt_getD hint _ _ ((DomainLike.mem_iff _ v).mp hmem)) hl)
  · obtain ⟨p, hp, hk, q, hq, l, hv, hkeep, htk, heq⟩ :=
      mem_canonicalFalsifiers.mp he
    subst e
    obtain ⟨hqlt, hqval⟩ := mem_zipIdx_iff'.mp hq
    have hqmem : q.1 ∈ orig.getD p.2 Dom.empty :=
      (DomainLike.mem_iff _ q.1).mpr (by
        rw [domElems_eq_enum, ← hqval]
        exact List.getElem_mem hqlt)
    have := valueLiteral_nb (allInt_getD hint _ _ ((DomainLike.mem_iff _ q.1).mp hqmem)) hv
    exact (noBoolAtom_norm _).mpr ((noBoolAtom_negate _).mpr this)

theorem pending_frameInts {orig : List Domain} {f : BranchFrame} (hint : AllIntBox orig)
    (hb : PendingBacked orig f) : ∀ d ∈ f.1, ∀ v ∈ d, ∃ k : Int, v = Value.int k := by
  intro d hd v hv
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hd
  have hget : (fullDomains f).getD i Dom.empty = f.doms[i] := by
    rw [fullDomains, Frame.domains, List.getD_eq_getElem?_getD,
      List.getElem?_eq_getElem hi]
    rfl
  have hvD : v ∈ (fullDomains f).getD i Dom.empty := by
    rw [hget]; exact hv
  exact allInt_getD hint _ v ((DomainLike.mem_iff _ v).mp (hb.fit _ v hvD))

theorem resumePending_nb {orig : List Domain} {bs : BranchState leaf} {f : BranchFrame}
    (hint : AllIntBox orig) (hb : PendingBacked orig f) :
    NBTrail (resumePending orig bs f).trail :=
  nbTrail_syncAll (resumePendingBase orig bs f) (pending_frameInts hint hb)
    (canonicalTrail_nb hint hb)

/-! ## The asserting literal of a recorded analysis -/

theorem asserting_nb {orig : List Domain} {cfg : SchedulerConfig leaf}
    (hco : LcgCore leaf orig cfg) (hreach : SchedulerReachable cfg)
    {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hnb : NBTrail cfg.branch.trail) : NoBoolAtom an.asserting.norm := by
  have hfals := lcg_normFalsified (cfg := cfg) (bs := cfg.branch) rfl hco.reach hreach hc ha
  obtain ⟨below, uip, -, hcanon⟩ := reachable_analysis_success leaf cfg ev an hreach hc ha
  have hhead : (uip.negate).norm ∈ an.learned := by
    rw [hcanon, ConflictAnalysis.normalized_learned, ConflictAnalysis.ofUIP_learned]
    exact List.mem_cons_self ..
  have hass : an.asserting = (uip.negate).norm := by
    rw [hcanon, ConflictAnalysis.normalized_asserting, ConflictAnalysis.ofUIP_asserting]
  obtain ⟨e, he, heq⟩ := hfals _ hhead
  have h1 := hnb e he
  rw [heq, noBoolAtom_norm, noBoolAtom_negate] at h1
  rw [hass, norm_norm]
  exact h1

/-! ## The jump arm -/

theorem nb_jump {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : LcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hreach : SupportedReach cfg.orig cfg.original cfg.props cfg)
    (h : LcgRunState leaf cfg.orig cfg) (hnb : NBCfg cfg)
    {ev : ConflictEvidence} {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf}
    {restored : BranchState leaf}
    (hc : cfg.conflict = some ev) (ha : ev.analysis = some an)
    (hcp : checkpointAt cfg.checkpoints an.backjumpLevel = some cp)
    (hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
      cfg.branch cfg.orig cfg.original cfg.props = some restored) :
    NBTrail restored.trail := by
  obtain ⟨g, hg, hres, hgood0⟩ := jump_good0 K hreach h (h.rootTrue K.fits) hc ha hcp hp
  have hass := asserting_nb h.core hreach.reachable hc ha hnb.1
  have hcpnb := hnb.2 cp (checkpointAt_mem hcp)
  have hrs : NBTrail (restorationState cp cfg.branch an g).trail := by
    rcases restorationState_trail_cases cp cfg.branch an g with ⟨ht, -⟩ | ⟨ht, -⟩
    · rw [ht]; exact hcpnb
    · rw [ht]; exact nbTrail_snoc hcpnb hass
  have hF : ∀ d ∈ (restorationState cp cfg.branch an g).frame.1,
      ∀ v ∈ d, ∃ k : Int, v = Value.int k := by
    have := frameInts_of K.int hgood0.fj.fits
    rw [syncAll_frame] at this
    exact this
  have hsy := nbTrail_syncAll (orig := cfg.orig) _ hF hrs
  have := nbTrail_closure K hgood0 hsy
  rw [hres]
  exact this

/-! ## The one-step law -/

theorem nbCfg_init {prio : List Nat} {actBump : Bool} {orig : List Domain} {original : List Clause} {props : List Propagator} :
    NBCfg (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) := by
  refine ⟨?_, ?_⟩
  · intro e he; simp [SchedulerConfig.init, BranchState.init] at he
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    intro e he
    simp [rootCheckpoint] at he

theorem nbCfg_step {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props)
    {cfg cfg' : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg)
    (h : LcgRunState leaf orig cfg) (hnb : NBCfg cfg)
    (hsucc : (schedulerNext cfg).successor = some cfg') :
    NBCfg cfg' := by
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hreach
  subst hor hon hpr
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _hsj⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · -- ROUTE 1: recorded evidence
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact hnb
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact hnb
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact hnb
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                have hj : NBTrail restored.trail := nb_jump K hreach h hnb hc ha hcp hp
                refine ⟨hj, ?_⟩
                intro cp' hcp'
                rw [stepLearnBackjumpAssert_checkpoints (cfg := cfg)
                  (p := BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                  (ev := ev) (restored := restored)] at hcp'
                exact hnb.2 cp' (List.mem_filter.mp hcp').1
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
              h.pend.pending f (by rw [hp]; exact List.mem_cons_self ..)
            refine ⟨?_, ?_⟩
            · rw [stepConsume_branch hp hcons]
              exact resumePending_nb K.int hpb
            · intro cp hcp
              have hck := stepConsume_checkpoints_nil hp hcons
              simp only [hck] at hcp
              cases hcp
  · -- ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj] at hsucc
      rw [successor_propagate] at hsucc
      cases hsucc
      exact ⟨nbTrail_stepNarrowSync K h.good hnb.1 hd, hnb.2⟩
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
              · rw [successor_decide] at hsucc
                cases hsucc
                exact hnb
              · rw [successor_decide] at hsucc
                cases hsucc
                obtain ⟨-, hspec, hlit, -⟩ := splitData_eq_some_iff.mp hs
                have hmem : v ∈ (fullDomains cfg.branch.frame).getD k Dom.empty := by
                  show v ∈ (cfg.branch.frame.doms.getD k Dom.empty)
                  exact (DomainLike.mem_iff _ v).mpr (by
                    rw [domElems_eq_enum, enum_getD_of_enum_cons hspec]
                    exact List.mem_cons_self)
                have hvint : ∃ i : Int, v = Value.int i :=
                  allInt_getD K.int k v
                    ((DomainLike.mem_iff _ v).mp (h.core.reach.full_fits k v hmem))
                have hlnb := valueLiteral_nb hvint hlit
                refine ⟨nbTrail_snoc hnb.1 ((noBoolAtom_norm _).mpr hlnb), ?_⟩
                intro cp hcp
                change cp ∈ DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints at hcp
                rcases List.mem_cons.mp hcp with rfl | hcp
                · exact hnb.1
                · exact hnb.2 cp hcp
          | none =>
              simp only [hl, hs] at hsucc
              rw [successor_localExclude] at hsucc
              cases hsucc
              exact hnb
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep] at hsucc
          rw [successor_localExclude] at hsucc
          cases hsucc
          exact hnb
      | cons c0 rest =>
          by_cases hlevel : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hlevel, successor_unsat] at hsucc
            cases hsucc
          · simp only [conflictStep, if_neg hlevel] at hsucc
            rw [successor_analyzeConflict] at hsucc
            cases hsucc
            exact ⟨hnb.1, by rw [stepAnalyzeConflictCounted_checkpoints]; exact hnb.2⟩
    · exact absurd ht terminalResult_ne_localExcluded

/-- **NO BOOLEAN-ATOM TRAIL LITERAL ALONG A SUPPORTED RUN OF THE KIT.** -/
theorem nbCfg_of_kit {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → NBCfg cfg := by
  intro cfg hreach
  induction hreach with
  | init hent => exact nbCfg_init
  | step hpre hsucc ih =>
      exact nbCfg_step K hpre (lcgRunState_of_supportedRun K hpre) ih hsucc

end LeanFzn.Solver.UIP.LcgNoBoolRun
