/-
Purpose: mixed-domain decision and redundant-skip preservation of semantic core.
Dependencies: LcgMixedDecisions gives exact value pins; LcgRunStep supplies
sort-independent core helpers and pooled decision literal production;
LcgMixedRunState supplies the combined mixed run invariant read by the consume arm.
DAG: mixed decision facts -> mixed core arms -> full scheduler assembly.
-/
import LeanFzn.Solver.UIP.Proofs.LcgMixedGood
import LeanFzn.Solver.UIP.Proofs.LcgMixedDecisions
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunState
import LeanFzn.Solver.UIP.Proofs.LcgRunStep
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Solver.UIP.LcgRunArms LeanFzn.Solver.UIP.LcgRunJump
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgReachable
open LeanFzn.Solver.UIP.LcgRunState LeanFzn.Solver.UIP.LcgRunStep
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedDecisions
open LeanFzn.Solver.UIP.LcgMixedRunState
namespace LeanFzn.Solver.UIP.LcgMixedCore
variable {leaf : Assignment → Bool}
theorem core_decide {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : MixedLcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hc : LcgCore leaf cfg.orig cfg) (hconf : cfg.conflict = none)
    {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (hs : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = false) :
    LcgCore leaf cfg.orig (stepDecide cfg v vs doms l) := by
  have hpin := lcgPinFits_shape hs hc.reach K.shape
  have hdom := (splitData_eq_some_iff.mp hs).1
  have hr : LcgReachableState leaf cfg.orig (stepDecide cfg v vs doms l).branch :=
    lcgReachable_decide hc.reach hdom (List.mem_cons_self ..) hpin (not_trailRedundant_iff.mp hred)
  have hck : (stepDecide cfg v vs doms l).checkpoints
      = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
  refine ⟨rfl, hr, ?_, ?_, ?_, ?_, ?_⟩
  · exact stepDecide_branchTrailVocabulary_at (cfg := cfg) hc.voc (lcg_splitLiteral_pooled hc.reach hs)
  · exact stepDecide_halignDBAt v vs doms l hc.db
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
    {cfg : SchedulerConfig leaf} (K : MixedLcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hc : LcgCore leaf cfg.orig cfg) (hconf : cfg.conflict = none)
    {l : Literal} {v : Value} {vs : Domain} {doms : List Domain}
    (hs : splitData cfg.branch.frame = some (l, v, vs, doms))
    (hred : TrailRedundant cfg.branch.trail l = true) :
    LcgCore leaf cfg.orig (stepDecideSkip cfg v doms) := by
  refine core_move hc rfl (lcgReachable_decideSkip hc.reach hs (lcgSkipTyped_shape hs hc.reach K.shape hred))
    hc.voc hc.db rfl (by rw [stepDecideSkip_conflict, hconf])

theorem core_propagate_shape {dcs : List DomConstraint} {raw : List Propagator}
    {cfg : SchedulerConfig leaf} (K : MixedLcgKit leaf cfg.orig cfg.original dcs raw cfg.props)
    (hc : LcgCore leaf cfg.orig cfg) (hg : MixedLcgGood leaf cfg.orig cfg.branch)
    (hconf : cfg.conflict = none) {d : ProductiveDeduction leaf cfg.branch}
    (hd : explainedDeduction cfg.original cfg.props cfg.branch = some d) :
    LcgCore leaf cfg.orig (stepPropagate cfg d) := by
  have hg' := hg.stepNarrowSync K hd
  exact core_move hc rfl hg'.reach hg'.voc hg'.db rfl (by rw [stepPropagate_conflict, hconf])

/-! ## Consume -/

theorem core_consume_shape {cfg next : SchedulerConfig leaf} {orig : List Domain}
    (hfits : ∀ a, leaf a = true → a.Fits orig)
    (h : LcgMixedRunState leaf orig cfg) {f : BranchFrame} {rest : List BranchFrame}
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


end LeanFzn.Solver.UIP.LcgMixedCore
