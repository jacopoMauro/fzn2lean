/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunState.lean
H2c (part 7): the combined run invariant `LcgRunState` and its one-step law along real dispatcher
successors, with NO `hbr`. See `LcgRunGood`, `LcgRunConflict`, `LcgRunArms`, `LcgRunJump`,
`LcgRunCert`, `LcgRunPending` for the ingredients.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunPending
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunInvariantStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRootBase
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunDropDef
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgEvents LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgAsserting LeanFzn.Solver.UIP.LcgRunConflict LeanFzn.Solver.UIP.LcgRunArms
open LeanFzn.Solver.UIP.LcgRunJump LeanFzn.Solver.UIP.LcgRunCert LeanFzn.Solver.UIP.LcgRunPending
open LeanFzn.Solver.UIP.LcgRootTrue LeanFzn.Solver.UIP.LcgRootBase LeanFzn.Solver.UIP.LcgRunDrop

namespace LeanFzn.Solver.UIP.LcgRunState

variable {leaf : Assignment → Bool}

/-- The branch/checkpoint/evidence part of the run invariant. -/
structure LcgCore (leaf : Assignment → Bool) (orig : List Domain) (cfg : SchedulerConfig leaf) :
    Prop where
  orig_eq : cfg.orig = orig
  reach : LcgReachableState leaf orig cfg.branch
  voc : TrailVocabularyAt (litPool orig) cfg.branch.trail
  db : DatabaseAlignedAt (litPool orig) cfg.branch.learned
  snaps : ∀ cp ∈ cfg.checkpoints, LcgSnapshot leaf orig cp
  cpVoc : ∀ cp ∈ cfg.checkpoints, TrailVocabularyAt (litPool orig) cp.trail
  ev : ∀ ev, cfg.conflict = some ev →
    LearnedEntailed leaf [ev.clause] ∧ LearnedEntailed leaf ev.learned ∧
      DatabaseAlignedAt (litPool orig) ev.learned

/-- **THE COMBINED RUN INVARIANT** (no `hbr`). -/
structure LcgRunState (leaf : Assignment → Bool) (orig : List Domain)
    (cfg : SchedulerConfig leaf) : Prop where
  core : LcgCore leaf orig cfg
  frameRun : FrameRun cfg
  pend : PendingSideInv orig cfg
  /-- H2e-2: reason-less level-0 entries of the branch and of every checkpoint trail hold at
  every leaf solution (reasoned level-0 entries then follow by `rootTrue_of_base`). -/
  rootBase : RootBase leaf cfg.branch.trail ∧ ∀ cp ∈ cfg.checkpoints, RootBase leaf cp.trail
  /-- H2f: the stack of frames (current branch, then pending) is sound: every leaf solution
  extending the pin prefix of a frame lies in it or in a frame above it. -/
  stack : StackSound cfg
  /-- H2f: a dead (or conflicted) branch frame covers no leaf solution. -/
  dead : DeadSound cfg
  /-- H2f: every saved checkpoint frame holds the leaf solutions of its pin prefix. -/
  cpSnd : CpSound cfg

theorem LcgRunState.rootTrue {orig : List Domain} {cfg : SchedulerConfig leaf}
    (h : LcgRunState leaf orig cfg) (hfits : ∀ a, leaf a = true → a.Fits orig) :
    RootTrue leaf cfg.branch.trail :=
  rootTrue_of_base h.core.reach hfits h.rootBase.1

theorem LcgRunState.good {orig : List Domain} {cfg : SchedulerConfig leaf}
    (h : LcgRunState leaf orig cfg) : LcgGood leaf orig cfg.branch := by
  have hj := h.frameRun.branch
  have hs := h.frameRun.shape
  rw [h.core.orig_eq] at hj hs
  exact ⟨h.core.reach, hj, hs, h.core.voc, h.core.db⟩

/-! ## Root -/

theorem frameRun_init {prio : List Nat} {actBump : Bool} {orig : List Domain} {original : List Clause} {props : List Propagator}
    (hint : AllIntBox orig) (hnd : ∀ d ∈ orig, (Dom.enum d).Nodup) :
    FrameRun (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) := by
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

theorem lcgRunState_init {prio : List Nat} {actBump : Bool} {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : LcgKit leaf orig original dcs raw props) (hent : LearnedEntailed leaf original) :
    LcgRunState leaf orig (SchedulerConfig.init (leaf := leaf) orig original props prio actBump) := by
  have hr0 : LcgReachableState leaf orig (BranchState.init (leaf := leaf) (⟨orig, []⟩ : BranchFrame)) :=
    lcgReachable_of_reachable (reachable_init leaf orig)
  refine ⟨⟨rfl, { hr0 with learned_ent := hent }, ?_, K.aligned, ?_, ?_, ?_⟩,
    frameRun_init K.int K.nd, PendingSideInv.init orig original props, ?_, ?_, ?_, ?_⟩
  · intro e he; simp [SchedulerConfig.init, BranchState.init] at he
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    exact ⟨BranchState.init (⟨orig, []⟩ : BranchFrame), hr0, rfl, rfl, rfl⟩
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    intro e he
    simp [rootCheckpoint] at he
  · intro ev h
    simp [SchedulerConfig.init] at h
  · refine ⟨?_, ?_⟩
    · intro e he; simp [SchedulerConfig.init, BranchState.init] at he
    · intro cp hcp
      simp only [SchedulerConfig.init, List.mem_singleton] at hcp
      subst hcp
      intro e he
      simp [rootCheckpoint] at he
  · exact ⟨fun a ha hp hc => hc (by
      simpa [SchedulerConfig.init, BranchState.init] using
        frameSndOrder_root K.fits a ha hp), trivial⟩
  · rintro (h | h)
    · simp [SchedulerConfig.init] at h
    · exact absurd rfl h
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    exact frameSndOrder_root K.fits

end LeanFzn.Solver.UIP.LcgRunState
