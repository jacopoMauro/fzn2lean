/-
File: LeanFzn/Solver/UIP/Proofs/LcgMixedRunState.lean
A1: the mixed-domain combined run invariant `LcgMixedRunState` and its root instance.
It is the integer `LcgRunState` template with `FrameRun` replaced by the stronger
`MixedFrameRun` (Boolean prefix pins on branch and checkpoints) and with the
`CanonicalCfg` syntax invariant added; `good` exports the `MixedLcgGood` bundle
used by the mixed scheduler arms.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunState
import LeanFzn.Solver.UIP.Proofs.LcgMixedGood
import LeanFzn.Solver.UIP.Proofs.LcgMixedFrameRun
import LeanFzn.Solver.UIP.Proofs.LcgCanonicalScheduler
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgRunState LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgRootTrue LeanFzn.Solver.UIP.LcgRunDrop
open LeanFzn.Solver.UIP.LcgCanonicalScheduler LeanFzn.Solver.UIP.LcgMixedGood

namespace LeanFzn.Solver.UIP.LcgMixedRunState

variable {leaf : Assignment → Bool}

/-- **THE MIXED COMBINED RUN INVARIANT.** Same fields and meanings as the
integer `LcgRunState`, with `FrameRun` replaced by `MixedFrameRun` and the
`CanonicalCfg` syntax invariant added. -/
structure LcgMixedRunState (leaf : Assignment → Bool) (orig : List Domain)
    (cfg : SchedulerConfig leaf) : Prop where
  core : LcgCore leaf orig cfg
  frameRun : MixedFrameRun cfg
  canonical : CanonicalCfg cfg
  pend : PendingSideInv orig cfg
  rootBase : RootBase leaf cfg.branch.trail ∧ ∀ cp ∈ cfg.checkpoints, RootBase leaf cp.trail
  stack : StackSound cfg
  dead : DeadSound cfg
  cpSnd : CpSound cfg

theorem LcgMixedRunState.good {orig : List Domain} {cfg : SchedulerConfig leaf}
    (h : LcgMixedRunState leaf orig cfg) : MixedLcgGood leaf orig cfg.branch := by
  have hj := h.frameRun.branch
  have hs := h.frameRun.shape
  rw [h.core.orig_eq] at hj hs
  exact ⟨h.core.reach, hj, hs, h.core.voc, h.core.db, h.frameRun.branchBoolPins,
    h.canonical.db⟩

theorem LcgMixedRunState.rootTrue {orig : List Domain} {cfg : SchedulerConfig leaf}
    (h : LcgMixedRunState leaf orig cfg) (hfits : ∀ a, leaf a = true → a.Fits orig) :
    RootTrue leaf cfg.branch.trail :=
  rootTrue_of_base h.core.reach hfits h.rootBase.1

theorem lcgMixedRunState_init {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) (hent : LearnedEntailed leaf original) :
    LcgMixedRunState leaf orig (SchedulerConfig.init (leaf := leaf) orig original props) := by
  have hr0 : LcgReachableState leaf orig (BranchState.init (leaf := leaf) (orig, [])) :=
    lcgReachable_of_reachable (reachable_init leaf orig)
  refine ⟨⟨rfl, { hr0 with learned_ent := hent }, ?_, K.aligned, ?_, ?_, ?_⟩,
    mixedFrameRun_init K.shape K.nd, canonicalCfg_none K.canonicalOriginal rfl,
    PendingSideInv.init orig original props, ?_, ?_, ?_, ?_⟩
  · intro e he; simp [SchedulerConfig.init, BranchState.init] at he
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    exact ⟨BranchState.init (orig, []), hr0, rfl, rfl, rfl⟩
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
  · exact ⟨fun a ha _ hc => hc (frameSnd_root K.fits a ha (List.nil_prefix)), trivial⟩
  · rintro (h | h)
    · simp [SchedulerConfig.init] at h
    · exact absurd rfl h
  · intro cp hcp
    simp only [SchedulerConfig.init, List.mem_singleton] at hcp
    subst hcp
    exact frameSnd_root K.fits

end LeanFzn.Solver.UIP.LcgMixedRunState
