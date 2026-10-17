/-
File: LeanFzn/Solver/UIP/Proofs/LcgKitFinal.lean
H2d: kit-level versions of the top LCG run results, with NO `hbr` and NO `hcertEnt`,
derived from `LcgRunState` (`lcgRunState_of_supportedRun`).
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunStep
import LeanFzn.Solver.UIP.Proofs.LcgAsserting
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgContract LeanFzn.Solver.UIP.LcgFamilies LeanFzn.Solver.UIP.LcgClamp
open LeanFzn.Solver.UIP.ClampPool LeanFzn.Solver.UIP LeanFzn.Solver.UIP.LcgRunInv
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunGood LeanFzn.Solver.UIP.LcgRunState
open LeanFzn.Solver.UIP.LcgRunStep LeanFzn.Solver.UIP.LcgEvidence

namespace LeanFzn.Solver.UIP.LcgKitFinal

variable {leaf : Assignment → Bool}

section
variable {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}

/-- `FrameRun` along a supported run of the kit (replaces `frameRun_of_supportedRun`). -/
theorem frameRun_of_kit (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    FrameRun cfg :=
  (lcgRunState_of_supportedRun K hreach).frameRun

/-- `FrameExplainedFull` along a supported run of the kit. -/
theorem frameExplainedFull_of_kit (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    FrameExplainedFull orig cfg.branch := by
  have h := (frameRun_of_kit K hreach).branch
  rw [SupportedReach.orig_eq hreach] at h
  exact frameExplainedFull_of_explDoms K.int h.expl

/-- `TrailSnapFixed` along a supported run of the kit (replaces `trailSnapFixed_of_clampedRun`). -/
theorem trailSnapFixed_of_kit (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    TrailSnapFixed orig cfg.branch.trail := fun e he =>
  snapLit_fixed_of_norm_pool ((lcgRunState_of_supportedRun K hreach).core.voc e he)

/-- `TrailRun` along a supported run of the kit (replaces `trailRun_of_supportedRun`). -/
theorem trailRun_of_kit (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg) :
    TrailRun cfg where
  branch := by
    rw [(lcgRunState_of_supportedRun K hreach).core.orig_eq]
    exact (lcgRunState_of_supportedRun K hreach).core.reach.trail_sem
  cps := fun cp hcp => by
    have h := (lcgRunState_of_supportedRun K hreach).core.snaps cp hcp
    rw [(lcgRunState_of_supportedRun K hreach).core.orig_eq]
    obtain ⟨bs, hbs, -, htr, -⟩ := h
    rw [← htr]
    exact hbs.trail_sem

/-- `RunSemContract` from the kit (no `hbr`). -/
theorem runSemContract_of_kit (K : LcgKit leaf orig original dcs raw props) :
    RunSemContract orig original props leaf :=
  runSemContract_of_families (dcs := dcs) (by rw [K.props_eq, K.raw_eq]) K.fam
    (fun hr => frameExplainedFull_of_kit K hr)
    (fun hr => trailSnapFixed_of_kit K hr)

/-- The `lcgKit` gate from the kit (no `hbr`). -/
theorem lcgKit_gate_of_kit (K : LcgKit leaf orig original dcs raw props) :
    (lcgKit lcgFamB).Gate leaf orig original props :=
  lcgKit_gate_of_families (dcs := dcs) (by rw [K.props_eq, K.raw_eq]) K.fam
    (fun hr => frameExplainedFull_of_kit K hr)
    (fun hr => trailSnapFixed_of_kit K hr)

/-- **THE CONDITIONAL RUN INVARIANT, kit level**: no `hbr`, no `hcertEnt`, no `hA`, no `hent`. -/
theorem lcgRunInvCond_of_kit (K : LcgKit leaf orig original dcs raw props)
    (hlive : DecideLive orig original props leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LcgRunInv' cfg := by
  intro cfg hreach
  have hS := lcgRunState_of_supportedRun K hreach
  have hor : cfg.orig = orig := SupportedReach.orig_eq hreach
  exact
    { entailed := hS.core.reach.learned_ent
      reasons := (trailRun_of_kit K hreach).branch
      evidence := fun ev an h1 h2 => evidenceRunCond_holds orig original props leaf hreach ev h1 an h2
      wipe := wipeoutOk_of_fits K.fits cfg hor
      closure := fun hdec =>
        closure_at_decide (by rw [hor]; exact K.int) hS.frameRun.branch (hlive hreach hdec) hdec }

end
end LeanFzn.Solver.UIP.LcgKitFinal
