/-
File: LeanFzn/Solver/UIP/Proofs/LcgPhaseTerminal.lean
Purpose: SAT terminal and whole-run transfer over semantic LCG reachability.
Dependencies: LcgKitFinal produces semantic reachability; SchedulerRunAssembly classifies
actual SAT dispatch; LcgPhaseKernel supplies the chronology-free computable driver.
DAG: these three proof leaves -> LcgPhaseTerminal -> public LCG integration.
-/
import LeanFzn.Solver.UIP.Proofs.LcgKitFinal
import LeanFzn.Solver.UIP.Proofs.SchedulerRunAssembly
import LeanFzn.Solver.UIP.Proofs.LcgPhaseKernel
import LeanFzn.Solver.UIP.Proofs.LcgLiveCoverage

namespace LeanFzn.Solver.UIP.LcgPhaseTerminal
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.UIP.RunAssembly
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgRunStep LeanFzn.Solver.UIP.LcgRunState
open LeanFzn.Solver.UIP.LcgRunDrop LeanFzn.Solver.UIP.LcgLiveCoverage

/-- The leaf check uses containment and length, both present in semantic reachability. -/
theorem leafWitness_solution {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : LcgReachableState leaf cfg.orig cfg.branch)
    (h : leafWitness leaf cfg = some w) : SolutionWitness leaf cfg.orig w := by
  obtain ⟨hframe, hleaf, rfl⟩ := leafWitness_eq_some_iff.mp h
  have hfe : cfg.branch.frame = ((([] : List Domain), cfg.branch.frame.2)) :=
    Prod.ext hframe rfl
  refine ⟨hleaf, ?_, ?_⟩
  · have hlen : (fullDomains ((([] : List Domain),
        cfg.branch.frame.2) : BranchFrame)).length = cfg.orig.length :=
      hfe ▸ hreach.length_ok
    simpa [fullDomains, Frame.domains] using hlen
  · intro slot value hget
    have hmem : value ∈ (fullDomains ((([] : List Domain),
        cfg.branch.frame.2) : BranchFrame)).getD slot [] := by
      have h1 : fullDomains ((([] : List Domain),
          cfg.branch.frame.2) : BranchFrame)
          = List.map (fun v => [v]) cfg.branch.frame.2 := by
        simp [fullDomains, Frame.domains]
      rw [h1, List.getD_eq_getElem?_getD, List.getElem?_map, hget]
      exact List.mem_singleton_self value
    rw [← hfe] at hmem
    exact hreach.full_fits slot value hmem


/-- A real SAT phase result is an original solution on every LCG kit run. -/
theorem phaseNext_sat_solution_of_kit {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hr : SupportedReach orig original props cfg) (hsat : phaseNext cfg = .sat w) :
    SolutionWitness leaf orig w := by
  have h := C2d.stableStep_sat_of_guarded (schedulerNext_eq_sat_imp (phaseNext_eq_sat_imp hsat))
  have hreach := (lcgRunState_of_supportedRun K hr).core.reach
  have hor := SupportedReach.orig_eq hr
  rw [← hor] at hreach
  have hsol : SolutionWitness leaf cfg.orig w := by
    unfold stableStep at h
    split at h
    · rename_i w' hw'
      cases h
      exact leafWitness_solution hreach hw'
    · split at h <;> cases h
  rwa [hor] at hsol

/-- The fuel-free semantic LCG entry returns sound SAT witnesses. -/
theorem solve_sat_solution_of_kit {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : LcgKit leaf orig original dcs raw props)
    (hent : LearnedEntailed leaf original) {w : Assignment}
    (hrun : LcgPhaseKernel.solve orig original props hent = .sat w) :
    SolutionWitness leaf orig w :=
  runSupportedPhase_sat_solution (LcgPhaseKernel.supportedPhaseKernel orig original props)
    (fun _ _ hr _ hs => phaseNext_sat_solution_of_kit K hr hs)
    (SchedulerConfig.init orig original props) (SupportedReach.init hent) hrun

/-- The exhausted frontier of a kit run excludes every leaf solution. -/
theorem dead_exhausted_of_kit {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hr : SupportedReach orig original props cfg)
    (hp : cfg.pending = []) (hd : cfg.status = .dead) :
    ∀ a, leaf a = true → False :=
  exhausted (of_kit K hr) ((lcgRunState_of_supportedRun K hr).dead (Or.inl hd)) hp

/-- A root terminal conflict excludes all leaf solutions: every trail entry is globally true,
so semantic narrowing completeness places every leaf solution in the conflicting frame. -/
theorem root_conflict_of_kit {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hr : SupportedReach orig original props cfg)
    (hz : cfg.branch.level = 0) {bs : BranchState leaf} {cs learned : List Clause}
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .conflict bs cs learned) :
    ∀ a, leaf a = true → False := by
  have h := lcgRunState_of_supportedRun K hr
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hr
  rw [hor, hon, hpr] at ht
  have hd := terminal_conflict_dead K h.good ht
  intro a ha
  apply hd a ha
  exact frame_covers_of_trail h.core.reach.length_ok (K.fits a ha)
    h.core.reach.prefix_forced h.core.reach.narrowing_complete (fun e he =>
      h.rootTrue K.fits e he (by have := h.core.reach.levels e he; omega) a ha)

/-- Every actual UNSAT phase result of a kit run excludes all leaf solutions. -/
theorem phaseNext_unsat_excludes_of_kit {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : LcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hr : SupportedReach orig original props cfg)
    (hu : phaseNext cfg = .unsat) : ∀ a, leaf a = true → False := by
  rcases phaseNext_unsat_cases hu with hbare | ⟨n, _, hp, hd, hs⟩ |
    ⟨n, d, _, _, hp, hd, hs, hs'⟩
  · rcases schedulerNext_eq_unsat_cases hbare with ⟨hp, hd⟩ |
      ⟨_, _, hz, bs, cs, learned, _, ht⟩
    · exact dead_exhausted_of_kit K hr hp hd
    · exact root_conflict_of_kit K hr hz ht
  · exact dead_exhausted_of_kit K (SupportedReach.step hr hs) hp hd
  · exact dead_exhausted_of_kit K (SupportedReach.step (SupportedReach.step hr hs) hs') hp hd

/-- The fuel-free initialized semantic LCG entry has sound UNSAT results. -/
theorem solve_unsat_excludes_of_kit {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : LcgKit leaf orig original dcs raw props)
    (hent : LearnedEntailed leaf original)
    (hrun : LcgPhaseKernel.solve orig original props hent = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False :=
  runSupportedPhase_unsat_excludes (LcgPhaseKernel.supportedPhaseKernel orig original props)
    (fun _ hr _ hs a ha => phaseNext_unsat_excludes_of_kit K hr hs a ha.1)
    (SchedulerConfig.init orig original props) (SupportedReach.init hent) hrun

end LeanFzn.Solver.UIP.LcgPhaseTerminal
