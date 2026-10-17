/-
File: LeanFzn/Solver/UIP/Proofs/LcgMixedPhaseTerminal.lean
A4c: SAT terminal and whole-run soundness transfer over MIXED (shape-typed) LCG
reachability. Verbatim twins of the six `LcgPhaseTerminal.*_of_kit` theorems with
`LcgKit` -> `MixedLcgKit`, `lcgRunState_of_supportedRun` ->
`lcgMixedRunState_of_supportedRun`, `LcgLiveCoverage.of_kit` ->
`LcgMixedLiveCoverage.of_kit_mixed` and `terminal_conflict_dead` ->
`terminal_conflict_dead_shape`. The K-free `leafWitness_solution` is reused
directly from `LcgPhaseTerminal` and the K-free driver lemmas from
`LcgPhaseKernel` / `SchedulerRunAssembly` keep the same call shape.
DAG: LcgMixedLiveCoverage + LcgMixedRunStep + LcgPhaseTerminal -> LcgMixedPhaseTerminal.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Solver.UIP.Proofs.LcgMixedLiveCoverage
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunState
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunDrop
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunStep
import LeanFzn.Solver.UIP.Proofs.LcgPhaseTerminal

namespace LeanFzn.Solver.UIP.LcgMixedPhaseTerminal
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b LeanFzn.Solver.UIP.RunAssembly
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP.LcgRunGood
open LeanFzn.Solver.UIP.LcgRunStep LeanFzn.Solver.UIP.LcgRunState
open LeanFzn.Solver.UIP.LcgRunDrop LeanFzn.Solver.UIP.LcgLiveCoverage
open LeanFzn.Solver.UIP.LcgPhaseTerminal
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedRunState
open LeanFzn.Solver.UIP.LcgMixedRunDrop LeanFzn.Solver.UIP.LcgMixedRunStep
open LeanFzn.Solver.UIP.LcgMixedLiveCoverage

/-- A real SAT phase result is an original solution on every mixed LCG kit run.
Twin of `LcgPhaseTerminal.phaseNext_sat_solution_of_kit`. -/
theorem phaseNext_sat_solution_of_kit_mixed {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hr : SupportedReach orig original props cfg) (hsat : phaseNext cfg = .sat w) :
    SolutionWitness leaf orig w := by
  have h := C2d.stableStep_sat_of_guarded (schedulerNext_eq_sat_imp (phaseNext_eq_sat_imp hsat))
  have hreach := (lcgMixedRunState_of_supportedRun K hr).core.reach
  have hor := SupportedReach.orig_eq hr
  rw [← hor] at hreach
  have hsol : SolutionWitness leaf cfg.orig w := by
    unfold stableStep at h
    split at h
    · rename_i w' hw'
      cases h
      exact LcgPhaseTerminal.leafWitness_solution hreach hw'
    · split at h <;> cases h
  rwa [hor] at hsol

/-- The fuel-free semantic LCG entry returns sound SAT witnesses on mixed kit runs.
Twin of `LcgPhaseTerminal.solve_sat_solution_of_kit`. -/
theorem solve_sat_solution_of_kit_mixed {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : MixedLcgKit leaf orig original dcs raw props)
    (hent : LearnedEntailed leaf original) {w : Assignment}
    (hrun : LcgPhaseKernel.solve orig original props hent = .sat w) :
    SolutionWitness leaf orig w :=
  runSupportedPhase_sat_solution (LcgPhaseKernel.supportedPhaseKernel orig original props)
    (fun _ _ hr _ hs => phaseNext_sat_solution_of_kit_mixed K hr hs)
    (SchedulerConfig.init orig original props) (SupportedReach.init hent) hrun

/-- The exhausted frontier of a mixed kit run excludes every leaf solution.
Twin of `LcgPhaseTerminal.dead_exhausted_of_kit`. -/
theorem dead_exhausted_of_kit_mixed {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hr : SupportedReach orig original props cfg)
    (hp : cfg.pending = []) (hd : cfg.status = .dead) :
    ∀ a, leaf a = true → False :=
  exhausted (of_kit_mixed K hr) ((lcgMixedRunState_of_supportedRun K hr).dead (Or.inl hd)) hp

/-- A root terminal conflict excludes all leaf solutions: every trail entry is globally true,
so semantic narrowing completeness places every leaf solution in the conflicting frame.
Twin of `LcgPhaseTerminal.root_conflict_of_kit`. -/
theorem root_conflict_of_kit_mixed {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hr : SupportedReach orig original props cfg)
    (hz : cfg.branch.level = 0) {bs : BranchState leaf} {cs learned : List Clause}
    (ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch = .conflict bs cs learned) :
    ∀ a, leaf a = true → False := by
  have h := lcgMixedRunState_of_supportedRun K hr
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hr
  rw [hor, hon, hpr] at ht
  have hd := terminal_conflict_dead_shape K h.good ht
  intro a ha
  apply hd a ha
  exact frame_covers_of_trail h.core.reach.length_ok (K.fits a ha)
    h.core.reach.prefix_forced h.core.reach.narrowing_complete (fun e he =>
      h.rootTrue K.fits e he (by have := h.core.reach.levels e he; omega) a ha)

/-- Every actual UNSAT phase result of a mixed kit run excludes all leaf solutions.
Twin of `LcgPhaseTerminal.phaseNext_unsat_excludes_of_kit`. -/
theorem phaseNext_unsat_excludes_of_kit_mixed {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : MixedLcgKit leaf orig original dcs raw props)
    {cfg : SchedulerConfig leaf} (hr : SupportedReach orig original props cfg)
    (hu : phaseNext cfg = .unsat) : ∀ a, leaf a = true → False := by
  rcases phaseNext_unsat_cases hu with hbare | ⟨n, _, hp, hd, hs⟩ |
    ⟨n, d, _, _, hp, hd, hs, hs'⟩
  · rcases schedulerNext_eq_unsat_cases hbare with ⟨hp, hd⟩ |
      ⟨_, _, hz, bs, cs, learned, _, ht⟩
    · exact dead_exhausted_of_kit_mixed K hr hp hd
    · exact root_conflict_of_kit_mixed K hr hz ht
  · exact dead_exhausted_of_kit_mixed K (SupportedReach.step hr hs) hp hd
  · exact dead_exhausted_of_kit_mixed K (SupportedReach.step (SupportedReach.step hr hs) hs') hp hd

/-- The fuel-free initialized semantic LCG entry has sound UNSAT results on mixed
kit runs. Twin of `LcgPhaseTerminal.solve_unsat_excludes_of_kit`. -/
theorem solve_unsat_excludes_of_kit_mixed {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {dcs : List DomConstraint}
    {raw props : List Propagator} (K : MixedLcgKit leaf orig original dcs raw props)
    (hent : LearnedEntailed leaf original)
    (hrun : LcgPhaseKernel.solve orig original props hent = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False :=
  runSupportedPhase_unsat_excludes (LcgPhaseKernel.supportedPhaseKernel orig original props)
    (fun _ hr _ hs a ha => phaseNext_unsat_excludes_of_kit_mixed K hr hs a ha.1)
    (SchedulerConfig.init orig original props) (SupportedReach.init hent) hrun

end LeanFzn.Solver.UIP.LcgMixedPhaseTerminal
