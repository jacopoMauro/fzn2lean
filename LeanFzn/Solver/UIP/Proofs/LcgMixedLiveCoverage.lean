/-
File: LeanFzn/Solver/UIP/Proofs/LcgMixedLiveCoverage.lean
A4c: global coverage of leaf solutions by the current branch and pending frontier
on MIXED (shape-typed) kit runs. `step_mixed` is the integer `LcgLiveCoverage.step`
with `LcgKit` -> `MixedLcgKit`, `LcgRunState` -> `LcgMixedRunState` and the two
K-carrying coverage lemmas replaced by their shape-typed twins
(`propagate_covers_shape`, `skip_covers_shape`); every other arm, and the coverage
predicate `LiveCoverage` itself (a K-free predicate over `SchedulerConfig`), is used
unchanged from `LcgLiveCoverage`. `of_kit_mixed` is the initialized closure over
`SupportedReach` using `lcgMixedRunState_of_supportedRun`.
DAG: LcgLiveCoverage + LcgMixedRunStep + LcgMixedRunDrop -> LcgMixedLiveCoverage
-> LcgMixedPhaseTerminal.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Solver.UIP.Proofs.LcgLiveCoverage
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunState
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunDrop
import LeanFzn.Solver.UIP.Proofs.LcgMixedRunStep

namespace LeanFzn.Solver.UIP.LcgMixedLiveCoverage
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.LcgRunGood LeanFzn.Solver.UIP.LcgRunState
open LeanFzn.Solver.UIP.LcgRunStep LeanFzn.Solver.UIP.LcgRunDrop
open LeanFzn.Solver.UIP.LcgLiveCoverage
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgMixedRunState
open LeanFzn.Solver.UIP.LcgMixedRunDrop LeanFzn.Solver.UIP.LcgMixedRunStep

variable {leaf : Assignment → Bool}

/-- Every dispatcher successor preserves global live coverage on a semantic mixed
kit run. Verbatim twin of `LcgLiveCoverage.step` with the mixed kit and the
shape-typed cover transfer of the propagate and redundant-split arms. -/
theorem step_mixed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) {cfg cfg' : SchedulerConfig leaf}
    (hr : SupportedReach orig original props cfg) (h : LcgMixedRunState leaf orig cfg)
    (hl : LiveCoverage cfg) (hsucc : (schedulerNext cfg).successor = some cfg') :
    LiveCoverage cfg' := by
  obtain ⟨hor, hon, hpr⟩ := SupportedReach.triple_eq hr
  subst hor hon hpr
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, _⟩ | ⟨hconf, hdead, hsj⟩ | ⟨hconf, hact, hrest⟩
  · have hdc := h.dead (Or.inr (by rw [hc]; exact Option.some_ne_none _))
    cases ha : ev.analysis with
    | none =>
        rw [C2d.schedulerNext_eq_backjump_none_analysis hc ha] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        exact stay hl rfl rfl
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            rw [C2d.schedulerNext_eq_backjump_no_checkpoint hc ha hcp] at hsucc
            rw [successor_chronologicalFallback] at hsucc
            cases hsucc
            exact stay hl rfl rfl
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
                cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                rw [C2d.schedulerNext_eq_backjump_perform_none hc ha hcp hp] at hsucc
                rw [successor_localExclude] at hsucc
                cases hsucc
                exact stay hl rfl rfl
            | some restored =>
                rw [C2d.schedulerNext_eq_backjump_jump hc ha hcp hp] at hsucc
                rw [successor_learnBackjumpAssert] at hsucc
                cases hsucc
                exact dead_replace hl rfl hdc
  · rw [hsj] at hsucc
    cases hcons : stepConsume cfg with
    | none => simp only [consumeStep, hcons] at hsucc; cases hsucc
    | some next =>
        simp only [consumeStep, hcons] at hsucc
        rw [successor_chronologicalFallback] at hsucc
        cases hsucc
        cases hp : cfg.pending with
        | nil => rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hp] at hcons; cases hcons
        | cons f rest =>
            have hdc := h.dead (Or.inl hdead)
            unfold stepConsume at hcons
            rw [hp] at hcons
            simp only [Option.some.injEq] at hcons
            subst hcons
            exact consume hl hp hdc (by simp [resumePending_frame]) rfl
  · rcases hrest with
      ⟨d, hd, hsj⟩ | ⟨bs, ht, hsj⟩ | ⟨bs, cs, learned, ht, hsj⟩ |
      ⟨bs, lit, reason, learned, ht, hsj⟩
    · rw [hsj, successor_propagate] at hsucc
      cases hsucc
      apply replace (cfg' := stepPropagate cfg d) hl rfl
      rw [stepPropagate_branch_frame]
      exact propagate_covers_shape K h.good hd
    · rw [hsj] at hsucc
      unfold stableStepGuarded at hsucc
      cases hw : leafWitness leaf cfg with
      | some w => simp only [hw, successor_sat] at hsucc; cases hsucc
      | none =>
          cases hs : splitData cfg.branch.frame with
          | none =>
              simp only [hw, hs, successor_localExclude] at hsucc
              cases hsucc
              exact stay hl rfl rfl
          | some p =>
              obtain ⟨l, v, vs, doms⟩ := p
              simp only [hw, hs] at hsucc
              split at hsucc
              · rename_i hred
                rw [successor_decide] at hsucc
                cases hsucc
                exact replace hl rfl (skip_covers_shape h.core.reach K.shape K.fits hs hred)
              · rw [successor_decide] at hsucc
                cases hsucc
                exact decide hl (splitData_eq_some_iff.mp hs).1
    · rw [hsj] at hsucc
      cases cs with
      | nil =>
          simp only [conflictStep, successor_localExclude] at hsucc
          cases hsucc
          exact stay hl rfl rfl
      | cons c rest =>
          by_cases hz : cfg.branch.level = 0
          · simp only [conflictStep, if_pos hz, successor_unsat] at hsucc; cases hsucc
          · simp only [conflictStep, if_neg hz, successor_analyzeConflict] at hsucc
            cases hsucc
            exact stay hl rfl rfl
    · exact absurd ht terminalResult_ne_localExcluded

/-- Global coverage is initialized and preserved on all actual supported mixed kit
runs. Verbatim twin of `LcgLiveCoverage.of_kit` with the mixed run-state induction
and `step_mixed`. -/
theorem of_kit_mixed {orig : List Domain} {original : List Clause}
    {dcs : List DomConstraint} {raw props : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg → LiveCoverage cfg := by
  intro cfg hr
  induction hr with
  | init hent =>
      intro a ha
      exact Or.inl (frameSnd_root K.fits a ha List.nil_prefix)
  | step hr hs ih => exact step_mixed K hr (lcgMixedRunState_of_supportedRun K hr) ih hs

end LeanFzn.Solver.UIP.LcgMixedLiveCoverage
