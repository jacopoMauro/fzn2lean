/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerStepO2.lean
`.learnBackjumpAssert` single-step decrease, C3a's OPEN ITEM assigned to the
integration owner)

Why a separate module: C3a's `Proofs/SchedulerProgress.lean` imports
`Proofs/SchedulerStep` (the arm table), so the rank and the dispatcher step
cannot be mentioned together in either file. This module imports BOTH and is
the only place the decrease obligation can be stated.

OWNER: C2d-resume / integration. Registration in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` is the
coordinator's call (`import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStepO2`).

C3a reserved the rank's third component (the decision level) for this arm and
asked for a trail-based no-revisit component plus UIP strictness
`an.backjumpLevel < level`. The two theorems below settle what is and is not
provable at the CURRENT rank.

Fact 1 (AVAILABLE, `learnBackjumpAssert_rank_lt_of_mass`): if the restored
ancestor frame is strictly lighter (`Frame.mass restored.frame <
Frame.mass cfg.branch.frame`), the rank decreases — `frontier` is untouched
by `stepLearnBackjumpAssert` and the second component pays.

Fact 2 (REFUTATION, `learnBackjumpAssert_rank_not_lt_self`): the shape C3b's
`JumpDecrease` currently states —
`∀ cfg p ev restored, RankLt (SchedulerRank (stepLearnBackjumpAssert cfg p ev
restored)) (SchedulerRank cfg)` — is FALSE for every leaf: `restored` is an
unconstrained parameter, `stepLearnBackjumpAssert` copies the branch
(`frame`/`level`) verbatim out of it and keeps `frontier`, so the instance
`restored := cfg.branch` yields a successor whose rank is literally EQUAL to
the predecessor's. Hence `¬ JumpDecrease leaf` for every `leaf` (apply the
refutation at `restored := cfg.branch`).

Routing: restate the obligation about the ACTUAL `perform` result and extend
the rank with a component that no restore can increase (C3a's trail-based
no-revisit debt). Level strictness ALONE is insufficient: the second
component can grow under a restore (the restored ancestor frame's mass is
unconstrained), and with the first component untouched no 3-component lex
disjunct then applies.

Zero `sorry`/`admit`/`decide`/`native_decide`.
DAG: Proofs.SchedulerStep + Proofs.SchedulerProgress -> this module.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerProgress
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.C2dO2
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- O2 (positive, consumable now): if the restore keeps the frontier cost
(pushing the restored ancestor in place of the conflict frame) and the
restored frame is strictly lighter, `SchedulerRank` decreases along
`.learnBackjumpAssert`. Note `frontier` is `cfg.branch.frame :: cfg.pending`,
so the first component changes with the restored frame and must be compared:
this hypothesis is the real content, not a convenience. -/
theorem learnBackjumpAssert_rank_lt_of_frontier_eq_of_mass {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) (restored : BranchState leaf)
    (hfront : frontierWeight (SchedulerConfig.frontier
        (stepLearnBackjumpAssert cfg p ev restored)) =
      frontierWeight (SchedulerConfig.frontier cfg))
    (hmass : Frame.mass restored.frame < Frame.mass cfg.branch.frame) :
    LeanFzn.Solver.UIP.C3a.RankLt
      (LeanFzn.Solver.UIP.C3a.SchedulerRank (stepLearnBackjumpAssert cfg p ev restored))
      (LeanFzn.Solver.UIP.C3a.SchedulerRank cfg) := by
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · simpa only [LeanFzn.Solver.UIP.C3a.SchedulerRank] using hfront
  · simpa only [LeanFzn.Solver.UIP.C3a.SchedulerRank, stepLearnBackjumpAssert]
      using hmass

/-- O2 (REFUTATION, first-class deliverable): the `.learnBackjumpAssert` rank
decrease does NOT hold for an arbitrary restored state. Instantiating
`restored := cfg.branch` (allowed by the current `∀` shape) yields a successor
rank EQUAL to the predecessor's, so no `RankLt` can exist. This is why C3b's
`JumpDecrease` cannot be proved as stated and must be restated over the
`perform` result plus a no-revisit rank component. -/
theorem learnBackjumpAssert_rank_not_lt_self {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf)
    (ev : ConflictEvidence) :
    ¬ LeanFzn.Solver.UIP.C3a.RankLt
      (LeanFzn.Solver.UIP.C3a.SchedulerRank (stepLearnBackjumpAssert cfg p ev cfg.branch))
      (LeanFzn.Solver.UIP.C3a.SchedulerRank cfg) := by
  have hrank : LeanFzn.Solver.UIP.C3a.SchedulerRank
        (stepLearnBackjumpAssert cfg p ev cfg.branch)
      = LeanFzn.Solver.UIP.C3a.SchedulerRank cfg := rfl
  rw [hrank]
  rintro (h | ⟨_, h | ⟨_, h⟩⟩) <;> omega

/-- O2 (assembled REFUTATION at `JumpDecrease`'s exact shape): C3b's
`JumpDecrease leaf` is definitionally `∀ cfg p ev restored, RankLt
(SchedulerRank (stepLearnBackjumpAssert cfg p ev restored)) (SchedulerRank
cfg)`, so it is false for every leaf — the `restored := cfg.branch` instance
is `learnBackjumpAssert_rank_not_lt_self`. C3b must restate it over the
`perform` result. -/
theorem not_jumpDecrease {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence) :
    ¬ (∀ (cfg' : SchedulerConfig leaf) (p' : BackjumpPlan leaf)
        (ev' : ConflictEvidence) (restored : BranchState leaf),
        LeanFzn.Solver.UIP.C3a.RankLt
          (LeanFzn.Solver.UIP.C3a.SchedulerRank
            (stepLearnBackjumpAssert cfg' p' ev' restored))
          (LeanFzn.Solver.UIP.C3a.SchedulerRank cfg')) :=
  fun h => learnBackjumpAssert_rank_not_lt_self cfg p ev (h cfg p ev cfg.branch)

end LeanFzn.Solver.UIP.C2dO2
