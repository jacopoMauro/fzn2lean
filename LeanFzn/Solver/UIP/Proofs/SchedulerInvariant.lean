/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerInvariant.lean

Purpose:
  The reachable scheduler invariant of the certified first-UIP/backjump
  driver, its root instantiation, and the non-vacuous initializer witness.

  `SchedulerInvariant cfg` is a property of the CONFIGURATION, never a
  transition premise: every field must be PRESERVED by the transitions of
  `schedulerNext` (PLAN S0: "no assumed transition-preservation field").
  The field → preserving-task map (INTERFACES §9.1, authoritative there):

  * `reachable`             — branch coherence (A1's eight-field
                              `ReachableState`); preserved by C2a
                              (init/propagate/decide), C2b (consume/resume),
                              C2c (restore/assert), assembled by C2d.
  * `checkpoints_identify`  — checkpoint identity; preserved by C2a
                              (decide pushes), C2b (consume/restore),
                              C2c (plan identity).
  * `pending_fits`          — pending-alternative provenance (static half:
                              sub-box frames); preserved by C2a (split
                              children), C2b (sibling resume). Dynamic
                              provenance is dead-region evidence at the
                              deletion site (C2b).
  * `branch_fits`           — box containment of the current frame;
                              preserved by C2a, and by C2c through
                              `DecisionCheckpoint.Identifies`.
  * `log_sound`             — sound exhaustion; preserved by C2b
                              (registration of a failed child only), C2c.
  * `coverage`              — coverage of the remaining search space;
                              preserved by C2a/C2b/C2c, assembled by C2d
                              for the `unsat` arm.
  * `learned_entailed`      — global entailment / explanation discipline of
                              the learned database; preserved by E1
                              (learned-clause discipline under insertion,
                              narrowing, restoration), C2c. The five
                              `unitFamilyB` families keep A3's evidence;
                              other multi-literal clauses are E1/E2's.

  `RootInvariant` is `SchedulerInvariant` at the real
  `SchedulerConfig.init`; `schedulerInvariant_init` is the initializer
  witness (a theorem, not a field), and `covers_root_init` discharges the
  coverage half at the root (INTERFACES §4 item 23, previously assigned to
  the C2 group). Because the initializer is the real root configuration
  with the real frontier `[(orig, [])]`, the invariant is non-vacuous by
  construction.

Dependencies:
  - LeanFzn.Solver.UIP.SchedulerState: `SchedulerConfig`, `SchedulerConfig.init`,
    `coverage`, `CoversRemainingLeaves`
  - LeanFzn.Solver.Propagation.Proofs.BranchState: `ReachableState`, `reachable_init`,
    `mem_allAssigns_of_getElem?`
  - LeanFzn.Solver.Propagation.BackjumpFrontier: `rootCheckpoint_identifies_init`,
    `ExhaustionLog`

DAG:
  SchedulerState -> Proofs.SchedulerInvariant (this module; consumed by the
  C2a/C2b/C2c/C2d proof tasks and D1a). No runtime module imports it.
-/

import LeanFzn.Solver.UIP.SchedulerState
import LeanFzn.Solver.Propagation.Proofs.BranchState
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- The reachable scheduler invariant (INTERFACES §9.1). Every field is a
property of the configuration; each is preserved by an identified task
(module header / INTERFACES §9.1) — no field is a transition premise. -/
structure SchedulerInvariant {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : Prop where
  /-- Branch coherence: the current branch is a reachable branch state of
      the original box (A1). Preserved by C2a/C2b/C2c, assembled by C2d. -/
  reachable : ReachableState leaf cfg.orig cfg.branch
  /-- Checkpoint identity: every saved checkpoint identifies the current
      branch at its own level (C1's `Identifies`). Preserved by C2a's
      `decide`, C2b's consume/restore, consumed by C2c. -/
  checkpoints_identify : ∀ cp ∈ cfg.checkpoints,
    cp.Identifies cfg.branch cp.level
  /-- Pending-alternative provenance (static half): every pending frame is
      a pointwise sub-box of the original box. Preserved by C2a (both
      split children) and C2b (sibling resume). -/
  pending_fits : ∀ f ∈ cfg.pending, ∀ i v,
    v ∈ (Frame.domains f).getD i [] → v ∈ cfg.orig.getD i []
  /-- The current frame is a pointwise sub-box of the original box.
      Preserved by C2a; restored by C2c through `Identifies`. -/
  branch_fits : ∀ i v,
    v ∈ (Frame.domains cfg.branch.frame).getD i [] → v ∈ cfg.orig.getD i []
  /-- Sound exhaustion: no leaf solution lies in a registered dead region.
      Preserved by C2b (registration of a failed child only, never a
      parent prefix), consumed by C2c/C2d. -/
  log_sound : ExhaustionLog.Sound leaf cfg.log
  /-- Coverage: the frontier enumerates every remaining original leaf
      solution or the learned database excludes it. Preserved by
      C2a/C2b/C2c; the C2d `unsat` arm uses the `pending = []` instance. -/
  coverage : cfg.coverage
  /-- Explanation discipline / global entailment: every clause ever added
      to the learned database is globally entailed (`LearnedEntailed`).
      Preserved by E1's learned-clause discipline (insertion of entailed
      clauses and reasons, under narrowing and restoration) and C2c. -/
  learned_entailed : ∀ c ∈ cfg.branch.learned, LearnedEntailed leaf [c]

/-- The root invariant: `SchedulerInvariant` at the real initial
configuration with the real frontier `[(orig, [])]` (INTERFACES §9.2). -/
def RootInvariant (leaf : Assignment → Bool) (orig : List Domain)
    (original : List Clause) (props : List Propagator) : Prop :=
  SchedulerInvariant (SchedulerConfig.init (leaf := leaf) orig original props)

/-- The root coverage obligation (INTERFACES §4 item 23, §9.2): the initial
frontier `[(orig, [])]` covers every original leaf solution. Discharged
here, not in the C2 group: it is the non-vacuity obligation of the root
invariant. -/
theorem covers_root_init (leaf : Assignment → Bool) (orig : List Domain) :
    CoversRemainingLeaves leaf orig [(orig, [])] [] := by
  intro a ⟨_, hfits⟩
  left
  obtain ⟨hlen, hmem⟩ := hfits
  refine ⟨(orig, []), List.mem_singleton_self _, a, ?_, by simp⟩
  exact mem_allAssigns_of_getElem? orig a hlen hmem

/-- Non-vacuous initializer witness (INTERFACES §9.2): the real
`SchedulerConfig.init` satisfies the reachable invariant. It is a theorem,
not a `Prop` field, and every field is inhabited at the root — in
particular the frontier is the real `[(orig, [])]` and the learned database
is the empty `BranchState.init` database. -/
theorem schedulerInvariant_init (leaf : Assignment → Bool)
    (orig : List Domain) (original : List Clause) (props : List Propagator) :
    RootInvariant leaf orig original props := by
  have hparts := SchedulerConfig.init_wellFormed_parts leaf orig original props
  have hreach := reachable_init leaf orig
  refine ⟨hreach, hparts.1, ?_, ?_, hparts.2, covers_root_init leaf orig, ?_⟩
  · -- no pending alternatives at the root
    intro f hf
    simp only [SchedulerConfig.init, List.not_mem_nil] at hf
  · -- the root frame is the whole box
    intro i v hv
    exact hreach.full_fits i v (by simpa only [SchedulerConfig.init,
      BranchState.init, fullDomains] using hv)
  · -- the root learned database is empty
    intro c hc
    simp only [SchedulerConfig.init, BranchState.init, List.not_mem_nil] at hc

/-- The `unsat` arm's coverage instance (INTERFACES §9.1/§9.3): with no
pending alternatives left and the current branch dead (the evidence C2d
supplies from the transition that reached the verdict — never a bare
`pending = []`), `coverage` says every original leaf solution is excluded
by the learned database. Stated here so the invariant and the §2.6 `unsat`
row cannot drift apart. -/
theorem SchedulerInvariant.unsat_coverage {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} (h : SchedulerInvariant cfg)
    (hpend : cfg.pending = [])
    (hdead : ∀ a, leaf a = true → FrameCovers cfg.branch.frame a → False) :
    ∀ a, OriginalLeaves leaf cfg.orig a →
      ∃ c ∈ cfg.branch.learned, ¬ c.SatisfiedBy a := by
  intro a ha
  rcases h.coverage a ha with ⟨f, hf, hcov⟩ | hdb
  · simp only [SchedulerConfig.frontier, hpend, List.mem_singleton] at hf
    rw [hf] at hcov
    exact absurd hcov (hdead a ha.1)
  · exact hdb

end LeanFzn.Solver.UIP
