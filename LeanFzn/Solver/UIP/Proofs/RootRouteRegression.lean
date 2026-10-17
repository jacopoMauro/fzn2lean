/-
File: LeanFzn/Solver/UIP/Proofs/RootRouteRegression.lean

Purpose: preserve the kernel refutation of the DELETED conflict-free root
route contract, and record the replacement's shape.

The former `RootRouteExcludes` contract claimed that every reachable
level-zero branch with no recorded conflict excludes all original leaf
solutions — with NO conflict event and NO evidence. That is false even at
satisfiable empty initialization: the initialization is reachable, has no
recorded conflict and level zero, while the empty assignment is an original
leaf solution.

The active chain instead consumes the ACTUAL terminal conflict event:
`RunAssembly.rootConflictExcludes_of_terminalEvent`
(`Proofs/SchedulerRunAssembly.lean`) derives the exclusion from
`terminalResult … = .conflict …` plus the concrete run premises
(`ReachableState`, `RootFactsBridge`, `LearnedEntailed`, `ClosureContract`),
and the real emission site is characterized by
`RunAssembly.schedulerNext_eq_unsat_cases`.

NO `sorry`, no custom axiom. Regression record only: no active proof depends
on this module.
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerRunAssembly
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

namespace RootRouteRegression

/-- The DELETED conflict-free root-route contract, verbatim in shape (as
previously written in `Proofs/SchedulerRunAssembly.lean`): exclusion at
EVERY reachable level-zero, conflict-free branch, with no conflict event and
no evidence. Kept ONLY as the subject of the refutation below; the active
chain never consumes it. -/
def RootRouteExcludesOld (orig : List Domain) (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
    cfg.conflict = none → cfg.branch.level = 0 →
      ∀ a, OriginalLeaves leaf orig a → False

/-- **KERNEL REFUTATION**: the old contract is false. Witness: the empty box
`orig = []`, the always-true leaf and the real initialized root
configuration `SchedulerConfig.init [] [] []`. Initialization is reachable
(`SchedulerReachable.init`), has no recorded conflict (`rfl`) and level zero
(`rfl`), yet the empty assignment `[]` is an original leaf solution — so the
claimed exclusion fails. This is the maintained regression PLAN A1 requires:
a satisfiable-empty-initialization counterexample to the conflict-free
guard. -/
theorem not_rootRouteExcludesOld :
    ¬ RootRouteExcludesOld ([] : List Domain) (fun _ => true) := by
  intro h
  have hreach : SchedulerReachable
      (SchedulerConfig.init (leaf := fun _ => true) ([] : List Domain)
        ([] : List Clause) ([] : List Propagator)) :=
    SchedulerReachable.init [] [] [] (fun _ hc => absurd hc (List.not_mem_nil))
  exact h hreach rfl rfl ([] : Assignment)
    ⟨rfl, rfl, fun slot value hget => by simp_all⟩

end RootRouteRegression

end LeanFzn.Solver.UIP
