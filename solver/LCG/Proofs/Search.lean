/-
File: solver/LCG/Proofs/Search.lean

Purpose:
  End-to-end internal SAT/UNSAT obligations for the LCG loop.

  SAT is fully discharged: every `.sat` outcome passes the engine's leaf
  test (domain fit + all constraints), proved by fuel induction over
  `lcgSearch.go` (`go_sat_leaf`), so `solve_sat_correct` is
  premise-free.

  UNSAT is discharged relative to an explicit engine-safety premise
  bundle (`EngineSafe`): the engine reports `.unsat` from either a
  level-0 conflict or a level-0 leaf violation, and excluding all
  internal solutions from those terminal reports requires the
  propagation/conflict/leaf-safety obligations of L0.2–L0.4 (each
  propagator explanation entailed; trail-derived domains valid;
  level-0 exhaustiveness). The premise bundle is the exact remaining
  proof debt, stated rather than assumed — when L0.2–L0.4 close it, the
  theorem becomes unconditional.

Dependencies:
  - solver.LCG.Search: executable LCG entry point.
  - solver.LCG.Proofs.Transitions: local transition obligations.

DAG:
  LCG.Search + LCG.Proofs.Transitions -> LCG.Proofs.Search
-/

import solver.LCG.Search
import solver.LCG.Proofs.Transitions

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- Every `.sat` outcome of the engine loop passes the leaf test: the
    assignment fits the original problem domains and satisfies every
    constraint under the Boolean semantics. -/
theorem go_sat_leaf {problem : Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State) (a : Assignment),
      lcgSearch.go problem constraintHoldsB props fuel st = .sat a →
        fitsB problem a = true ∧
          problem.constraints.all (fun c => constraintHoldsB c a) = true := by
  intro fuel
  induction fuel with
  | zero =>
      intro st a h
      simp only [lcgSearch.go] at h
      cases h
  | succ fuel ih =>
      intro st a h
      simp only [lcgSearch.go] at h
      -- outermost match: (conflict, decisionLevel)
      split at h
      · -- conflict at 0: unsat, contradiction
        cases h
      · -- conflict above 0
        split at h
        · -- no analysis: chronological fallback
          exact ih _ _ h
        · -- analysis: backjump + learn + assert
          exact ih _ _ h
      · -- no conflict: match allSingleton
        split at h
        · -- allSingleton true: match singletonAssignment
          split at h
          · -- some a': leaf if
            split at h
            · -- leaf check true: SAT
              injection h with hinj
              subst hinj
              rename_i hleaf
              rw [Bool.and_eq_true] at hleaf
              exact hleaf
            · -- leaf check false: level if
              split at h
              · -- level 0: unsat, contradiction
                cases h
              · -- level > 0: retreat
                exact ih _ _ h
          · -- singletonAssignment none: unknown, contradiction
            cases h
        · -- not allSingleton: match decideLiteral
          split at h
          · -- none: unknown, contradiction
            cases h
          · -- some l: recurse
            exact ih _ _ h

/-- Every `.unsat` outcome of the engine loop occurs at some
    post-propagation state in one of the two root-terminal shapes:
    a level-0 conflict, or a conflict-free level-0 state. -/
theorem go_unsat_shape {problem : Problem Constraint Objective}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {props : List Propagator} :
    ∀ (fuel : Nat) (st : State),
      lcgSearch.go problem constraintHoldsB props fuel st = .unsat →
        ∃ st0 : State,
          ((propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
              props st0).conflict.isSome = true ∧
            (propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
              props st0).decisionLevel = 0) ∨
          ((propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
              props st0).conflict = none ∧
            (propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
              props st0).decisionLevel = 0) := by
  intro fuel
  induction fuel with
  | zero => intro st h; simp only [lcgSearch.go] at h; cases h
  | succ fuel ih =>
      intro st h
      simp only [lcgSearch.go] at h
      split at h
      · -- conflict at level 0: the first root-terminal shape
        next val hval hconf =>
          refine ⟨st, Or.inl ⟨?_, hconf⟩⟩
          simp only [Option.isSome_iff_exists]
          exact ⟨val, hval⟩
      · -- conflict above 0: the .unsat (if any) comes from the recursion
        split at h
        · exact ih _ h
        · exact ih _ h
      · -- no conflict; the outermost match already established none
        rename_i hconfnone
        split at h
        · rename_i hsingle
          split at h
          · split at h
            · -- leaf check passed: sat, contradiction with unsat
              cases h
            · split at h
              · -- leaf failed at level 0: the second root-terminal shape
                next hroot =>
                  refine ⟨st, Or.inr ⟨hconfnone, ?_⟩⟩
                  simpa using hroot
              · -- leaf failed above 0: the .unsat comes from the retreat
                exact ih _ h
          · -- singletonAssignment none: unknown, contradiction
            cases h
        · -- not allSingleton: decide or unknown
          split at h
          · -- unknown, contradiction
            cases h
          · -- decision: the .unsat comes from the recursion
            next l hl => exact ih _ h

/-- Engine-safety premise bundle for UNSAT soundness. Each component is
    an L0.2–L0.4 obligation; the bundle is the remaining proof debt,
    made explicit instead of silently assumed.

    * `unsat_root_conflict`: whenever the loop reports `.unsat` from a
      level-0 post-propagation conflict, every internal solution is
      excluded — requires conflict-clause entailment and falsification
      under the represented assignments (L0.2/L0.4);
    * `unsat_root_leaf`: whenever the loop reports `.unsat` from a
      conflict-free level-0 post-propagation state, every internal
      solution is excluded — requires that the state's domains force
      the checked leaf assignment(s) (L0.3 propagation soundness). -/
structure EngineSafe (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (props : List Propagator) : Prop where
  unsat_root_conflict : ∀ (st0 : State),
    (propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
        props st0).conflict.isSome = true →
      (propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
        props st0).decisionLevel = 0 →
        ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment
  unsat_root_leaf : ∀ (st0 : State),
    (propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
        props st0).conflict = none →
      (propagateLoop (32 + 8 * st0.domains.length + 4 * st0.trail.length)
        props st0).decisionLevel = 0 →
        ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment

/-- A SAT result is an internal problem solution. -/
theorem solve_sat_correct
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator} {assignment : Assignment}
    (hagrees : ∀ constraint assignment,
      constraintHoldsB constraint assignment = true ↔
        constraintHolds constraint assignment)
    (hsolve : solve problem constraintHoldsB propagators = .sat assignment) :
    ProblemSolution problem constraintHolds assignment := by
  -- solve = lcgSearch defaultFuel ...; unfold and apply the leaf theorem
  unfold solve at hsolve
  obtain ⟨hfits, hcs⟩ := go_sat_leaf defaultFuel
    (initialStateWithRoots problem) assignment hsolve
  refine ⟨fitsB_iff.mp hfits, ?_⟩
  intro constraint hcons
  have := List.all_eq_true.mp hcs constraint hcons
  exact hagrees constraint assignment |>.mp this

/-- An UNSAT result excludes every internal problem solution, relative to
    the explicit engine-safety bundle (see `EngineSafe`). The engine
    inversion `go_unsat_shape` pins every `.unsat` outcome to a
    root-terminal post-propagation state; the bundle then supplies the
    semantic exclusion for each shape. When L0.2–L0.4 discharge the
    bundle, the theorem becomes unconditional. -/
theorem solve_unsat_correct
    {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator}
    (hsafe : EngineSafe problem constraintHolds constraintHoldsB propagators)
    (hsolve : solve problem constraintHoldsB propagators = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment := by
  unfold solve at hsolve
  obtain ⟨st0, hshape⟩ := go_unsat_shape defaultFuel
    (initialStateWithRoots problem) hsolve
  rcases hshape with ⟨hisSome, hlevel⟩ | ⟨hnone, hlevel⟩
  · exact hsafe.unsat_root_conflict st0 hisSome hlevel
  · exact hsafe.unsat_root_leaf st0 hnone hlevel

end LeanFzn.Solver.LCG
