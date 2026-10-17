/-
File: LeanFzn/Checker/Objective.lean

Purpose:
  The objective value of a checked solution (PLAN.md task O1).  An
  optimizing solver prints improving solutions; to validate the claimed
  objective trajectory, `checkedObjective` re-checks a solution with the
  verified front door and returns the source objective evaluated at the
  solution's completed store.  `checkedObjective_sound` is its verified
  twin: a returned value is the objective of a satisfying,
  parameter-honest store of the model.  (Optimality itself quantifies
  over all stores and is certified by the solver's UNSAT proof, not
  here.)

Dependencies:
  - LeanFzn.Checker.Check: `checkModelSolution`, its correctness.
-/

import LeanFzn.Checker.Check

open LeanFzn.Semantics
open LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Checker.Solution

/-- The objective value of a solution accepted by `checkModelSolution`
    (`none` if rejected, malformed, or the model has no integer
    objective). -/
def checkedObjective (m : Model) (sol : String) : Option Int :=
  match checkModelSolution m sol with
  | .accepted =>
      match parseSolution (stripSeparators sol) with
      | .ok es => m.solve.objective (completedStore m es)
      | .error _ => none
  | _ => none

/-- **Soundness of `checkedObjective`.** -/
theorem checkedObjective_sound {m : Model} {sol : String} {i : Int}
    (h : checkedObjective m sol = some i) :
    ∃ es, parseSolution (stripSeparators sol) = .ok es ∧
      Satisfies fullSig fullInterp m (completedStore m es) ∧
      ParamHonest m (completedStore m es) ∧
      m.solve.objective (completedStore m es) = some i := by
  unfold checkedObjective at h
  split at h
  · rename_i hacc
    obtain ⟨es, hparse, _, hpar, hsat⟩ := checkModelSolution_accepted hacc
    rw [hparse] at h
    exact ⟨es, hparse, hsat, hpar, h⟩
  · cases h

end LeanFzn.Checker
