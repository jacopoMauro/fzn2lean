/-
Purpose: Correctness and equivalence theorems for the objective checker.
Dependencies: Checker.Runtime.Objective and correctness of earlier checker layers.
DAG: Runtime.Objective -> Proofs.Objective -> public Checker.Objective import.
-/
import LeanFzn.Checker.Runtime.Objective
import LeanFzn.Checker.Proofs.Check

open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker

open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Checker.Solution

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
