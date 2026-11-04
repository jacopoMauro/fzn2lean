/-
Purpose: Public source-model satisfaction on Core alone, with explicit unknown outcomes.
Dependencies: Engine.Search and compiler normalization/exactness; no legacy solver.
DAG: compiler + Core soundness -> source SAT/UNSAT theorems -> public driver.
-/
import LeanFzn.Engine.Search
import LeanFzn.Compiler.Proofs.Normalize

namespace LeanFzn.Core
open LeanFzn LeanFzn.Engine LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Semantics.Globals LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Integration

inductive Result where
  | sat (store : Store)
  | unsat
  | unsupported (reason : String)
  | unknown (reason : String)

/-- The compiled Core-only seam; give-up stays unknown. -/
def solveCompiled (p : CompiledProblem DomConstraint) (o : SearchConfig := {})
    (fuel : Nat := coreFuel) : SearchResult :=
  match coreSolve p o fuel with
  | .sat a => .sat a
  | .unsat => .unsat
  | .gaveUp => .unknown

theorem solveCompiled_sat {p : CompiledProblem DomConstraint} {o : SearchConfig}
    {fuel : Nat} {a : List Value} (h : solveCompiled p o fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveCompiled at h
  cases hc : coreSolve p o fuel with
  | sat a' => simp [hc] at h; cases h; exact coreSolve_sat hc
  | unsat => simp [hc] at h
  | gaveUp => simp [hc] at h

theorem solveCompiled_unsat {p : CompiledProblem DomConstraint} {o : SearchConfig}
    {fuel : Nat} (h : solveCompiled p o fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveCompiled at h
  cases hc : coreSolve p o fuel with
  | sat a => simp [hc] at h
  | unsat => exact coreSolve_unsat hc
  | gaveUp => simp [hc] at h

/-- Compile and run Core once. No solver is selected when Core cannot decide. -/
def solveModel (m : Model) (o : SearchConfig := {}) (fuel : Nat := coreFuel) : Result :=
  match compileModelFull m with
  | .error e => .unsupported e
  | .ok p =>
      if gateOkFast (propagationProblem p) then
        match solveCompiled p o fuel with
        | .sat a => .sat (p.toStore a)
        | .unsat => .unsat
        | .unknown => .unknown "Core search incomplete (gaveUp)"
      else .unsupported "Core requires nonempty finite integer/Boolean domains"

/-- The same result with the actual Core counters, without a second solve. -/
def solveModelWithStats (m : Model) (o : SearchConfig := {}) (fuel : Nat := coreFuel) :
    Result × EngineStats :=
  match compileModelFull m with
  | .error e => (.unsupported e, {})
  | .ok p =>
      if gateOkFast (propagationProblem p) then
        let (r, st) := coreSolveFull p o fuel
        match r with
        | .sat a => (.sat (p.toStore a), st)
        | .unsat => (.unsat, st)
        | .gaveUp => (.unknown "Core search incomplete (gaveUp)", st)
      else (.unsupported "Core requires nonempty finite integer/Boolean domains", {})

theorem solveModelWithStats_fst (m : Model) (o : SearchConfig) (fuel : Nat) :
    (solveModelWithStats m o fuel).1 = solveModel m o fuel := by
  unfold solveModelWithStats solveModel
  cases hc : compileModelFull m with
  | error e => rfl
  | ok p =>
      simp only
      split
      · unfold solveCompiled coreSolve
        cases coreSolveFull p o fuel with
        | mk r st => cases r <;> rfl
      · rfl

theorem solveModel_sat_correct {m : Model} {o : SearchConfig} {fuel : Nat} {store : Store}
    (hwf : WellFormed fullSig m) (h : solveModel m o fuel = .sat store) :
    Satisfies fullSig fullInterp m store := by
  unfold solveModel at h
  cases hc : compileModelFull m with
  | error e => simp [hc] at h
  | ok p =>
      simp only [hc] at h
      split at h
      · cases hs : solveCompiled p o fuel with
        | sat a =>
            simp [hs] at h
            cases h
            obtain ⟨hm, ha⟩ := solveCompiled_sat hs
            exact ⟨hwf, (compileFull_exact hc hwf hm ha).1⟩
        | unsat => simp [hs] at h
        | unknown => simp [hs] at h
      · cases h

theorem solveModel_unsat_correct {m : Model} {o : SearchConfig} {fuel : Nat}
    (hwf : WellFormed fullSig m) (h : solveModel m o fuel = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧ LeanFzn.Semantics.ParamHonest m store := by
  unfold solveModel at h
  cases hc : compileModelFull m with
  | error e => simp [hc] at h
  | ok p =>
      simp only [hc] at h
      split at h
      · cases hs : solveCompiled p o fuel with
        | sat a => simp [hs] at h
        | unsat =>
            rintro ⟨store, hsat, hp⟩
            obtain ⟨a, hm, ha⟩ := compileFull_covers hc hwf hsat.2 hp
            have hn := solveCompiled_unsat hs a hm
            rw [ha] at hn
            cases hn
        | unknown => simp [hs] at h
      · cases h

end LeanFzn.Core
