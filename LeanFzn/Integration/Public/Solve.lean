/-
Purpose: Public source-model satisfaction on Core alone, with explicit unknown outcomes.
Dependencies: Engine.Search and compiler normalization/exactness; no legacy solver.
DAG: compiler + Core soundness -> source SAT/UNSAT theorems -> public driver.
-/
import LeanFzn.Engine.Search
import LeanFzn.Checker.Proofs.Check
import LeanFzn.Compiler.Proofs.Normalize
import LeanFzn.Integration.Public.Gate
import LeanFzn.Integration.Public.Preprocess

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

/-- Compile and run Core once, returning the actual Core counters without a
second solve.  A give-up carries its diagnostic cause in the public reason
string; the cause never changes the verdict. -/
def solveModelWithStats (m : Model) (o : SearchConfig := {}) (fuel : Nat := coreFuel) :
    Result × EngineStats :=
  match compileModelFull m with
  | .error e => (.unsupported e, {})
  | .ok p =>
      if gateOkFast (propagationProblem p) then
        let (r, st) := coreSolveFullPre p o none fuel
        match r with
        | .sat a => (.sat (p.toStore a), st)
        | .unsat => (.unsat, st)
        | .gaveUp => (.unknown (giveUpReason st), st)
      else (.unsupported "Core requires nonempty finite integer/Boolean domains", {})

/-- The gated satisfaction route: the input carries its own admission,
well-formedness and printable-name proofs, so the verdict needs no extra
hypothesis.  The body is the raw route on the gate's model, which is why
every verdict theorem below is a definitional rewrite of the existing one. -/
def gatedSolveModelWithStats (g : GatedModel) (o : SearchConfig := {})
    (fuel : Nat := coreFuel) : Result × EngineStats :=
  solveModelWithStats g.model o fuel

/-- The gated satisfaction route without counters. -/
def gatedSolveModel (g : GatedModel) (o : SearchConfig := {}) (fuel : Nat := coreFuel) :
    Result :=
  (gatedSolveModelWithStats g o fuel).1

/-- Compile and run Core once. No solver is selected when Core cannot decide. -/
def solveModel (m : Model) (o : SearchConfig := {}) (fuel : Nat := coreFuel) : Result :=
  (solveModelWithStats m o fuel).1

theorem solveModelWithStats_fst (m : Model) (o : SearchConfig) (fuel : Nat) :
    (solveModelWithStats m o fuel).1 = solveModel m o fuel := rfl

theorem gatedSolveModelWithStats_fst (g : GatedModel) (o : SearchConfig) (fuel : Nat) :
    (gatedSolveModelWithStats g o fuel).1 = gatedSolveModel g o fuel := rfl

theorem gatedSolveModel_eq (g : GatedModel) (o : SearchConfig) (fuel : Nat) :
    gatedSolveModel g o fuel = solveModel g.model o fuel := rfl

theorem solveModel_sat_correct {m : Model} {o : SearchConfig} {fuel : Nat} {store : Store}
    (hwf : WellFormed fullSig m) (h : solveModel m o fuel = .sat store) :
    Satisfies fullSig fullInterp m store := by
  unfold solveModel at h
  unfold solveModelWithStats at h
  cases hc : compileModelFull m with
  | error e => simp [hc] at h
  | ok p =>
      simp only [hc] at h
      split at h
      · cases hs : coreSolveFullPre p o none fuel with
        | mk r st =>
          cases r with
          | sat a =>
              simp [hs] at h
              cases h
              obtain ⟨hm, ha⟩ := coreSolveFullPre_sat hs
              exact ⟨hwf, (compileFull_exact hc hwf hm ha).1⟩
          | unsat => simp [hs] at h
          | gaveUp => simp [hs] at h
      · cases h

theorem solveModel_unsat_correct {m : Model} {o : SearchConfig} {fuel : Nat}
    (hwf : WellFormed fullSig m) (h : solveModel m o fuel = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧ LeanFzn.Semantics.ParamHonest m store := by
  unfold solveModel at h
  unfold solveModelWithStats at h
  cases hc : compileModelFull m with
  | error e => simp [hc] at h
  | ok p =>
      simp only [hc] at h
      split at h
      · cases hs : coreSolveFullPre p o none fuel with
        | mk r st =>
          cases r with
          | sat a => simp [hs] at h
          | unsat =>
              rintro ⟨store, hsat, hp⟩
              obtain ⟨a, hm, ha⟩ := compileFull_covers hc hwf hsat.2 hp
              have hn := coreSolveFullPre_unsat (p := p) (o := o) (prev := none)
                (fuel := fuel) (st := st) (by rw [hs]) a hm
              rw [ha] at hn
              cases hn
          | gaveUp => simp [hs] at h
      · cases h

/-! ## Gate-carrying verdict theorems

These state the same claims as `solveModel_sat_correct`/`solveModel_unsat_correct`
without a well-formedness premise: the `GatedModel` carries it, and admission is
part of the claim, not an assumption.  The proofs are the raw ones applied to
`g.model`; the gate never re-runs a check. -/

/-- A gated SAT witness is a satisfying store of the gated (and therefore of
the raw) model, whose admission and well-formedness are established. -/
theorem gatedSolveModel_sat_correct {g : GatedModel} {o : SearchConfig} {fuel : Nat}
    {store : Store} (h : gatedSolveModel g o fuel = .sat store) :
    LeanFzn.Semantics.Admission.Admitted g.model ∧
      WellFormed fullSig g.model ∧
      Satisfies fullSig fullInterp g.model store ∧
      (g.model.variables.all fun d => LeanFzn.Parser.Lexer.printableSolutionNameB d.name.name) = true := by
  have hraw : solveModel g.model o fuel = .sat store := h
  have hwf := (@LeanFzn.Checker.wellFormedFastB_iff g.model).mp g.wfFast
  exact ⟨g.admitted, hwf, solveModel_sat_correct hwf hraw, g.printables⟩

/-- A gated UNSAT verdict excludes every parameter-honest satisfying store of
the gated model: no well-formedness hypothesis survives. -/
theorem gatedSolveModel_unsat_correct {g : GatedModel} {o : SearchConfig} {fuel : Nat}
    (h : gatedSolveModel g o fuel = .unsat) :
    LeanFzn.Semantics.Admission.Admitted g.model ∧
      WellFormed fullSig g.model ∧
      ¬ ∃ store, Satisfies fullSig fullInterp g.model store ∧
        LeanFzn.Semantics.ParamHonest g.model store := by
  have hraw : solveModel g.model o fuel = .unsat := h
  have hwf := (@LeanFzn.Checker.wellFormedFastB_iff g.model).mp g.wfFast
  exact ⟨g.admitted, hwf, solveModel_unsat_correct hwf hraw⟩

/-- The driver's rule for raw input: if the gate accepts `m` and the gated
satisfaction route returns a verdict, that verdict's claim holds for `m`. -/
theorem gatedSolveModel_unsat_correct_raw {m : Model} {g : GatedModel}
    {o : SearchConfig} {fuel : Nat} (hg : gate m = .ok g)
    (h : gatedSolveModel g o fuel = .unsat) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧
      LeanFzn.Semantics.ParamHonest m store := by
  obtain ⟨hgm, -, -, -⟩ := gate_ok_facts hg
  obtain ⟨-, -, hlim⟩ := gatedSolveModel_unsat_correct h
  rw [hgm] at hlim
  exact hlim

end LeanFzn.Core
