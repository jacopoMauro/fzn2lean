/-
Purpose: Core-only certified linear optimization with explicit incomplete runs.
Dependencies: Engine.Search, shared generic optimization and compiler correctness.
DAG: Core search -> partial certified oracle -> generic branch-and-bound -> public driver.
The legacy solver and its unconditional completion contract are not imported.
-/
import LeanFzn.Engine.Search
import LeanFzn.Integration.Optimization.Partial

namespace LeanFzn.Core
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Engine LeanFzn.Integration

/-- A Core give-up is an incomplete optimization round. No fallback is run. -/
def coreVerdictWith (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {})
    (fuel : Nat := coreFuel) : CertVerdict :=
  match coreSolveWith p o prev fuel with
  | .sat a => .sat a
  | .unsat => .unsat
  | .gaveUp => .fail

theorem coreVerdictWith_sat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat} {a : List Value}
    (h : coreVerdictWith prev p o fuel = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold coreVerdictWith at h
  cases hc : coreSolveWith p o prev fuel with
  | sat a' => simp [hc] at h; cases h; exact coreSolveWith_sat hc
  | unsat => simp [hc] at h
  | gaveUp => simp [hc] at h

theorem coreVerdictWith_unsat {prev : Option (List Value)}
    {p : CompiledProblem DomConstraint} {o : SearchConfig} {fuel : Nat}
    (h : coreVerdictWith prev p o fuel = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold coreVerdictWith at h
  cases hc : coreSolveWith p o prev fuel with
  | sat a => simp [hc] at h
  | unsat => exact coreSolveWith_unsat hc
  | gaveUp => simp [hc] at h

/-- The partial Core oracle, optionally bounded for development/regression checks. -/
def corePartialSolver (o : SearchConfig := {}) (fuel : Nat := coreFuel) : PartialCertSolver where
  solveWith prev p := coreVerdictWith prev p o fuel
  sat_sound := fun _ _ _ h => coreVerdictWith_sat h
  unsat_sound := fun _ _ h => coreVerdictWith_unsat h

/-- Generic B&B adapter. Its completeness gate is deliberately false. -/
def coreSolver (o : SearchConfig := {}) (fuel : Nat := coreFuel) : CertSolver :=
  (corePartialSolver o fuel).asCertSolver

/-- Core-only linear branch-and-bound. `complete = false` retains valid incumbents. -/
def optimizeCore (m : Model) (o : SearchConfig := {}) (fuel : Nat := coreFuel) :=
  optimizeCertified (coreSolver o fuel) m

theorem optimizeCore_solution_sound {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) (hwf : WellFormed fullSig m)
    {s : List Value × Int} (hs : s ∈ run.sols) :
    Satisfies fullSig fullInterp m (p.toStore s.1) ∧ LeanFzn.Semantics.ParamHonest m (p.toStore s.1) ∧
      m.solve.objective (p.toStore s.1) = some s.2 :=
  optimizeCertified_solution_sound h hwf hs

theorem optimizeCore_improving {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) :
    ∃ spec : ObjectiveSpec, run.sols.Pairwise (fun s t => betterB spec.dir t.2 s.2 = true) :=
  optimizeCertified_improving h

theorem optimizeCore_optimal {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) {s : List Value × Int}
    (hlast : run.sols.getLast? = some s) :
    IsSolution fullSig fullInterp m (p.toStore s.1) :=
  optimizeCertified_optimal h hwf hcomp hlast

theorem optimizeCore_unsat {o : SearchConfig} {fuel : Nat} {m : Model}
    {p : CompiledProblem DomConstraint} {run : OptRun}
    (h : optimizeCore m o fuel = .ok (p, run)) (hwf : WellFormed fullSig m)
    (hcomp : run.complete = true) (hnil : run.sols = []) :
    ¬ ∃ store, Satisfies fullSig fullInterp m store ∧ LeanFzn.Semantics.ParamHonest m store :=
  optimizeCertified_unsat h hwf hcomp hnil

end LeanFzn.Core
