/-
File: LeanFzn/Integration/Solve/Core.lean

N9: the public seam for the certified Core engine.  `solveSearchConfigCore`
runs the fuel-bounded `coreSolve`; when Core makes no claim it falls back to
the already-certified kernel route `solveSearchConfig`.  The stats-preserving
twin `solveSearchConfigCoreFull` returns the terminal `EngineStats` of the
identical run for the `--engine=core --stats` driver.

Every verdict is inherited from a proved entry: Core SAT/UNSAT from
`coreSolve_sat`/`coreSolve_unsat`, the fallback from
`solveSearchConfig_sat`/`solveSearchConfig_unsat`; `_total` uses
`solveSearchConfig_verdict` on the only fallback branch.
-/
import LeanFzn.Engine.Search
import LeanFzn.Legacy.Integration.Kernel.Annot

namespace LeanFzn.Integration

open LeanFzn LeanFzn.Engine LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation

/-- Core's default-fuel run, falling back to the certified kernel route when
Core gives up. -/
def solveSearchConfigCore (p : CompiledProblem DomainFiltering.DomConstraint)
    (o : SearchConfig) : SearchResult :=
  match coreSolve p o coreFuel with
  | .sat a => .sat a
  | .unsat => .unsat
  | .gaveUp => solveSearchConfig p o

/-- Stats-preserving twin: the verdict of `solveSearchConfigCore` together
with the terminal engine counters of the run that produced it. -/
def solveSearchConfigCoreFull (p : CompiledProblem DomainFiltering.DomConstraint)
    (o : SearchConfig) : SearchResult × EngineStats :=
  match coreSolveFull p o coreFuel with
  | (.sat a, st) => (.sat a, st)
  | (.unsat, st) => (.unsat, st)
  | (.gaveUp, st) =>
      match solveSearchConfig p o with
      | .sat a => (.sat a, st)
      | .unsat => (.unsat, st)
      | .unknown => (.unknown, st)

/-- Core's SAT answers are source solutions. -/
theorem solveSearchConfigCore_sat
    {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig} {a : List Value}
    (h : solveSearchConfigCore p o = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold solveSearchConfigCore at h
  cases hc : coreSolve p o coreFuel with
  | sat a' =>
      simp [hc] at h
      cases h
      exact coreSolve_sat hc
  | unsat => simp [hc] at h
  | gaveUp =>
      simp [hc] at h
      exact solveSearchConfig_sat h

/-- Core's UNSAT answers refute every source solution. -/
theorem solveSearchConfigCore_unsat
    {p : CompiledProblem DomainFiltering.DomConstraint}
    {o : SearchConfig}
    (h : solveSearchConfigCore p o = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold solveSearchConfigCore at h
  cases hc : coreSolve p o coreFuel with
  | sat a' => simp [hc] at h
  | unsat =>
      simp [hc] at h
      exact coreSolve_unsat hc
  | gaveUp =>
      simp [hc] at h
      exact solveSearchConfig_unsat h

/-- The Core seam is total: it never returns `.unknown`. -/
theorem solveSearchConfigCore_total
    (p : CompiledProblem DomainFiltering.DomConstraint) (o : SearchConfig) :
    solveSearchConfigCore p o ≠ .unknown := by
  unfold solveSearchConfigCore
  cases hc : coreSolve p o coreFuel with
  | sat a => simp
  | unsat => simp
  | gaveUp =>
      simp
      exact solveSearchConfig_verdict p o

/-- The first component of the stats twin is the certified verdict. -/
theorem solveSearchConfigCoreFull_fst
    (p : CompiledProblem DomainFiltering.DomConstraint) (o : SearchConfig) :
    (solveSearchConfigCoreFull p o).1 = solveSearchConfigCore p o := by
  unfold solveSearchConfigCoreFull solveSearchConfigCore
  cases hcf : coreSolveFull p o coreFuel with
  | mk r st =>
      cases r with
      | sat a => simp [coreSolve, hcf]
      | unsat => simp [coreSolve, hcf]
      | gaveUp =>
          cases hk : solveSearchConfig p o <;> simp [coreSolve, hcf]

end LeanFzn.Integration
