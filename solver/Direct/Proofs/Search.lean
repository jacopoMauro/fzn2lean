/-
File: solver/Direct/Proofs/Search.lean

Purpose:
  Proves the executable reference search sound and complete for its compiled
  finite problem, by delegating to the generic exhaustive-search theorems
  (`solver/Search.lean`'s `search_some`/`search_none`, PLAN.md D3's
  prescribed reuse).

Dependencies:
  - solver.Direct.Search: executable reference search (`solveCompiled` is
    `search (accepts problem) problem.domains []`).
  - solver.Search (transitively): `search_some` and `search_none`.

DAG:
  solver.Direct.Search -> solver.Direct.Proofs.Search
  -> solver.Direct.Correctness
-/

import solver.Direct.Search
import solver.Propagators

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Solver

/-- A returned assignment belongs to the initial finite space and satisfies
    every compiled constraint. -/
theorem solveCompiled_sat {problem : CompiledProblem DomConstraint} {assignment : List Value}
    (hsolve : solveCompiled problem = some assignment) :
    assignment ∈ allAssigns problem.domains ∧
      accepts problem assignment = true := by
  obtain ⟨a, ha, hrfl, hleaf⟩ := LeanFzn.Solver.search_some (accepts problem)
    problem.domains [] assignment hsolve
  rw [List.nil_append] at hrfl hleaf
  rw [hrfl]
  exact ⟨ha, hleaf⟩

/-- Failure of exhaustive compiled search excludes every accepted assignment
    in the initial finite space. -/
theorem solveCompiled_unsat {problem : CompiledProblem DomConstraint}
    (hsolve : solveCompiled problem = none) :
    ∀ assignment ∈ allAssigns problem.domains,
      accepts problem assignment = false := by
  intro assignment ha
  have h := LeanFzn.Solver.search_none (accepts problem) problem.domains []
    hsolve assignment ha
  simpa using h

end LeanFzn.Solver.Direct
