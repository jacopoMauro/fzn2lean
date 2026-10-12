/-
File: LeanFzn/Solver/Reference/Proofs/Search.lean

Purpose:
  Proves the executable reference search sound and complete for its compiled
  finite problem, by delegating to the generic exhaustive-search theorems
  (`LeanFzn/Solver/Reference/Enumerate.lean`'s `search_some`/`search_none`, PLAN.md D3's
  prescribed reuse).

Dependencies:
  - LeanFzn.Solver.Reference.Search: executable reference search (`solveCompiled` is
    `search (accepts problem) problem.domains []`).
  - LeanFzn.Solver.Reference.Enumerate (transitively): `search_some` and `search_none`.

DAG:
  LeanFzn.Solver.Reference.Search -> LeanFzn.Solver.Reference.Proofs.Search
  -> LeanFzn.Compiler.Correctness
-/

import LeanFzn.Solver.Reference.Search
import LeanFzn.Solver.Propagation.DomainConstraints


namespace LeanFzn.Solver.Reference
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Compiler
open LeanFzn LeanFzn.Solver

/-- A returned assignment belongs to the initial finite space and satisfies
    every compiled constraint. -/
theorem solveCompiled_sat {problem : CompiledProblem LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint} {assignment : List Value}
    (hsolve : solveCompiled problem = some assignment) :
    assignment ∈ allAssigns problem.domains ∧
      accepts problem assignment = true := by
  obtain ⟨a, ha, hrfl, hleaf⟩ := LeanFzn.Solver.Reference.search_some (accepts problem)
    problem.domains [] assignment hsolve
  rw [List.nil_append] at hrfl hleaf
  rw [hrfl]
  exact ⟨ha, hleaf⟩

/-- Failure of exhaustive compiled search excludes every accepted assignment
    in the initial finite space. -/
theorem solveCompiled_unsat {problem : CompiledProblem LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint}
    (hsolve : solveCompiled problem = none) :
    ∀ assignment ∈ allAssigns problem.domains,
      accepts problem assignment = false := by
  intro assignment ha
  have h := LeanFzn.Solver.Reference.search_none (accepts problem) problem.domains []
    hsolve assignment ha
  simpa using h

end LeanFzn.Solver.Reference
