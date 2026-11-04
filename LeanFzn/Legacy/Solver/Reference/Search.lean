/-
File: LeanFzn/Solver/Reference/Search.lean

Purpose:
  Contains the executable reference search and model-level driver for the
  direct LeanFzn.Solver. Contains no semantic correctness proofs.

Dependencies:
  - LeanFzn.Solver.Core.Enumerate: generic terminating finite Cartesian-product search.
  - LeanFzn.Compiler.Compile: compiled problems and their internal leaf test.

DAG:
  LeanFzn.Solver.Core.Enumerate + LeanFzn.Compiler.Compile + LeanFzn.Compiler.Types -> LeanFzn.Solver.Reference.Search
-/

import LeanFzn.Legacy.Solver.Reference.Enumerate
import LeanFzn.Compiler.Compile


namespace LeanFzn.Solver.Reference
open LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Compiler
open LeanFzn

/-- Search a compiled finite problem for a complete accepted assignment. -/
def solveCompiled (problem : CompiledProblem LeanFzn.Solver.Propagation.DomainFiltering.DomConstraint) :
    Option (List Value) :=
  LeanFzn.Solver.Reference.search (accepts problem) (problem.domains.map Dom.enum) []

/-- Direct LeanFzn.Solver driver. Rendering and the external solution checker are not
    called here. A successful assignment is mapped directly to a `Store`. -/
def solve (model : Model) : Result :=
  match compileModel model with
  | .error reason => .unsupported reason
  | .ok problem =>
      match solveCompiled problem with
      | some assignment => .sat (problem.toStore assignment)
      | none => .unsat

end LeanFzn.Solver.Reference
