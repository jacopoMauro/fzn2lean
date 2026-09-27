/-
File: solver/Direct/Search.lean

Purpose:
  Contains the executable reference search and model-level driver for the
  direct solver. Contains no semantic correctness proofs.

Dependencies:
  - solver.Search: generic terminating finite Cartesian-product search.
  - solver.Direct.Compile: compiled problems and their internal leaf test.

DAG:
  solver.Search + solver.Direct.Compile + solver.Direct.Types -> solver.Direct.Search
-/

import solver.Search
import solver.Direct.Compile

namespace LeanFzn.Solver.Direct

open LeanFzn

/-- Search a compiled finite problem for a complete accepted assignment. -/
def solveCompiled (problem : CompiledProblem DomConstraint) :
    Option (List Value) :=
  LeanFzn.Solver.search (accepts problem) problem.domains []

/-- Direct solver driver. Rendering and the external solution checker are not
    called here. A successful assignment is mapped directly to a `Store`. -/
def solve (model : Model) : Result :=
  match compileModel model with
  | .error reason => .unsupported reason
  | .ok problem =>
      match solveCompiled problem with
      | some assignment => .sat (problem.toStore assignment)
      | none => .unsat

end LeanFzn.Solver.Direct
