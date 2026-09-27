/-
File: solver/Core/Semantics.lean

Purpose:
  Defines architecture-independent semantic relations for core assignments.

Dependencies:
  - solver.Core.Types: shared domains and assignments.

DAG:
  solver.Core.Types -> solver.Core.Semantics -> all solver architectures
-/

import solver.Core.Types

namespace LeanFzn.Solver.Core

open LeanFzn

/-- A complete assignment contains one value for every domain. -/
def Assignment.Fits (domains : List Domain) (assignment : Assignment) : Prop :=
  assignment.length = domains.length ∧
    ∀ slot value, assignment[slot]? = some value →
      value ∈ domains.getD slot []

end LeanFzn.Solver.Core
