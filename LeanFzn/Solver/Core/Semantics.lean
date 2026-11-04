/-
File: LeanFzn/Solver/Core/Semantics.lean

Purpose:
  Defines architecture-independent semantic relations for core assignments.

Dependencies:
  - LeanFzn.Solver.Core.Types: shared domains and assignments.

DAG:
  LeanFzn.Solver.Core.Types -> LeanFzn.Solver.Core.Semantics -> all LeanFzn.Solver architectures
-/

import LeanFzn.Solver.Core.Types
open LeanFzn.Semantics


namespace LeanFzn.Solver.Core

open LeanFzn

/-- A complete assignment contains one value for every domain.  The carrier
    is abstracted so the same relation covers compiler source slots
    (`List Value`) and the compact runtime domains (`Dom`). -/
def Assignment.Fits {α : Type} [DomainLike α]
    (domains : List α) (assignment : Assignment) : Prop :=
  assignment.length = domains.length ∧
    ∀ slot value, assignment[slot]? = some value →
      value ∈ domains.getD slot DomainLike.empty

end LeanFzn.Solver.Core
