/-
File: solver/Tree/Types.lean

Purpose:
  Defines operational state for classical domain-narrowing tree search.

Dependencies:
  - solver.Core.Types: shared problems, slots, domains, and assignments.

DAG:
  solver.Core.Types -> solver.Tree.Types -> tree-search implementations
-/

import solver.Core.Types

namespace LeanFzn.Solver.Tree

open LeanFzn LeanFzn.Solver.Core

/-- A branch decision fixing one slot to one value. -/
structure Decision where
  slot : Slot
  value : Value
  deriving Repr

/-- A forbidden conjunction of tree-search decisions. -/
abbrev NoGood := List Decision

/-- Reference restoration record for a domain update. -/
structure TrailEntry where
  slot : Slot
  previous : Domain
  deriving Repr

/-- Logical/reference state for classical CP tree search. Optimized sparse
    states refine to this view. -/
structure State where
  domains : List Domain
  decisions : List Decision
  trail : List TrailEntry
  nogoods : List NoGood
  deriving Repr

end LeanFzn.Solver.Tree
