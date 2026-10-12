/-
File: LeanFzn/Solver/Core/Types.lean

Purpose:
  Defines the representation-neutral semantic problem vocabulary shared by
  every LeanFzn.Solver architecture.

Dependencies:
  - LeanFzn.Semantics.Model: `Value` and `Store`.

Why:
  Constraint and objective payloads remain parameters so existing specialized
  representations can be ported without duplicating variables, domains, or
  assignment semantics. Operational states live in architecture layers.

DAG:
  LeanFzn.Semantics.Model -> LeanFzn.Solver.Core.Types -> all LeanFzn.Solver approaches
-/

import LeanFzn.Semantics.Model
open LeanFzn.Semantics


namespace LeanFzn.Solver.Core

open LeanFzn

/-- Stable position of a decision variable in a compiled problem. -/
abbrev Slot := Nat

/-- Finite candidate values for one slot. -/
abbrev Domain := List Value

/-- One value per slot, in problem order. -/
abbrev Assignment := List Value

/-- Shared compiled-problem container.

The constraint and objective languages are parameters. The initial port uses
the existing `DomConstraint`; future richer kernels may instantiate the same
container without changing search-state vocabulary. -/
structure Problem (Constraint : Type) (Objective : Type := Unit) where
  names : List String
  domains : List Domain
  constraints : List Constraint
  objective : Objective

/-- Common search outcome before source-level store reconstruction. -/
inductive SearchResult where
  | sat (assignment : Assignment)
  | unsat
  | unknown
  deriving Repr

end LeanFzn.Solver.Core
