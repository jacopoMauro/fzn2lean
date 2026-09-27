/-
File: solver/LCG/Types.lean

Purpose:
  Defines the operational vocabulary for a CP-SAT/lazy-clause-generation
  solver: integer atoms, signed literals, clauses, explanations, trails,
  decision levels, learned clauses, and propagation queues.

Dependencies:
  - solver.Core.Types: shared problems, assignments, slots, and domains.

DAG:
  solver.Core.Types -> solver.LCG.Types
-/

import solver.Core.Semantics

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- Atomic propositions exposed to the Boolean reasoning layer. More integer
    encodings can be added without changing clauses or the implication trail. -/
inductive Atom where
  | boolEq (slot : Slot) (value : Bool)
  | intLe (slot : Slot) (upper : Int)
  deriving Repr, DecidableEq

/-- A signed atom. Positive literals assert the atom; negative literals assert
    its negation. -/
structure Literal where
  atom : Atom
  positive : Bool
  deriving Repr, DecidableEq

/-- SAT-style disjunction of literals. -/
abbrev Clause := List Literal

/-- Explanation attached to an implied literal. It must eventually be proved
    entailed by the compiled problem and earlier trail facts. -/
structure Reason where
  clause : Clause
  deriving Repr

/-- One entry in the implication trail. A missing reason marks a decision. -/
structure TrailEntry where
  literal : Literal
  level : Nat
  reason : Option Reason
  deriving Repr

/-- Output of conflict analysis: an entailed clause, the level to restore,
    and the literal asserted by that clause after backjumping. -/
structure ConflictAnalysis where
  learned : Clause
  backjumpLevel : Nat
  asserting : Literal
  deriving Repr

/-- Identifies a registered propagator in the wake-up queue. -/
abbrev PropagatorId := Nat

/-- Operational state of the LCG solver. -/
structure State where
  domains : List Domain
  trail : List TrailEntry
  decisionLevel : Nat
  clauses : List Clause
  learned : List Clause
  queue : List PropagatorId
  conflict : Option Clause
  deriving Repr

/-! The `queue` field is reserved for the two-watched-literal
    propagation schedule (L0.4's wake-up queue). The current engine
    sweeps the whole propagator list each round and never reads it;
    it stays a (write-only) placeholder so the future scheduler can
    drop in without a state-shape change. -/

/-- A compiled problem plus its initial SAT clauses. Constraint-specific
    propagators are registered separately so algorithms and proofs can be
    layered independently. -/
structure Problem (Constraint : Type) (Objective : Type := Unit) extends
    Core.Problem Constraint Objective where
  clauses : List Clause

end LeanFzn.Solver.LCG
