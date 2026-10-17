/-
File: solver/Tree/Invariants.lean

Purpose:
  States well-formedness and solution-set preservation contracts for
  classical tree-search state. Contains no executable code.

Dependencies:
  - solver.Tree.Operations: tree-search state and logical operations.

DAG:
  solver.Tree.Operations -> solver.Tree.Invariants -> tree adapters
-/

import solver.Tree.Operations

namespace LeanFzn.Solver.Tree

open LeanFzn LeanFzn.Solver.Core

/-- Structural well-formedness of the common compiled problem container. -/
def ProblemWellFormed (problem : Problem Constraint Objective) : Prop :=
  problem.names.length = problem.domains.length

/-- The common state remains aligned with its problem and only narrows initial
    domains. Specialized states must refine to a state satisfying this. -/
def StateWellFormed (problem : Problem Constraint Objective)
    (state : State) : Prop :=
  state.domains.length = problem.domains.length ∧
    ∀ slot value, value ∈ state.domains.getD slot [] →
      value ∈ problem.domains.getD slot []

/-- Assignments currently represented by a state, before applying a
    constraint-language-specific satisfaction predicate. -/
def Represents (state : State) (assignment : Assignment) : Prop :=
  assignment.Fits state.domains ∧ ¬ state.Excludes assignment

/-- A transition is safe when it retains every represented assignment that
    satisfies the chosen internal constraint semantics. -/
def PreservesSolutions (satisfies : Assignment → Prop)
    (before after : State) : Prop :=
  ∀ assignment, Represents before assignment → satisfies assignment →
    Represents after assignment

/-- A contradiction result is sound when the state represents no satisfying
    assignment. -/
def Contradictory (satisfies : Assignment → Prop) (state : State) : Prop :=
  ¬ ∃ assignment, Represents state assignment ∧ satisfies assignment

end LeanFzn.Solver.Tree
