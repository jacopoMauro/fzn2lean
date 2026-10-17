/-
File: solver/Tree/Operations.lean

Purpose:
  Defines executable operations on the classical tree-search reference state.
  Contains no correctness proofs.

Dependencies:
  - solver.Tree.Types: tree-search state over the common problem vocabulary.

DAG:
  solver.Tree.Types -> solver.Tree.Operations
-/

import solver.Core.Semantics
import solver.Tree.Types

namespace LeanFzn.Solver.Tree

open LeanFzn LeanFzn.Solver.Core

/-- Initial reference state of a compiled problem. -/
def initialState (problem : Problem Constraint Objective) : State :=
  { domains := problem.domains, decisions := [], trail := [], nogoods := [] }

/-- Replace one slot domain when the slot exists. -/
def setDomain (state : State) (slot : Slot) (domain : Domain) : State :=
  { state with domains := state.domains.set slot domain }

/-- Record a decision and narrow its slot to the selected singleton. -/
def decide (state : State) (decision : Decision) : State :=
  let previous := state.domains.getD decision.slot []
  { domains := state.domains.set decision.slot [decision.value]
    decisions := decision :: state.decisions
    trail := { slot := decision.slot, previous := previous } :: state.trail
    nogoods := state.nogoods }

/-- A decision agrees with a complete assignment. -/
def Decision.Matches (decision : Decision) (assignment : Assignment) : Prop :=
  assignment[decision.slot]? = some decision.value

/-- A NoGood is violated when all of its decisions match. -/
def NoGood.Violated (nogood : NoGood) (assignment : Assignment) : Prop :=
  ∀ decision ∈ nogood, decision.Matches assignment

/-- A state excludes an assignment when one of its learned NoGoods is
    violated. -/
def State.Excludes (state : State) (assignment : Assignment) : Prop :=
  ∃ nogood ∈ state.nogoods, nogood.Violated assignment

end LeanFzn.Solver.Tree
