/-
File: solver/LCG/Operations.lean

Purpose:
  Defines proof-free literal evaluation (including the shared integer view
  of values), trail manipulation, clause insertion, propagator results, and
  the propagator interface for the LCG solver.

Dependencies:
  - solver.LCG.TrailEval: trail-derived literal evaluation and the
    executable first-UIP conflict analysis backing `analyzeConflict`.

DAG:
  solver.LCG.Types -> solver.LCG.TrailEval -> solver.LCG.Operations
-/

import solver.LCG.TrailEval

namespace LeanFzn

/-- Integer view of a value: integers themselves, Booleans as 0/1, and
    nothing for sets and arrays. Declared here (LCG layer) because only
    the order encoding depends on it. -/
def Value.intView : Value → Option Int
  | .int i => some i
  | .bool b => some (if b then 1 else 0)
  | _ => none

end LeanFzn

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- The integer view of the value carried by slot `s` of an assignment. -/
def slotInt (a : Assignment) (s : Nat) : Option Int :=
  a[s]?.bind Value.intView

/-- Evaluate an atom on a complete core assignment. `none` means that the
    assignment lacks the slot or carries a value of the wrong type. -/
def Atom.eval (atom : Atom) (assignment : Assignment) : Option Bool :=
  match atom with
  | .boolEq slot expected =>
      match assignment[slot]? with
      | some (.bool actual) => some (actual == expected)
      | _ => none
  | .intLe slot upper =>
      (slotInt assignment slot).map fun actual => decide (actual ≤ upper)

/-- Evaluate a signed literal on a complete assignment. -/
def Literal.eval (literal : Literal) (assignment : Assignment) : Option Bool :=
  literal.atom.eval assignment |>.map fun value =>
    if literal.positive then value else !value

/-- A clause is true when at least one literal is true. -/
def Clause.SatisfiedBy (clause : Clause) (assignment : Assignment) : Prop :=
  ∃ literal ∈ clause, literal.eval assignment = some true

/-- Enter a new decision level. -/
def newDecisionLevel (state : State) : State :=
  { state with decisionLevel := state.decisionLevel + 1 }

/-- Append a decision or propagated literal to the implication trail. -/
def enqueue (state : State) (literal : Literal) (reason : Option Reason) : State :=
  { state with
    trail := state.trail ++ [{ literal, level := state.decisionLevel, reason }] }

/-- Add a learned clause to the active clause database. -/
def learn (state : State) (clause : Clause) : State :=
  { state with learned := clause :: state.learned }

/-- Reference backjump operation on the Boolean trail. Domain restoration is
    added with the integer trail during L0.4. -/
def backjump (state : State) (level : Nat) : State :=
  { state with
    trail := state.trail.filter fun entry => entry.level ≤ level
    decisionLevel := level
    conflict := none }

/-- Conflict analysis: executable first-UIP resolution over `state.trail`
    (see `analyzeTrail` in `solver/LCG/TrailEval.lean`). The learned clause is
    the negated first UIP together with the below-level falsified literals;
    the backjump level is the highest level appearing among them (zero when
    there are none), and `asserting` is the UIP literal. `none` is returned
    when the conflict clause does not resolve to a unique current-level
    literal, which the engine treats as a request for chronological
    backtracking. -/
def analyzeConflict (state : State) : Option ConflictAnalysis :=
  match state.conflict with
  | none => none
  | some conflictClause =>
      match analyzeTrail state.trail state.decisionLevel conflictClause with
      | none => none
      | some (below, uip) =>
          let backjumpLevel :=
            below.foldl (fun acc p => max acc p.2) 0
          let learned := uip.negate :: below.map fun p => p.1
          some { learned, backjumpLevel, asserting := uip.negate }

/-- Result of running one propagator. -/
inductive PropagationResult where
  | stable
  | implied (literal : Literal) (reason : Reason)
  | conflict (reason : Clause)

/-- Constraint propagators report deductions together with explanations that
    the proof layer must show are valid. -/
structure Propagator where
  watches : List Atom
  run : State → PropagationResult

/-- Initial LCG state. -/
def initialState (problem : Problem Constraint Objective) : State :=
  { domains := problem.domains
    trail := []
    decisionLevel := 0
    clauses := problem.clauses
    learned := []
    queue := []
    conflict := none }

end LeanFzn.Solver.LCG
