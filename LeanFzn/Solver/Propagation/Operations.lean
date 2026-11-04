/-
File: LeanFzn/Solver/Propagation/Operations.lean

Purpose:
  Defines proof-free literal evaluation (including the shared integer view
  of values), trail manipulation, clause insertion, propagator results, and
  the propagator interface for the LCG LeanFzn.Solver.

Dependencies:
  - LeanFzn.Solver.Propagation.TrailEval: trail-derived literal evaluation and the
    executable first-UIP conflict analysis backing `analyzeConflict`.

DAG:
  LeanFzn.Solver.Propagation.Types -> LeanFzn.Solver.Propagation.TrailEval -> LeanFzn.Solver.Propagation.Operations
-/

import LeanFzn.Solver.Propagation.TrailEval
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Semantics

/-- Integer view of a value: integers themselves, Booleans as 0/1, and
    nothing for sets and arrays. Declared here (LCG layer) because only
    the order encoding depends on it. -/
def Value.intView : Value → Option Int
  | .int i => some i
  | .bool b => some (if b then 1 else 0)
  | _ => none

end LeanFzn.Semantics

namespace LeanFzn.Solver.Propagation
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
  | .intNe slot value =>
      (slotInt assignment slot).map fun actual => decide (actual ≠ value)

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
    (see `analyzeTrail` in `LeanFzn/Solver/UIP/TrailEval.lean`). The learned clause is
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

/-- Beta-reduction of the `run` projection of a literal propagator. -/
@[simp] theorem Propagator.run_mk {w : List Atom} {r : State → PropagationResult} :
    ({ watches := w, run := r } : Propagator).run = r := rfl

/-- Initial LCG state. -/
def initialState (problem : Problem Constraint Objective) : State :=
  { domains := problem.domains
    trail := []
    decisionLevel := 0
    clauses := problem.clauses
    learned := []
    queue := []
    conflict := none }

/-- Structural membership of an integer in the `Value.intView` image of a
domain: integers as themselves and Booleans as 0/1.  This is *not*
`Dom.memBool d (.int i)`: on a Boolean-valued domain, `i = 0`/`i = 1` must
match `.bool false`/`.bool true`. -/
def memIntViewB (d : Dom) (i : Int) : Bool :=
  match d.rep with
  | .small true _ bits =>
      (i == 0 && bits.toNat.testBit 0) || (i == 1 && bits.toNat.testBit 1)
  | .small false off bits =>
      decide (off ≤ i) && decide (i - off < (64 : Int)) &&
        bits.toNat.testBit (i - off).toNat
  | .holes lo hi hs =>
      decide (lo ≤ i) && decide (i ≤ hi) && !(Dom.memHoles hs i)
  | .general vs => vs.any fun v => Value.intView v == some i

private theorem filterMap_intView_map_int (L : List Int) :
    (L.map Value.int).filterMap Value.intView = L := by
  induction L with
  | nil => rfl
  | cons x xs ih =>
      change x :: (List.map Value.int xs).filterMap Value.intView = x :: xs
      rw [ih]

/-- Exactness of `memIntViewB` against the `Value.intView` image.  Stated
here (next to the definition) so the runtime pool cache below the explained
propagation layer can use it; `ExplainedPropagation.memIntViewB_iff` is the
same statement kept at its historical site. -/
theorem memIntViewB_iff_intView (d : Dom) (i : Int) :
    memIntViewB d i = true ↔ i ∈ (Dom.enum d).filterMap Value.intView := by
  cases d with
  | mk rep =>
    cases rep with
    | small isBool off bits =>
      cases isBool with
      | true =>
          show ((i == 0 && bits.toNat.testBit 0) ||
              (i == 1 && bits.toNat.testBit 1)) = true ↔
            i ∈ (Dom.smallBools bits).filterMap Value.intView
          rw [List.mem_filterMap, Bool.or_eq_true]
          constructor
          · rintro (h | h)
            · rw [Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨hi0, hb0⟩ := h
              refine ⟨.bool false, ?_, ?_⟩
              · rw [Dom.mem_smallBools_bool]; simpa using hb0
              · rw [hi0]; rfl
            · rw [Bool.and_eq_true, beq_iff_eq] at h
              obtain ⟨hi1, hb1⟩ := h
              refine ⟨.bool true, ?_, ?_⟩
              · rw [Dom.mem_smallBools_bool]; simpa using hb1
              · rw [hi1]; rfl
          · rintro ⟨v, hv, hiv⟩
            rw [Dom.mem_smallBools] at hv
            obtain ⟨b, rfl, hb⟩ := hv
            cases b with
            | false =>
                simp only [Value.intView, Bool.false_eq_true, if_false,
                  Option.some.injEq] at hiv
                rw [← hiv]
                have hb' : bits.toNat.testBit 0 = true := by simpa using hb
                simp [hb']
            | true =>
                simp only [Value.intView, if_true, Option.some.injEq] at hiv
                rw [← hiv]
                have hb' : bits.toNat.testBit 1 = true := by simpa using hb
                simp [hb']
      | false =>
          show (decide (off ≤ i) && decide (i - off < (64 : Int)) &&
              bits.toNat.testBit (i - off).toNat) = true ↔
            i ∈ ((Dom.smallInts off bits).map Value.int).filterMap Value.intView
          rw [filterMap_intView_map_int, Dom.mem_smallInts_int]
          rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
          simp [and_assoc]
    | holes lo hi hs =>
      show (decide (lo ≤ i) && decide (i ≤ hi) && !(Dom.memHoles hs i)) = true ↔
        i ∈ ((Dom.holesInts lo hi hs).map Value.int).filterMap Value.intView
      rw [filterMap_intView_map_int, Dom.mem_holesInts]
      rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq]
      rw [Bool.not_eq_true', Dom.memHoles_eq_false]
      simp [and_assoc]
    | general vs =>
      show (vs.any fun v => Value.intView v == some i) = true ↔
        i ∈ vs.filterMap Value.intView
      rw [List.any_eq_true, List.mem_filterMap]
      constructor
      · rintro ⟨v, hv, he⟩
        exact ⟨v, hv, beq_iff_eq.mp he⟩
      · rintro ⟨v, hv, he⟩
        exact ⟨v, hv, beq_iff_eq.mpr he⟩

end LeanFzn.Solver.Propagation
