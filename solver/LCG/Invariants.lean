/-
File: solver/LCG/Invariants.lean

Purpose:
  Defines the semantic meaning and invariants of LCG clauses, trails,
  explanations, learned clauses, and conflicts.

Dependencies:
  - solver.LCG.Operations: executable LCG operations.

DAG:
  solver.LCG.Operations -> solver.LCG.Invariants -> LCG proof modules
-/

import solver.LCG.Operations

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core

/-- Internal solutions of a common problem under a supplied constraint
    semantics. -/
def ProblemSolution (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (assignment : Assignment) : Prop :=
  assignment.Fits problem.domains ∧
    ∀ constraint ∈ problem.constraints, constraintHolds constraint assignment

/-- A clause is globally entailed when every internal problem solution
    satisfies it. -/
def Clause.EntailedBy (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop) (clause : Clause) : Prop :=
  ∀ assignment, ProblemSolution problem constraintHolds assignment →
    clause.SatisfiedBy assignment

/-- A complete assignment agrees with every literal currently on the trail. -/
def State.TrailSatisfied (state : State) (assignment : Assignment) : Prop :=
  ∀ entry ∈ state.trail, entry.literal.eval assignment = some true

/-- Logical assignments represented by an LCG state. -/
def State.Represents (state : State) (assignment : Assignment) : Prop :=
  assignment.Fits state.domains ∧ state.TrailSatisfied assignment ∧
    (∀ clause ∈ state.clauses, clause.SatisfiedBy assignment) ∧
    (∀ clause ∈ state.learned, clause.SatisfiedBy assignment)

/-- Structural and semantic invariant expected at every reachable LCG state. -/
def State.WellFormed (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop) (state : State) : Prop :=
  state.domains.length = problem.domains.length ∧
    (∀ entry ∈ state.trail, entry.level ≤ state.decisionLevel) ∧
    (∀ clause ∈ state.learned, clause.EntailedBy problem constraintHolds)

/-- A conflict is sound when no represented internal solution exists. -/
def State.SoundConflict (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop) (state : State) : Prop :=
  state.conflict.isSome →
    ¬ ∃ assignment, ProblemSolution problem constraintHolds assignment ∧
      state.Represents assignment

/-! ## Reason validity and analysis readiness

The analyzer consumes trail reasons. Their soundness is not implied by
`analyzeConflict state = some analysis` alone (PLAN.md L0.4, steps 2–3):
the semantic content of every reason — global entailment, the propagated
pivot, applicability to earlier trail entries, and strict chronology —
must be an invariant of reachable states, so the analyzer's assumptions
come from reachability rather than being postulated at the call site. -/

/-- The reason attached to a trail entry is valid when its clause is
    entailed by the internal problem and its pivot is the entry's own
    literal. (Applicability and chronology are carried separately by
    `TrailEntry.Chronological`.) -/
def Reason.Valid {Constraint : Type} (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (reason : Reason) (pivot : Literal) : Prop :=
  reason.clause.EntailedBy problem constraintHolds ∧
    (decide (pivot ∈ reason.clause) = true)

/-- Strict trail chronology: if the entry carries a reason, every clause
    literal other than the pivot is falsified by an earlier entry on the
    given trail. -/
def TrailEntry.Chronological (trail : List TrailEntry) (entry : TrailEntry) :
    Prop :=
  ∀ (r : Reason), r ∈ entry.reason →
    ∀ l ∈ r.clause, l ≠ entry.literal →
      ∃ i : Nat, ∃ hlt : i < trail.length,
        (trail[i]'hlt).literal = l.negate

/-- Bounded existential variant: purely positional, used by
    reachability proofs. -/
def TrailEntry.ChronologicalAt (trail : List TrailEntry) (pos : Nat)
    (entry : TrailEntry) : Prop :=
  pos < trail.length ∧
    ∀ (r : Reason), r ∈ entry.reason →
      ∀ l ∈ r.clause, l ≠ entry.literal →
        ∃ i : Nat, ∃ hlt : i < trail.length,
          (trail[i]'hlt).literal = l.negate ∧ i < pos

/-- Root-level trail facts are semantically unconditional: an entry
    enqueued at level zero (domain/Boolean facts established before any
    decision) is true in every internal problem solution. The analyzer
    relies on this when it drops a literal falsified only by a root
    entry: such a literal can never be the satisfying witness of a
    solution, so discarding it preserves entailment. -/
def RootFacts (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop)
    (trail : List TrailEntry) : Prop :=
  ∀ e ∈ trail, e.level = 0 →
    ∀ a, ProblemSolution problem constraintHolds a →
      e.literal.eval a = some true

/-- The conflict analysis precondition bundle: the state's conflict is
    an entailed clause, every trail reason is valid for its pivot, the
    trail is chronologically consistent, and root-level entries are true
    in every internal solution. This is the reachability invariant L0.4
    steps 2–3 must establish via transition preservation. Membership
    over `Option` uses `Option.mem`. -/
def State.AnalysisReady (problem : Problem Constraint Objective)
    (constraintHolds : Constraint → Assignment → Prop) (state : State) :
    Prop :=
  (∀ cc ∈ state.conflict, cc.EntailedBy problem constraintHolds) ∧
    (∀ e ∈ state.trail, ∀ r ∈ e.reason, Reason.Valid problem
      constraintHolds r e.literal) ∧
    RootFacts problem constraintHolds state.trail ∧
    -- reachability premise: reason clauses contain only normalized
    -- literals (the engine builds explanations from trail facts and
    -- order literals, both normalized); required for the resolution
    -- branch's degenerate corner (raw l with l.norm = pivot)
    (∀ e ∈ state.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l = l.norm)

end LeanFzn.Solver.LCG
