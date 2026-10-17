/-
File: LeanFzn/Solver/Propagation/ConflictResolution.lean

Purpose:
  The conflict-analysis contract for the explained branch state. This
  module freezes the interface P1.D consumes:

  * `BranchState.toState` — the projection into the historical `State`
    vocabulary, so the executable first-UIP analyzer
    (`analyzeConflict`, proved correct in `Proofs/Transitions.lean`)
    applies to branch states directly;
  * `AnalysisContract` — the semantic obligations of an analysis result:
    global entailment, legal target level, strict descent, conflict
    falsification, and the asserting/unit property after restoration;
  * `ConflictShape` — the classification the plan requires: root
    conflicts, analyzable non-root conflicts, and unsupported
    explanation shapes (empty local explanations are handled by the
    branch-nogood construction, never promoted to global UNSAT);
  * `analysisAllowance` — an input-dependent allowance replacing the
    historical constant `4 * len² + 256` whose insufficiency for long
    clauses is proved in `Proofs/ConflictResolution.lean`.

Dependencies:
  - LeanFzn.Solver.Propagation.BranchState (P1.A): the state record.
  - LeanFzn.Solver.Propagation.ExplainedPropagation (P1.B): the learned-clause and
    reason vocabulary (`LearnedEntailed`, `StepChronology`).

DAG:
  BranchState + ExplainedPropagation -> ConflictResolution
  -> Proofs.ConflictResolution -> BackjumpFrontier (P1.D).
-/

import LeanFzn.Solver.Propagation.BranchState
import LeanFzn.Solver.Propagation.ExplainedPropagation
import LeanFzn.Solver.Propagation.LcgAnalyzer
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## Projection into the historical state vocabulary -/

/-- Project a branch state into the historical `State` record so the
executable analyzer and its theorems apply unchanged. The `conflict`
slot is supplied by the caller (it is an event, not a branch field).

The projected domains are the FULL box in ORIGINAL slot order
(`Frame.domains`, PLAN A1): the singleton domains of the chosen prefix
followed by the remaining domains. Projecting the remaining domains
alone and keeping original slot indices would shift every index past
the prefix. -/
def BranchState.toState (bs : BranchState leaf) (conflict : Option Clause) :
    State where
  domains := Frame.domains bs.frame
  trail := bs.trail
  decisionLevel := bs.level
  clauses := []
  learned := bs.learned
  queue := []
  conflict := conflict

@[simp] theorem BranchState.toState_trail (bs : BranchState leaf)
    (conflict : Option Clause) : (bs.toState conflict).trail = bs.trail := rfl

@[simp] theorem BranchState.toState_level (bs : BranchState leaf)
    (conflict : Option Clause) :
    (bs.toState conflict).decisionLevel = bs.level := rfl

@[simp] theorem BranchState.toState_conflict (bs : BranchState leaf)
    (conflict : Option Clause) :
    (bs.toState conflict).conflict = conflict := rfl

/-- Running the executable analyzer on a branch state with a conflict
clause. -/
def BranchState.analyze (bs : BranchState leaf) (c : Clause) :
    Option ConflictAnalysis :=
  analyzeConflict (bs.toState (some c))

/-! ## The analysis contract -/

/-- The semantic obligations of an analysis result at a branch. Every
field is a separate obligation so P1.D can cite exactly the one it
needs:

* `entailed` — the learned clause is a consequence of the original
  problem (the strongest form: satisfied at every internal solution);
* `level` — the target level never exceeds the branch's level;
* `descends` — at a positive level the target strictly descends (so
  the scheduler makes progress);
* `falsifiedAtConflict` — the learned clause is false at the branch's
  current trail, which is what makes it a *conflict* clause;
* `assertingUnit` — after restoring the target level, exactly the
  asserting literal is not falsified: the clause is unit and would
  enqueue exactly that literal. -/
structure AnalysisContract {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (bs : BranchState leaf) (c : Clause) (an : ConflictAnalysis) : Prop where
  /-- the learned clause is entailed by the internal problem -/
  entailed : Clause.EntailedBy problem constraintHolds an.learned
  /-- the target level is legal -/
  level : an.backjumpLevel ≤ bs.level
  /-- a positive branch level strictly descends -/
  descends : bs.level = 0 ∨ an.backjumpLevel < bs.level
  /-- the learned clause is falsified by the current trail -/
  falsifiedAtConflict : ∀ q ∈ an.learned,
    ∃ e ∈ bs.trail, e.literal = q.negate
  /-- after restoration, every literal other than the asserting one is
      falsified by the surviving trail -/
  assertingUnit : ∀ q ∈ an.learned, q ≠ an.asserting →
    ∃ e ∈ bs.trail, e.level ≤ an.backjumpLevel ∧ e.literal = q.negate
  /-- the asserting literal is the negation of a conflict-level trail
      entry (it names the first UIP) -/
  assertedLevel : ∃ e ∈ bs.trail,
    e.literal = an.asserting.negate ∧ e.level = bs.level

/-! ## Conflict classification

The plan requires distinguishing root conflicts, analyzable non-root
conflicts, and unsupported explanation shapes: an empty local
explanation proves only that the branch is dead, never that the
problem is unsatisfiable. -/

/-- The three shapes a reported conflict can take. -/
inductive ConflictShape where
  /-- a conflict at level 0: the whole problem is unsatisfiable -/
  | root
  /-- a conflict above level 0 with a nonempty analyzable clause -/
  | analyzable
  /-- an empty (or otherwise unanalyzable) local explanation: only the
      branch is excluded, via a branch nogood -/
  | local
  deriving DecidableEq, Repr

/-- Classify a conflict clause at a branch level. -/
def ConflictShape.ofConflict (level : Nat) (c : Clause) : ConflictShape :=
  if c.isEmpty then .local
  else if level = 0 then .root else .analyzable

/-- Only an analyzable clause produces an analysis; root conflicts are
reported directly, and local explanations go to the nogood path. -/
def ConflictShape.analysisInput : ConflictShape → Bool
  | .analyzable => true
  | _ => false

/-! ## The analysis allowance

The historical analyzer ran with the constant `4 * len² + 256`. That
constant cannot cover arbitrary clause lengths (proved in
`Proofs/ConflictResolution.lean`), so the new driver uses an
input-dependent allowance: the conflict clause's length plus the total
length of every trail reason clause, times the trail length, which is
exactly the budget the worklist can consume (each trail entry is
marked at most once, and each mark re-seeds at most one reason
clause). -/

/-- Total literal budget available to the analysis: the conflict
clause plus every reason clause on the trail. -/
def reasonBudget (trail : List TrailEntry) (c : Clause) : Nat :=
  c.length + (trail.map fun e => match e.reason with
    | some r => r.clause.length
    | none => 0).sum

/-- The input-dependent analysis allowance. Supersedes the historical
constant: it depends on the actual clause lengths, so long clauses and
long reasons are not truncated. -/
def analysisAllowance (trail : List TrailEntry) (c : Clause) : Nat :=
  (reasonBudget trail c + 1) * (trail.length + 1) + 1

/-- The historical constant allowance, retained for comparison and as the
floor the computed allowance is taken against. -/
def historicalAllowance (trail : List TrailEntry) : Nat :=
  4 * trail.length * trail.length + 256

/-- Analyze a conflict clause with the LCG analyzer (`LcgAnalyzer.lean`:
root drop, semantic falsifiers, bounded reason falsifiers) over the original
domains `orig`. The loop runs at `analysisFuel`, which is proved sufficient
for EVERY input (`analyzeAtAllowance_complete`, `AnalysisCompletion.lean`),
so a `none` result is always a semantic stop. -/
def analyzeAtAllowance (orig : List Domain) (trail : List TrailEntry) (lvl : Nat)
    (c : Clause) : Option (List (Literal × Nat) × Literal) :=
  analyzeLoop orig trail lvl (analysisFuel trail c) (initAnalysisState c)

/-! ## The analysis record of one run

`ConflictAnalysis.ofRun` is the record the computed-allowance entry
point's witness pair produces: the learned clause is the negated UIP
followed by the below-level falsifiers, the target level is the
fold-max of their levels, and the asserting literal is the negated UIP.

It is DEFINITIONALLY the construction C1 freezes as
`ConflictAnalysis.ofUIP` (`SchedulerState.lean`, downstream of this
module and therefore not nameable here) and the inline record
`BranchState.analyzeWithAllowance` used to build: the two agree by
`rfl`, so a certificate proved for `ofRun` is a certificate for the
scheduler's `ofUIP` record. -/

/-- The `ConflictAnalysis` record of one computed-allowance run. -/
def ConflictAnalysis.ofRun (below : List (Literal × Nat)) (uip : Literal) :
    ConflictAnalysis where
  learned := uip.negate :: below.map fun p => p.1
  backjumpLevel := below.foldl (fun acc p => max acc p.2) 0
  asserting := uip.negate

@[simp] theorem ConflictAnalysis.ofRun_learned
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofRun below uip).learned
      = uip.negate :: below.map fun p => p.1 := rfl

@[simp] theorem ConflictAnalysis.ofRun_backjumpLevel
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofRun below uip).backjumpLevel
      = below.foldl (fun acc p => max acc p.2) 0 := rfl

@[simp] theorem ConflictAnalysis.ofRun_asserting
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofRun below uip).asserting = uip.negate := rfl

/-- CANONICAL FORM of an analysis record: the learned clause's literals
and the asserting literal are stored normalized. `Literal.norm_eval`
makes this SEMANTICALLY identical to the raw record, and it is the form
whose enqueue obligations (asserting-literal membership in the learned
clause) become structurally provable: the raw record's head is the
*unnormalized* negation `uip.negate`, which for Boolean pins is not a
normal form (`(posBool s b).negate.norm = posBool s (!b)`), while the
normalized record's asserting literal is its own normal form.

The transfer lemma `RestorationCertificate.normalized`
(`RestorationCertificate.lean`) lifts every certificate to this form, so
the scheduler may use the canonical record without weakening anything. -/
def ConflictAnalysis.normalized (an : ConflictAnalysis) : ConflictAnalysis where
  learned := an.learned.map Literal.norm
  backjumpLevel := an.backjumpLevel
  asserting := an.asserting.norm

@[simp] theorem ConflictAnalysis.normalized_learned (an : ConflictAnalysis) :
    an.normalized.learned = an.learned.map Literal.norm := rfl

@[simp] theorem ConflictAnalysis.normalized_backjumpLevel
    (an : ConflictAnalysis) : an.normalized.backjumpLevel = an.backjumpLevel := rfl

@[simp] theorem ConflictAnalysis.normalized_asserting (an : ConflictAnalysis) :
    an.normalized.asserting = an.asserting.norm := rfl

/-- The canonical record's asserting literal is normalization-stable: the
structural enqueue obligation `(asserting.norm ∈ learned) = True` is
therefore satisfied by the membership of the record's own head. -/
theorem ConflictAnalysis.normalized_asserting_norm (an : ConflictAnalysis) :
    an.normalized.asserting.norm = an.normalized.asserting :=
  norm_norm an.asserting

/-- The canonical form of the allowance run's record. -/
def ConflictAnalysis.ofRunNormalized (below : List (Literal × Nat))
    (uip : Literal) : ConflictAnalysis :=
  (ConflictAnalysis.ofRun below uip).normalized

@[simp] theorem ConflictAnalysis.ofRunNormalized_asserting
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofRunNormalized below uip).asserting
      = (uip.negate).norm := rfl

@[simp] theorem ConflictAnalysis.ofRunNormalized_backjumpLevel
    (below : List (Literal × Nat)) (uip : Literal) :
    (ConflictAnalysis.ofRunNormalized below uip).backjumpLevel
      = below.foldl (fun acc p => max acc p.2) 0 := rfl

/-- Analyze with the input-dependent allowance: the analysis is run at
`analysisFuel`, not at the historical constant, so long clauses and long
reason clauses are not truncated. -/
def BranchState.analyzeWithAllowance (orig : List Domain) (bs : BranchState leaf)
    (c : Clause) : Option ConflictAnalysis :=
  (analyzeAtAllowance orig bs.trail bs.level c).map
    (fun p => ConflictAnalysis.ofRun p.1 p.2)

/-- The allowance run's record is what `analyzeWithAllowance` returns. -/
theorem BranchState.analyzeWithAllowance_eq_map_ofRun (orig : List Domain)
    (bs : BranchState leaf) (c : Clause) :
    bs.analyzeWithAllowance orig c =
      (analyzeAtAllowance orig bs.trail bs.level c).map
        (fun p => ConflictAnalysis.ofRun p.1 p.2) := rfl

end LeanFzn.Solver.Propagation
