/-
File: LeanFzn/Solver/Propagation/BranchState.lean

Purpose:
  Freeze the branch-state vocabulary shared by the first-UIP work
  packages: an analysis-ready branch couples the finite-domain frame of
  the active driver (`BranchFrame` from `Frontier.lean`) with a
  chronological explanation trail (`Types.lean`'s `TrailEntry`), and a
  representation relation connects such a state to the complete
  assignments the frontier machinery already reasons about
  (`FrameCovers` from `FrontierSemantics.lean`).

  This module owns ONLY the frozen interfaces:
    * `BranchState`            — the state record;
    * `BranchState.Represents` — the coverage relation to complete
                                  assignments;
    * `BranchState.init`, `BranchState.decide`,
      `BranchState.recordImplied`, `BranchState.learnGlobal` — the
                                  transition vocabulary;
    * `BranchState.WellFormed` — the structural invariant every
                                  transition preserves;
    * transition-contract theorems with the exact missing hypotheses
      stated as premises (see `Proofs/BranchState.lean`).

Dependencies:
  - LeanFzn.Solver.Propagation.FrontierSemantics: `BranchFrame`, `FrameCovers`.
  - LeanFzn.Solver.Propagation.Invariants: trail/representation vocabulary that the
    Boolean layer already uses (`State.Represents`), imported through
    `Operations`.

DAG:
  FrontierSemantics + Operations (-> Invariants) -> BranchState
  -> ExplainedPropagation (P1.B) -> ConflictResolution (P1.C)
  -> BackjumpFrontier (P1.D).
  `BranchState` deliberately does NOT import `DomPruning` (which must
  stay downstream of `Search` to avoid its existing proof cycle).
-/

import LeanFzn.Solver.Propagation.FrontierSemantics
import LeanFzn.Solver.Propagation.Invariants
open LeanFzn.Semantics LeanFzn.Solver.Propagation



namespace LeanFzn.Solver.Propagation
open LeanFzn.Solver.Core

/-! ## The branch state -/

/-- An analysis-ready branch: the finite-domain frame of the active
`prunedSolve` driver, the chronological explanation trail over it, and
the global learned-clause database (shared across branches; every
member must be globally entailed — see `LearnedEntailed`).

Design notes (PLAN P1.A item 1):

* The frame carries the *domains and chosen prefix* exactly as the
  active driver sees them; the trail is a chronological record of why
  each narrowing happened, not a second domain representation.
* Decisions are trail entries with `reason = none`; propagated
  deductions carry their entailed reason clause.
* Learned clauses are GLOBAL state (they survive backjumps and sibling
  branches); the frame and trail are PER-BRANCH state restored by
  backtracking to a saved prefix. -/
structure BranchState (leaf : Assignment → Bool) where
  /-- Finite-domain frame: remaining domains and chosen prefix. -/
  frame : BranchFrame
  /-- Chronological explanation trail; later entries are later in the
      list (append order = time order). -/
  trail : List TrailEntry
  /-- Current decision level of this branch. -/
  level : Nat
  /-- Globally entailed learned clauses, shared across branches. -/
  learned : List Clause
  deriving Repr

/-! ## The representation relation -/

/-- A complete assignment is represented by a branch state when it is
covered by the frame, satisfies the trail, and satisfies every learned
clause. This is the frame-level analogue of `State.Represents` from
`Invariants.lean`, reusing `FrameCovers` rather than introducing an
unrelated completeness notion (PLAN P1.A item 2). -/
def BranchState.Represents (bs : BranchState leaf) (a : Assignment) : Prop :=
  FrameCovers bs.frame a ∧
    (∀ e ∈ bs.trail, e.literal.eval a = some true) ∧
    (∀ c ∈ bs.learned, c.SatisfiedBy a)

/-- Every learned clause is globally entailed by the problem's leaf
semantics (the frame-level analogue of `Clause.EntailedBy` with the
leaf playing the role of the internal problem's solution test). -/
def LearnedEntailed (leaf : Assignment → Bool) (db : List Clause) : Prop :=
  ∀ c ∈ db, ∀ a, leaf a = true → c.SatisfiedBy a

/-! ## Duplicate-safe trail discipline (A1)

`TrailLiteralsDistinct` lives here (moved from
`LeanFzn/Solver/UIP/RestorationCertificate.lean`) because `ReachableState`
(`Proofs/BranchState.lean`) carries it as its eighth field: every
consumer can cite `hreach.distinct` instead of taking a caller-supplied
distinctness hypothesis (INTERFACES.md §2.1 FORM 1).

POLICY (the duplicate/forced-decision case). A decision that pins a
literal an earlier trail entry already records — deciding a value whose
head remaining domain is a singleton — would duplicate an entry and
destroy the property; the same holds for an enqueue of an already
recorded deduction. `ReachableState` therefore records the discipline as
an invariant, and the concrete decision/enqueue transitions must supply
it: `reachable_decide` takes an explicit branching-pin freshness premise
(`TrailLiteralsDistinct.decide_duplicates` shows the premise is
necessary), and the narrowing path instantiates
`TrailLiteralsDistinct.append_singleton` (exported by A1 in
`Proofs/BranchState.lean`). -/

/-- Trail literals occur at most once, up to normalization. The two halves
are used differently: the first identifies a lookup result with the
chronology witness (the restoration certificate's conjuncts), and the
second forbids a repeated ENTRY, which is what makes `earlierThan`
irreflexive and hence kills the analyzer's re-marking of a consumed
pivot (B1). -/
def TrailLiteralsDistinct (trail : List TrailEntry) : Prop :=
  (∀ (e : TrailEntry), e ∈ trail → ∀ (e₂ : TrailEntry), e₂ ∈ trail →
    e₂.literal = e.literal.norm → e₂ = e) ∧ List.Nodup trail

/-! ## Trail falsification (A1) -/

/-- Every literal of `c` is the negation of a recorded trail literal.
This is the exact shape `analyzerInput_of_conflict` consumes: the
`falsified` field of `AnalyzerInput`. It is the same proposition the
conflict-resolution layer calls `TrailFalsifies` (`Proofs/ConflictResolution.lean`,
which B2 aliases to this definition). -/
def FalsifiedByTrail (bs : BranchState leaf) (c : Clause) : Prop :=
  ∀ q ∈ c, ∃ e ∈ bs.trail, e.literal = q.negate

/-! ## Chronology -/

/-- `e'` appears strictly before `e` on the trail (append order =
    chronological order). -/
def TrailEntry.earlierThan (trail : List TrailEntry) (e' e : TrailEntry) : Prop :=
  ∃ i j : Nat, ∃ _hi : i < trail.length, ∃ _hj : j < trail.length,
    trail[i]'_hi = e' ∧ trail[j]'_hj = e ∧ i < j

/-! ## The structural invariant -/

/-- Helper: the canonical positive literal for a Boolean slot. -/
def Literal.boolOfSlot (slot : Nat) (b : Bool) : Literal :=
  { atom := .boolEq slot b, positive := true }

/-- Structural well-formedness of a branch state: trail levels are
bounded, trail literals are normalized, reasons are entailed and have
their pivot as a member, non-pivot reason literals have strictly
earlier falsifiers on the trail (chronology), and the learned database
is globally entailed. This is the branch-level counterpart of
`RunInv`/`AnalysisReady` specialized to the frame driver. -/
def BranchState.WellFormed (bs : BranchState leaf) : Prop :=
  (∀ e ∈ bs.trail, e.level ≤ bs.level) ∧
    (∀ e ∈ bs.trail, e.literal = e.literal.norm) ∧
    (∀ e ∈ bs.trail, ∀ r ∈ e.reason,
      LearnedEntailed leaf [r.clause] ∧ (e.literal ∈ r.clause) = True) ∧
    (∀ e ∈ bs.trail, ∀ r ∈ e.reason, ∀ l ∈ r.clause, l ≠ e.literal →
      ∃ e' ∈ bs.trail, e'.literal = l.negate ∧
        TrailEntry.earlierThan bs.trail e' e) ∧
    LearnedEntailed leaf bs.learned

/-! ## Transition vocabulary -/

/-- Initialize the branch state at the root: the whole original
frontier frame, empty trail, level zero, empty learned database. -/
def BranchState.init (f : BranchFrame) : BranchState leaf where
  frame := f
  trail := []
  level := 0
  learned := []

/-- Enter a fresh decision level and record a decision literal. The
decision gets `reason = none`; a decision is any normalized literal
whose assertion keeps the branch representable (see
`BranchState.decide_preserves`). -/
def BranchState.decide (bs : BranchState leaf) (l : Literal) :
    BranchState leaf :=
  { bs with
    trail := bs.trail ++ [{ literal := l.norm, level := bs.level + 1,
                             reason := none }]
    level := bs.level + 1 }

/-- Record a propagation deduction at the current level with its
entailed reason clause. The literal is normalized on the trail; the
frame itself is narrowed separately by the propagation layer
(P1.B's `ExplainedPropagation`), which keeps this operation purely
additive to the trail. -/
def BranchState.recordImplied (bs : BranchState leaf)
    (l : Literal) (r : Reason) : BranchState leaf :=
  { bs with
    trail := bs.trail ++ [{ literal := l.norm, level := bs.level,
                             reason := some r }] }

/-- Add a globally entailed clause to the shared learned database. -/
def BranchState.learnGlobal (bs : BranchState leaf) (c : Clause) :
    BranchState leaf :=
  { bs with learned := c :: bs.learned }

/-- Restore a branch to the state it had at the target decision level:
keep exactly the trail entries at or below the level, drop the
decision that opened the level, and set the level back. The frame is
restored by the P1.D scheduler; this projection only repairs the
trail/level components. -/
def BranchState.restoreLevel (bs : BranchState leaf) (target : Nat) :
    BranchState leaf :=
  { bs with
    trail := bs.trail.filter fun e => e.level ≤ target
    level := target }

/-! ## Boolean pin hygiene -/

/-- The executable gate describing that a Boolean pin decision is a
filtering operation: the pinned literal must be normalized (Boolean
facts stored positively, see `TrailEval.lean`'s `Literal.norm`). Used
by P1.B to justify pins without `domOfLit`'s unrestricted singleton
overwrite. -/
def BranchState.pinLiteral (slot : Nat) (b : Bool) : Literal :=
  (Literal.boolOfSlot slot b).norm

end LeanFzn.Solver.Propagation
