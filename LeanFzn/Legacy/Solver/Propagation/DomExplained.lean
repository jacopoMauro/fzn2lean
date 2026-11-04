/-
File: LeanFzn/Solver/Propagation/DomExplained.lean

Purpose:
  The CONCRETE domain kit for the supported fragment of the explained
  closure (INTERFACES §2.2, §2.8; PLAN A3). This module owns the
  vocabulary A3 proves facts about:

  * `unitFamilyB` — the executable classification of the supported
    propagator fragment (the unit-explanation constant families
    `leConstHi`, `leConstLo`, `ltConstHi`, `ltConstLo`, `constEq`);
  * `UnitLearned` — the learned-database discipline of the supported
    fragment: every learned clause is a normalized unit clause. For such
    databases the per-state explanation obligations are VACUOUS, so the
    concrete kit needs no caller-supplied evidence functions;
  * `LearnedExplained` — the per-state content of A2's
    `UnitClauseEvidence` (unit-literal membership + recorded falsifiers);
    `UnitLearned` IMPLIES it (proofs in `Proofs/DomExplained.lean`);
  * `DomReachable` — A3's supported state class (coherent reachable
    branch + explained learned database);
  * `classifyConflict` / `DomConflictEvidence` — the root/analyzable/local
    classification (I0 §2.8) and its sound per-shape payload.

  No declaration here asserts anything about concrete inputs; the
  proofs live in `LeanFzn/Solver/UIP/Proofs/DomExplained.lean`.

Dependencies:
  - LeanFzn.Solver.Propagation.ExplainedPropagation: `ClosureContract`, `clauseRemaining`,
    `DomReasonRecorded`, `ReachableState` (through Proofs.BranchState).
  - LeanFzn.Solver.Propagation.ConflictResolution: `ConflictShape`.

DAG:
  BranchState + ExplainedPropagation + ConflictResolution
    -> DomExplained (this file) -> Proofs.DomExplained -> A3 consumers
    (B2 / C2 / D1) and no module below this file.

Ownership: task A3. The import lines the coordinator must queue:

    import LeanFzn.Legacy.Solver.Propagation.DomExplained
    import LeanFzn.Legacy.Solver.UIP.Proofs.DomExplained
-/

import LeanFzn.Legacy.Solver.Propagation.ExplainedPropagation
import LeanFzn.Legacy.Solver.Propagation.ConflictResolution
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core

/-! ## The supported propagator fragment -/

/-- The SUPPORTED propagator fragment: the constant-bound and
constant-equality families, whose explanation clauses are single
normalized literals (`propLeConstHi`, `propLeConstLo`, `propLtConstHi`,
`propLtConstLo`, `propConstEq`). Every other registered family is
explicitly UNSUPPORTED by this kit and keeps the sound local fallback
(`DomConflictEvidence.excluded` / `StepContract.conflictExcludes`); see
`Proofs/DomExplained.lean`. -/
def unitFamilyB : DomConstraint → Bool
  | .leConstHi _ _ => true
  | .leConstLo _ _ => true
  | .ltConstHi _ _ => true
  | .ltConstLo _ _ => true
  | .constEq _ _ => true
  | _ => false

/-- The executable supported-problem gate: every constraint of the
problem belongs to the supported fragment. -/
def domSupportedB (problem : Problem DomConstraint Unit) : Bool :=
  problem.constraints.all unitFamilyB

/-! ## Learned-database hygiene of the supported fragment -/

/-- The learned databases of the supported fragment: every clause is a
NORMALIZED UNIT clause. The explained closure's own learning produces
exactly such clauses when the propagator kit is the supported fragment
(`explainedClosure` learns the reason clauses of `.implied` events and
never learns on `.conflict` events). -/
def UnitLearned (db : List Clause) : Prop :=
  ∀ c ∈ db, ∃ q : Literal, c = [q] ∧ q = q.norm

/-- The behavioral profile of the supported propagator kit, as the
maintenance proofs consume it: every implied explanation is a normalized
unit clause, and every conflict explanation is empty or a normalized unit
clause. `propagatorEvidence_unit` proves this profile for the concrete
registration `dcs.filterMap propagatorOfProved` with all constraints in
the supported fragment. -/
def UnitRunProfile (props : List Propagator) : Prop :=
  (∀ p ∈ props, ∀ st l r, p.run st = .implied l r →
    ∃ q : Literal, r.clause = [q] ∧ q = q.norm) ∧
  (∀ p ∈ props, ∀ st c, p.run st = .conflict c →
    c = [] ∨ ∃ q : Literal, c = [q] ∧ q = q.norm)

/-- The per-state content of A2's `UnitClauseEvidence`: every learned
clause that is unit in the current frame has a normalized unit literal
and recorded falsifiers for its other literals. This is the discipline
the concrete kit maintains; `UnitLearned` implies it vacuously. -/
def LearnedExplained (leaf : Assignment → Bool) (bs : BranchState leaf) : Prop :=
  ∀ c ∈ bs.learned, ∀ l, clauseRemaining bs.frame c = [l] →
    (l.norm ∈ c) = True ∧ DomReasonRecorded leaf bs l c

/-- A3's supported state class: a coherent reachable branch whose learned
database is explained. The `ReachableState` half is A1/A2's frozen
invariant; the second half is the learned-database discipline this kit
supplies and maintains. -/
def DomReachable (leaf : Assignment → Bool) (orig : List Domain)
    (bs : BranchState leaf) : Prop :=
  ReachableState leaf orig bs ∧ LearnedExplained leaf bs

/-! ## E1 — learned-clause provenance (PLAN E1)

The broad discipline premise (`∀ bs, ReachableState leaf orig bs →
LearnedExplained leaf bs`, the `hDisc` argument of
`domExplainedContract_of_problem`) quantifies over states the driver
never visits and is not stable under the transitions: a narrowing can
make an arbitrary multi-literal learned clause unit for the first time.
E1 replaces it with `LearnedProvenance`, the provenance of the ACTUAL
insertion events: every clause ever added to the learned database
carries `ClauseProvenance`, i.e. SOME recorded pivot literal
(`RecordedWith`): the pivot is normalized, is a member of the clause,
and every other member's exact negation is recorded on the trail. The
invariant is inhabited at the root, preserved by globally entailed
insertion, narrowing and the restoration operations of
`RestorationCertificate` (see
`LeanFzn/Solver/UIP/Proofs/LearnedExplanation.lean`), and it is exactly what the
database scan consumes: `recordedWith_stepChronology` derives normalized
pivot membership and the chronological falsifiers of a unit shape whose
remaining literal is a recorded pivot. Both predicates are `Prop` (the
pivot is existentially quantified) so the transition proofs can
case-split on the Prop-valued database memberships. -/

/-- Provenance of ONE learned clause at a NAMED pivot: the clause was
introduced as the reason of a recorded deduction whose entry literal
(normalized) is `p`, `p` is a clause member, and every other member's
exact negation is recorded on the trail. -/
def RecordedWith (leaf : Assignment → Bool) (bs : BranchState leaf)
    (c : Clause) (p : Literal) : Prop :=
  p = p.norm ∧ (p ∈ c) = True ∧
    ∀ q ∈ c, q ≠ p → q.negate ∈ bs.trail.map TrailEntry.literal

/-- The provenance of a learned clause: SOME pivot recorded it. The
existential keeps this in `Prop` (so it can be eliminated into the
proof cases of the transition lemmas, unlike a data-carrying structure);
consumers destructure the witness and use `RecordedWith`'s content. -/
def ClauseProvenance (leaf : Assignment → Bool) (bs : BranchState leaf)
    (c : Clause) : Prop :=
  ∃ p : Literal, RecordedWith leaf bs c p

/-- E1's invariant of actual reachable execution: every clause in the
learned database carries its insertion provenance. Replaces the broad
`LearnedExplained` premise; the preservation lemmas live in
`LeanFzn/Solver/UIP/Proofs/LearnedExplanation.lean`. -/
def LearnedProvenance (leaf : Assignment → Bool) (bs : BranchState leaf) : Prop :=
  ∀ c ∈ bs.learned, ClauseProvenance leaf bs c

/-- **UNIT-CLAUSE PROVENANCE IS VACUOUS** (P1 `hprov` endgame): a
normalized unit clause has provenance in ANY branch state — the pivot is
the literal itself, the membership holds by construction, and the
co-member conjunct is vacuous. This is why a UNIT learned fragment's
`LearnedProvenance` survives every trail truncation (consume/jump
restoration), unlike multi-literal clauses whose pivots need recorded
falsifiers. -/
theorem unit_clause_provenance {leaf : Assignment → Bool}
    {bs : BranchState leaf} {q : Literal} (h : q = q.norm) :
    ClauseProvenance leaf bs [q] :=
  ⟨q, h, by simp, by
    intro q' hq' hne
    simp at hq'
    exact absurd hq' hne⟩

/-! ## Conflict classification (I0 §2.8) -/

/-- Classify one selected conflict event (`nextPruningEvent` =
`.conflict cs`) with the frozen `ConflictShape` vocabulary: an empty
payload (database refutation or empty propagator explanation) is
`.local`; otherwise the first named clause decides root vs. analyzable
by the branch level. -/
def classifyConflict (level : Nat) (cs : List Clause) : ConflictShape :=
  match cs with
  | [] => .local
  | c :: _ => ConflictShape.ofConflict level c

/-- The sound payload of one classified conflict event:

  * `excluded` — every leaf solution the branch REPRESENTS is excluded
    (the branch-relative statement; it is NEVER a global claim);
  * `entailed` — the reported clauses are globally entailed (vacuous for
    the `.local` empty payload);
  * `shape_eq` — the shape is the classification of the actual event.

  A global UNSAT verdict requires the ROOT configuration and the
  leaf-covers-the-root-frame bridge (proved in `Proofs/DomExplained.lean`
  as `rootConflict_excludes_all`), not merely `.root` of a classification.

  The structure lives in `Type` because it carries the classified SHAPE as
  data (a `Prop`-valued structure may only carry proofs); its proof fields
  are the two soundness obligations. -/
structure DomConflictEvidence (leaf : Assignment → Bool)
    (bs : BranchState leaf) (cs : List Clause) where
  shape : ConflictShape
  shape_eq : shape = classifyConflict bs.level cs
  excluded : ∀ a, leaf a = true → bs.Represents a → False
  entailed : LearnedEntailed leaf cs

end LeanFzn.Solver.Propagation
