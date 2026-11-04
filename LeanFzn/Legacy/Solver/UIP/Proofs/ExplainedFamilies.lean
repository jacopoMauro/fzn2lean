/-
File: LeanFzn/Solver/UIP/Proofs/ExplainedFamilies.lean

Purpose:
  Concrete explanation evidence for the propagator families BEYOND the
  five unit families of `Proofs/DomExplained.lean`, plus the published
  FAMILY MATRIX (route per registered family, with the evidence or the
  fallback soundness named).

  THE FAMILY MATRIX (families of `propagatorOfProved`,
  `LeanFzn/Solver/UIP/Proofs/Propagators.lean`):

  | family        | route                          | evidence / fallback theorem | file |
  |---------------|--------------------------------|------------------------------|------|
  | leConstHi     | explained deduction (unit)     | `unitEvidence_leConstHi`, `propagatorEvidence_unit` | Proofs/DomExplained.lean |
  | leConstLo     | explained deduction (unit)     | `unitEvidence_leConstLo`     | Proofs/DomExplained.lean |
  | ltConstHi     | explained deduction (unit)     | `unitEvidence_ltConstHi`     | Proofs/DomExplained.lean |
  | ltConstLo     | explained deduction (unit)     | `unitEvidence_ltConstLo`     | Proofs/DomExplained.lean |
  | constEq       | explained deduction (unit)     | `unitEvidence_constEqInt/Bool/Set/Array` | Proofs/DomExplained.lean |
  | boolNotSlot   | explained deduction (non-unit) | `explains_boolNotSlot`       | this file |
  | boolAndSlot   | explained deduction (non-unit) | `explains_boolAndSlot`       | this file |
  | boolOrSlot    | explained deduction (non-unit) | `explains_boolOrSlot`        | this file |
  | neSlot        | explained CONFLICT (both sides pinned to one value → `[x≠c, y≠c]` / `[x=¬b, y=¬b]`); value-removal implication stays the proved local fallback | `propNe_conflict_falsified`, `propNe_conflict_entailed` | Proofs/Propagators.lean |
  | leSlot, ltSlot, eqSlot, plusSlot, linLe, linEq, timesSlot, minSlot, maxSlot, absSlot | proved local fallback (explained route deferred) | `propagatorsOfProved_safeUniv`, `propagatorsOfProved_entitled`, `DomConflictEvidence.excluded` | Proofs/Propagators.lean, LCG/DomExplained.lean |
  | allDiff       | explained conflict (Hall clause payload → `.analyzable`/`.root`, PLAN U1b) + explained value ELIMINATIONS (PLAN L8: a fixed slot's value is removed from the other slots, reason `allDiffElimClause`) | `propAllDiffLCG_conflict_falsified`, `propAllDiffLCG_conflict_entailed`, `propAllDiffLCG_conflict_nofit`, `propAllDiffLCG_implied_inv`, `propAllDiffLCG_sem` | Proofs/Fam/AllDiff.lean, LcgFamiliesAllDiff.lean |

  Deferred rows: the 11 deferred families still carry per-family
  REASON-VALIDITY theorems in their `Fam/*` modules
  (`propLinLe2_reason_valid`, `propLinEq2_reason_valid`,
  `propTimes_reason_valid`, `propMin_reason_valid` / `propMax` /
  `propAbs`, the `propBool*_reason_safe` family, `propNe_implied_inv`,
  ...), so their STRONGER explained route is available; this module does
  NOT claim the E2 pivot/range/falsifier derivation for them and the
  matrix routes them through the PROVED LOCAL FALLBACK whose soundness
  is the two named front-door theorems (`propagatorsOfProved_safeUniv`,
  `propagatorsOfProved_entitled`) plus A3's branch-local
  `DomConflictEvidence.excluded`. No source family loses a sound
  complete route.

  For the three Boolean rows this module DERIVES, from the actual `run`
  equations (the emit inversions), all of:
  * `reason_norm` — the explanation clause is normalized;
  * `pivot_mem` — the normalized pivot is a clause member;
  * `slot_range` — the pivot names an in-range slot of the box the run
    read (the `UnitEvidence`/`PropagatorEvidence` frame form);
  * `falsifier_pin` — every non-pivot literal asserts the OPPOSITE of a
    Boolean pin the run read, hence is false at every fitting assignment
    (`posBool_pin_falsified`, `boolean_falsified`): the order-upgrade
    falsifier content derivable from the runtime result alone.

  NON-UNITNESS is witnessed by the concrete public fixtures (the
  instances are stated at arbitrary parameters `i, j, k`, so the
  witness lives at concrete parameter values):
  `boolAnd_nonunit_reason_fixture` (THREE literals),
  `boolNot_sparse_emit` and `boolOr2_nonunit_emit` (TWO literals).

  Fixtures: sparse domains, negative bounds and Boolean/int separation
  are concrete `example`s (kernel reduction, no `native_decide`);
  `boolAnd_nonunit_reason_fixture` is the required non-unit conditional
  reason (THREE literals) with its falsifiers frame-dead.

Dependencies:
  - LeanFzn.Solver.UIP.Proofs.DomExplained: `valueMemB_ne_nil`,
    `getD_ne_nil_lt`, `slot_lt_frameState`.
  - LeanFzn.Solver.Propagation.Proofs.Fam.Bool: `implyBool` + inversions, pin lemmas,
    `posBool2_norm` / `posBool3_norm`, `posBool_norm`.

DAG:
  Proofs.DomExplained + Proofs.Fam.Bool -> Proofs.ExplainedFamilies
    -> (E3 / C2a consumers). No runtime module imports this one.

Import line for the coordinator to register:

    import LeanFzn.Legacy.Solver.UIP.Proofs.ExplainedFamilies
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.DomExplained
import LeanFzn.Solver.Propagation.Proofs.Fam.Bool
import LeanFzn.Legacy.Solver.Propagation.Proofs.Fam.AllDiff
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler

/-! ## The route taxonomy and the executable matrix -/

/-- The route of one registered propagator family (PLAN E2):
    `explainedDeduction` — the family's implied explanations carry the
    derived pivot/range/falsifier evidence; `analyzableConflict` — the
    family reports a non-empty derived conflict clause classified by
    `classifyConflict` (I0 §2.8, materialized by A3's
    `conflictEvidence_at`); `localFallback` — the family keeps the
    proved branch-local exclusion route only. -/
inductive FamilyRoute where
  | explainedDeduction
  | analyzableConflict
  | localFallback
  deriving DecidableEq, Repr

/-- The executable family matrix. The `explainedDeduction` rows are
    the five unit families (A3, `Proofs/DomExplained.lean`) and the
    three Boolean families (this file). Every other registered family
    keeps the proved local fallback (see the header table). -/
def familyRoute : DomConstraint → FamilyRoute
  | .leConstHi _ _ => .explainedDeduction
  | .leConstLo _ _ => .explainedDeduction
  | .ltConstHi _ _ => .explainedDeduction
  | .ltConstLo _ _ => .explainedDeduction
  | .constEq _ _ => .explainedDeduction
  | .boolNotSlot _ _ => .explainedDeduction
  | .boolAndSlot _ _ _ => .explainedDeduction
  | .boolOrSlot _ _ _ => .explainedDeduction
  | .leSlot _ _ => .localFallback
  | .ltSlot _ _ => .localFallback
  | .eqSlot _ _ => .localFallback
  | .neSlot _ _ => .localFallback
  | .boolClauseSlot _ _ => .localFallback
  | .arrayBoolAndSlot _ _ => .localFallback
  | .bool2intSlot _ _ => .localFallback
  | .boolEqSlot _ _ => .localFallback
  | .arrayIntElementSlot _ _ _ => .localFallback
  | .arrayVarIntElementSlot _ _ _ => .localFallback
  | .arrayVarBoolElementSlot _ _ _ => .localFallback
  | .eqReifSlot _ _ _ => .localFallback
  | .leReifSlot _ _ _ => .localFallback
  | .neReifSlot _ _ _ => .localFallback
  | .linEqReif _ _ _ _ => .localFallback
  | .linLeReif _ _ _ _ => .localFallback
  | .linNeReif _ _ _ _ => .localFallback
  | .plusSlot _ _ _ => .localFallback
  | .linLe _ _ _ => .localFallback
  | .linEq _ _ _ => .localFallback
  | .linNe _ _ _ => .localFallback
  | .timesSlot _ _ _ => .localFallback
  | .minSlot _ _ _ => .localFallback
  | .maxSlot _ _ _ => .localFallback
  | .absSlot _ _ => .localFallback
  | .allDiff _ => .localFallback
  | .minPair _ _ _ => .localFallback
  | .maxPair _ _ _ => .localFallback
  | .divGen _ _ _ => .localFallback
  | .modGen _ _ _ => .localFallback
  | .maxGen _ _ => .localFallback
  | .minGen _ _ => .localFallback
  | .setInSlot _ _ => .localFallback
  | .setInReifSlot _ _ _ => .localFallback

example : familyRoute (.leConstHi 0 3) = .explainedDeduction := rfl
example : familyRoute (.constEq 2 (.bool true)) = .explainedDeduction := rfl
example : familyRoute (.boolAndSlot 0 1 2) = .explainedDeduction := rfl
example : familyRoute (.linLe [1, 2] [0, 1] 5) = .localFallback := rfl
example : familyRoute (.allDiff [0, 1, 2]) = .localFallback := rfl

/-- The matrix is total and two-valued: every registered family is either
    an explained-deduction row (the five unit families and the three
    Boolean families) or a proved-local-fallback row (the 12 deferred
    families plus the conflict-only `allDiff` row, whose empty payload
    routes `.local`). No family row claims an unexplained route. -/
theorem familyRoute_explained_or_fallback (dc : DomConstraint) :
    familyRoute dc = .explainedDeduction ∨ familyRoute dc = .localFallback := by
  cases dc <;> (first | exact Or.inl rfl | exact Or.inr rfl)

/-! ## The frame-level explanation evidence of a non-unit family -/

/-- The derived explanation obligations of a family whose reasons are
    CONDITIONAL (2+ literals). `slot_range` is the frame form of the
    `UnitEvidence`/`PropagatorEvidence` range obligation; `falsifier_pin`
    is the order-upgrade falsifier content derivable from the runtime
    result alone: every non-pivot literal asserts the OPPOSITE of a
    Boolean pin the run read. Non-unitness itself is witnessed by the
    concrete public fixtures below. -/
structure ExplainsNonUnit (p : Propagator) : Prop where
  /-- the explanation clause is normalized -/
  reason_norm : ∀ st l r, p.run st = .implied l r → ∀ q ∈ r.clause, q = q.norm
  /-- the normalized pivot is a clause member -/
  pivot_mem : ∀ st l r, p.run st = .implied l r → (l.norm ∈ r.clause) = True
  /-- the pivot names an in-range slot of the box the run read -/
  slot_range : ∀ f, frameViewedB f = true → ∀ l r,
    p.run (frameState f) = .implied l r →
      l.atom.slot < (fullDomains f).length
  /-- every falsifier literal asserts the opposite of a pin the run read -/
  falsifier_pin : ∀ st l r, p.run st = .implied l r →
    ∀ q ∈ r.clause, q ≠ l.norm →
      ∃ s0 : Nat, ∃ b0 : Bool, q = posBool s0 b0 ∧
        domBoolPin st.domains s0 (!b0) = true

/-! The NON-UNIT part is witnessed by the concrete public fixtures
(`boolAnd_nonunit_reason_fixture`, `boolNot_sparse_emit`,
`boolOr2_nonunit_emit`): a `nonunit` field inside `ExplainsNonUnit`
would have to range over the instance's arbitrary parameters `i, j, k`
and could not be witnessed by a concrete state. -/

/-- The shared `implyBool` stage: an implied emission exposes the pin it
    read, the reason clause is the nogood, and the head `posBool s b`
    lives at an in-range slot. -/
theorem implyBool_frame_explains {st : State} {s : Nat} {b : Bool}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : implyBool st s b ng = .implied l r) :
    r.clause = ng ∧ l = posBool s b ∧ s < st.domains.length := by
  obtain ⟨hmem, hl, hcl⟩ := implyBool_implied_inv_mem h
  refine ⟨hcl.symm ▸ rfl, hl, ?_⟩
  by_cases hlt : s < st.domains.length
  · exact hlt
  · exact absurd (slotEnum_nil_of_length_le hlt) (valueMemB_ne_nil hmem)

/-- The pivot obligation from the shared stage. -/
theorem implyBool_frame_pivot {st : State} {s : Nat} {b : Bool}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : implyBool st s b ng = .implied l r) (hmem : posBool s b ∈ ng) :
    (l.norm ∈ r.clause) = True := by
  obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h
  rw [hc, hl, posBool_norm]
  simpa using hmem

/-- The clause-normality obligation from the shared stage. -/
theorem implyBool_frame_norm {st : State} {s : Nat} {b : Bool}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : implyBool st s b ng = .implied l r)
    (hng : ∀ q ∈ ng, q = q.norm) :
    ∀ q ∈ r.clause, q = q.norm := by
  obtain ⟨hc, _, _⟩ := implyBool_frame_explains h
  intro q hq
  rw [hc] at hq
  exact hng q hq

/-- The slot-range obligation from the shared stage. -/
theorem implyBool_frame_slot {st : State} {s : Nat} {b : Bool}
    {ng : Clause} {l : Literal} {r : Reason}
    (h : implyBool st s b ng = .implied l r) :
    l.atom.slot < st.domains.length := by
  obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h
  rw [hl]
  exact hlt

/-! ## Fixtures (defined before the instances that witness them)

Minimal concrete boxes; every emission is proved by kernel reduction
(`rfl`), never `native_decide`. -/

/-- A bare state over the given domains (empty trail and databases). -/
private def esState (doms : List Domain) : State where
  domains := doms
  trail := []
  decisionLevel := 0
  clauses := []
  learned := []
  queue := []
  conflict := none

/-- Sparse/Boolean: slot 1 is pinned to `true` and slot 0 has a sparse
    two-value domain; `bool_not` implies `0 = false` with the two-literal
    conditional reason `[0 = false, 1 = false]`. -/
private def boolSparseState : State :=
  esState [Dom.ofList [.bool false, .bool true], Dom.ofList [.bool true]]

/-- The sparse-domain Boolean deduction, by kernel reduction. -/
theorem boolNot_sparse_emit :
    propBoolNot boolSparseState 0 1 =
      .implied (posBool 0 false)
        { clause := [posBool 0 false, posBool 1 false] } := rfl

/-- The non-unit conditional reason fixture, `bool_and`: both inputs
    pinned true and the output still free — the implication carries the
    THREE-literal reason `[2 = true, 0 = false, 1 = false]`. -/
private def boolAnd3State : State :=
  esState [Dom.ofList [.bool true], Dom.ofList [.bool true],
    Dom.ofList [.bool false, .bool true]]

/-- The three-literal emission, by kernel reduction. -/
theorem boolAnd3_nonunit_emit :
    propBoolAnd boolAnd3State 0 1 2 =
      .implied (posBool 2 true)
        { clause := [posBool 2 true, posBool 0 false, posBool 1 false] } :=
  rfl

/-- The `bool_or` non-unit witness: both inputs pinned false and the
    output still free — the THREE-literal reason
    `[2 = false, 0 = true, 1 = true]`. -/
private def boolOr3State : State :=
  esState [Dom.ofList [.bool false], Dom.ofList [.bool false],
    Dom.ofList [.bool true, .bool false]]

/-- The three-literal or-emission, by kernel reduction. -/
theorem boolOr3_nonunit_emit :
    propBoolOr boolOr3State 0 1 2 =
      .implied (posBool 2 false)
        { clause := [posBool 2 false, posBool 0 true, posBool 1 true] } :=
  rfl

/-- A two-literal fixture: slot 0 pinned true, the output slot 1 still
    free; `bool_or 0 1 1` implies `1 = true` with the conditional reason
    `[1 = true, 0 = false]`. -/
private def boolOr2State : State :=
  esState [Dom.ofList [.bool true], Dom.ofList [.bool false, .bool true]]

/-- The two-literal or-emission, by kernel reduction. -/
theorem boolOr2_nonunit_emit :
    propBoolOr boolOr2State 0 1 1 =
      .implied (posBool 1 true)
        { clause := [posBool 1 true, posBool 0 false] } := rfl

/-- BRANCH-CONDITIONAL REASON, branch A: slot 0 decided `true`. -/
private def boolOrBranchAState : State :=
  esState [Dom.ofList [.bool true], Dom.ofList [.bool false, .bool true],
    Dom.ofList [.bool false, .bool true]]

/-- BRANCH-CONDITIONAL REASON, branch B: slot 1 decided `true`. -/
private def boolOrBranchBState : State :=
  esState [Dom.ofList [.bool false, .bool true], Dom.ofList [.bool true],
    Dom.ofList [.bool false, .bool true]]

/-- **THE BRANCH-CONDITIONAL REASON** (required fixture): the SAME family
at the SAME parameters emits the SAME conclusion `2 = true` on both
branch reads, but the reason — hence its non-pivot falsifier literal —
is CONDITIONAL on which input the branch decided: slot 0 in branch A
(cause `0 = false`), slot 1 in branch B (cause `1 = false`). The pin
tests pin the conditionality to the actual branch decision, and the
reason clauses are provably different. -/
theorem boolOr_branch_conditional_reason :
    propBoolOr boolOrBranchAState 0 1 2
        = .implied (posBool 2 true)
            { clause := [posBool 2 true, posBool 0 false] } ∧
      propBoolOr boolOrBranchBState 0 1 2
        = .implied (posBool 2 true)
            { clause := [posBool 2 true, posBool 1 false] } ∧
      domBoolPin boolOrBranchAState.domains 0 true = true ∧
      domBoolPin boolOrBranchBState.domains 1 true = true ∧
      domBoolPin boolOrBranchBState.domains 0 true = false ∧
      ([posBool 0 false] : Clause) ≠ [posBool 1 false] := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- Negative bounds: the interval domain `[-9, -2]` with the constant
    `-4`: `int_lt(-4, x)` implies `x > -4` (the unit reason
    `[negLe 0 (-4)]`), an emission at NEGATIVE bounds. -/
private def negBoundState : State :=
  esState [Dom.ofList [.int (-9), .int (-2)]]

/-- The negative-bound unit deduction, by kernel reduction. -/
example : LeanFzn.Solver.Propagation.propLtConstLo negBoundState 0 (-4) =
    .implied (negLe 0 (-3 - 1)) { clause := [negLe 0 (-4)] } := rfl

/-! ## The actual CP conflict rows: `neSlot` and `allDiff` (explained conflicts)

Two concrete conflicts of the CP propagators, each now carrying its
EXPLAINED clause instead of the former empty payload:

* `propNe` on two slots pinned to the same value reports `[x ≠ c, y ≠ c]`
  (integer shape) or `[x = ¬b, y = ¬b]` (Boolean shape);
* `propAllDiffLCG` on a pigeonhole reports its Hall clause (per in-range
  slot: below the domain minimum, above its maximum, or equal to a hole).

Both clauses are FALSE at every assignment fitting the state they were read
from (`propNe_conflict_falsified`, `propAllDiffLCG_conflict_falsified`) and
ENTAILED by the constraint at every sort-faithful assignment
(`propNe_conflict_entailed`, `propAllDiffLCG_conflict_entailed`), so
`classifyConflict` routes them `.analyzable` at every positive level
(`.root` at level 0) instead of `.local`. -/

/-- Two Boolean slots pinned to `true`: the pigeonhole count fires. -/
private def allDiffCPState : State := esState [Dom.ofList [.bool true], Dom.ofList [.bool true]]

/-- The Hall clause of the pigeonhole: each slot is below 1 or above 1. -/
def allDiffCPClause : Clause :=
  [posLe 0 0, negLe 0 1, posLe 1 0, negLe 1 1]

/-- The actual CP conflict, by kernel reduction. -/
theorem allDiffCP_conflict :
    propAllDiffLCG allDiffCPState [0, 1] = .conflict allDiffCPClause := rfl

/-- The conflict's exclusion content: no assignment fits the CP state's
domains and satisfies `allDiff [0, 1]` (the pigeonhole). -/
theorem allDiffCP_nofit {a : Assignment}
    (hfit : Core.Assignment.Fits allDiffCPState.domains a) :
    ¬ (DomConstraint.allDiff [0, 1]).SatisfiedBy a :=
  fun hcons => propAllDiffLCG_conflict_nofit allDiffCP_conflict a hfit hcons

/-- The Hall clause is falsified by every assignment fitting the CP state. -/
theorem allDiffCP_falsified {a : Assignment}
    (hfit : Core.Assignment.Fits allDiffCPState.domains a) :
    ∀ q ∈ allDiffCPClause, q.eval a = some false :=
  propAllDiffLCG_conflict_falsified allDiffCP_conflict hfit

/-- The Hall clause is entailed by `allDiff [0, 1]` at every faithful
assignment. -/
theorem allDiffCP_entailed {a : Assignment}
    (hsat : (DomConstraint.allDiff [0, 1]).SatisfiedBy a)
    (hfaith : FrameFaithful allDiffCPState.domains a) :
    ∃ l ∈ allDiffCPClause, l.eval a = some true :=
  propAllDiffLCG_conflict_entailed allDiffCP_conflict (by simp [allDiffCPClause]) hsat hfaith

/-- The actual CP conflict's NON-EMPTY payload routes `.analyzable` at every
positive level and `.root` at level 0: the Hall clause feeds the analyzer
(the former empty payload was `.local` at every level). -/
theorem allDiffCP_routes_analyzable (level : Nat) (hlvl : 0 < level) :
    classifyConflict level [allDiffCPClause] = ConflictShape.analyzable ∧
      classifyConflict 0 [allDiffCPClause] = ConflictShape.root := by
  refine ⟨?_, rfl⟩
  have : level ≠ 0 := by omega
  simp [classifyConflict, ConflictShape.ofConflict, allDiffCPClause, this]

/-- Two integer slots pinned to `3`. -/
private def neIntCPState : State := esState [Dom.ofList [.int 3], Dom.ofList [.int 3]]

/-- Two Boolean slots pinned to `true`. -/
private def neBoolCPState : State := esState [Dom.ofList [.bool true], Dom.ofList [.bool true]]

/-- The integer `propNe` conflict reports `[x ≠ 3, y ≠ 3]`. -/
theorem neCP_int_conflict :
    propNe neIntCPState 0 1 = .conflict [posNe 0 3, posNe 1 3] := rfl

/-- The Boolean `propNe` conflict reports `[x = ¬b, y = ¬b]`. -/
theorem neCP_bool_conflict :
    propNe neBoolCPState 0 1 = .conflict [posBool 0 false, posBool 1 false] := rfl

/-- The `propNe` conflict clauses are falsified by every assignment fitting
the state. -/
theorem neCP_int_falsified {a : Assignment}
    (hfit : Core.Assignment.Fits neIntCPState.domains a) :
    ∀ q ∈ [posNe 0 3, posNe 1 3], q.eval a = some false :=
  propNe_conflict_falsified neCP_int_conflict hfit

theorem neCP_bool_falsified {a : Assignment}
    (hfit : Core.Assignment.Fits neBoolCPState.domains a) :
    ∀ q ∈ [posBool 0 false, posBool 1 false], q.eval a = some false :=
  propNe_conflict_falsified neCP_bool_conflict hfit

/-! ## The three Boolean families: `ExplainsNonUnit` instances -/

/-- The `boolNotSlot` family: every obligation derived from the emit
    inversion `propBoolNot_emit`. -/
theorem explains_boolNotSlot (i j : Nat) :
    ExplainsNonUnit
      ({ watches := [.intLe i 0, .intLe j 0], run := fun st => propBoolNot st i j } :
        Propagator) where
  reason_norm := by
    intro st l r hrun q hq
    rcases propBoolNot_emit hrun with
      ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · exact implyBool_frame_norm h2 (posBool2_norm i false j false) q hq
    · exact implyBool_frame_norm h2 (posBool2_norm i true j true) q hq
    · exact implyBool_frame_norm h2 (posBool2_norm j false i false) q hq
    · exact implyBool_frame_norm h2 (posBool2_norm j true i true) q hq
    · cases hstable
  pivot_mem := by
    intro st l r hrun
    rcases propBoolNot_emit hrun with
      ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · cases hstable
  slot_range := by
    intro f _ l r hrun
    rcases propBoolNot_emit hrun with
      ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · cases hstable
  falsifier_pin := by
    intro st l r hrun q hq hne
    rcases propBoolNot_emit hrun with
      ⟨hp, h2⟩ | ⟨hp, h2⟩ | ⟨hp, h2⟩ | ⟨hp, h2⟩ | hstable
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨j, false, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨j, true, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨i, false, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨i, true, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · cases hstable

/-- The `boolAndSlot` family: every obligation derived from the emit
    inversion `propBoolAnd_emit`. -/
theorem explains_boolAndSlot (i j k : Nat) :
    ExplainsNonUnit
      ({ watches := [.intLe i 0, .intLe j 0, .intLe k 0], run := fun st => propBoolAnd st i j k } :
        Propagator) where
  reason_norm := by
    intro st l r hrun q hq
    rcases propBoolAnd_emit hrun with
      ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · exact implyBool_frame_norm h2
        (posBool3_norm k true i false j false) q hq
    · exact implyBool_frame_norm h2
        (posBool3_norm j false i false k true) q hq
    · exact implyBool_frame_norm h2
        (posBool3_norm i false j false k true) q hq
    · exact implyBool_frame_norm h2 (posBool2_norm k false i true) q hq
    · exact implyBool_frame_norm h2 (posBool2_norm k false j true) q hq
    · cases hstable
  pivot_mem := by
    intro st l r hrun
    rcases propBoolAnd_emit hrun with
      ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · cases hstable
  slot_range := by
    intro f _ l r hrun
    rcases propBoolAnd_emit hrun with
      ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · cases hstable
  falsifier_pin := by
    intro st l r hrun q hq hne
    rcases propBoolAnd_emit hrun with
      ⟨hpi, hpj, h2⟩ | ⟨hpi, hpk, h2⟩ | ⟨hpj, hpk, h2⟩ |
      ⟨hp, h2⟩ | ⟨hp, h2⟩ | hstable
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · rcases List.mem_cons.mp hq with hq | hq
        · refine ⟨i, false, hq, ?_⟩
          simpa using hpi
        · refine ⟨j, false, List.mem_singleton.mp hq, ?_⟩
          simpa using hpj
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · rcases List.mem_cons.mp hq with hq | hq
        · refine ⟨i, false, hq, ?_⟩
          simpa using hpi
        · refine ⟨k, true, List.mem_singleton.mp hq, ?_⟩
          simpa using hpk
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · rcases List.mem_cons.mp hq with hq | hq
        · refine ⟨j, false, hq, ?_⟩
          simpa using hpj
        · refine ⟨k, true, List.mem_singleton.mp hq, ?_⟩
          simpa using hpk
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨i, true, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨j, true, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · cases hstable

/-- The `boolOrSlot` family: every obligation derived from the emit
    inversion `propBoolOr_emit`. -/
theorem explains_boolOrSlot (i j k : Nat) :
    ExplainsNonUnit
      ({ watches := [.intLe i 0, .intLe j 0, .intLe k 0], run := fun st => propBoolOr st i j k } :
        Propagator) where
  reason_norm := by
    intro st l r hrun q hq
    rcases propBoolOr_emit hrun with
      ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · exact implyBool_frame_norm h2
        (posBool3_norm k false i true j true) q hq
    · exact implyBool_frame_norm h2
        (posBool3_norm j true i true k false) q hq
    · exact implyBool_frame_norm h2
        (posBool3_norm i true j true k false) q hq
    · exact implyBool_frame_norm h2 (posBool2_norm k true i false) q hq
    · exact implyBool_frame_norm h2 (posBool2_norm k true j false) q hq
    · cases hstable
  pivot_mem := by
    intro st l r hrun
    rcases propBoolOr_emit hrun with
      ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc, hl, posBool_norm]
      simp
    · cases hstable
  slot_range := by
    intro f _ l r hrun
    rcases propBoolOr_emit hrun with
      ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, _, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | hstable
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · obtain ⟨_, hl, hlt⟩ := implyBool_frame_explains h2
      rw [hl]
      exact slot_lt_frameState hlt
    · cases hstable
  falsifier_pin := by
    intro st l r hrun q hq hne
    rcases propBoolOr_emit hrun with
      ⟨hpi, hpj, h2⟩ | ⟨hpi, hpk, h2⟩ | ⟨hpj, hpk, h2⟩ |
      ⟨hp, h2⟩ | ⟨hp, h2⟩ | hstable
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · rcases List.mem_cons.mp hq with hq | hq
        · refine ⟨i, true, hq, ?_⟩
          simpa using hpi
        · refine ⟨j, true, List.mem_singleton.mp hq, ?_⟩
          simpa using hpj
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · rcases List.mem_cons.mp hq with hq | hq
        · refine ⟨i, true, hq, ?_⟩
          simpa using hpi
        · refine ⟨k, false, List.mem_singleton.mp hq, ?_⟩
          simpa using hpk
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · rcases List.mem_cons.mp hq with hq | hq
        · refine ⟨j, true, hq, ?_⟩
          simpa using hpj
        · refine ⟨k, false, List.mem_singleton.mp hq, ?_⟩
          simpa using hpk
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨i, false, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · obtain ⟨hc, hl, _⟩ := implyBool_frame_explains h2
      rw [hc] at hq
      rw [hl] at hne
      rw [posBool_norm] at hne
      rcases List.mem_cons.mp hq with hq | hq
      · exact absurd hq hne
      · refine ⟨j, false, List.mem_singleton.mp hq, ?_⟩
        simpa using hp
    · cases hstable

/-! ## The falsifier consequence: non-pivot literals are frame-dead -/

/-- A literal asserting the opposite of a Boolean pin is false at every
    assignment fitting the domains the run read. This is the
    order-upgrade falsifier consequence of `falsifier_pin`, derived
    from the runtime result (no caller-supplied falsifier data). -/
theorem posBool_pin_falsified {st : State} {a : Assignment}
    (hfit : Core.Assignment.Fits st.domains a)
    {s0 : Nat} {b0 : Bool} (hp : domBoolPin st.domains s0 (!b0) = true) :
    (posBool s0 b0).eval a = some false := by
  have hread := fits_of_domBoolPin (st := st) hfit hp
  simp only [posBool, Literal.eval, Atom.eval, hread]
  cases b0 <;> rfl

/-- The family-level falsifier consequence: every non-pivot literal of a
    Boolean family's explanation is false at every fitting assignment. -/
theorem boolean_falsified {p : Propagator} (hev : ExplainsNonUnit p)
    {st : State} {l : Literal} {r : Reason}
    (hrun : p.run st = .implied l r) {q : Literal} (hq : q ∈ r.clause)
    (hne : q ≠ l.norm) {a : Assignment}
    (hfit : Core.Assignment.Fits st.domains a) :
    q.eval a = some false := by
  obtain ⟨s0, b0, rfl, hp⟩ := hev.falsifier_pin st l r hrun q hq hne
  exact posBool_pin_falsified hfit hp

/-! ## Coverage examples: sparse domains, negative bounds, Boolean/int -/

/-- Boolean/int separation: the `domBoolPin` test is `false` on an
    integer singleton (no Boolean is pinned) and `true` on the Boolean
    singleton — the pin vocabulary never conflates `.int 1` with
    `.bool true`. -/
example : domBoolPin [Dom.ofList [.int 1]] 0 true = false := rfl
example : domBoolPin [Dom.ofList [.bool true]] 0 true = true := rfl

/-- Boolean/int separation at the propagator level: on integer domains
    the Boolean families never fire (`.stable`), so integer slots are
    untouched by the Boolean explanation route. -/
example : propBoolNot (esState [Dom.ofList [.int 1], Dom.ofList [.int 0]]) 0 1 = .stable := rfl
example : propBoolAnd (esState [Dom.ofList [.int 1], Dom.ofList [.int 1], Dom.ofList [.int 0]]) 0 1 2
    = .stable := rfl

/-- A conditional reason is only CONDITIONAL: the same family stays
    `.stable` when the cause pin is absent (sparse domains do not
    fabricate reasons). -/
example :
    propBoolOr (esState [Dom.ofList [.bool false, .bool true], Dom.ofList [.bool false, .bool true]])
      0 1 0 = .stable := rfl

/-- THE REQUIRED NON-UNIT FIXTURE (2+ literals): the `bool_and` reason
    is a conditional clause of THREE literals. -/
theorem boolAnd_nonunit_reason_fixture :
    ∃ st l r, propBoolAnd st 0 1 2 = .implied l r ∧ 2 ≤ r.clause.length :=
  ⟨boolAnd3State, posBool 2 true,
    { clause := [posBool 2 true, posBool 0 false, posBool 1 false] },
    boolAnd3_nonunit_emit, by simp⟩

/-- The fixture's falsifier literals are false at every fitting
    assignment of the fixture state (order-upgrade falsifiers derived
    from the runtime result, not supplied by the caller). -/
theorem boolAnd3_falsifiers_dead {a : Assignment}
    (hfit : Core.Assignment.Fits boolAnd3State.domains a) :
    (posBool 0 false).eval a = some false ∧
      (posBool 1 false).eval a = some false := by
  constructor
  · exact boolean_falsified (explains_boolAndSlot 0 1 2)
      boolAnd3_nonunit_emit (by decide) (by decide) hfit
  · exact boolean_falsified (explains_boolAndSlot 0 1 2)
      boolAnd3_nonunit_emit (by decide) (by decide) hfit

/-- The `boolOrSlot` twin fixture: a two-literal conditional reason whose
    falsifier is frame-dead. -/
theorem boolOr2_falsifier_dead {a : Assignment}
    (hfit : Core.Assignment.Fits boolOr2State.domains a) :
    (posBool 0 false).eval a = some false :=
  boolean_falsified (explains_boolOrSlot 0 1 1)
    boolOr2_nonunit_emit (by decide) (by decide) hfit

/-- The sparse-domain `boolNot` reason is a valid conditional clause and
    its falsifier is frame-dead at every fitting assignment. -/
theorem boolNot_sparse_falsifier_dead {a : Assignment}
    (hfit : Core.Assignment.Fits boolSparseState.domains a) :
    (posBool 1 false).eval a = some false :=
  boolean_falsified (explains_boolNotSlot 0 1)
    boolNot_sparse_emit (by decide) (by decide) hfit

/-! ## The fallback rows: deferred families keep the local route

The deferred rows of the matrix keep the PROVED LOCAL FALLBACK:
* `propagatorsOfProved_safeUniv` and `propagatorsOfProved_entitled`
  (`Proofs/Propagators.lean`) prove the registered kit's implied/conflict
  soundness and the state-relative conflict entitlement;
* A3's `DomConflictEvidence.excluded` (`LCG/DomExplained.lean`) exports
  the branch-relative exclusion payload, and `classifyConflict` routes
  an EMPTY payload to `.local`;
* `allDiff` reports the explained Hall-clause payload on conflicts
  (`propAllDiffLCG_conflict_falsified`, `propAllDiffLCG_conflict_entailed`);
  its exclusion is `propAllDiffLCG_conflict_nofit` and, since PLAN L8, its
  value eliminations are explained by the same-family reason clause
  (`propAllDiffLCG_implied_inv`, `propAllDiffLCG_sem`,
  `Proofs/Fam/AllDiff.lean` + `LcgFamiliesAllDiff.lean`), so the family is
  NOT conflict-only any more; `neSlot`'s
  both-pinned conflict is explained likewise (`propNe_conflict_falsified`,
  `propNe_conflict_entailed`, `Proofs/Propagators.lean`).

Nothing here is a `sorry`/`admit`/`axiom`; the deferred rows are a
deliberate scope boundary, not a gap in a claimed proof. -/

#print axioms LeanFzn.Solver.UIP.implyBool_frame_explains
#print axioms LeanFzn.Solver.UIP.explains_boolNotSlot
#print axioms LeanFzn.Solver.UIP.explains_boolAndSlot
#print axioms LeanFzn.Solver.UIP.explains_boolOrSlot
#print axioms LeanFzn.Solver.UIP.posBool_pin_falsified
#print axioms LeanFzn.Solver.UIP.boolean_falsified
#print axioms LeanFzn.Solver.UIP.boolNot_sparse_emit
#print axioms LeanFzn.Solver.UIP.boolAnd3_nonunit_emit
#print axioms LeanFzn.Solver.UIP.boolAnd_nonunit_reason_fixture
#print axioms LeanFzn.Solver.UIP.boolAnd3_falsifiers_dead
#print axioms LeanFzn.Solver.UIP.boolOr_branch_conditional_reason
#print axioms LeanFzn.Solver.UIP.allDiffCP_conflict
#print axioms LeanFzn.Solver.UIP.allDiffCP_nofit
#print axioms LeanFzn.Solver.UIP.allDiffCP_routes_analyzable
#print axioms LeanFzn.Solver.UIP.allDiffCP_falsified
#print axioms LeanFzn.Solver.UIP.allDiffCP_entailed
#print axioms LeanFzn.Solver.UIP.neCP_int_conflict
#print axioms LeanFzn.Solver.UIP.neCP_bool_conflict
#print axioms LeanFzn.Solver.UIP.familyRoute_explained_or_fallback

end LeanFzn.Solver.UIP
