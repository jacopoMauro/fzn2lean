/-
File: LeanFzn/Integration/Proofs/FallbackMulti.lean

Purpose: **the F1 fragment/evidence COVERAGE MATRIX and the PROVED
chronological fallback for the families the unit-evidence route cannot
cover.** `boolNot_recorded_fails` (`Proofs/CompiledShape.lean`) is a
kernel refutation of the unrestricted `PropagatorEvidence` contract at a
non-unit Boolean family, so the `SupportedInput.evidence` interface -
which is what `supportedInput_of_compiled[_domSupportedB]` assembles -
covers the five constant-bound/constant-equality families ONLY. This
module records the exact matrix and proves that the FULL accepted
fragment (all twenty registered families) is covered by the fallback
route instead, with no fragment gate on the fallback side.

THE COVERAGE MATRIX (accepted source shape -> translated `DomConstraint`
-> per-family route). "unit" = the `SupportedInput.evidence` route
(`unitFamilyB` + `propagatorEvidence_unit`, whose per-family backing is
`propagatorOfProved_unitEvidence` / the eight `unitEvidence_*` family
lemmas of `Proofs/DomExplained.lean`); "fallback" = the proved
registration route named in the last column (the per-family lemmas of
§4 below, whose statements are the family borders of the twenty-arm
dispatch `propagatorsOfProved_fitexcl`, `Proofs/FallbackFit.lean`).

| accepted source shape (`compileModel`) | translated family | unit backing | no-unit (refutation/definitional) | fallback (proved) |
| --- | --- | --- | --- | --- |
| int_eq x y | eqSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_eqSlot` |
| int_eq x k / int_eq k y | constEq | `unitEvidence_constEqInt/Bool/Set/Array` | - | `fallbackFitexcl_constEq` |
| int_ne x y | neSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_neSlot` |
| int_le x y | leSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_leSlot` |
| int_le x k / int_le k y | leConstHi / leConstLo | `unitEvidence_leConstHi/Lo` | - | `fallbackFitexcl_leConstHi/Lo` |
| int_lt x y | ltSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_ltSlot` |
| int_lt x k / int_lt k y | ltConstHi / ltConstLo | `unitEvidence_ltConstHi/Lo` | - | `fallbackFitexcl_ltConstHi/Lo` |
| int_gt x k / int_gt k x | ltConstLo / ltConstHi | idem | - | idem |
| int_ge x k / int_ge k x | leConstLo / leConstHi | idem | - | idem |
| int_plus x y z | plusSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_plusSlot` |
| int_plus x y k | linEq [1,1] [i,j] k | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_linEq` |
| int_lin_eq ks xs b | linEq | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_linEq` |
| int_lin_le ks xs b | linLe | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_linLe` |
| all_different [xs] | allDiff | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_allDiff` |
| int_times x y z | timesSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_timesSlot` |
| int_min / int_max x y z | minSlot / maxSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_minSlot/maxSlot` |
| int_abs x y | absSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_absSlot` |
| bool_not x y | boolNotSlot | - | **`boolNot_recorded_fails`** (kernel), registered form `boolNotRegistered_recorded_fails` | `fallbackFitexcl_boolNotSlot` |
| bool_not x k / bool_not k x | constEq | `unitEvidence_constEqBool` | - | `fallbackFitexcl_constEq` |
| bool_and x y z | boolAndSlot | - | `unitFamilyB = false` (rfl), `evidenceClass = .explainedNonUnit` (E2) | `fallbackFitexcl_boolAndSlot` |
| bool_and x true z / true y z | eqSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_eqSlot` |
| bool_and x false z / false y z | constEq z false | `unitEvidence_constEqBool` | - | `fallbackFitexcl_constEq` |
| bool_or x y z | boolOrSlot | - | `unitFamilyB = false` (rfl), `evidenceClass = .explainedNonUnit` (E2) | `fallbackFitexcl_boolOrSlot` |
| bool_or x true z / true y z | constEq z true | `unitEvidence_constEqBool` | - | `fallbackFitexcl_constEq` |
| bool_or x false z / false y z | eqSlot | - | `unitFamilyB = false` (rfl) | `fallbackFitexcl_eqSlot` |

HONESTY OF THE UNIT ROWS: the "unit backing" column cites the
per-family `unitEvidence_*` witness (the `UnitEvidence` triple) plus the
list-level producer `propagatorEvidence_unit` (`PropagatorEvidence` for
`dcs.filterMap propagatorOfProved` over unit-only `dcs`) and its profile
`unitRunProfile_proved`; these are the ONLY families for which the
`SupportedInput.evidence` field is available. The `boolNotSlot` row's
no-unit column carries the KERNEL refutation of the interface field
itself; the `boolAndSlot`/`boolOrSlot` rows are excluded from the unit
route DEFINITIONALLY (`unitFamilyB = false`, so no
`propagatorOfProved_unitEvidence` witness can exist) - no additional
kernel refutation is claimed for them beyond their E2 classification.

Parameter semantics: `compileModel` resolves scalar parameters through
`parEnv` (`compileArgVal`); a parameter occurrence is compiled as its
literal value, so it lands in the `constEq`/`*ConstHi`/`*ConstLo` rows
above (unit route), or is REJECTED exactly as before when it appears in
an `all_different`/linear variable array (`allDiffSlots`/`linSlots`
error; source acceptance unchanged).

Auxiliary semantics: `AuxShape.expand` rewrites the nine pinning shapes
into already-certified shapes over FRESH aux slots
(`timesSlot`/`neSlot`/`boolAndSlot`/`boolOrSlot`/`constEq`), whose
domains are singleton int/bool pins (`AuxShape.pin`/`pin2`,
`modelAuxSlots_pinval`). Those pins are shape-typed and int-viewed by
`shapeTypedDomains_of_compileModel` - the row of each rewritten
constraint in the table above applies verbatim. In detail
(`LeanFzn/Compiler/Compile.lean`): the int_times literal shapes expand to
auxiliary `int_times` triples (`timesSlot`), the int_ne literal shapes to
`int_ne` pairs (`neSlot`), `bool_and(x,y,false)`/`bool_or(x,y,true)` to a
variable `bool_and`/`bool_or` (`boolAndSlot`/`boolOrSlot`) plus a
`bool_not(aux, b)` pin (`constEq`, UNIT), and
`bool_and(x,y,true)`/`bool_or(x,y,false)` to two `bool_not(_, b)` pins
(`constEq`, UNIT); the literal `bool_not(x/k, b)` shapes compile directly
to `constEq x (!b)` (UNIT).

MULTIPLE RESOLUTIONS: the analyzed (conflict-analysis) route consumes the
STATE-FREE entitlements `propagatorsOfProved_reasonSafeUniv` +
`propagatorsOfProved_just` + `propagatorsOfProved_conflictEntitled`
(Proofs/Reason.lean) - all twenty families, NO unit gate. The unit route's
`supported_conflict_clause_unit` (`Proofs/DomExplained.lean`, N1) shows
the analyzed payloads of the SUPPORTED KIT are unit clauses; that kit is
therefore NOT a general multiple-resolution explanation interface, and
this module does not advertise it as one. The general fallback route is
proved here at exactly the master theorem's premise shapes.

Source acceptance: this module does not touch `compileModel`, `gateOk`,
`accepts` or any acceptance function; it proves that the fallback route
consumes NO `unitFamilyB`/`domSupportedB` premise (only the compiled
linLe/linEq length gates, which are compiler invariants produced by
`compiled_linLe_shape`/`compiled_linEq_shape`).

Contents:
  * §1 the evidence classification and the route predicates.
  * §2 the registered refutation witness for `boolNotSlot 0 1`.
  * §3 the retained (unit) route singleton evidence.
  * §4 the fallback route per family (`fallbackFitexcl_*`, all twenty).
  * §5 the assembled obligation producers at the master-theorem shapes.
  * §6 the compiled entry: every premise derived from `compileModel`
    success except the master's own `hsolvable`.

NO `sorry`, NO custom axiom, NO statement weakening; the closures
`unitFamilyB`/`familyRoute`/`propagatorOfProved` are only CITIED.
Registration owes the umbrella import line
`LeanFzn.Integration.Proofs.FallbackMulti` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Integration.Proofs.CompiledEntry
import LeanFzn.Solver.UIP.Proofs.DomExplained
import LeanFzn.Solver.UIP.Proofs.ExplainedFamilies
import LeanFzn.Solver.Propagation.Proofs.FallbackFit
import LeanFzn.Solver.Propagation.Proofs.FallbackRaw
import LeanFzn.Integration.Certified
open LeanFzn.Compiler.Domains
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Integration
open LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-! ## §1 The evidence classification and the route predicates -/

/-- F1's evidence classification of the twenty registered families
(`propagatorOfProved` is total on `DomConstraint`):
`unitEvidence` = the five constant-bound/constant-equality families the
`propagatorEvidence_unit` producer covers; `explainedNonUnit` = the three
Boolean families whose explanation clauses are genuinely non-unit (E2,
`Proofs/ExplainedFamilies.lean`); `deferredFallback` = the remaining
twelve families. The classification is orthogonal to the fallback route:
ALL twenty families have a registered proved propagator and are covered
by the fallback lemmas of §4. -/
inductive EvidenceClass where
  | unitEvidence
  | explainedNonUnit
  | deferredFallback
  deriving DecidableEq, Repr

/-- The classification function (see `EvidenceClass`). -/
def evidenceClass : DomConstraint → EvidenceClass
  | .leConstHi _ _ => .unitEvidence
  | .leConstLo _ _ => .unitEvidence
  | .ltConstHi _ _ => .unitEvidence
  | .ltConstLo _ _ => .unitEvidence
  | .constEq _ _ => .unitEvidence
  | .boolNotSlot _ _ => .explainedNonUnit
  | .boolAndSlot _ _ _ => .explainedNonUnit
  | .boolOrSlot _ _ _ => .explainedNonUnit
  | _ => .deferredFallback

/-- The unit route is EXACTLY the five constant families: `unitFamilyB`
holds iff the evidence class is `unitEvidence`. -/
theorem unitEvidenceRoute_iff_class (dc : DomConstraint) :
    unitFamilyB dc = true ↔ evidenceClass dc = .unitEvidence := by
  cases dc <;> simp [unitFamilyB, evidenceClass]

/-- F1 coverage predicate (unit route): the `propagatorEvidence_unit`
producer supplies the singleton evidence contract. -/
def UnitEvidenceRoute (dc : DomConstraint) : Prop :=
  unitFamilyB dc = true

/-- F1 coverage predicate (fallback route): a proved propagator is
registered for the family, so the per-family fits-exclusion (§4) applies;
and the conflict/trail-nogood obligations of §5 apply to the registration
it belongs to. -/
def FallbackRoute (dc : DomConstraint) : Prop :=
  ∃ p : Propagator, propagatorOfProved dc = some p

/-- The fallback route is TOTAL on the accepted fragment: every translated
constraint family has a registered proved propagator (no source family is
left without a proved route). -/
theorem fallbackRoute_total (dc : DomConstraint) : FallbackRoute dc := by
  cases dc <;> exact ⟨_, rfl⟩

/-- The unit route is a sub-route of the fallback route. -/
theorem unitEvidenceRoute_subset_fallback {dc : DomConstraint}
    (_h : UnitEvidenceRoute dc) : FallbackRoute dc :=
  fallbackRoute_total dc

/-- THE HONESTY STATEMENT: the unit-evidence route does NOT cover the
whole accepted fragment - `bool_not` over two variable slots is registered
and fallback-covered but not unit-covered - so unit-only coverage cannot
be advertised as general multiple-resolution LeanFzn.Solver.UIP. -/
theorem unitEvidenceRoute_not_general :
    ∃ dc : DomConstraint, ¬ UnitEvidenceRoute dc ∧ FallbackRoute dc := by
  refine ⟨.boolNotSlot 0 1, ?_, fallbackRoute_total (.boolNotSlot 0 1)⟩
  show ¬ (unitFamilyB (.boolNotSlot 0 1) = true)
  decide

/-- CROSS-LINK to the E2 matrix: the unit route is a sub-route of E2's
explained-deduction rows (`familyRoute`, `Proofs/ExplainedFamilies.lean`). -/
theorem unitEvidence_familyRoute_explained (dc : DomConstraint)
    (h : unitFamilyB dc = true) : familyRoute dc = .explainedDeduction := by
  cases dc <;> simp_all [unitFamilyB, familyRoute]

/-! ## §2 The registered refutation witness for `bool_not` -/

/-- The `propagatorOfProved` image of `boolNotSlot 0 1` (the registered
non-unit Boolean family). -/
def boolNotRegistered : Propagator :=
  { watches := [], run := fun st => propBoolNot st 0 1 }

/-- The registration equation, definitionally. -/
theorem propagatorOfProved_boolNotSlot_0_1 :
    propagatorOfProved (.boolNotSlot 0 1) = some boolNotRegistered := rfl

/-- The witness frame: sparse Boolean domains, empty trail. -/
private def boolNotWitnessState (leaf : Assignment → Bool) : BranchState leaf :=
  { frame := ([[.bool false, .bool true], [.bool true]], []), trail := [], level := 0, learned := [] }

/-- **THE REGISTERED `PropagatorEvidence` REFUTATION (membership form)**:
any propagator list containing the registered `bool_not(0,1)` propagator
fails `PropagatorEvidence`: at the empty-trail state over the sparse
Boolean frame `[[false,true],[true]]` the propagator emits the two-literal
reason `[0=false, 1=false]`, whose non-pivot literal `1 = false` has no
recorded trail falsifier (the trail is empty). This is
`boolNot_recorded_fails` (`Proofs/CompiledShape.lean`) in the form the
registration consumes: the failing object is the actual image of
`propagatorOfProved`. -/
theorem boolNotRegistered_recorded_fails {leaf : Assignment → Bool}
    {props : List Propagator} (hmem : boolNotRegistered ∈ props) :
    ¬ PropagatorEvidence leaf props := by
  intro h
  have hbad := h.recorded (boolNotWitnessState leaf) boolNotRegistered hmem
    (posBool 0 false)
    { clause := [posBool 0 false, posBool 1 false] }
    (by rfl)
    (posBool 1 false) (by simp) (by decide)
  simp [boolNotWitnessState] at hbad

/-- **THE COMPILED-FRAGMENT REFUTATION**: a successfully compiled problem
whose constraint list contains `boolNotSlot 0 1` cannot supply the
`SupportedInput.evidence` field for the registered propagator list - the
interface is genuinely unit-only over the accepted fragment. -/
theorem compiled_boolNotFragment_evidence_fails {leaf : Assignment → Bool}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hdc : DomConstraint.boolNotSlot 0 1 ∈ compiled.constraints) :
    ¬ PropagatorEvidence leaf
      (compiled.constraints.filterMap propagatorOfProved) :=
  boolNotRegistered_recorded_fails
    (List.mem_filterMap.mpr ⟨.boolNotSlot 0 1, hdc, rfl⟩)

/-! ## §3 The retained (unit) route: singleton evidence per unit family -/

/-- **THE UNIT-ROUTE SINGLETON CONTRACT**: for every family the unit gate
accepts (`UnitEvidenceRoute dc`) and every registered image `p`, the
singleton propagator list `[p]` carries the full `PropagatorEvidence`
(derived from `propagatorEvidence_unit`, the five-family producer). This
is the per-family soundness lemma of the retained rows. -/
theorem unitFamily_propagatorEvidence {dc : DomConstraint}
    (h : UnitEvidenceRoute dc) {p : Propagator}
    (hp : propagatorOfProved dc = some p) (leaf : Assignment → Bool) :
    PropagatorEvidence leaf [p] := by
  have hpe := propagatorEvidence_unit (leaf := leaf) [dc]
    (fun dc' hdc' => by
      rw [List.mem_singleton] at hdc'
      rw [hdc']
      exact h)
  simpa [hp] using hpe

/-! ## §4 The fallback route per registered family

Each lemma is the family's own border of the twenty-arm dispatch
`propagatorsOfProved_fitexcl` (`Proofs/FallbackFit.lean`): at every
domain-coherent state, a conflict reported by the family's proved
propagator for a constraint PRESENT IN THE PROBLEM excludes every
assignment fitting the state's domains from the internal problem
solutions. The `eqSlot`/`neSlot` rows consume the problem-level
`IntViewedDoms`; the `linLe`/`linEq` rows consume the compiler's
equal-length gate; `allDiff` needs no state premise. -/

/-- Fallback border: `leSlot`. -/
theorem fallbackFitexcl_leSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j : Nat} (hdc : DomConstraint.leSlot i j ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propLe st i j = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLe_safe st i j).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `ltSlot`. -/
theorem fallbackFitexcl_ltSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j : Nat} (hdc : DomConstraint.ltSlot i j ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propLt st i j = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLt_safe st i j).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `eqSlot`. -/
theorem fallbackFitexcl_eqSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {i j : Nat} (hdc : DomConstraint.eqSlot i j ∈ problem.constraints) :
    ∀ (st : State), DomainCoherent problem st → ∀ (c : Clause),
      propEq st i j = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st hcoh c hrun a hfit ha =>
    (propEq_safe st i j (intViewedDoms_of_coherent hview hcoh)).2.1
      c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `neSlot`. -/
theorem fallbackFitexcl_neSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {i j : Nat} (hdc : DomConstraint.neSlot i j ∈ problem.constraints) :
    ∀ (st : State), DomainCoherent problem st → ∀ (c : Clause),
      propNe st i j = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st hcoh c hrun a hfit ha =>
    (propNe_safe st i j (intViewedDoms_of_coherent hview hcoh)).2.1
      c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `plusSlot`. -/
theorem fallbackFitexcl_plusSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j k : Nat} (hdc : DomConstraint.plusSlot i j k ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propPlus st i j k = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propPlus_safe st i j k).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `linLe` (under the compiler's equal-length gate). -/
theorem fallbackFitexcl_linLe {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hdc : DomConstraint.linLe coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length) :
    ∀ (st : State) (c : Clause), propLinLe2 st coeffs is b = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLinLe2_safe st coeffs is b hlen).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `leConstHi`. -/
theorem fallbackFitexcl_leConstHi {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i : Nat} {c2 : Int} (hdc : DomConstraint.leConstHi i c2 ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), LeanFzn.Solver.Propagation.propLeConstHi st i c2 = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLeConstHi_safe st i c2).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `leConstLo`. -/
theorem fallbackFitexcl_leConstLo {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i : Nat} {c2 : Int} (hdc : DomConstraint.leConstLo i c2 ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), LeanFzn.Solver.Propagation.propLeConstLo st i c2 = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLeConstLo_safe st i c2).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `ltConstHi`. -/
theorem fallbackFitexcl_ltConstHi {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i : Nat} {c2 : Int} (hdc : DomConstraint.ltConstHi i c2 ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), LeanFzn.Solver.Propagation.propLtConstHi st i c2 = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLtConstHi_safe st i c2).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `ltConstLo`. -/
theorem fallbackFitexcl_ltConstLo {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i : Nat} {c2 : Int} (hdc : DomConstraint.ltConstLo i c2 ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), LeanFzn.Solver.Propagation.propLtConstLo st i c2 = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLtConstLo_safe st i c2).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `constEq`. -/
theorem fallbackFitexcl_constEq {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i : Nat} {v : Value} (hdc : DomConstraint.constEq i v ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), LeanFzn.Solver.Propagation.propConstEq st i v = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propConstEq_safe st i v).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `boolNotSlot` (the registered `bool_not` family the
unit route cannot cover). -/
theorem fallbackFitexcl_boolNotSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j : Nat} (hdc : DomConstraint.boolNotSlot i j ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propBoolNot st i j = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propBoolNot_safe st i j).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `boolAndSlot`. -/
theorem fallbackFitexcl_boolAndSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j k : Nat} (hdc : DomConstraint.boolAndSlot i j k ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propBoolAnd st i j k = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propBoolAnd_safe st i j k).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `boolOrSlot`. -/
theorem fallbackFitexcl_boolOrSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j k : Nat} (hdc : DomConstraint.boolOrSlot i j k ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propBoolOr st i j k = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propBoolOr_safe st i j k).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `minSlot`. -/
theorem fallbackFitexcl_minSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j k : Nat} (hdc : DomConstraint.minSlot i j k ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propMin st i j k = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propMin_safe st i j k).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `maxSlot`. -/
theorem fallbackFitexcl_maxSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j k : Nat} (hdc : DomConstraint.maxSlot i j k ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propMax st i j k = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propMax_safe st i j k).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `absSlot`. -/
theorem fallbackFitexcl_absSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i k : Nat} (hdc : DomConstraint.absSlot i k ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propAbs st i k = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propAbs_safe st i k).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `linEq` (under the compiler's equal-length gate). -/
theorem fallbackFitexcl_linEq {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hdc : DomConstraint.linEq coeffs is b ∈ problem.constraints)
    (hlen : coeffs.length = is.length) :
    ∀ (st : State) (c : Clause), propLinEq2 st coeffs is b = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propLinEq2_safe st coeffs is b hlen).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `timesSlot`. -/
theorem fallbackFitexcl_timesSlot {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {i j k : Nat} (hdc : DomConstraint.timesSlot i j k ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propTimes st i j k = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st c hrun a hfit ha =>
    (propTimes_safe st i j k).2.1 c hrun a hfit (ha.2 _ hdc)

/-- Fallback border: `allDiff` (the pigeonhole exclusion; no state
premise beyond the reported conflict). -/
theorem fallbackFitexcl_allDiff {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {is : List Nat} (hdc : DomConstraint.allDiff is ∈ problem.constraints) :
    ∀ (st : State) (c : Clause), propAllDiffLCG st is = .conflict c →
      ∀ a, a.Fits st.domains →
        ¬ ProblemSolution problem DomConstraint.SatisfiedBy a :=
  fun st _c hrun a hfit ha => propAllDiffLCG_fitexcl hdc st hrun a hfit ha

/-! ## §5 The assembled fallback obligations at the master-theorem shapes -/

/-- **THE NONEMPTY-CLAUSE FALLBACK ENTITLEMENT (the `hconfraw`/`hconfent`
shape)**: over the proved registration, at every conflict-free RunInv
entry whose propagation ends conflict-carrying with a NONEMPTY clause on
which the analysis fails, the reported clause is entailed - ALL twenty
families, no unit gate. This is `propagatorsOfProved_conflictraw`
(`Proofs/FallbackRaw.lean`); the `hsolvable` premise is the same
problem-level premise the master theorem carries. -/
theorem fallbackCoverage_nonempty_of_proved
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (hsolvable : ∃ b, ProblemSolution problem
      DomConstraint.SatisfiedBy b)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem DomConstraint.SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      ∀ cc, (propagateLoop (engineFuel st) props st).conflict
          = some cc →
        analyzeConflict (propagateLoop (engineFuel st) props st) = none →
        cc ≠ [] →
        Clause.EntailedBy problem DomConstraint.SatisfiedBy cc :=
  propagatorsOfProved_conflictraw hview hprops hlin hlinE
    hsolvable hdb

/-- **THE EMPTY-CLAUSE FALLBACK NOGOOD (the `hfallbackng` shape)**: over
the proved registration, at every conflict-free RunInv entry whose
propagation ends with the EMPTY conflict clause and passes the executable
pins gate, the chronological-fallback trail nogood - the negations of the
positive-level trail literals, normalized - is entailed: ALL twenty
families. The reason side is derived here from
`propagatorsOfProved_reasonSafeUniv` + `propagatorsOfProved_just`; the
fits-exclusion is `propagateLoop_conflict_nofit_empty` with the
twenty-arm per-family assembly `propagatorsOfProved_fitexcl_nolinle`
(`Proofs/FallbackFit.lean`). No `unitFamilyB` premise anywhere. -/
theorem fallbackCoverage_empty_of_proved
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem DomConstraint.SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      trailBoolPinsOk problem
        (propagateLoop (engineFuel st) props st).trail = true →
      (propagateLoop (engineFuel st) props st).conflict = some [] →
      Clause.EntailedBy problem DomConstraint.SatisfiedBy
        (List.map (fun e => e.literal.negate.norm)
          (List.filter (fun e => decide (e.level > 0))
            (propagateLoop (engineFuel st) props st).trail)) :=
  propagatorsOfProved_fallbackng_discharged hview hprops hlin hlinE
    (propagatorsOfProved_reasonSafeUniv hview hprops hlin hlinE)
    (fun acc hcoh hlv hrootF hrooted =>
      propagatorsOfProved_just hview hprops hlin hlinE
        acc hcoh hlv hrooted hrootF)
    hdb

/-- The conjunction of the two routes (the complete F1 fallback
obligation set over the proved registration). -/
theorem fallbackCoverage_of_proved
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (hsolvable : ∃ b, ProblemSolution problem
      DomConstraint.SatisfiedBy b)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem DomConstraint.SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) :
    (∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      ∀ cc, (propagateLoop (engineFuel st) props st).conflict
          = some cc →
        analyzeConflict (propagateLoop (engineFuel st) props st) = none →
        cc ≠ [] →
        Clause.EntailedBy problem DomConstraint.SatisfiedBy cc) ∧
    (∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      trailBoolPinsOk problem
        (propagateLoop (engineFuel st) props st).trail = true →
      (propagateLoop (engineFuel st) props st).conflict = some [] →
      Clause.EntailedBy problem DomConstraint.SatisfiedBy
        (List.map (fun e => e.literal.negate.norm)
          (List.filter (fun e => decide (e.level > 0))
            (propagateLoop (engineFuel st) props st).trail))) :=
  ⟨fallbackCoverage_nonempty_of_proved hview hprops hlin hlinE
      hsolvable hdb,
   fallbackCoverage_empty_of_proved hview hprops hlin hlinE hdb⟩

/-! ## §6 The compiled entry: all premises discharged from `compileModel` -/

/-- The compiled clause base is empty. -/
theorem compiled_clauseDatabase_empty
    (compiled : LeanFzn.Compiler.CompiledProblem DomConstraint) :
    (LeanFzn.Integration.toLCG compiled).clauses = [] := rfl

private theorem compiledView {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled) :
    IntViewedDoms (LeanFzn.Integration.toLCG compiled).domains :=
  intViewedDomains_of_shapeTyped
    (shapeTypedDomains_of_compileModel_toLCG
      (problem := LeanFzn.Integration.toLCG compiled) hc rfl)

private theorem compiledHprops
    (compiled : LeanFzn.Compiler.CompiledProblem DomConstraint) :
    ∀ p ∈ compiled.constraints.filterMap propagatorOfProved,
      ∃ dc ∈ (LeanFzn.Integration.toLCG compiled).constraints,
        propagatorOfProved dc = some p :=
  fun _ hp => propagatorsOfProved_mem hp

private theorem compiledHlin {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled) :
    ∀ dc ∈ (LeanFzn.Integration.toLCG compiled).constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length :=
  fun _ hmem _ _ _ hdc => compiled_linLe_shape hc hmem hdc

private theorem compiledHlinE {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled) :
    ∀ dc ∈ (LeanFzn.Integration.toLCG compiled).constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length :=
  fun _ hmem _ _ _ hdc => compiled_linEq_shape hc hmem hdc

private theorem compiledHdb
    (compiled : LeanFzn.Compiler.CompiledProblem DomConstraint) :
    ∀ c ∈ (LeanFzn.Integration.toLCG compiled).clauses, ∀ a,
      ProblemSolution (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true :=
  fun c hmem _ _ =>
    absurd (show c ∈ ([] : List Clause) from hmem) (by simp)

/-- **THE COMPILED `hfallbackng` PRODUCER (PLAN F1's fallback landing)**:
the master theorem's fallback-nogood premise, derived for the FULL
compiled fragment (all twenty families, no unit gate) from compilation
success alone. -/
theorem compiled_hfallbackng_of_compileModel {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled) :
    ∀ (st : State), st.conflict = none →
      RunInv (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy
        (compiled.constraints.filterMap propagatorOfProved) st →
      TrailDistinct st.trail →
      trailBoolPinsOk (LeanFzn.Integration.toLCG compiled)
        (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st).trail
          = true →
      (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st).conflict
          = some [] →
      Clause.EntailedBy (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy
        (List.map (fun e => e.literal.negate.norm)
          (List.filter (fun e => decide (e.level > 0))
            (propagateLoop (engineFuel st)
              (compiled.constraints.filterMap propagatorOfProved) st).trail)) :=
  fallbackCoverage_empty_of_proved (problem := LeanFzn.Integration.toLCG compiled)
    (props := compiled.constraints.filterMap propagatorOfProved)
    (compiledView hc) (compiledHprops compiled)
    (compiledHlin hc) (compiledHlinE hc) (compiledHdb compiled)

/-- **THE COMPILED `hconfent` PRODUCER** (nonempty-clause conflict
entitlement at every conflict-free RunInv entry, the shape
`go_unsat_entry_invariant`'s `hconfent` consumes): derived for the full
compiled fragment from compilation success + the master's own `hsolvable`
premise. -/
theorem compiled_hconfent_norm_of_compileModel {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hsolvable : ∃ b, ProblemSolution (LeanFzn.Integration.toLCG compiled)
      DomConstraint.SatisfiedBy b) :
    ∀ (st : State), st.conflict = none →
      RunInv (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy
        (compiled.constraints.filterMap propagatorOfProved) st →
      ∀ cc, (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st).conflict
          = some cc →
        cc ≠ [] →
        Clause.EntailedBy (LeanFzn.Integration.toLCG compiled)
          DomConstraint.SatisfiedBy cc :=
  propagatorsOfProved_conflictEntitled (problem := LeanFzn.Integration.toLCG compiled)
    (props := compiled.constraints.filterMap propagatorOfProved)
    (compiledView hc) hsolvable (compiledHprops compiled)
    (compiledHlin hc) (compiledHlinE hc) (compiledHdb compiled)

/-- **THE COMPILED `hconfraw` PRODUCER** (the analysis-failure
nonempty-clause learning entitlement): the master-shape premises
including the analysis-failure observable, derived for the full compiled
fragment (the analysis observables are not consumed - the entitlement is
state-free). -/
theorem compiled_hconfraw_of_compileModel {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hsolvable : ∃ b, ProblemSolution (LeanFzn.Integration.toLCG compiled)
      DomConstraint.SatisfiedBy b) :
    ∀ (st : State), st.conflict = none →
      RunInv (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy
        (compiled.constraints.filterMap propagatorOfProved) st →
      TrailDistinct st.trail →
      ∀ cc, (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st).conflict
          = some cc →
        analyzeConflict (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st) = none →
        cc ≠ [] →
        Clause.EntailedBy (LeanFzn.Integration.toLCG compiled)
          DomConstraint.SatisfiedBy cc :=
  fallbackCoverage_nonempty_of_proved (problem := LeanFzn.Integration.toLCG compiled)
    (props := compiled.constraints.filterMap propagatorOfProved)
    (compiledView hc) (compiledHprops compiled)
    (compiledHlin hc) (compiledHlinE hc) hsolvable (compiledHdb compiled)

/-- **THE COMPILED FALLBACK COVERAGE**: the conjunction of the two
master-shape obligations over the whole accepted fragment. This is the
F1 landing: the full fragment is covered by a PROVED chronological
fallback, and no previously accepted program is rejected or gated by it.
-/
theorem fallbackCoverage_of_compiled {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hsolvable : ∃ b, ProblemSolution (LeanFzn.Integration.toLCG compiled)
      DomConstraint.SatisfiedBy b) :
    (∀ (st : State), st.conflict = none →
      RunInv (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy
        (compiled.constraints.filterMap propagatorOfProved) st →
      TrailDistinct st.trail →
      ∀ cc, (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st).conflict
          = some cc →
        analyzeConflict (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st) = none →
        cc ≠ [] →
        Clause.EntailedBy (LeanFzn.Integration.toLCG compiled)
          DomConstraint.SatisfiedBy cc) ∧
    (∀ (st : State), st.conflict = none →
      RunInv (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy
        (compiled.constraints.filterMap propagatorOfProved) st →
      TrailDistinct st.trail →
      trailBoolPinsOk (LeanFzn.Integration.toLCG compiled)
        (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st).trail
          = true →
      (propagateLoop (engineFuel st)
          (compiled.constraints.filterMap propagatorOfProved) st).conflict
          = some [] →
      Clause.EntailedBy (LeanFzn.Integration.toLCG compiled) DomConstraint.SatisfiedBy
        (List.map (fun e => e.literal.negate.norm)
          (List.filter (fun e => decide (e.level > 0))
            (propagateLoop (engineFuel st)
              (compiled.constraints.filterMap propagatorOfProved) st).trail))) :=
  ⟨compiled_hconfraw_of_compileModel hc hsolvable,
   compiled_hfallbackng_of_compileModel hc⟩

#print axioms LeanFzn.Integration.fallbackCoverage_nonempty_of_proved
#print axioms LeanFzn.Integration.fallbackCoverage_empty_of_proved
#print axioms LeanFzn.Integration.compiled_hfallbackng_of_compileModel
#print axioms LeanFzn.Integration.compiled_hconfent_norm_of_compileModel

end LeanFzn.Integration
