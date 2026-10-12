/-
File: LeanFzn/Integration/Proofs/FallbackPolicy.lean
certified-fallback integration contract)

PURPOSE. The public first-UIP activation routes a parsed + compiled model
by ONE executable predicate:

  `firstUIPRouteB problem := domSupportedB problem`

i.e. the concrete unit LCG route (the singleton-unit explanation kit, its
compiled `SupportedInput` adapter and the certified first-UIP package
built on it) serves exactly the problems whose translated constraint list
lies in the five constant families (`unitEvidenceRoute_iff_class`:
`leConstHi`/`leConstLo`/`ltConstHi`/`ltConstLo`/`constEq` of constant
arguments, including the Boolean/aux constant rows); every other
translated model keeps the certified CHRONOLOGICAL route (the named
reference), with the per-family fallback obligations proved in
`FallbackMulti` (`fallbackRoute_total`, `fallbackCoverage_of_compiled`).

SOURCE SEMANTICS. Routing is decided AFTER the existing front door
(parser + `LeanFzn.Compiler.compileModel` + the certified gates): parameter
resolution and auxiliary-slot expansion are the compiler's business
(`compileArgVal` / `AuxShape`), unchanged by this policy. Scalar
parameters resolve to literal values and land in the constant families
(unit route); variable-array forms (`int_lin_*`, `int_plus` over
variables, `all_different`, two-variable Boolean connective forms) keep
their existing source acceptance and take the chronological route.
`domSupportedB` has NO runtime call site inside the translation path, so
source acceptance is untouched by the routing decision.

MULTIPLE-RESOLUTION OBLIGATION (RETAINED, UNMET). The unit route's
analyzed conflict payloads are singleton units by construction
(`supported_conflict_clause_unit`, `unitLearned_ofUIP_normalized_of_singleton`),
so the concrete first-UIP route is NOT a general multiple-resolution LCG:
`unitEvidenceRoute_not_general` exhibits a registered, fallback-covered
family (`boolNotSlot`) outside the unit route, and
`compiled_boolNotFragment_evidence_fails` shows the unit evidence contract
cannot be assembled for it. The milestone's multiple-resolution
requirement (T1) therefore remains an explicit UNMET obligation for
non-unit fragments — neither fallback coverage nor constructed-state
fixtures satisfy it, and no multi-literal learned-clause producer is
claimed by this policy.

NO `sorry`, NO custom axiom.
-/
import LeanFzn.Integration.Proofs.CompiledShape
import LeanFzn.Integration.Proofs.CompiledEntry
import LeanFzn.Integration.Proofs.FallbackMulti
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler LeanFzn.Integration


namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The routing predicate and its two directions -/

/-- THE PUBLIC ROUTING PREDICATE: a compiled LCG problem takes the
concrete first-UIP unit route iff its translated constraint list passes
the supported-family gate. (`domSupportedB` is the executable
`List.all unitFamilyB`; it has no runtime call site in the translation
path.) -/
def firstUIPRouteB (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Bool :=
  domSupportedB problem

/-- ROUTE TRUE ⇒ the compiled unit adapter's hypotheses are all discharged:
a gate-true compiled model yields the `SupportedInput` the concrete
first-UIP package consumes. The caller supplies only the existing
front-door facts (`compileModel` success and the compiled-input gates);
the routing decision adds no fragment assumption. -/
theorem firstUIPRoute_supportedInput {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit} {m : Model}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hdoms : problem.domains = compiled.domains)
    (hin : CompiledInput leaf problem)
    (hr : firstUIPRouteB problem = true) :
    SupportedInput leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) :=
  supportedInput_of_compiled_domSupportedB hc hdoms hin hr

/-- A Boolean list whose `all` is `false` has a `false` entry
(constructive, core-only). -/
private theorem all_false_exists {α : Type} {p : α → Bool} :
    ∀ {l : List α}, l.all p = false → ∃ a ∈ l, p a = false := by
  intro l
  induction l with
  | nil => intro h; simp at h
  | cons a rest ih =>
      intro h
      simp only [List.all_cons] at h
      cases hp : p a with
      | false => exact ⟨a, List.mem_cons_self .., hp⟩
      | true =>
          simp only [hp, Bool.true_and] at h
          obtain ⟨b, hb, hpb⟩ := ih h
          exact ⟨b, List.mem_cons_of_mem _ hb, hpb⟩

/-- ROUTE FALSE ⇒ some translated family is outside the unit route, so the
concrete first-UIP evidence obligation fails there and the problem must
take the certified chronological route (whose per-family fallback is
PROVED: `fallbackRoute_total`). -/
theorem firstUIPRoute_false_witness {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : firstUIPRouteB problem = false) :
    ∃ dc ∈ problem.constraints, ¬ UnitEvidenceRoute dc := by
  obtain ⟨dc, hmem, hdc⟩ := all_false_exists (p := unitFamilyB) h
  refine ⟨dc, hmem, ?_⟩
  show ¬ unitFamilyB dc = true
  rw [hdc]
  simp

/-! ## §2 The scope matrix (documentation as code)

The routing decision is per translated family
(`unitEvidenceRoute_iff_class`); the table is the executable decision:

| translated family (DomConstraint)          | route                |
| ---                                        | ---                  |
| `leConstHi` / `leConstLo`                  | first-UIP unit route |
| `ltConstHi` / `ltConstLo`                  | first-UIP unit route |
| `constEq` (int/bool/set/array constants)   | first-UIP unit route |
| `boolNotSlot` (two-variable `bool_not`)    | chronological (fallback; unit evidence REFUTED) |
| `boolAndSlot` / `boolOrSlot` (non-const)   | chronological (fallback) |
| `eqSlot` / `neSlot` / `leSlot` / `ltSlot`  | chronological (fallback) |
| `plusSlot` / `timesSlot` / `minSlot` / `maxSlot` / `absSlot` | chronological (fallback) |
| `linEq` / `linLe`                          | chronological (fallback) |
| `allDiff`                                  | chronological (fallback) |

Both routes preserve the accepted source fragment: the chronological
route is the existing public certified path (the named reference), and
the unit route is entered only on `firstUIPRouteB = true`. -/

/-- The unit route's family membership is exactly the evidence class
(cross-link to the F1 matrix, `unitEvidenceRoute_iff_class`). -/
theorem firstUIPRoute_family_iff (dc : DomConstraint) :
    unitFamilyB dc = true ↔ evidenceClass dc = .unitEvidence :=
  unitEvidenceRoute_iff_class dc

/-- THE RETAINED UNMET OBLIGATION (PLAN F1/T1): the unit route is not
general — a registered, fallback-covered family sits outside it, so
non-unit multiple-resolution capability is NOT supported by this
milestone's concrete first-UIP route. -/
theorem multipleResolution_obligation_retained :
    ∃ dc : DomConstraint, ¬ UnitEvidenceRoute dc ∧ FallbackRoute dc :=
  unitEvidenceRoute_not_general

end LeanFzn.Integration
