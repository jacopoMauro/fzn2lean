/-
File: LeanFzn/Integration/Proofs/CompiledShape.lean

Purpose: the F1 producer for `SupportedInput.shape` (the run box's
`ShapeTypedDomains` discipline) from a successful compilation:

  §1 `shapeTypedDomains_of_compileModel` — every domain of a compiled
     problem is int-shaped or bool-shaped (declaration forms `xs.map
     Value.int` / `[.bool false, .bool true]` and aux singleton pins
     `[.int k]` / `[.bool b]`). Mirrors `LeanFzn.Compiler.domains_intViewed`'s
     inversion kit, producing the UNIFORM shape per domain instead of the
     pointwise int-view property.
  §2 `shapeTypedDomains_toLCG` — the LCG-side form (the LCG problem's
     domains are the compiled problem's, definitionally).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Integration.Proofs.CompiledShape` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedProviders
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core

/-- **F1 SHAPE PRODUCER**: every domain of a successfully compiled problem
is int-shaped or bool-shaped. The model half uses the declaration inversion
(`declSlots_mem` + `compileModel_vars_basic` + `declSlot_basic_inv`, with
the two `VarDomain` constructors' value lists); the aux half uses the
singleton-pin spec (`modelAuxSlots_spec` + `modelAuxSlots_pinval`). -/
theorem shapeTypedDomains_of_compileModel {m : Model}
    {compiled : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok compiled) :
    LeanFzn.Solver.UIP.ShapeTypedDomains compiled.domains := by
  obtain ⟨_, slots, dcs, ⟨slots0, hslots0, hslots⟩, _, hasm⟩ :=
    compileModel_ok_inv hc
  have hdoms : compiled.domains = slots.map Prod.snd := by
    show compiled.domains = slots.map Prod.snd
    rw [hasm]
    rfl
  rw [hdoms, hslots, List.map_append]
  intro d hd
  rcases List.mem_append.mp hd with hmodel | haux
  · -- a model slot's domain: a declaration's value list
    obtain ⟨p, hpmem, hpget⟩ := List.mem_map.mp hmodel
    obtain ⟨d2, hd2mem, hds⟩ := declSlots_mem m.variables slots0
      (declSlots_of_slotsChecked hslots0) p hpmem
    obtain ⟨ty, n, anns, hshape⟩ := compileModel_vars_basic hc d2 hd2mem
    obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv
      (p := p) (by rw [← hshape]; exact hds)
    have hddom : d = dom.values := by
      rw [← hpget, hpair]
    cases hdom2 : dom with
    | intDom xs =>
        left
        intro v hv
        rw [hddom, hdom2] at hv
        exact intDom_values_int v hv
    | boolDom =>
        right
        intro v hv
        rw [hddom, hdom2] at hv
        exact boolDom_values_bool hv
  · -- an aux slot's domain: a singleton int/bool pin
    obtain ⟨p, hpmem, hpget⟩ := List.mem_map.mp haux
    obtain ⟨v2, hsingle⟩ := (modelAuxSlots_spec hslots0).2 p hpmem
    have hd' : d = [v2] := by
      rw [← hpget, hsingle]
    rcases modelAuxSlots_pinval hslots0 p hpmem v2 hsingle with
      ⟨k, hk⟩ | ⟨b, hb⟩
    · left
      intro v hv
      rw [hd'] at hv
      obtain rfl := List.mem_singleton.mp hv
      rw [hk]
      exact ⟨k, rfl⟩
    · right
      intro v hv
      rw [hd'] at hv
      obtain rfl := List.mem_singleton.mp hv
      rw [hb]
      exact ⟨b, rfl⟩

end LeanFzn.Integration
namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core

/-- The LCG-side form: the LCG problem's domains are the compiled
problem's (`toLCG` copies them verbatim). -/
theorem shapeTypedDomains_of_compileModel_toLCG {m : Model}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hdoms : problem.domains = compiled.domains) :
    ShapeTypedDomains problem.domains := by
  rw [hdoms]
  exact LeanFzn.Integration.shapeTypedDomains_of_compileModel hc

/-! ## §3 The F1 compiled-input assembly -/

/-- Shape-typed domains are int-viewed (an int is its own integer view, a
Bool has the 0/1 view). Gate-free route to `SupportedInput.viewed`. -/
theorem intViewedDomains_of_shapeTyped {orig : List Domain}
    (hshape : ShapeTypedDomains orig) :
    ∀ d ∈ orig, IntViewedDomain d := by
  intro d hd v hv
  rcases hshape d hd with hint | hbool
  · obtain ⟨k, rfl⟩ := hint v hv
    simp [Value.intView]
  · obtain ⟨b, rfl⟩ := hbool v hv
    cases b <;> simp [Value.intView]

/-- **F1 (L2) THE COMPILED SUPPORTED-INPUT ASSEMBLY**: every
`SupportedInput` field of a successfully compiled, gate-accepted,
unit-supported problem. Fields 1/3/4/5 are the landed `CompiledInput`
producers, field 2 is the compile-model shape producer, and field 6 is
the unit-family evidence producer. The `hSupp` premise is the honest
fragment gate: `PropagatorEvidence.recorded` is FALSE for the genuinely
non-unit Boolean families (`boolNot_recorded_fails` below), so the
restriction is kernel-justified, not silent — runtime acceptance is
untouched (`domSupportedB` has no runtime call site). -/
theorem supportedInput_of_compiled {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {m : Model} {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hdoms : problem.domains = compiled.domains)
    (hin : CompiledInput leaf problem)
    (hSupp : ∀ dc ∈ problem.constraints, unitFamilyB dc = true) :
    SupportedInput leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) where
  leaf_fits := fun _ ha => hin.leaf_fits ha
  shape := shapeTypedDomains_of_compileModel_toLCG hc hdoms
  viewed := hin.intViewedDomains
  original_entailed := fun c hc' => hin.leaf_clauses c hc'
  contract := hin.propagationContract
  evidence := propagatorEvidence_unit problem.constraints hSupp

/-- The executable fragment-gate form: `domSupportedB problem = true`. -/
theorem supportedInput_of_compiled_domSupportedB {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    {m : Model} {compiled : LeanFzn.Compiler.CompiledProblem DomConstraint}
    (hc : LeanFzn.Compiler.compileModel m = .ok compiled)
    (hdoms : problem.domains = compiled.domains)
    (hin : CompiledInput leaf problem)
    (hSupp : domSupportedB problem = true) :
    SupportedInput leaf problem.domains problem.clauses
      (problem.constraints.filterMap propagatorOfProved) :=
  supportedInput_of_compiled hc hdoms hin (unitFamilyB_of_domSupportedB hSupp)

/- The compiled-problem instance: the LCG problem's domains are the
compiled problem's definitionally (`hdoms := rfl`). The `LeanFzn.Integration.toLCG`
wrapper lives in `LeanFzn.Integration.Proofs.CompiledEntry` (it needs the CLI
module, which is not in this file's cone). -/

/-! ## §4 The kernel witness forcing the `hSupp` fragment gate -/

/-- The genuinely non-unit Boolean family's registered propagator shape. -/
private def boolNotProp : Propagator :=
  { watches := [.intLe 0 0, .intLe 1 0], run := fun st => propBoolNot st 0 1 }

/-- **THE `PropagatorEvidence.recorded` REFUTATION WITNESS**: at the
empty-trail state over the sparse Boolean frame `[[false,true],[true]]`,
the registered `bool_not(0,1)` propagator emits the two-literal reason
`[0=false, 1=false]`; the non-pivot literal `1 = false` has no recorded
trail falsifier (the trail is empty). Hence `PropagatorEvidence.recorded`
is unsatisfiable for any propagator list containing this family — the
`hSupp` unit restriction of `supportedInput_of_compiled` is forced by the
frozen field type, not a convenience. -/
theorem boolNot_recorded_fails {leaf : Assignment → Bool} :
    ¬ PropagatorEvidence leaf ([boolNotProp] : List Propagator) := by
  intro h
  have hbad := h.recorded
    ({ frame := ([[.bool false, .bool true], [.bool true]], []),
       trail := [], level := 0, learned := [] } : BranchState leaf)
    boolNotProp (by simp)
    (posBool 0 false)
    { clause := [posBool 0 false, posBool 1 false] }
    (by rfl)
    (posBool 1 false) (by simp) (by decide)
  simp at hbad

end LeanFzn.Integration
