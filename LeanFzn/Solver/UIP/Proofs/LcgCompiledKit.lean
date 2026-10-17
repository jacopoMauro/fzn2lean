/-
Purpose: construct the clamped LCG kit from executable compiled-problem gates.
Dependencies: CompiledScheduler provides leaf fits and propagation correctness;
LcgEmissionTyped provides slot-aware emission typing; LcgRunGood defines the kit.
DAG: compiled input and family proofs -> this producer -> LCG run certification.
The current frame proofs require integer-only boxes; Boolean support is R3b.
-/
import LeanFzn.Solver.UIP.Proofs.LcgRunGood
import LeanFzn.Solver.UIP.Proofs.LcgEmissionTyped
import LeanFzn.Solver.UIP.Proofs.LcgPropContract

namespace LeanFzn.Solver.UIP.LcgCompiledKit
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LcgRunGood LcgRunInv LcgFamilies LcgEmissionTyped

/-- Checks precisely the domain, family and slot requirements of the current kit.
No run invariant, restoration fact or progress conclusion is checked here. -/
def kitGateB (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Bool :=
  problem.domains.all (fun d => d.all (fun v => match v with
    | .int _ => true | _ => false) && decide (d.map Value.intView).Nodup) &&
  problem.constraints.all (fun dc => lcgFamB dc &&
    (dcSlots dc).all (fun s => decide (s < problem.domains.length)))

theorem allInt_of_gate {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : kitGateB problem = true) : AllIntBox problem.domains := by
  simp only [kitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro d hd v hv
  have hh := (h.1 d hd).1 v hv
  cases v <;> simp_all

theorem nodup_of_gate {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : kitGateB problem = true) : ∀ d ∈ problem.domains, d.Nodup := by
  simp only [kitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro d hd
  exact List.Pairwise.of_map Value.intView (fun _ _ hn he => hn (congrArg Value.intView he))
    (of_decide_eq_true (h.1 d hd).2)

theorem families_of_gate {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : kitGateB problem = true) : ∀ dc ∈ problem.constraints, lcgFamB dc = true := by
  simp only [kitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro dc hd
  exact (h.2 dc hd).1

theorem slots_of_gate {leaf : Assignment → Bool} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hin : CompiledInput leaf problem) (h : kitGateB problem = true) :
    ∀ dc ∈ problem.constraints, ∀ s ∈ dcSlots dc, SlotOK problem.domains s := by
  simp only [kitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro dc hd s hs
  have hlt : s < problem.domains.length := of_decide_eq_true
    ((h.2 dc hd).2 s hs)
  refine ⟨problem.domains[s], List.getElem?_eq_getElem hlt, ?_⟩
  have hn := gate_nonempty hin.gate _ (List.getElem_mem hlt)
  intro he
  rw [he] at hn
  simp at hn

/-- A concrete producer: all kit fields come from problem-level gates,
TOGETHER WITH the honest alignment fact for the original clause database
(compiled source inputs instantiate it from the `bool_clause` seed; see
`LcgSeedClauses.seedClauses_aligned_of_slotOK`). -/
theorem kit_of_compiled {leaf : Assignment → Bool} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hin : CompiledInput leaf problem) (h : kitGateB problem = true)
    (haligned : DatabaseAligned problem.domains problem.clauses) :
    LcgKit leaf problem.domains problem.clauses problem.constraints
      (problem.constraints.filterMap propagatorOfProved)
      (clampProps problem.domains (problem.constraints.filterMap propagatorOfProved)) where
  raw_eq := rfl
  props_eq := rfl
  fam := families_of_gate h
  int := allInt_of_gate h
  nd := nodup_of_gate h
  fits := fun _ ha => hin.leaf_fits ha
  contract := hin.propagationContract
  typed := emissionTyped_of_families (families_of_gate h)
    (shape_of_allInt (allInt_of_gate h)) (slots_of_gate hin h)
  aligned := haligned

/-- The `problem.clauses = []` instance of `kit_of_compiled`: unchanged
shape for the consumers of the empty original clause database. -/
theorem kit_of_compiled_nil {leaf : Assignment → Bool} {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hin : CompiledInput leaf problem) (h : kitGateB problem = true)
    (hc : problem.clauses = []) :
    LcgKit leaf problem.domains problem.clauses problem.constraints
      (problem.constraints.filterMap propagatorOfProved)
      (clampProps problem.domains (problem.constraints.filterMap propagatorOfProved)) := by
  have haligned : DatabaseAligned problem.domains problem.clauses := by
    rw [hc]
    exact databaseAligned_nil problem.domains
  exact kit_of_compiled hin h haligned

end LeanFzn.Solver.UIP.LcgCompiledKit
