/-
Purpose: construct the clamped mixed LCG kit from executable compiled-problem
gates (the mixed twin of LcgCompiledKit: int/bool-uniform domains, discharged
as `ShapeTypedDomains` instead of `AllIntBox`).
Dependencies: CompiledScheduler provides leaf fits and propagation correctness;
LcgEmissionTyped provides slot-aware emission typing; LcgMixedGood defines the
mixed kit; Semantics.StdLib supplies the proven sort-based executable twin
`intsAllDifferentFast` (P3b's linear-time route gate).
DAG: compiled input and family proofs -> this producer -> mixed LCG run
certification. The integer kit and its accepted theorems remain intact.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedGood
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgEmissionTyped
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPropContract
import LeanFzn.Semantics.StdLib

namespace LeanFzn.Solver.UIP.LcgMixedCompiledKit
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LcgRunGood LcgRunInv LcgFamilies LcgEmissionTyped
open LeanFzn.Solver.UIP.LcgMixedGood LeanFzn.Solver.UIP.LcgCanonicalClauses

/-- Checks precisely the domain, shape, family and slot requirements of the
mixed kit: every domain value is an integer or Boolean (no sets/arrays), every
domain is kind-uniform (all integers or all Booleans), integer views are
duplicate-free, and every constraint passes `lcgFamB` with all named slots in
range. No run invariant, restoration fact or progress conclusion is checked
here. -/
def mixedKitGateB (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Bool :=
  problem.domains.all (fun d =>
    ((Dom.enum d).all (fun v => match v with
      | .int _ => true
      | .bool _ => true
      | _ => false) &&
      (((Dom.enum d).all (fun v => match v with | .int _ => true | _ => false) ||
        (Dom.enum d).all (fun v => match v with | .bool _ => true | _ => false)) &&
       decide ((Dom.enum d).map Value.intView).Nodup))) &&
  problem.constraints.all (fun dc => lcgFamB dc &&
    (dcSlots dc).all (fun s => decide (s < problem.domains.length)))

/-! ### P3b: linear-time duplicate check

`mixedKitGateB` decides `(d.map Value.intView).Nodup` with the pairwise
`List.Nodup` decider, which is quadratic in the domain size: on the
`proteindesign12` challenge instances (`domMax = 39 424`, `Σ|d| = 3 272 799`)
the route gate alone needs ~23 minutes, so the search never starts inside the
60 s / 300 s budgets (PLAN P3/P3b). The fast twin below codes each view as an
integer (`none ↦ 1`, `some i ↦ 2 * i`), sorts the codes and scans adjacent
pairs — `O(|d| log |d|)` — reusing the proven sort-based twin
`intsAllDifferentFast`. `mixedKitGateFastB_eq` proves the fast gate equal to
`mixedKitGateB`, so every gate theorem keeps its statement verbatim and every
consumer keeps its behaviour; only the evaluation cost changes. -/

/-- Integer code of a value view: `none` becomes the odd `1`, `some i` the
even `2 * i`. Injective, hence duplicate-preserving and reflecting. -/
def viewCode : Option Int → Int
  | none => 1
  | some i => 2 * i

theorem viewCode_injective : Function.Injective viewCode := by
  intro a b h
  cases a with
  | none =>
      cases b with
      | none => rfl
      | some j => exact absurd h (by simp only [viewCode]; omega)
  | some i =>
      cases b with
      | none => exact absurd h.symm (by simp only [viewCode]; omega)
      | some j =>
          exact congrArg some (show i = j by simp only [viewCode] at h; omega)

/-- The injective view code preserves duplicate-freeness. -/
theorem pairwise_ne_map_viewCode {l : List (Option Int)} :
    List.Pairwise (fun a b => a ≠ b) (l.map viewCode) ↔
      List.Pairwise (fun a b => a ≠ b) l := by
  rw [List.pairwise_map]
  constructor
  · intro h
    exact h.imp (fun {a b} (hne : viewCode a ≠ viewCode b) (he : a = b) =>
      hne (congrArg viewCode he))
  · intro h
    exact h.imp (fun {a b} (hne : a ≠ b) (he : viewCode a = viewCode b) =>
      hne (viewCode_injective he))

theorem nodup_map_viewCode {l : List (Option Int)} :
    (l.map viewCode).Nodup ↔ l.Nodup :=
  pairwise_ne_map_viewCode

/-- Sort-based duplicate check for a list of views (`O(n log n)`): the
sorting twin `intsAllDifferentFast` at the injective view code. -/
def viewsNodupFastB (l : List (Option Int)) : Bool :=
  intsAllDifferentFast (l.map viewCode)

theorem viewsNodupFastB_iff (l : List (Option Int)) :
    viewsNodupFastB l = true ↔ l.Nodup := by
  rw [viewsNodupFastB, intsAllDifferentFast_iff, nodup_map_viewCode]

/-! ### S7c: the structural mixed gate

The four enumeration scans of `mixedKitGateFastB` are replaced by structural
tests: `Dom.allIntBStruct` / `Dom.allBoolBStruct` (compact representations are
kind-uniform by construction) and `viewsNodupStruct` (compact representations
are duplicate-free by construction).  Only `.general` still reads its stored
list; the equality theorems below keep the gate's meaning unchanged. -/

/-- A value is an integer or a Boolean (the kinds the mixed kit accepts). -/
def isIntOrBoolV (v : Value) : Bool :=
  match v with
  | .int _ => true
  | .bool _ => true
  | _ => false

theorem isIntOrBoolV_int (i : Int) : isIntOrBoolV (.int i) = true := rfl

theorem isIntOrBoolV_bool (b : Bool) : isIntOrBoolV (.bool b) = true := rfl

theorem all_isIntOrBoolV_map_int (l : List Int) :
    (l.map Value.int).all isIntOrBoolV = true := by
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨i, _hmem, rfl⟩ := List.mem_map.mp hv
  rfl

theorem all_isIntOrBoolV_smallBools (bits : UInt64) :
    (Dom.smallBools bits).all isIntOrBoolV = true := by
  rw [List.all_eq_true]
  intro v hv
  obtain ⟨b, rfl⟩ := Dom.eq_bool_of_mem_smallBools hv
  rfl

/-- Every value of the domain is an integer or a Boolean. -/
def allIntOrBoolStruct (d : Dom) : Bool :=
  match d.rep with
  | .general vs => vs.all (fun v => match v with
      | .int _ => true
      | .bool _ => true
      | _ => false)
  | _ => true

/-- The structural integer-kind test, spelled with the literal lambda of
    `mixedKitGateB`. -/
theorem allIntBStruct_eq_enum (d : Dom) :
    Dom.allIntBStruct d = (Dom.enum d).all (fun v => match v with
      | .int _ => true
      | _ => false) := by
  rw [Dom.allIntBStruct_eq]
  rfl

/-- The structural Boolean-kind test, spelled with the literal lambda of
    `mixedKitGateB`. -/
theorem allBoolBStruct_eq_enum (d : Dom) :
    Dom.allBoolBStruct d = (Dom.enum d).all (fun v => match v with
      | .bool _ => true
      | _ => false) := by
  rw [Dom.allBoolBStruct_eq]
  rfl

theorem allIntOrBoolStruct_eq (d : Dom) :
    allIntOrBoolStruct d = (Dom.enum d).all (fun v => match v with
      | .int _ => true
      | .bool _ => true
      | _ => false) := by
  cases d with
  | mk rep =>
      cases rep with
      | general vs => rfl
      | small b off bits =>
          cases b with
          | true =>
              show true = (Dom.smallBools bits).all isIntOrBoolV
              exact (all_isIntOrBoolV_smallBools bits).symm
          | false =>
              show true = ((Dom.smallInts off bits).map Value.int).all isIntOrBoolV
              exact (all_isIntOrBoolV_map_int (Dom.smallInts off bits)).symm
      | holes lo hi hs =>
          show true = ((Dom.holesInts lo hi hs).map Value.int).all isIntOrBoolV
          exact (all_isIntOrBoolV_map_int (Dom.holesInts lo hi hs)).symm

theorem map_valueIntView_eq (l : List Value) :
    l.map Dom.valueIntView = l.map Value.intView :=
  List.map_congr_left (fun v _ => Dom.valueIntView_eq_value_intView v)

theorem enum_small_true (off : Int) (bits : UInt64) :
    Dom.enum ⟨Dom.Rep.small true off bits⟩ = Dom.smallBools bits := rfl

theorem enum_small_false (off : Int) (bits : UInt64) :
    Dom.enum ⟨Dom.Rep.small false off bits⟩ =
      (Dom.smallInts off bits).map Value.int := rfl

theorem enum_holes (lo hi : Int) (hs : List Int) :
    Dom.enum ⟨Dom.Rep.holes lo hi hs⟩ =
      (Dom.holesInts lo hi hs).map Value.int := rfl

/-- The integer views of the enumeration are duplicate-free, read
    structurally: the compact representations are duplicate-free by
    construction; `.general` keeps the sort-based scan. -/
def viewsNodupStruct (d : Dom) : Bool :=
  match d.rep with
  | .general vs => viewsNodupFastB (vs.map Value.intView)
  | _ => true

theorem viewsNodupStruct_eq (d : Dom) :
    viewsNodupStruct d = viewsNodupFastB ((Dom.enum d).map Value.intView) := by
  cases d with
  | mk rep =>
      cases rep with
      | general vs => rfl
      | small b off bits =>
          cases b with
          | true =>
              show true = viewsNodupFastB ((Dom.smallBools bits).map Value.intView)
              refine ((viewsNodupFastB_iff _).mpr ?_).symm
              have h := Dom.intViewNodup_small true off bits
              rw [enum_small_true, map_valueIntView_eq] at h
              exact h
          | false =>
              show true = viewsNodupFastB
                (((Dom.smallInts off bits).map Value.int).map Value.intView)
              refine ((viewsNodupFastB_iff _).mpr ?_).symm
              have h := Dom.intViewNodup_small false off bits
              rw [enum_small_false, map_valueIntView_eq] at h
              exact h
      | holes lo hi hs =>
          show true = viewsNodupFastB
            (((Dom.holesInts lo hi hs).map Value.int).map Value.intView)
          refine ((viewsNodupFastB_iff _).mpr ?_).symm
          have h := Dom.intViewNodup_holes lo hi hs
          rw [enum_holes, map_valueIntView_eq] at h
          exact h

/-- The structural twin of `mixedKitGateB`: the per-domain kind and
    duplicate checks are O(1) on the compact representations (only
    `.general` reads its stored list), and the duplicate test is the
    sort-based `viewsNodupFastB`. -/
def mixedKitGateFastB (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) : Bool :=
  problem.domains.all (fun d =>
    (allIntOrBoolStruct d &&
      ((Dom.allIntBStruct d || Dom.allBoolBStruct d) &&
       viewsNodupStruct d))) &&
  problem.constraints.all (fun dc => lcgFamB dc &&
    (dcSlots dc).all (fun s => decide (s < problem.domains.length)))

/-- **P3b ROUTE-GATE EQUALITY**: the fast gate decides exactly `mixedKitGateB`
(same result on every problem; only the evaluation cost differs). -/
theorem mixedKitGateFastB_eq
    (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit) :
    mixedKitGateFastB problem = mixedKitGateB problem := by
  rw [Bool.eq_iff_iff]
  simp only [mixedKitGateFastB, mixedKitGateB, List.all_eq_true, Bool.and_eq_true,
    Bool.or_eq_true, allIntOrBoolStruct_eq, allIntBStruct_eq_enum,
    allBoolBStruct_eq_enum, viewsNodupStruct_eq, viewsNodupFastB_iff,
    decide_eq_true_iff]

/-- The gate's shape discipline: every domain is int-shaped or bool-shaped
(the kind-uniformity disjunction, read propositionally). -/
theorem shape_of_mixedGate {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : mixedKitGateB problem = true) : ShapeTypedDomains problem.domains := by
  simp only [mixedKitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro d hd
  obtain ⟨-, hor, -⟩ := h.1 d hd
  simp only [Bool.or_eq_true, List.all_eq_true] at hor
  rcases hor with hint | hbool
  · left
    intro v hv
    have hvE : v ∈ Dom.enum d := by
      rw [← domElems_eq_enum]
      exact (DomainLike.mem_iff d v).mp hv
    have hh := hint v hvE
    cases v <;> simp_all
  · right
    intro v hv
    have hvE : v ∈ Dom.enum d := by
      rw [← domElems_eq_enum]
      exact (DomainLike.mem_iff d v).mp hv
    have hh := hbool v hvE
    cases v <;> simp_all

/-- Duplicate-freeness of the integer views, mirroring `nodup_of_gate`. -/
theorem nodup_of_mixedGate {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : mixedKitGateB problem = true) : ∀ d ∈ problem.domains, (Dom.enum d).Nodup := by
  simp only [mixedKitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro d hd
  obtain ⟨-, -, hnd⟩ := h.1 d hd
  exact List.Pairwise.of_map Value.intView (fun _ _ hn he => hn (congrArg Value.intView he))
    (of_decide_eq_true hnd)

/-- Every constraint lies in the `lcgFamB` gate, mirroring `families_of_gate`. -/
theorem families_of_mixedGate {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (h : mixedKitGateB problem = true) : ∀ dc ∈ problem.constraints, lcgFamB dc = true := by
  simp only [mixedKitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro dc hd
  exact (h.2 dc hd).1

/-- Every slot a constraint names is `SlotOK`: in range with a nonempty domain.
Mirrors `slots_of_gate` (the executable source gate supplies nonemptiness). -/
theorem slots_of_mixedGate {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hin : CompiledInput leaf problem) (h : mixedKitGateB problem = true) :
    ∀ dc ∈ problem.constraints, ∀ s ∈ dcSlots dc, SlotOK problem.domains s := by
  simp only [mixedKitGateB, Bool.and_eq_true, List.all_eq_true] at h
  intro dc hd s hs
  have hlt : s < problem.domains.length := of_decide_eq_true
    ((h.2 dc hd).2 s hs)
  refine ⟨problem.domains[s], List.getElem?_eq_getElem hlt, ?_⟩
  have hn := gate_nonempty hin.gate _ (List.getElem_mem hlt)
  intro he
  rw [Dom.length_eq_enum, he] at hn
  simp at hn

/-- A concrete producer: all mixed kit fields come from problem-level gates,
TOGETHER WITH the two honest database facts: the original clause database is
canonical and pool-aligned. (Compiled source inputs instantiate them from the
`bool_clause` seed; see `LcgSeedClauses.seedClauses_canonical` and
`LcgSeedClauses.seedClauses_aligned_of_slotOK`.) -/
theorem kit_of_compiled_mixed {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hin : CompiledInput leaf problem) (h : mixedKitGateB problem = true)
    (hcanon : DatabaseCanonical problem.clauses)
    (haligned : DatabaseAligned problem.domains problem.clauses) :
    MixedLcgKit leaf problem.domains problem.clauses problem.constraints
      (problem.constraints.filterMap propagatorOfProved)
      (clampProps problem.domains (problem.constraints.filterMap propagatorOfProved)) where
  raw_eq := rfl
  props_eq := rfl
  fam := families_of_mixedGate h
  shape := shape_of_mixedGate h
  canonicalOriginal := hcanon
  nd := nodup_of_mixedGate h
  fits := fun _ ha => hin.leaf_fits ha
  contract := hin.propagationContract
  typed := emissionTyped_of_families (families_of_mixedGate h)
    (shape_of_mixedGate h) (slots_of_mixedGate hin h)
  aligned := haligned

/-- The `problem.clauses = []` instance of `kit_of_compiled_mixed`: the
empty original clause database is canonical and aligned, so the old shape
(no database hypotheses) is unchanged for its consumers. -/
theorem kit_of_compiled_mixed_nil {leaf : Assignment → Bool}
    {problem : LeanFzn.Solver.Propagation.Problem DomConstraint Unit}
    (hin : CompiledInput leaf problem) (h : mixedKitGateB problem = true)
    (hc : problem.clauses = []) :
    MixedLcgKit leaf problem.domains problem.clauses problem.constraints
      (problem.constraints.filterMap propagatorOfProved)
      (clampProps problem.domains (problem.constraints.filterMap propagatorOfProved)) := by
  have hcanon : DatabaseCanonical problem.clauses := by
    rw [hc]
    exact databaseCanonical_nil
  have haligned : DatabaseAligned problem.domains problem.clauses := by
    rw [hc]
    exact databaseAligned_nil problem.domains
  exact kit_of_compiled_mixed hin h hcanon haligned

end LeanFzn.Solver.UIP.LcgMixedCompiledKit
