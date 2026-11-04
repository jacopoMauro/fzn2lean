import LeanFzn.Semantics.ValueEquality
import LeanFzn.Semantics.Globals
import LeanFzn.Parser.Parser
import LeanFzn.Solver.Core.CompactDomain


/-!
# Finite-domain extraction for the reference LeanFzn.Solver (PLAN.md 6.1, 6.2)

The reference LeanFzn.Solver of PLAN 6.2 searches an explicit finite list of
candidate values per variable.  This module extracts those lists from
a parsed FlatZinc model:

* `VarDomain` — the domain of one search variable: a finite integer
  value list, or the two Booleans;
* `varDomain` — the domain of a basic variable type, rejecting with a
  reason everything not finitely enumerable in this phase (unbounded
  `var int`, set variables);
* `modelSlots` — the search slots of a model: one `(name, values)`
  pair per *initializer-free* basic variable, in declaration order.

Only initializer-free basic variables are search slots.  Variables
with initializers — including every array variable, which the grammar
pins to `= <array-literal>` — are never searched: the solution
checker's store completion (`LeanFzn.Checker.Solution.completedStore`)
derives their values from the initializers, exactly as it does for a
LeanFzn.Solver-produced solution string (see `Tests/Gecode.lean`, whose alias
arrays `ab = [b1, b2, ...]` are completed from the scalars).

The extraction is faithful to the checker's domain semantics:
`varDomain_values_iff` proves that the candidate values of an
extracted domain are exactly the values accepted by
`BasicVarType.contains` (the relation behind `varDeclsOkB`), so any
UNSAT soundness quantified over all assignments of the extracted
domains ranges over exactly the values the declared domains admit.

A basic variable named `array1d` cannot be emitted as a solution line
(`array1d` is FlatZinc's array-value keyword in solution strings, and
the entry parser reserves it), so such models are rejected as out of
fragment.

There are NO arbitrary size caps: any finite integer range or
enumerated domain is accepted, however large, and the product of the
slot cardinalities is not checked. (Eager domain-list construction
can still be expensive on huge declarations; a later lazy/range
representation is a separate refinement, not an admission cutoff.)
Genuinely infinite domains (unbounded `var int`, set variables)
remain outside the finite fragment and are rejected with a reason.
-/

namespace LeanFzn.Solver.Propagation
namespace Dom

open LeanFzn
open LeanFzn.Semantics
open LeanFzn.Semantics.Evaluation

/-- **Compiler-facing range equality.**  The compact direct-range
    constructor `Dom.ofIntRange` is exactly the canonical
    `Dom.ofList` form of the materialized interval enumeration
    `setElems (.interval lo hi)`, for every pair of bounds (reversed
    ranges included).  This is the compiler-owned name for the
    interface law landed with the S1 `Domain := Dom` switch; the
    construction itself is in `Solver/Core/CompactDomain.lean`, so the
    compiler never repeats the canonical-constructor decision
    conditions. -/
theorem ofIntRange_eq (lo hi : Int) :
    ofIntRange lo hi =
      ofList ((LeanFzn.Semantics.Evaluation.setElems (.interval lo hi)).map Value.int) :=
  ofIntRange_eq_ofList lo hi

end Dom
end LeanFzn.Solver.Propagation

namespace LeanFzn.Compiler.Domains
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn LeanFzn.Solver.Propagation

/-- The finite domain of one search variable: a finite list of
    integer values (a materialized range or an enumerated set) or the
    two Booleans. -/
inductive VarDomain where
  /-- A finite integer domain, as its explicit list of values.  An
      empty list is an empty domain (for example from a reversed
      range `lo..hi` with `hi < lo`, resolution R1). -/
  | intDom (xs : List Int)
  /-- The Boolean domain `[false, true]`. -/
  | boolDom
  deriving Repr

/-- The candidate values of a domain, as store `Value`s. -/
def VarDomain.values : VarDomain → List Value
  | .intDom xs => xs.map Value.int
  | .boolDom => [.bool false, .bool true]

/-- The number of values of an integer range, computed without
    materializing the value list. -/
def rangeSize (lo hi : Int) : Nat :=
  if hi < lo then 0 else (hi - lo + 1).toNat

/-- `rangeSize` agrees with the materialized length. -/
private theorem rangeSize_eq (lo hi : Int) :
    rangeSize lo hi = (setElems (.interval lo hi)).length := by
  by_cases h : hi < lo
  · simp only [rangeSize, setElems, if_pos h, List.length_nil]
  · simp only [rangeSize, setElems, if_neg h, List.length_map, List.length_range]

/-- The finite domain of a basic variable type, if it is finitely
    enumerable: `var bool` is the two Booleans, `var lo..u` and
    `var {..}` are their value lists (empty for a reversed range,
    R1).  Unbounded `var int` and set variables are rejected with a
    reason — they are outside the finite fragment this phase searches.
    There is no cardinality cap: any finite domain is accepted. -/
def varDomain : BasicVarType → Except String VarDomain
  | .par .bool => .ok .boolDom
  | .par .int => .error "unbounded var int is outside the finite fragment"
  | .par .setOfInt => .error "set variables are outside the finite fragment"
  | .intRange lo hi => .ok (.intDom (setElems (.interval lo hi)))
  | .intSet xs => .ok (.intDom xs)
  | .setOfIntRange _ _ => .error "set variables are outside the finite fragment"
  | .setOfIntSet _ => .error "set variables are outside the finite fragment"

/-- **Extraction faithfulness**: the candidate values of an extracted
    domain are exactly the values the checker's domain relation
    `BasicVarType.contains` accepts (the relation `varDeclsOkB`
    enforces on every variable).  This makes any UNSAT soundness
    quantified over all assignments of the extracted domains a
    quantification over exactly the declared finite domains. -/
theorem varDomain_values_iff {ty : BasicVarType} {d : VarDomain}
    (h : varDomain ty = .ok d) {v : Value} :
    v ∈ d.values ↔ ty.contains v := by
  cases ty with
  | par t =>
      cases t with
      | bool =>
          have hd : d = .boolDom := by
            simp only [varDomain] at h
            exact (Except.ok.inj h).symm
          subst hd
          cases v with
          | bool b => cases b <;> simp [VarDomain.values, BasicVarType.contains]
          | int i => simp [VarDomain.values, BasicVarType.contains]
          | setOfInt s => simp [VarDomain.values, BasicVarType.contains]
          | array vs => simp [VarDomain.values, BasicVarType.contains]
      | int => simp only [varDomain] at h; simp at h
      | setOfInt => simp only [varDomain] at h; simp at h
  | intRange lo hi =>
      have hd : d = .intDom (setElems (.interval lo hi)) := (Except.ok.inj h).symm
      subst hd
      cases v with
      | int x =>
          simp only [VarDomain.values, List.mem_map, BasicVarType.contains]
          constructor
          · rintro ⟨i, himem, heq⟩
            injection heq with hix
            subst hix
            exact setElems_mem_iff.mpr himem
          · intro hcont
            exact ⟨x, setElems_mem_iff.mp hcont, rfl⟩
      | bool b => simp [VarDomain.values, BasicVarType.contains]
      | setOfInt s => simp [VarDomain.values, BasicVarType.contains]
      | array vs => simp [VarDomain.values, BasicVarType.contains]
  | intSet xs =>
      have hd : d = .intDom xs := (Except.ok.inj h).symm
      subst hd
      cases v with
      | int x =>
          simp only [VarDomain.values, List.mem_map, BasicVarType.contains]
          constructor
          · rintro ⟨i, himem, heq⟩
            injection heq with hix
            subst hix
            exact himem
          · intro hmem
            exact ⟨x, hmem, rfl⟩
      | bool b => simp [VarDomain.values, BasicVarType.contains]
      | setOfInt s => simp [VarDomain.values, BasicVarType.contains]
      | array vs => simp [VarDomain.values, BasicVarType.contains]
  | setOfIntRange lo hi => simp only [varDomain] at h; simp at h
  | setOfIntSet xs => simp only [varDomain] at h; simp at h

/-! ## Direct `Dom` extraction (S6)

The reference extraction below materializes every finite domain as a
`List Value`; the compiler then canonicalizes that list with
`Dom.ofList`.  Wide intervals (1HZ5: 3.27M values) pay this twice.
The twins in this section build the *same* canonical `Dom` directly:
`Dom.ofIntRange` for `var lo..hi` and `Dom.ofList` for the genuinely
enumerated shapes.  The forward theorems below prove the projections
(`Dom.enum`/`canonSlot`) and the compiler equality in
`LeanFzn.Compiler.Compile` (`compileModelFast_eq`). -/

/-- Projection of a compiled slot back to the legacy value list. -/
def enumSlot (p : String × Dom) : String × List Value :=
  (p.1, Dom.enum p.2)

/-- Canonicalization test on a compiled slot: the domain is the
    `Dom.ofList` normal form of its own enumeration. -/
def canonSlot (p : String × Dom) : String × Dom :=
  (p.1, Dom.ofList (Dom.enum p.2))

/-- Convert a legacy value slot to its direct `Dom` form. -/
def ofListSlot (p : String × List Value) : String × Dom :=
  (p.1, Dom.ofList p.2)

@[simp] theorem enumSlot_ofListSlot (p : String × List Value) :
    enumSlot (ofListSlot p) = p := by
  cases p with
  | mk n vs => simp [enumSlot, ofListSlot, Dom.enum_ofList]

@[simp] theorem canonSlot_ofListSlot (p : String × List Value) :
    canonSlot (ofListSlot p) = ofListSlot p := by
  cases p with
  | mk n vs => simp [canonSlot, ofListSlot, Dom.enum_ofList]

/-- Fast twin of `varDomain`: the same rejections, but the accepted
    domain is built in compact form.  An interval never materializes
    its value list. -/
def varDomainDom : BasicVarType → Except String Dom
  | .par .bool => .ok (Dom.ofList [.bool false, .bool true])
  | .par .int => .error "unbounded var int is outside the finite fragment"
  | .par .setOfInt => .error "set variables are outside the finite fragment"
  | .intRange lo hi => .ok (Dom.ofIntRange lo hi)
  | .intSet xs => .ok (Dom.ofList (xs.map Value.int))
  | .setOfIntRange _ _ => .error "set variables are outside the finite fragment"
  | .setOfIntSet _ => .error "set variables are outside the finite fragment"

/-- `varDomainDom` enumerates exactly like `varDomain`. -/
theorem varDomainDom_eq (ty : BasicVarType) :
    (varDomainDom ty).map Dom.enum = (varDomain ty).map VarDomain.values := by
  cases ty with
  | par t =>
      cases t with
      | bool =>
          simp [varDomainDom, varDomain, VarDomain.values, Dom.enum_ofList,
                Except.map]
      | int => simp [varDomainDom, varDomain, Except.map]
      | setOfInt => simp [varDomainDom, varDomain, Except.map]
  | intRange lo hi =>
      simp [varDomainDom, varDomain, VarDomain.values, Dom.enum_ofIntRange,
            Except.map]
  | intSet xs =>
      simp [varDomainDom, varDomain, VarDomain.values, Dom.enum_ofList,
            Except.map]
  | setOfIntRange lo hi => simp [varDomainDom, varDomain, Except.map]
  | setOfIntSet xs => simp [varDomainDom, varDomain, Except.map]

/-- Every `Dom` produced by `varDomainDom` is in `Dom.ofList` normal
    form (so canonicalizing its enumeration returns it unchanged). -/
theorem varDomainDom_canonical {ty : BasicVarType} {d : Dom}
    (h : varDomainDom ty = .ok d) :
    Dom.ofList (Dom.enum d) = d := by
  cases ty with
  | par t =>
      cases t with
      | bool =>
          simp [varDomainDom] at h
          subst h
          simp [Dom.enum_ofList]
      | int => simp [varDomainDom] at h
      | setOfInt => simp [varDomainDom] at h
  | intRange lo hi =>
      simp [varDomainDom] at h
      subst h
      rw [Dom.enum_ofIntRange]
      exact (Dom.ofIntRange_eq lo hi).symm
  | intSet xs =>
      simp [varDomainDom] at h
      subst h
      rw [Dom.enum_ofList]
  | setOfIntRange lo hi => simp [varDomainDom] at h
  | setOfIntSet xs => simp [varDomainDom] at h

/-- The search slot of one variable declaration, if any: an
    initializer-free basic variable with a finite domain.  Variables
    with initializers (and array variables, which the grammar always
    gives initializers) are not searched — their values are derived
    by store completion.  A variable named `array1d` cannot appear in
    a solution line (the entry parser reserves the keyword), so it is
    rejected. -/
def declSlot (d : VarDeclItem) : Except String (Option (String × List Value)) :=
  match d with
  | .basic ty n _ none =>
      if n.name == "array1d" then
        .error "variable named 'array1d' cannot be emitted in a solution string"
      else
        match varDomain ty with
        | .ok dom => .ok (some (n.name, dom.values))
        | .error e => .error e
  | _ => .ok none

/-- The search slots of a list of variable declarations, in order. -/
def declSlots : List VarDeclItem → Except String (List (String × List Value))
  | [] => .ok []
  | d :: rest =>
      match declSlot d with
      | .error e => .error e
      | .ok none => declSlots rest
      | .ok (some p) => (declSlots rest).map (fun slots => p :: slots)

/-- Fast twin of `declSlot`: the same name rejection and the same
    extraction errors, but the slot domain is built in compact form. -/
def declSlotDom (d : VarDeclItem) : Except String (Option (String × Dom)) :=
  match d with
  | .basic ty n _ none =>
      if n.name == "array1d" then
        .error "variable named 'array1d' cannot be emitted in a solution string"
      else
        match varDomainDom ty with
        | .ok dom => .ok (some (n.name, dom))
        | .error e => .error e
  | _ => .ok none

/-- Fast twin of `declSlots`: the same order, names and rejections,
    with each domain built directly as a `Dom`. -/
def declSlotsDom : List VarDeclItem → Except String (List (String × Dom))
  | [] => .ok []
  | d :: rest =>
      match declSlotDom d with
      | .error e => .error e
      | .ok none => declSlotsDom rest
      | .ok (some p) => (declSlotsDom rest).map (fun slots => p :: slots)

/-- `declSlotDom` reproduces the legacy slot list under `enumSlot`. -/
theorem declSlotDom_eq (d : VarDeclItem) :
    (declSlotDom d).map (Option.map enumSlot) = declSlot d := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | some e => rfl
      | none =>
          cases hb : (n.name == "array1d") with
          | true => simp [declSlotDom, declSlot, hb, Except.map]
          | false =>
              simp only [declSlotDom, declSlot, hb, Bool.false_eq_true, if_false]
              cases ty with
              | par t =>
                  cases t <;>
                    simp [varDomainDom, varDomain, VarDomain.values, enumSlot,
                          Dom.enum_ofList, Except.map, Option.map]
              | intRange lo hi =>
                  simp [varDomainDom, varDomain, VarDomain.values, enumSlot,
                        Dom.enum_ofIntRange, Except.map, Option.map]
              | intSet xs =>
                  simp [varDomainDom, varDomain, VarDomain.values, enumSlot,
                        Dom.enum_ofList, Except.map, Option.map]
              | setOfIntRange lo hi =>
                  simp [varDomainDom, varDomain, Except.map, Option.map]
              | setOfIntSet xs =>
                  simp [varDomainDom, varDomain, Except.map, Option.map]
  | array ty n anns value => rfl

/-- Every slot produced by `declSlotDom` is in canonical (`Dom.ofList`)
    normal form. -/
theorem declSlotDom_canonical (d : VarDeclItem)
    {o : Option (String × Dom)} (h : declSlotDom d = .ok o) :
    Option.map canonSlot o = o := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | some e =>
          simp [declSlotDom] at h
          subst h
          rfl
      | none =>
          cases hb : (n.name == "array1d") with
          | true => simp [declSlotDom, hb] at h
          | false =>
              simp only [declSlotDom, hb, Bool.false_eq_true, if_false] at h
              cases ty with
              | par t =>
                  cases t with
                  | bool =>
                      simp [varDomainDom] at h
                      subst h
                      simp [canonSlot]
                  | int => simp [varDomainDom] at h
                  | setOfInt => simp [varDomainDom] at h
              | intRange lo hi =>
                  simp [varDomainDom] at h
                  subst h
                  simp [canonSlot, Dom.enum_ofIntRange, Dom.ofIntRange_eq]
              | intSet xs =>
                  simp [varDomainDom] at h
                  subst h
                  simp [canonSlot]
              | setOfIntRange lo hi => simp [varDomainDom] at h
              | setOfIntSet xs => simp [varDomainDom] at h
  | array ty n anns value =>
      simp [declSlotDom] at h
      subst h
      rfl

/-- `declSlotsDom` reproduces the legacy slot list under `enumSlot`. -/
theorem declSlotsDom_eq (ds : List VarDeclItem) :
    (declSlotsDom ds).map (List.map enumSlot) = declSlots ds := by
  induction ds with
  | nil => rfl
  | cons d rest ih =>
      unfold declSlotsDom declSlots
      cases hd : declSlotDom d with
      | error e =>
          have h := declSlotDom_eq d
          rw [hd] at h
          simp only [Except.map] at h
          rw [← h]
          rfl
      | ok o =>
          have h := declSlotDom_eq d
          rw [hd] at h
          cases o with
          | none =>
              simp only [hd] at h ⊢
              simp only [Option.map, Except.map] at h
              rw [← h]
              exact ih
          | some p =>
              simp only [hd] at h ⊢
              simp only [Option.map, Except.map] at h
              rw [← h]
              simp only [Except.map]
              cases hr : declSlotsDom rest with
              | error e =>
                  rw [hr] at ih
                  simp only [Except.map] at ih
                  rw [← ih]
              | ok slots =>
                  rw [hr] at ih
                  simp only [Except.map] at ih
                  rw [← ih]
                  simp only [Except.map, List.map_cons]
                  try rfl

/-- Every slot list produced by `declSlotsDom` is canonical. -/
theorem declSlotsDom_canonical (ds : List VarDeclItem)
    {slots : List (String × Dom)} (h : declSlotsDom ds = .ok slots) :
    slots.map canonSlot = slots := by
  induction ds generalizing slots with
  | nil =>
      simp [declSlotsDom] at h
      subst h
      rfl
  | cons d rest ih =>
      unfold declSlotsDom at h
      cases hd : declSlotDom d with
      | error e => simp [hd, Except.map] at h
      | ok o =>
          cases o with
          | none =>
              simp only [hd] at h ⊢
              exact ih h
          | some p =>
              simp only [hd] at h ⊢
              cases hr : declSlotsDom rest with
              | error e => simp [hr, Except.map] at h
              | ok rs =>
                  simp only [hr, Except.map, Except.ok.injEq] at h
                  subst h
                  simp only [List.map_cons]
                  rw [ih hr]
                  have hp := declSlotDom_canonical d hd
                  have hp' : canonSlot p = p := by
                    have hsome : some (canonSlot p) = some p := by
                      simpa using hp
                    exact Option.some.inj hsome
                  rw [hp']

/-- The number of complete assignments of a list of domains (the
    number of search leaves). -/
def leavesProduct : List (List Value) → Nat
  | [] => 1
  | d :: rest => d.length * leavesProduct rest

/-- **The search slots of a model**, with the reason for a refusal:
    for each initializer-free basic variable, its name and its finite
    candidate values, in declaration order.  Fails when a variable
    is outside the finite fragment (unbounded or set variables,
    unemittable names).  There is no leaves-product cap: any finite
    product is accepted.  A model whose every variable has an
    initializer has the empty slot list (search decides the empty
    assignment). -/
def slotsChecked (m : Model) : Except String (List (String × List Value)) :=
  declSlots m.variables

/-- Fast twin of `slotsChecked`: the same slots in declaration order,
    with every domain built directly as a compact `Dom`. -/
def slotsCheckedDom (m : Model) : Except String (List (String × Dom)) :=
  declSlotsDom m.variables

/-- **Slot extraction agreement (S6)**: enumerating each compact slot
    domain reproduces exactly the legacy `List Value` slot list,
    including the same rejection reason on failure. -/
theorem slotsCheckedDom_eq (m : Model) :
    (slotsCheckedDom m).map (List.map enumSlot) = slotsChecked m :=
  declSlotsDom_eq m.variables

/-- Every slot list produced by `slotsCheckedDom` is canonical. -/
theorem slotsCheckedDom_canonical (m : Model)
    {slots : List (String × Dom)} (h : slotsCheckedDom m = .ok slots) :
    slots.map canonSlot = slots :=
  declSlotsDom_canonical m.variables h

/-- **The search slots of a model**: for each initializer-free basic
    variable, its name and its finite candidate values, in
    declaration order.  `none` when a variable is outside the finite
    fragment (unbounded or set variables, unemittable names).  A model
    whose every variable has an initializer has the empty slot list
    (search decides the empty assignment). -/
def modelSlots (m : Model) : Option (List (String × List Value)) :=
  (slotsChecked m).toOption

/-- `modelSlots` succeeds exactly when `slotsChecked` does, on the
    same slots. -/
theorem modelSlots_eq {m : Model} {slots : List (String × List Value)} :
    modelSlots m = some slots ↔ slotsChecked m = .ok slots := by
  simp only [modelSlots]
  cases h : slotsChecked m with
  | error e =>
      simp only [Except.toOption]
      constructor
      · intro hcontra
        cases hcontra
      · intro hcontra
        cases hcontra
  | ok s =>
      simp only [Except.toOption]
      constructor
      · intro he
        cases he
        rfl
      · intro he
        have hs : s = slots := Except.ok.inj he
        rw [hs]

/-- The names of the search slots, in declaration order (empty when
    extraction failed). -/
def slotNames (m : Model) : List String :=
  match modelSlots m with
  | some slots => slots.map Prod.fst
  | none => []

/-- The candidate-value lists of the search slots, in declaration
    order (empty when extraction failed). -/
def slotDomains (m : Model) : List (List Value) :=
  match modelSlots m with
  | some slots => slots.map Prod.snd
  | none => []

/-- `slotNames` and `slotDomains` are the projections of a successful
    extraction. -/
theorem slotNames_domains_of_modelSlots {m : Model}
    {slots : List (String × List Value)} (h : modelSlots m = some slots) :
    slotNames m = slots.map Prod.fst ∧ slotDomains m = slots.map Prod.snd := by
  constructor
  · simp only [slotNames, h]
  · simp only [slotDomains, h]

/-! ## Structural value equality (`BEq Value`)

The checker's own structural equality `Value.eqB`
(`LeanFzn/FznStdLib.lean`), proved reflexive and sound
(`value_eqB_refl` / `value_eqB_iff`), is exactly the right `BEq`
instance for the solver layers (the development's established
pattern: reuse the proved Boolean twin instead of deriving a fresh
equality).  Moved here from the retired `LeanFzn.Solver/Enum.lean` so the
shared slot-domain layer carries it. -/

/-- The checker's structural value equality, as the `BEq` instance. -/
instance : BEq Value := ⟨Value.eqB⟩

/-- `Value.eqB` is reflexive and sound, so it is a lawful equality. -/
instance : LawfulBEq Value := {
  eq_of_beq := fun {_ _} h => value_eqB_iff.mp h
  rfl := fun {_} => value_eqB_refl _
}

end LeanFzn.Compiler.Domains
