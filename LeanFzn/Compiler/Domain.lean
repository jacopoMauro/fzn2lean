import LeanFzn.Semantics.ValueEquality
import LeanFzn.Semantics.Globals
import LeanFzn.Parser.Parser


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

namespace LeanFzn.Compiler.Domains
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn

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
