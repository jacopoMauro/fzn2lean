import LeanFzn.Semantics.ValueEquality
/-
File: LeanFzn/Compiler/Extract.lean

Purpose:
Extraction of slot-indexed constraints from a FlatZinc model's
constraint list.  Each recognized predicate-argument shape is
translated to a `DomConstraint` over the model's search-slot
positions, so the propagators of `LeanFzn.Solver/Propagators.lean` can
narrow the slot domains during search.
-/

import LeanFzn.Semantics.Globals
import LeanFzn.Parser.Parser
import LeanFzn.Compiler.Domain
import LeanFzn.Solver.Propagation.DomainConstraints
open LeanFzn.Compiler.Domains


/-! ## Slot-name indexing

`nameIndex names s` is the position of `s` in the slot-name list, if
any. -/

namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals

/-- The position of a name in the slot list, if present. -/
def nameIndex : List String → String → Option Nat
  | [], _ => none
  | n :: ns, s => if n == s then some 0 else (nameIndex ns s).map (· + 1)

theorem nameIndex_some : ∀ (names : List String) (s : String) (i : Nat),
    nameIndex names s = some i → i < names.length ∧ names[i]? = some s := by
  intro names
  induction names with
  | nil =>
      intro s i h
      simp only [nameIndex] at h
      exact absurd h (by simp)
  | cons n ns ih =>
      intro s i h
      simp only [nameIndex] at h
      by_cases hne : n == s
      · rw [if_pos hne] at h
        have hi : 0 = i := Option.some.inj h
        subst hi
        exact ⟨by simp, by simp [beq_iff_eq.mp hne]⟩
      · rw [if_neg hne] at h
        cases h2 : nameIndex ns s with
        | none => rw [h2] at h; exact absurd h (by simp)
        | some j =>
            rw [h2] at h
            have hij : j + 1 = i := (Option.some.inj h)
            subst hij
            obtain ⟨hjlt, hget⟩ := ih s j h2
            constructor
            · simp only [List.length_cons]
              omega
            · rw [List.getElem?_cons_succ]
              exact hget

/-- From an in-bounds successful option lookup, the bang read
    returns the same value (the bridge `hvals`-style premises need). -/
theorem getElem_of_getElem? {α : Type} [Inhabited α] {l : List α}
    {i : Nat} {x : α} (_hlt : i < l.length) (hget : l[i]? = some x) :
    l[i]! = x := by
  rw [List.getElem!_eq_getElem?_getD, hget]
  rfl

/-! ## The extracted shapes

Recognized predicate-argument shapes (all other shapes are skipped):

| model constraint (shape)                  | `DomConstraint`       |
|--------------------------------------------|-----------------------|
| `int_eq(x, y)` (both slot names)           | `eqSlot i j`          |
| `int_eq(x, k)` / `int_eq(k, x)`             | `constEq i (.int k)`  |
| `int_ne(x, y)` (both slot names)           | `neSlot i j`          |
| `int_le(x, y)` (both slot names)           | `leSlot i j`          |
| `int_le(x, c)` (literal bound above)       | `leConstHi i c`       |
| `int_le(c, x)` (literal bound below)       | `leConstLo i c`       |
| `int_plus(x, y, z)` (three slot names)     | `plusSlot i j k`      |
| `all_different([x₁, …, xₘ])` (explicit     | `allDiff [i₁, …]`     |
|  array of slot names)                       |                       |
| `int_lin_eq([c₁,…], [x₁,…], b)` (par       | `linEq [c₁,…] [i₁,…] b` |
|  coeff array, slot array, int literal)      |                       |
| `int_lin_le([c₁,…], [x₁,…], b)`             | `linLe [c₁,…] [i₁,…] b` |
| `int_lin_ne([c₁,…], [x₁,…], b)`             | `linNe [c₁,…] [i₁,…] b` |
| `int_times(x, y, z)` (three slot names)     | `timesSlot i j k`     |
| `int_min(x, y, z)` (three slot names)       | `minSlot i j k`       |
| `int_max(x, y, z)` (three slot names)       | `maxSlot i j k`       |
| `int_abs(x, y)` (two slot names)            | `absSlot i k`         |
| `int_lt(x, y)` (both slot names)            | `ltSlot i j`          |
| `int_lt(x, c)` (literal bound above)        | `ltConstHi i c`       |
| `int_lt(c, x)` (literal bound below)        | `ltConstLo i c`       |
| `bool_not(x, y)` (two slot names)           | `boolNotSlot i j`     |
| `bool_and(x, y, z)` (three slot names)      | `boolAndSlot i j k`   |
| `bool_or(x, y, z)` (three slot names)       | `boolOrSlot i j k`    |

Everything else — other predicate names, array arguments on scalar
predicates, literals in `int_ne`/`int_plus` positions (e.g.
`int_plus(x, y, 5)` — a future bounds-propagation shape), arguments
that are not search slots (parameters, initializer-bound array
elements), an `all_different` argument that is a single identifier
naming an *array* variable (search slots are only scalar variables,
and array variables always have initializers, so an array-identifier
argument can never be a slot array), array literals with non-slot
elements (e.g. `all_different([x, 2])`), wrong arities — is simply
**not extracted**.  The extracted set is always a *subset* of the
model's constraints, so pruning with it can only remove assignments
that violate a constraint the model really imposes
(`extractConstraints_holds`, below); constraints of other shapes keep
being enforced by the full leaf check (the verified checker), which
stays the sole arbiter of satisfaction.  A weaker extraction costs
pruning power, never soundness.

## Soundness

`extractConstraints_holds` is the bridge lemma `prunedSearch_none`
(the pruning fixpoint layer) needs, stated at the store level: if a store
satisfies the model's constraint list under `fullInterp` (the
`SatisfiesDyn` constraint half, the very thing
`checkModelSolution_correct` certifies for accepted solutions) and the
store maps each slot name to the assignment's value at that slot
(the emitter round-trip obligation), then every extracted
`DomConstraint` is `SatisfiedBy` the assignment.

Connecting the store-value hypothesis to the leaf predicate — the
string round trip "the checker accepted the text emitted from `a`,
therefore the completed store assigns the slot names `a`'s values" —
is not proven here; the integrated UNSAT theorems carry that step as
an explicit licence.  (`completedStore_entry` in
`LeanFzn/FznSolution.lean` now gives the store side of that round trip:
the completed store maps every assigned name to its written value.) -/

/-- The slot positions of an `all_different` array: every element
    must be a slot name, in order. -/
def allDiffIndices : List String → List BasicExpr → Option (List Nat)
  | _, [] => some []
  | names, .ident x :: rest =>
      match nameIndex names x.name with
      | some i => (allDiffIndices names rest).map (fun is => i :: is)
      | none => none
  | _, _ => none

/-- The integer coefficients of a `par` array literal of integers:
    every element must be an integer literal, in order. -/
def linCoeffs : ArrayLiteral → Option (List Int)
  | [] => some []
  | .lit (.int k) :: rest => (linCoeffs rest).map (fun ks => k :: ks)
  | _ :: _ => none

/-- The slot positions of a linear constraint's variable array: every
    element must be a slot name, in order. -/
def linIndices : List String → ArrayLiteral → Option (List Nat)
  | _, [] => some []
  | names, .ident x :: rest =>
      match nameIndex names x.name with
      | some i => (linIndices names rest).map (fun is => i :: is)
      | none => none
  | _, _ => none

/-- The integer literals of an `array_int_element` constant array:
    every element must be an integer literal, in order. -/
def intLits : ArrayLiteral → Option (List Int)
  | [] => some []
  | .lit (.int k) :: rest => (intLits rest).map (fun ks => k :: ks)
  | _ :: _ => none

/-- The general integer operand of an `int_max` / `int_min` / `int_div` /
    `int_mod` argument (PLAN C6): a slot name resolves to its position,
    an integer literal to itself. -/
def intArgOf (names : List String) : BasicExpr → Option DomIntArg
  | .ident x => (nameIndex names x.name).map DomIntArg.slot
  | .lit (.int k) => some (.lit k)
  | _ => none

/-- The slot-indexed reading of one model constraint, if its shape is
    one the propagators understand (see the module table).  `names`
    are the search-slot names; the returned positions index
    them. -/
def extractConstraint (names : List String) (c : ConstraintItem) : Option DomConstraint :=
  match c.name.name with
  | "int_eq" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some j => some (.eqSlot i j)
          | _, _ => none
      | [.basic (.ident x), .basic (.lit (.int k))] =>
          (nameIndex names x.name).map (fun i => .constEq i (.int k))
      | [.basic (.lit (.int k)), .basic (.ident y)] =>
          (nameIndex names y.name).map (fun i => .constEq i (.int k))
      | _ => none
  | "int_ne" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some j => some (.neSlot i j)
          | _, _ => none
      | _ => none
  | "int_le" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some j => some (.leSlot i j)
          | _, _ => none
      | [.basic (.ident x), .basic (.lit (.int k))] =>
          (nameIndex names x.name).map (fun i => .leConstHi i k)
      | [.basic (.lit (.int k)), .basic (.ident y)] =>
          (nameIndex names y.name).map (fun i => .leConstLo i k)
      | _ => none
  | "int_plus" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names z.name with
          | some i, some j, some k => some (.plusSlot i j k)
          | _, _, _ => none
      | _ => none
  | "all_different" =>
      match c.args with
      | [.array elems] => (allDiffIndices names elems).map DomConstraint.allDiff
      | _ => none
  | "int_lin_eq" =>
      match c.args with
      | [.array ks, .array elems, .basic (.lit (.int b))] =>
          match linCoeffs ks, linIndices names elems with
          | some coeffs, some is =>
              if coeffs.length == is.length then some (.linEq coeffs is b) else none
          | _, _ => none
      | _ => none
  | "int_lin_le" =>
      match c.args with
      | [.array ks, .array elems, .basic (.lit (.int b))] =>
          match linCoeffs ks, linIndices names elems with
          | some coeffs, some is =>
              if coeffs.length == is.length then some (.linLe coeffs is b) else none
          | _, _ => none
      | _ => none
  | "int_times" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names z.name with
          | some i, some j, some k => some (.timesSlot i j k)
          | _, _, _ => none
      | _ => none
  | "int_min" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names z.name with
          | some i, some j, some k => some (.minSlot i j k)
          | _, _, _ => none
      | [.basic a₀, .basic a₁, .basic a₂] =>
          match intArgOf names a₀, intArgOf names a₁, intArgOf names a₂ with
          | some o₀, some o₁, some o₂ => some (.minPair o₀ o₁ o₂)
          | _, _, _ => none
      | _ => none
  | "int_max" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names z.name with
          | some i, some j, some k => some (.maxSlot i j k)
          | _, _, _ => none
      | [.basic a₀, .basic a₁, .basic a₂] =>
          match intArgOf names a₀, intArgOf names a₁, intArgOf names a₂ with
          | some o₀, some o₁, some o₂ => some (.maxPair o₀ o₁ o₂)
          | _, _, _ => none
      | _ => none
  | "int_abs" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some k => some (.absSlot i k)
          | _, _ => none
      | _ => none
  | "int_lt" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some j => some (.ltSlot i j)
          | _, _ => none
      | [.basic (.ident x), .basic (.lit (.int k))] =>
          (nameIndex names x.name).map (fun i => .ltConstHi i k)
      | [.basic (.lit (.int k)), .basic (.ident y)] =>
          (nameIndex names y.name).map (fun i => .ltConstLo i k)
      | _ => none
  | "bool_not" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some j => some (.boolNotSlot i j)
          | _, _ => none
      | _ => none
  | "bool_and" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names z.name with
          | some i, some j, some k => some (.boolAndSlot i j k)
          | _, _, _ => none
      | _ => none
  | "bool_or" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names z.name with
          | some i, some j, some k => some (.boolOrSlot i j k)
          | _, _, _ => none
      | _ => none
  | "int_lin_ne" =>
      match c.args with
      | [.array ks, .array elems, .basic (.lit (.int b))] =>
          match linCoeffs ks, linIndices names elems with
          | some coeffs, some is =>
              if coeffs.length == is.length then some (.linNe coeffs is b) else none
          | _, _ => none
      | _ => none
  | "bool_clause" =>
      match c.args with
      | [.array elems1, .array elems2] =>
          match linIndices names elems1, linIndices names elems2 with
          | some ps, some ns => some (.boolClauseSlot ps ns)
          | _, _ => none
      | _ => none
  | "array_bool_and" =>
      match c.args with
      | [.array elems, .basic (.ident r)] =>
          match linIndices names elems, nameIndex names r.name with
          | some is, some k => some (.arrayBoolAndSlot is k)
          | _, _ => none
      | _ => none
  | "bool2int" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some k => some (.bool2intSlot i k)
          | _, _ => none
      | _ => none
  | "bool_eq" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y)] =>
          match nameIndex names x.name, nameIndex names y.name with
          | some i, some j => some (.boolEqSlot i j)
          | _, _ => none
      | _ => none
  | "array_int_element" =>
      match c.args with
      | [.basic (.ident x), .array elems, .basic (.ident y)] =>
          match intLits elems, nameIndex names x.name,
            nameIndex names y.name with
          | some xs, some i, some k => some (.arrayIntElementSlot xs i k)
          | _, _, _ => none
      | _ => none
  | "array_var_int_element" =>
      match c.args with
      | [.basic (.ident x), .array elems, .basic (.ident y)] =>
          match linIndices names elems, nameIndex names x.name,
            nameIndex names y.name with
          | some is, some i, some k => some (.arrayVarIntElementSlot is i k)
          | _, _, _ => none
      | _ => none
  | "array_var_bool_element" =>
      match c.args with
      | [.basic (.ident x), .array elems, .basic (.ident y)] =>
          match linIndices names elems, nameIndex names x.name,
            nameIndex names y.name with
          | some is, some i, some k => some (.arrayVarBoolElementSlot is i k)
          | _, _, _ => none
      | _ => none
  | "int_eq_reif" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident r)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names r.name with
          | some i, some j, some k => some (.eqReifSlot i j k)
          | _, _, _ => none
      | _ => none
  | "int_le_reif" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident r)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names r.name with
          | some i, some j, some k => some (.leReifSlot i j k)
          | _, _, _ => none
      | _ => none
  | "int_ne_reif" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident r)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names r.name with
          | some i, some j, some k => some (.neReifSlot i j k)
          | _, _, _ => none
      | _ => none
  | "int_lin_eq_reif" =>
      match c.args with
      | [.array ks, .array elems, .basic (.lit (.int b)),
          .basic (.ident r)] =>
          match linCoeffs ks, linIndices names elems,
            nameIndex names r.name with
          | some coeffs, some is, some k =>
              if coeffs.length == is.length then
                some (.linEqReif coeffs is b k) else none
          | _, _, _ => none
      | _ => none
  | "int_lin_le_reif" =>
      match c.args with
      | [.array ks, .array elems, .basic (.lit (.int b)),
          .basic (.ident r)] =>
          match linCoeffs ks, linIndices names elems,
            nameIndex names r.name with
          | some coeffs, some is, some k =>
              if coeffs.length == is.length then
                some (.linLeReif coeffs is b k) else none
          | _, _, _ => none
      | _ => none
  | "int_lin_ne_reif" =>
      match c.args with
      | [.array ks, .array elems, .basic (.lit (.int b)),
          .basic (.ident r)] =>
          match linCoeffs ks, linIndices names elems,
            nameIndex names r.name with
          | some coeffs, some is, some k =>
              if coeffs.length == is.length then
                some (.linNeReif coeffs is b k) else none
          | _, _, _ => none
      | _ => none
  | "int_div" =>
      match c.args with
      | [.basic a₀, .basic a₁, .basic a₂] =>
          match intArgOf names a₀, intArgOf names a₁, intArgOf names a₂ with
          | some o₀, some o₁, some o₂ => some (.divGen o₀ o₁ o₂)
          | _, _, _ => none
      | _ => none
  | "int_mod" =>
      match c.args with
      | [.basic a₀, .basic a₁, .basic a₂] =>
          match intArgOf names a₀, intArgOf names a₁, intArgOf names a₂ with
          | some o₀, some o₁, some o₂ => some (.modGen o₀ o₁ o₂)
          | _, _, _ => none
      | _ => none
  | "array_int_maximum" =>
      match c.args with
      | [.basic (.ident x), .array elems] =>
          match nameIndex names x.name, linIndices names elems with
          | some k, some is =>
              some (.maxGen (is.map DomIntArg.slot) (.slot k))
          | _, _ => none
      | _ => none
  | "array_int_minimum" =>
      match c.args with
      | [.basic (.ident x), .array elems] =>
          match nameIndex names x.name, linIndices names elems with
          | some k, some is =>
              some (.minGen (is.map DomIntArg.slot) (.slot k))
          | _, _ => none
      | _ => none
  | _ => none

/-! ## The extracted list -/

/-- **The propagation set of a model**: every constraint of an
    extractable shape, translated to slot positions against the
    model's search slots (`slotsChecked` — the same gate
    `solveModel` uses, so the indices align with the searched
    domains).  A failed slot extraction makes the constraint set
    unextractable (reported, never guessed); constraints of other
    shapes are skipped (the leaf check still enforces them). -/
def extractConstraints (m : Model) : Except String (List DomConstraint) := do
  let slots ← slotsChecked m
  let names := slots.map Prod.fst
  return m.constraints.filterMap (extractConstraint names)

/-- The extracted constraint set, as an empty list when the model is
    outside the searched fragment.  Only for theorem statements and
    callers that treat a failed extraction as "no propagation". -/
def extractDomConstraints (m : Model) : List DomConstraint :=
  (extractConstraints m).toOption.getD []

/-! ## Soundness of the extraction

One lemma per predicate name, then the generic fold over the model's
constraint list.  Each name lemma inverts `ConstraintItem.Holds
fullInterp store` for the matched argument shape and concludes the
slot values relate the way the `DomConstraint` demands.
-/

section HoldsBridge

/-- `fullInterp` delegates to `stdInterp` on the three names of the
    first extraction round. -/
theorem fullInterp_of_extracted (n : String)
    (hn : n = "int_eq" ∨ n = "int_ne" ∨ n = "int_le") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The same bridge for the two further standard names extracted in
    this round (`int_plus`, `all_different`). -/
theorem fullInterp_of_extracted' (n : String)
    (hn : n = "int_plus" ∨ n = "all_different" ∨ n = "int_lin_eq"
      ∨ n = "int_lin_le") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The same bridge for the names of the propagator-extension round
    (`int_times`, `int_min`, `int_max`, `int_abs`, `int_lt`,
    `bool_not`, `bool_and`, `bool_or`). -/
theorem fullInterp_of_extracted'' (n : String)
    (hn : n = "int_times" ∨ n = "int_min" ∨ n = "int_max" ∨ n = "int_abs"
      ∨ n = "int_lt" ∨ n = "bool_not" ∨ n = "bool_and" ∨ n = "bool_or") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The same bridge for `int_lin_ne` (C1). -/
theorem fullInterp_of_extracted_linNe (n : String) (hn : n = "int_lin_ne") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  subst hn
  simp only [fullInterp]
  rw [if_neg (by decide)]

/-- The same bridge for `bool_clause` (C2). -/
theorem fullInterp_of_extracted_boolClause (n : String)
    (hn : n = "bool_clause") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  subst hn
  simp only [fullInterp]
  rw [if_neg (by decide)]

/-- The same bridge for the C3 Boolean families (`array_bool_and`,
    `bool2int`, `bool_eq`). -/
theorem fullInterp_of_extracted_boolArr (n : String)
    (hn : n = "array_bool_and" ∨ n = "bool2int" ∨ n = "bool_eq") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The same bridge for the C4 element families (`array_int_element`,
    `array_var_int_element`, `array_var_bool_element`). -/
theorem fullInterp_of_extracted_elem (n : String)
    (hn : n = "array_int_element" ∨ n = "array_var_int_element"
      ∨ n = "array_var_bool_element") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The same bridge for the C5 reified families (`int_eq_reif`,
    `int_le_reif`, `int_ne_reif`, `int_lin_eq_reif`, `int_lin_le_reif`,
    `int_lin_ne_reif`). -/
theorem fullInterp_of_extracted_reif (n : String)
    (hn : n = "int_eq_reif" ∨ n = "int_le_reif" ∨ n = "int_ne_reif"
      ∨ n = "int_lin_eq_reif" ∨ n = "int_lin_le_reif"
      ∨ n = "int_lin_ne_reif") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The same bridge for the C6 general-arithmetic families (`int_div`,
    `int_mod`) and array maximum/minimum forms (`array_int_maximum`,
    `array_int_minimum`); `int_max`/`int_min` are covered by
    `fullInterp_of_extracted''`. -/
theorem fullInterp_of_extracted_arith (n : String)
    (hn : n = "int_div" ∨ n = "int_mod" ∨ n = "array_int_maximum"
      ∨ n = "array_int_minimum") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- An in-bounds bang read is the option read (the `getElem_as_some`
    form of `Compiler/Proofs/CompileCore`, base-layer copy). -/
theorem getElem_bang_some {a : List Value} {i : Nat} (h : i < a.length) :
    a[i]? = some a[i]! := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- A slot list's bang-read `eqB` disjunction agrees with the
    option-read `slotIsBoolB` disjunction, at in-bounds slots. -/
theorem bang_any_eqB_iff_slotIsBoolB {a : List Value} {is : List Nat}
    {b : Bool} (hin : ∀ i ∈ is, i < a.length) :
    ((is.map (fun i => a[i]!)).any (fun v => v.eqB (.bool b)) = true) ↔
      (is.any (fun i => slotIsBoolB a i b) = true) := by
  rw [List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨v, hv, hvb⟩
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    refine ⟨i, hi, ?_⟩
    unfold slotIsBoolB
    rw [getElem_bang_some (hin i hi)]
    exact hvb
  · rintro ⟨i, hi, hib⟩
    refine ⟨a[i]!, List.mem_map_of_mem (f := fun i => a[i]!) hi, ?_⟩
    unfold slotIsBoolB at hib
    rw [getElem_bang_some (hin i hi)] at hib
    exact hib

/-- The interpretation of a holding constraint is about its own
    name: transport `hinterp` to the spelled-out name. -/
theorem interp_of_hname {c : ConstraintItem}
    {n : String} (hname : c.name.name = n) {args : List Value}
    (hinterp : fullInterp c.name args) :
    fullInterp (Ident.mk n) args := by
  have hc : c.name = Ident.mk n := by
    cases hc : c.name with
    | mk m =>
        rw [hc] at hname
        simp only at hname
        rw [← hname]
  rw [hc] at hinterp
  exact hinterp

/-- Inversion of argument evaluation for two identifier arguments: both
    store lookups succeed and the evaluated list is the two values. -/
theorem mapM_two_ident {store : Store} {c : ConstraintItem}
    {x y : Ident} {args : List Value}
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vx vy, store x = some vx ∧ store y = some vy ∧ args = [vx, vy] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
  cases hsx : store x with
  | none => rw [hsx] at hmap; simp at hmap
  | some vx =>
      rw [hsx] at hmap
      cases hsy : store y with
      | none => rw [hsy] at hmap; simp at hmap
      | some vy =>
          rw [hsy] at hmap
          exact ⟨vx, vy, rfl, rfl, by simpa using hmap.symm⟩

/-- Inversion of argument evaluation for three identifier arguments. -/
theorem mapM_three_ident {store : Store} {c : ConstraintItem}
    {x y z : Ident} {args : List Value}
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.ident z)])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vx vy vz, store x = some vx ∧ store y = some vy ∧ store z = some vz ∧
      args = [vx, vy, vz] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
  cases hsx : store x with
  | none => rw [hsx] at hmap; simp at hmap
  | some vx =>
      rw [hsx] at hmap
      cases hsy : store y with
      | none => rw [hsy] at hmap; simp at hmap
      | some vy =>
          rw [hsy] at hmap
          cases hsz : store z with
          | none => rw [hsz] at hmap; simp at hmap
          | some vz =>
              rw [hsz] at hmap
              exact ⟨vx, vy, vz, rfl, rfl, rfl, by simpa using hmap.symm⟩

/-- Inversion of argument evaluation for an identifier and an integer
    literal. -/
theorem mapM_two_const {store : Store} {c : ConstraintItem}
    {x : Ident} {k : Int} {args : List Value}
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k))])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vx, store x = some vx ∧ args = [vx, .int k] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval,
    BasicLiteral.denote] at hmap
  cases hsx : store x with
  | none => rw [hsx] at hmap; simp at hmap
  | some vx =>
      rw [hsx] at hmap
      exact ⟨vx, rfl, by simpa using hmap.symm⟩

/-- Inversion of argument evaluation for an integer literal and an
    identifier. -/
theorem mapM_two_const' {store : Store} {c : ConstraintItem}
    {y : Ident} {k : Int} {args : List Value}
    (hargs : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident y)])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vy, store y = some vy ∧ args = [.int k, vy] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval,
    BasicLiteral.denote] at hmap
  cases hsy : store y with
  | none => rw [hsy] at hmap; simp at hmap
  | some vy =>
      rw [hsy] at hmap
      exact ⟨vy, rfl, by simpa using hmap.symm⟩

/-- Inversion of argument evaluation for an array argument followed by
    an identifier argument. -/
theorem mapM_arr_ident {store : Store} {c : ConstraintItem}
    {elems : ArrayLiteral} {r : Ident} {args : List Value}
    (hargs : c.args = [Expr.array elems, Expr.basic (.ident r)])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vs vr, elems.mapM (BasicExpr.eval store) = some vs ∧
      store r = some vr ∧ args = [.array vs, vr] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
  cases h1 : elems.mapM (BasicExpr.eval store) with
  | none => rw [h1] at hmap; simp at hmap
  | some vs =>
      rw [h1] at hmap
      cases h2 : store r with
      | none => rw [h2] at hmap; simp at hmap
      | some vr =>
          rw [h2] at hmap
          exact ⟨vs, vr, rfl, rfl, by simpa using hmap.symm⟩

/-- Inversion of argument evaluation for an identifier, an array, and an
    identifier argument. -/
theorem mapM_ident_arr_ident {store : Store} {c : ConstraintItem}
    {x y : Ident} {elems : ArrayLiteral} {args : List Value}
    (hargs : c.args = [Expr.basic (.ident x), Expr.array elems,
        Expr.basic (.ident y)])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vx vs vy, store x = some vx ∧
      elems.mapM (BasicExpr.eval store) = some vs ∧
      store y = some vy ∧ args = [vx, .array vs, vy] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
  cases h1 : store x with
  | none => rw [h1] at hmap; simp at hmap
  | some vx =>
      rw [h1] at hmap
      cases h2 : elems.mapM (BasicExpr.eval store) with
      | none => rw [h2] at hmap; simp at hmap
      | some vs =>
          rw [h2] at hmap
          cases h3 : store y with
          | none => rw [h3] at hmap; simp at hmap
          | some vy =>
              rw [h3] at hmap
              exact ⟨vx, vs, vy, rfl, rfl, rfl, by simpa using hmap.symm⟩

/-- Inversion of `Holds` for `int_eq(slot, slot)`: the store's values
    at the two names are equal. -/
theorem holds_int_eq_slot {store : Store} {c : ConstraintItem}
    {x y : Ident}
    (hname : c.name.name = "int_eq")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ vx vy, store x = some vx ∧ store y = some vy ∧ vx = vy := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_eq") [vx, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted "int_eq" (Or.inl rfl)] at h1
  have hmatch : (match [vx, vy] with
    | [.int a, .int b] => a = b
    | _ => False) := h1
  cases vx with
  | int p =>
      cases vy with
      | int q => exact ⟨.int p, .int q, hsx, hsy, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_eq(slot, literal)`: the store's
    value at the name is the literal. -/
theorem holds_int_eq_const {store : Store} {c : ConstraintItem}
    {x : Ident} {k : Int}
    (hname : c.name.name = "int_eq")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    store x = some (.int k) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, hsx, hargsv⟩ := mapM_two_const hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_eq") [vx, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted "int_eq" (Or.inl rfl)] at h1
  have hmatch : (match [vx, .int k] with
    | [.int a, .int b] => a = b
    | _ => False) := h1
  cases vx with
  | int p =>
      have hpk : p = k := by simpa using hmatch
      rw [hpk] at hsx
      exact hsx
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_eq(literal, slot)`: symmetric to
    `holds_int_eq_const`. -/
theorem holds_int_eq_const' {store : Store} {c : ConstraintItem}
    {y : Ident} {k : Int}
    (hname : c.name.name = "int_eq")
    (hargs : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    store y = some (.int k) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vy, hsy, hargsv⟩ := mapM_two_const' hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_eq") [.int k, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted "int_eq" (Or.inl rfl)] at h1
  have hmatch : (match [.int k, vy] with
    | [.int a, .int b] => a = b
    | _ => False) := h1
  cases vy with
  | int q =>
      have hqk : k = q := by simpa using hmatch
      rw [← hqk] at hsy
      exact hsy
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_ne(slot, slot)`: the store's values
    at the two names differ. -/
theorem holds_int_ne_slot {store : Store} {c : ConstraintItem}
    {x y : Ident}
    (hname : c.name.name = "int_ne")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ vx vy, store x = some vx ∧ store y = some vy ∧ vx ≠ vy := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_ne") [vx, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted "int_ne" (Or.inr (Or.inl rfl))] at h1
  have hmatch : (match [vx, vy] with
    | [.int a, .int b] => a ≠ b
    | _ => False) := h1
  cases vx with
  | int p =>
      cases vy with
      | int q => exact ⟨.int p, .int q, hsx, hsy, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_le(slot, slot)`: the store's values
    at the two names are ordered. -/
theorem holds_int_le_slot {store : Store} {c : ConstraintItem}
    {x y : Ident}
    (hname : c.name.name = "int_le")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.int p) ∧ store y = some (.int q) ∧ p ≤ q := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_le") [vx, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted "int_le" (Or.inr (Or.inr rfl))] at h1
  have hmatch : (match [vx, vy] with
    | [.int a, .int b] => a ≤ b
    | _ => False) := h1
  cases vx with
  | int p =>
      cases vy with
      | int q => exact ⟨p, q, hsx, hsy, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_le(slot, literal)`: the store's
    value at the name is an integer at most the literal. -/
theorem holds_int_le_const {store : Store} {c : ConstraintItem}
    {x : Ident} {k : Int}
    (hname : c.name.name = "int_le")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ p ≤ k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, hsx, hargsv⟩ := mapM_two_const hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_le") [vx, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted "int_le" (Or.inr (Or.inr rfl))] at h1
  have hmatch : (match [vx, .int k] with
    | [.int a, .int b] => a ≤ b
    | _ => False) := h1
  cases vx with
  | int p => exact ⟨p, hsx, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_le(literal, slot)`: the store's
    value at the name is an integer at least the literal. -/
theorem holds_int_le_const' {store : Store} {c : ConstraintItem}
    {y : Ident} {k : Int}
    (hname : c.name.name = "int_le")
    (hargs : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k ≤ p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vy, hsy, hargsv⟩ := mapM_two_const' hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_le") [.int k, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted "int_le" (Or.inr (Or.inr rfl))] at h1
  have hmatch : (match [.int k, vy] with
    | [.int a, .int b] => a ≤ b
    | _ => False) := h1
  cases vy with
  | int q => exact ⟨q, hsy, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a three-slot `int_plus`: the store's
    values at the three names are integers with the first two
    summing to the third. -/
theorem holds_int_plus_slot {store : Store} {c : ConstraintItem}
    {x y z : Ident}
    (hname : c.name.name = "int_plus")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.ident z)])
    (h : c.Holds fullInterp store) :
    ∃ p q r, store x = some (.int p) ∧ store y = some (.int q) ∧
      store z = some (.int r) ∧ p + q = r := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, vz, hsx, hsy, hsz, hargsv⟩ :=
    mapM_three_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_plus") [vx, vy, vz] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted' "int_plus" (Or.inl rfl)] at h1
  have hmatch : (match [vx, vy, vz] with
    | [.int a, .int b, .int w] => a + b = w
    | _ => False) := h1
  cases vx with
  | int p =>
      cases vy with
      | int q =>
          cases vz with
          | int r => exact ⟨p, q, r, hsx, hsy, hsz, by simpa using hmatch⟩
          | bool w => exact absurd hmatch (by simp)
          | setOfInt w => exact absurd hmatch (by simp)
          | array w => exact absurd hmatch (by simp)
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a three-slot arithmetic constraint
    (`int_times` / `int_min` / `int_max`): the store's values at the
    three names are integers combined by the operation. -/
theorem holds_int_ternary_slot
    (op : String)
    (hop : Int → Int → Int)
    (hop8 : op = "int_times" ∨ op = "int_min" ∨ op = "int_max" ∨ op = "int_abs"
      ∨ op = "int_lt" ∨ op = "bool_not" ∨ op = "bool_and" ∨ op = "bool_or")
    (hsem : ∀ args : List Value,
      stdInterp (Ident.mk op) args =
        (match args with
        | [.int a, .int b, .int w] => w = hop a b
        | _ => False))
    {store : Store} {c : ConstraintItem} {x y z : Ident}
    (hname : c.name.name = op)
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.ident z)])
    (h : c.Holds fullInterp store) :
    ∃ p q r, store x = some (.int p) ∧ store y = some (.int q) ∧
      store z = some (.int r) ∧ hop p q = r := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, vz, hsx, hsy, hsz, hargsv⟩ :=
    mapM_three_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk op) [vx, vy, vz] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted'' op hop8] at h1
  have hmatch : (match [vx, vy, vz] with
    | [.int a, .int b, .int w] => w = hop a b
    | _ => False) := by
    have hsem' := hsem [vx, vy, vz]
    rw [hsem'] at h1
    exact h1
  cases vx with
  | int p =>
      cases vy with
      | int q =>
          cases vz with
          | int r =>
              have hopr : hop p q = r := by
                have hr : r = hop p q := by simpa using hmatch
                exact hr.symm
              exact ⟨p, q, r, hsx, hsy, hsz, hopr⟩
          | bool w => exact absurd hmatch (by simp)
          | setOfInt w => exact absurd hmatch (by simp)
          | array w => exact absurd hmatch (by simp)
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a two-slot `int_abs`: the store's values
    at the two names are integers with the second the absolute value
    of the first. -/
theorem holds_int_abs_slot {store : Store} {c : ConstraintItem}
    {x y : Ident}
    (hname : c.name.name = "int_abs")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p r, store x = some (.int p) ∧ store y = some (.int r) ∧
      (if p < 0 then -p else p) = r := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_abs") [vx, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted'' "int_abs"
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))] at h1
  have hmatch : (match [vx, vy] with
    | [.int a, .int b] => b = if a < 0 then -a else a
    | _ => False) := h1
  cases vx with
  | int p =>
      cases vy with
      | int r =>
          have habs : (if p < 0 then -p else p) = r := by
            have hr : r = if p < 0 then -p else p := by simpa using hmatch
            exact hr.symm
          exact ⟨p, r, hsx, hsy, habs⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a two-slot `int_lt`: the store's values at
    the two names are integers with the first strictly below the
    second. -/
theorem holds_int_lt_slot {store : Store} {c : ConstraintItem}
    {x y : Ident}
    (hname : c.name.name = "int_lt")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.int p) ∧ store y = some (.int q) ∧ p < q := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lt") [vx, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted'' "int_lt"
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))] at h1
  have hmatch : (match [vx, vy] with
    | [.int a, .int b] => a < b
    | _ => False) := h1
  cases vx with
  | int p =>
      cases vy with
      | int q => exact ⟨p, q, hsx, hsy, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_lt(slot, literal)`: the store's
    value at the name is an integer strictly below the literal. -/
theorem holds_int_lt_const {store : Store} {c : ConstraintItem}
    {x : Ident} {k : Int}
    (hname : c.name.name = "int_lt")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ p < k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, hsx, hargsv⟩ := mapM_two_const hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lt") [vx, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted'' "int_lt"
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))] at h1
  have hmatch : (match [vx, .int k] with
    | [.int a, .int b] => a < b
    | _ => False) := h1
  cases vx with
  | int p => exact ⟨p, hsx, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_lt(literal, slot)`: the store's
    value at the name is an integer strictly above the literal. -/
theorem holds_int_lt_const' {store : Store} {c : ConstraintItem}
    {y : Ident} {k : Int}
    (hname : c.name.name = "int_lt")
    (hargs : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k < p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vy, hsy, hargsv⟩ := mapM_two_const' hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lt") [.int k, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted'' "int_lt"
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))] at h1
  have hmatch : (match [.int k, vy] with
    | [.int a, .int b] => a < b
    | _ => False) := h1
  cases vy with
  | int q => exact ⟨q, hsy, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a two-slot `bool_not`: the store's values
    at the two names are opposite Booleans. -/
theorem holds_bool_not_slot {store : Store} {c : ConstraintItem}
    {x y : Ident}
    (hname : c.name.name = "bool_not")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.bool p) ∧ store y = some (.bool q) ∧
      q = !p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "bool_not") [vx, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted'' "bool_not"
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))] at h1
  have hmatch : (match [vx, vy] with
    | [.bool a, .bool b] => b = !a
    | _ => False) := h1
  cases vx with
  | bool p =>
      cases vy with
      | bool q => exact ⟨p, q, hsx, hsy, by simpa using hmatch⟩
      | int w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | int w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a three-slot Boolean connective
    (`bool_and` / `bool_or`): the store's values at the three names
    are Booleans combined by the operation. -/
theorem holds_bool_ternary_slot
    (op : String) (f : Bool → Bool → Bool)
    (hop8 : op = "int_times" ∨ op = "int_min" ∨ op = "int_max" ∨ op = "int_abs"
      ∨ op = "int_lt" ∨ op = "bool_not" ∨ op = "bool_and" ∨ op = "bool_or")
    (hsem : ∀ args : List Value,
      stdInterp (Ident.mk op) args =
        (match args with
        | [.bool a, .bool b, .bool w] => w = f a b
        | _ => False))
    {store : Store} {c : ConstraintItem} {x y z : Ident}
    (hname : c.name.name = op)
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.ident z)])
    (h : c.Holds fullInterp store) :
    ∃ p q r, store x = some (.bool p) ∧ store y = some (.bool q) ∧
      store z = some (.bool r) ∧ f p q = r := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, vz, hsx, hsy, hsz, hargsv⟩ :=
    mapM_three_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk op) [vx, vy, vz] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted'' op hop8] at h1
  have hmatch : (match [vx, vy, vz] with
    | [.bool a, .bool b, .bool w] => w = f a b
    | _ => False) := by
    have hsem' := hsem [vx, vy, vz]
    rw [hsem'] at h1
    exact h1
  cases vx with
  | bool p =>
      cases vy with
      | bool q =>
          cases vz with
          | bool r =>
              have hfr : f p q = r := by
                have hr : r = f p q := by simpa using hmatch
                exact hr.symm
              exact ⟨p, q, r, hsx, hsy, hsz, hfr⟩
          | int w => exact absurd hmatch (by simp)
          | setOfInt w => exact absurd hmatch (by simp)
          | array w => exact absurd hmatch (by simp)
      | int w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | int w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of argument evaluation for the linear shape: two array
    arguments evaluate to their element-value lists and the literal to
    its integer. -/
theorem mapM_lin {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int} {args : List Value}
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k))])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vs1 vs2, ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      args = [.array vs1, .array vs2, .int k] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval,
    BasicLiteral.denote] at hmap
  cases h1 : ks.mapM (BasicExpr.eval store) with
  | none => rw [h1] at hmap; simp at hmap
  | some vs1 =>
      rw [h1] at hmap
      cases h2 : elems.mapM (BasicExpr.eval store) with
      | none => rw [h2] at hmap; simp at hmap
      | some vs2 =>
          rw [h2] at hmap
          exact ⟨vs1, vs2, rfl, rfl, by simpa using hmap.symm⟩

/-- Inversion of argument evaluation for two array arguments, an
    integer literal and an identifier (the reified linear shape
    `int_lin_*_reif(coeffs, xs, b, r)`). -/
theorem mapM_lin_reif {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int} {r : Ident} {args : List Value}
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k)), Expr.basic (.ident r)])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vs1 vs2 vr, ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      store r = some vr ∧ args = [.array vs1, .array vs2, .int k, vr] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval,
    BasicLiteral.denote] at hmap
  cases h1 : ks.mapM (BasicExpr.eval store) with
  | none => rw [h1] at hmap; simp at hmap
  | some vs1 =>
      rw [h1] at hmap
      cases h2 : elems.mapM (BasicExpr.eval store) with
      | none => rw [h2] at hmap; simp at hmap
      | some vs2 =>
          rw [h2] at hmap
          cases h3 : store r with
          | none => rw [h3] at hmap; simp at hmap
          | some vr =>
              rw [h3] at hmap
              exact ⟨vs1, vs2, vr, rfl, rfl, rfl, by simpa using hmap.symm⟩

/-- Inversion of `Holds` for an `int_lin_eq` on slots. -/
theorem holds_int_lin_eq {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int}
    (hname : c.name.name = "int_lin_eq")
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ vs1 vs2, ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      dotProduct vs1 vs2 = some k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vs1, vs2, hvs1, hvs2, hargsv⟩ := mapM_lin hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lin_eq") [.array vs1, .array vs2, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted' "int_lin_eq" (Or.inr (Or.inr (Or.inl rfl)))] at h1
  exact ⟨vs1, vs2, hvs1, hvs2, h1⟩

/-- Inversion of `Holds` for an `int_lin_le` on slots. -/
theorem holds_int_lin_le {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int}
    (hname : c.name.name = "int_lin_le")
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ vs1 vs2, ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      dotLe vs1 vs2 k = true := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vs1, vs2, hvs1, hvs2, hargsv⟩ := mapM_lin hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lin_le") [.array vs1, .array vs2, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted' "int_lin_le" (Or.inr (Or.inr (Or.inr rfl)))] at h1
  exact ⟨vs1, vs2, hvs1, hvs2, h1⟩

/-- Inversion of `Holds` for an `int_lin_ne` on slots. -/
theorem holds_int_lin_ne {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int}
    (hname : c.name.name = "int_lin_ne")
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ vs1 vs2, ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      dotNe vs1 vs2 k = true := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vs1, vs2, hvs1, hvs2, hargsv⟩ := mapM_lin hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lin_ne") [.array vs1, .array vs2, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_linNe "int_lin_ne" rfl] at h1
  exact ⟨vs1, vs2, hvs1, hvs2, h1⟩

/-- Inversion of `Holds` for an explicit-array `all_different`: the
    array's elements all evaluate, and the values are pairwise
    different. -/
theorem holds_all_different {store : Store} {c : ConstraintItem}
    {elems : ArrayLiteral}
    (hname : c.name.name = "all_different")
    (hargs : c.args = [Expr.array elems])
    (h : c.Holds fullInterp store) :
    ∃ vs, elems.mapM (BasicExpr.eval store) = some vs ∧
      valuesAllDifferent vs = true := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval] at hmap
  cases hev : elems.mapM (BasicExpr.eval store) with
  | none => rw [hev] at hmap; simp at hmap
  | some vs =>
      rw [hev] at hmap
      have hargsv : args = [.array vs] := by simpa using hmap.symm
      subst hargsv
      have h1' : fullInterp (Ident.mk "all_different") [.array vs] :=
        interp_of_hname hname hinterp
      rw [fullInterp_of_extracted' "all_different" (Or.inr (Or.inl rfl))] at h1'
      exact ⟨vs, rfl, h1'⟩

/-- Inversion of `Holds` for a `bool_clause` on two slot arrays: both
    arrays evaluate and the standard disjunction holds. -/
theorem holds_bool_clause {store : Store} {c : ConstraintItem}
    {elems1 elems2 : ArrayLiteral}
    (hname : c.name.name = "bool_clause")
    (hargs : c.args = [Expr.array elems1, Expr.array elems2])
    (h : c.Holds fullInterp store) :
    ∃ vs1 vs2, elems1.mapM (BasicExpr.eval store) = some vs1 ∧
      elems2.mapM (BasicExpr.eval store) = some vs2 ∧
      ((vs1.any (fun x => x.eqB (.bool true))) ||
        (vs2.any (fun y => y.eqB (.bool false)))) = true := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval] at hmap
  cases h1 : elems1.mapM (BasicExpr.eval store) with
  | none => rw [h1] at hmap; simp at hmap
  | some vs1 =>
      rw [h1] at hmap
      cases h2 : elems2.mapM (BasicExpr.eval store) with
      | none => rw [h2] at hmap; simp at hmap
      | some vs2 =>
          rw [h2] at hmap
          have hargsv : args = [.array vs1, .array vs2] :=
            by simpa using hmap.symm
          subst hargsv
          have h1' : fullInterp (Ident.mk "bool_clause")
              [.array vs1, .array vs2] :=
            interp_of_hname hname hinterp
          rw [fullInterp_of_extracted_boolClause "bool_clause" rfl] at h1'
          exact ⟨vs1, vs2, rfl, rfl, h1'⟩

/-- A slot list's bang-read `eqB` conjunction agrees with the
    option-read `slotIsBoolB` conjunction, at in-bounds slots (the
    `all`-twin of `bang_any_eqB_iff_slotIsBoolB`). -/
theorem bang_all_eqB_iff_slotIsBoolB {a : List Value} {is : List Nat}
    {b : Bool} (hin : ∀ i ∈ is, i < a.length) :
    (is.all (fun i => (a[i]!).eqB (.bool b)) = true) ↔
      (is.all (fun i => slotIsBoolB a i b) = true) := by
  rw [List.all_eq_true, List.all_eq_true]
  constructor
  · intro h i hi
    have h' := h i hi
    unfold slotIsBoolB
    rw [getElem_bang_some (hin i hi)]
    exact h'
  · intro h i hi
    have h' := h i hi
    unfold slotIsBoolB at h'
    rw [getElem_bang_some (hin i hi)] at h'
    exact h'

/-- Inversion of `Holds` for an `array_bool_and` on a slot array and a
    slot target: the array evaluates and the target Boolean IS the
    `all` of the element read. -/
theorem holds_array_bool_and {store : Store} {c : ConstraintItem}
    {elems : ArrayLiteral} {r : Ident}
    (hname : c.name.name = "array_bool_and")
    (hargs : c.args = [Expr.array elems, Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ vs vr, elems.mapM (BasicExpr.eval store) = some vs ∧
      store r = some vr ∧
      vr = .bool (vs.all (fun x => x.eqB (.bool true))) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vs, vr, hvs, hsr, hargsv⟩ := mapM_arr_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "array_bool_and") [.array vs, vr] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_boolArr "array_bool_and" (Or.inl rfl)] at h1
  have hmatch : (match [.array vs, vr] with
    | [.array xs, .bool r] => r = (xs.all (fun x => x.eqB (.bool true)))
    | _ => False) := h1
  cases vr with
  | bool p => exact ⟨vs, .bool p, hvs, hsr, by simpa using hmatch⟩
  | int w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a `bool2int`: the store's Boolean source
    and integer target are related by the 0/1 view. -/
theorem holds_bool2int {store : Store} {c : ConstraintItem}
    {b : Ident} {i : Ident}
    (hname : c.name.name = "bool2int")
    (hargs : c.args = [Expr.basic (.ident b), Expr.basic (.ident i)])
    (h : c.Holds fullInterp store) :
    ∃ p k, store b = some (.bool p) ∧ store i = some (.int k) ∧
      k = (if p then 1 else 0) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vb, vi, hsb, hsi, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "bool2int") [vb, vi] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_boolArr "bool2int" (Or.inr (Or.inl rfl))] at h1
  have hmatch : (match [vb, vi] with
    | [.bool a, .int j] => j = (if a then 1 else 0)
    | _ => False) := h1
  cases vb with
  | bool p =>
      cases vi with
      | int k => exact ⟨p, k, hsb, hsi, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | int w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for a `bool_eq`: the store's values at the two
    names are equal Booleans. -/
theorem holds_bool_eq {store : Store} {c : ConstraintItem}
    {x y : Ident}
    (hname : c.name.name = "bool_eq")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.bool p) ∧ store y = some (.bool q) ∧
      p = q := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_two_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "bool_eq") [vx, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_boolArr "bool_eq" (Or.inr (Or.inr rfl))] at h1
  have hmatch : (match [vx, vy] with
    | [.bool a, .bool b] => a = b
    | _ => False) := h1
  cases vx with
  | bool p =>
      cases vy with
      | bool q => exact ⟨p, q, hsx, hsy, by simpa using hmatch⟩
      | int w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | int w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `int_eq_reif`: the store's two reads and
    the reification slot's Boolean satisfy the truth-value agreement
    `R ↔ x = y` of the source predicate. -/
theorem holds_int_eq_reif {store : Store} {c : ConstraintItem}
    {x y r : Ident}
    (hname : c.name.name = "int_eq_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ (p : Int) (q : Int) (rb : Bool),
      store x = some (.int p) ∧ store y = some (.int q) ∧
      store r = some (.bool rb) ∧ (rb = true ↔ p = q) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, vr, hsx, hsy, hsz, hargsv⟩ := mapM_three_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_eq_reif") [vx, vy, vr] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1
  cases vx with
  | int a =>
      cases vy with
      | int b =>
          cases vr with
          | bool rb =>
              exact ⟨a, b, rb, hsx, hsy, hsz,
                (reif_disj_iff (a = b) rb).mp h1⟩
          | int w => exfalso; exact h1.elim
          | setOfInt w => exfalso; exact h1.elim
          | array w => exfalso; exact h1.elim
      | bool w => exfalso; exact h1.elim
      | setOfInt w => exfalso; exact h1.elim
      | array w => exfalso; exact h1.elim
  | bool w => exfalso; exact h1.elim
  | setOfInt w => exfalso; exact h1.elim
  | array w => exfalso; exact h1.elim

/-- Inversion of `Holds` for `int_le_reif`: the truth-value agreement
    `R ↔ p ≤ q` of the source predicate. -/
theorem holds_int_le_reif {store : Store} {c : ConstraintItem}
    {x y r : Ident}
    (hname : c.name.name = "int_le_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ (p : Int) (q : Int) (rb : Bool),
      store x = some (.int p) ∧ store y = some (.int q) ∧
      store r = some (.bool rb) ∧ (rb = true ↔ p ≤ q) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, vr, hsx, hsy, hsz, hargsv⟩ := mapM_three_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_le_reif") [vx, vy, vr] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_reif "int_le_reif"
    (Or.inr (Or.inl rfl))] at h1
  cases vx with
  | int p =>
      cases vy with
      | int q =>
          cases vr with
          | bool rb =>
              have hdisj : (rb = true ∧ p ≤ q) ∨ (rb = false ∧ ¬ p ≤ q) := by
                rcases h1 with ⟨hrb, hle⟩ | ⟨hrb, hgt⟩
                · exact Or.inl ⟨hrb, hle⟩
                · exact Or.inr ⟨hrb, fun hle => by omega⟩
              exact ⟨p, q, rb, hsx, hsy, hsz,
                (reif_disj_iff (p ≤ q) rb).mp hdisj⟩
          | int w => exfalso; exact h1.elim
          | setOfInt w => exfalso; exact h1.elim
          | array w => exfalso; exact h1.elim
      | bool w => exfalso; exact h1.elim
      | setOfInt w => exfalso; exact h1.elim
      | array w => exfalso; exact h1.elim
  | bool w => exfalso; exact h1.elim
  | setOfInt w => exfalso; exact h1.elim
  | array w => exfalso; exact h1.elim

/-- Inversion of `Holds` for `int_ne_reif`: the truth-value agreement
    `R ↔ x ≠ y` of the source predicate. -/
theorem holds_int_ne_reif {store : Store} {c : ConstraintItem}
    {x y r : Ident}
    (hname : c.name.name = "int_ne_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ (p : Int) (q : Int) (rb : Bool),
      store x = some (.int p) ∧ store y = some (.int q) ∧
      store r = some (.bool rb) ∧ (rb = true ↔ p ≠ q) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vy, vr, hsx, hsy, hsz, hargsv⟩ := mapM_three_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_ne_reif") [vx, vy, vr] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_reif "int_ne_reif"
    (Or.inr (Or.inr (Or.inl rfl)))] at h1
  cases vx with
  | int a =>
      cases vy with
      | int b =>
          cases vr with
          | bool rb =>
              have hd : (rb = true ∧ a ≠ b) ∨ (rb = false ∧ a = b) := by
                rcases h1 with ⟨hrb, hne⟩ | ⟨hrb, heq⟩
                · exact Or.inl ⟨hrb, hne⟩
                · exact Or.inr ⟨hrb, heq⟩
              refine ⟨a, b, rb, hsx, hsy, hsz, ?_⟩
              rcases hd with ⟨hrb, hne⟩ | ⟨hrb, heq⟩
              · exact (reif_disj_iff (a ≠ b) rb).mp (Or.inl ⟨hrb, hne⟩)
              · exact (reif_disj_iff (a ≠ b) rb).mp
                  (Or.inr ⟨hrb, fun hne => hne heq⟩)
          | int w => exfalso; exact h1.elim
          | setOfInt w => exfalso; exact h1.elim
          | array w => exfalso; exact h1.elim
      | bool w => exfalso; exact h1.elim
      | setOfInt w => exfalso; exact h1.elim
      | array w => exfalso; exact h1.elim
  | bool w => exfalso; exact h1.elim
  | setOfInt w => exfalso; exact h1.elim
  | array w => exfalso; exact h1.elim

/-- Inversion of `Holds` for `int_lin_eq_reif`: the truth-value
    agreement `R ↔ dotProduct coeffs xs = some b`. -/
theorem holds_int_lin_eq_reif {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int} {r : Ident}
    (hname : c.name.name = "int_lin_eq_reif")
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k)), Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ (vs1 : List Value) (vs2 : List Value) (rb : Bool),
      ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      store r = some (.bool rb) ∧
      (rb = true ↔ dotProduct vs1 vs2 = some k) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vs1, vs2, vr, hvs1, hvs2, hsr, hargsv⟩ := mapM_lin_reif hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lin_eq_reif")
      [.array vs1, .array vs2, .int k, vr] := interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_reif "int_lin_eq_reif"
    (Or.inr (Or.inr (Or.inr (Or.inl rfl))))] at h1
  cases vr with
  | bool rb =>
      have hdisj : (rb = true ∧ dotProduct vs1 vs2 = some k) ∨
          (rb = false ∧ ¬ dotProduct vs1 vs2 = some k) := by
        rcases h1 with ⟨hrb, hdot⟩ | ⟨hrb, hdot⟩
        · exact Or.inl ⟨hrb, hdot⟩
        · exact Or.inr ⟨hrb, hdot⟩
      exact ⟨vs1, vs2, rb, hvs1, hvs2, hsr,
        (reif_disj_iff (dotProduct vs1 vs2 = some k) rb).mp hdisj⟩
  | int w => exfalso; exact h1.elim
  | setOfInt w => exfalso; exact h1.elim
  | array w => exfalso; exact h1.elim

/-- Inversion of `Holds` for `int_lin_le_reif`: the truth-value
    agreement `R ↔ dotLe coeffs xs b`. -/
theorem holds_int_lin_le_reif {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int} {r : Ident}
    (hname : c.name.name = "int_lin_le_reif")
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k)), Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ (vs1 : List Value) (vs2 : List Value) (rb : Bool),
      ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      store r = some (.bool rb) ∧
      (rb = true ↔ dotLe vs1 vs2 k = true) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vs1, vs2, vr, hvs1, hvs2, hsr, hargsv⟩ := mapM_lin_reif hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lin_le_reif")
      [.array vs1, .array vs2, .int k, vr] := interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_reif "int_lin_le_reif"
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))] at h1
  cases vr with
  | bool rb =>
      have hdisj : (rb = true ∧ dotLe vs1 vs2 k = true) ∨
          (rb = false ∧ ¬ dotLe vs1 vs2 k = true) := by
        rcases h1 with ⟨hrb, hle⟩ | ⟨hrb, hle⟩
        · exact Or.inl ⟨hrb, hle⟩
        · exact Or.inr ⟨hrb, fun htrue => by rw [hle] at htrue; exact absurd htrue (by simp)⟩
      exact ⟨vs1, vs2, rb, hvs1, hvs2, hsr,
        (reif_disj_iff (dotLe vs1 vs2 k = true) rb).mp hdisj⟩
  | int w => exfalso; exact h1.elim
  | setOfInt w => exfalso; exact h1.elim
  | array w => exfalso; exact h1.elim

/-- Inversion of `Holds` for `int_lin_ne_reif`: the truth-value
    agreement `R ↔ dotNe coeffs xs b`. -/
theorem holds_int_lin_ne_reif {store : Store} {c : ConstraintItem}
    {ks elems : ArrayLiteral} {k : Int} {r : Ident}
    (hname : c.name.name = "int_lin_ne_reif")
    (hargs : c.args = [Expr.array ks, Expr.array elems,
        Expr.basic (.lit (.int k)), Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ (vs1 : List Value) (vs2 : List Value) (rb : Bool),
      ks.mapM (BasicExpr.eval store) = some vs1 ∧
      elems.mapM (BasicExpr.eval store) = some vs2 ∧
      store r = some (.bool rb) ∧
      (rb = true ↔ dotNe vs1 vs2 k = true) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vs1, vs2, vr, hvs1, hvs2, hsr, hargsv⟩ := mapM_lin_reif hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_lin_ne_reif")
      [.array vs1, .array vs2, .int k, vr] := interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_reif "int_lin_ne_reif"
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))] at h1
  cases vr with
  | bool rb =>
      have hdisj : (rb = true ∧ dotNe vs1 vs2 k = true) ∨
          (rb = false ∧ ¬ dotNe vs1 vs2 k = true) := by
        rcases h1 with ⟨hrb, hne⟩ | ⟨hrb, hne⟩
        · exact Or.inl ⟨hrb, hne⟩
        · exact Or.inr ⟨hrb, fun htrue => by rw [hne] at htrue; exact absurd htrue (by simp)⟩
      exact ⟨vs1, vs2, rb, hvs1, hvs2, hsr,
        (reif_disj_iff (dotNe vs1 vs2 k = true) rb).mp hdisj⟩
  | int w => exfalso; exact h1.elim
  | setOfInt w => exfalso; exact h1.elim
  | array w => exfalso; exact h1.elim

/-- Inversion of `Holds` for an `array_int_element` over an explicit
    constant integer array: the store's values at the index and target
    names and the source interpretation's 1-based read relation. -/
theorem holds_array_int_element {store : Store} {c : ConstraintItem}
    {elems : ArrayLiteral} {x y : Ident}
    (hname : c.name.name = "array_int_element")
    (hargs : c.args = [Expr.basic (.ident x), Expr.array elems,
        Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ vs vx vy, elems.mapM (BasicExpr.eval store) = some vs ∧
      store x = some vx ∧ store y = some vy ∧
      (match [vx, .array vs, vy] with
        | [.int i, .array xs, .int e] => valuesGet1 xs i = some (.int e)
        | _ => False) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vs, vy, hsx, hvs, hsy, hargsv⟩ :=
    mapM_ident_arr_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "array_int_element") [vx, .array vs, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_elem "array_int_element" (Or.inl rfl)] at h1
  exact ⟨vs, vx, vy, hvs, hsx, hsy, h1⟩

/-- Inversion of `Holds` for an `array_var_int_element` over an
    explicit slot array. -/
theorem holds_array_var_int_element {store : Store} {c : ConstraintItem}
    {elems : ArrayLiteral} {x y : Ident}
    (hname : c.name.name = "array_var_int_element")
    (hargs : c.args = [Expr.basic (.ident x), Expr.array elems,
        Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ vs vx vy, elems.mapM (BasicExpr.eval store) = some vs ∧
      store x = some vx ∧ store y = some vy ∧
      (match [vx, .array vs, vy] with
        | [.int i, .array xs, .int e] => valuesGet1 xs i = some (.int e)
        | _ => False) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vs, vy, hsx, hvs, hsy, hargsv⟩ :=
    mapM_ident_arr_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "array_var_int_element")
      [vx, .array vs, vy] := interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_elem "array_var_int_element"
    (Or.inr (Or.inl rfl))] at h1
  exact ⟨vs, vx, vy, hvs, hsx, hsy, h1⟩

/-- Inversion of `Holds` for an `array_var_bool_element` over an
    explicit slot array. -/
theorem holds_array_var_bool_element {store : Store} {c : ConstraintItem}
    {elems : ArrayLiteral} {x y : Ident}
    (hname : c.name.name = "array_var_bool_element")
    (hargs : c.args = [Expr.basic (.ident x), Expr.array elems,
        Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ vs vx vy, elems.mapM (BasicExpr.eval store) = some vs ∧
      store x = some vx ∧ store y = some vy ∧
      (match [vx, .array vs, vy] with
        | [.int i, .array xs, .bool e] => valuesGet1 xs i = some (.bool e)
        | _ => False) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vs, vy, hsx, hvs, hsy, hargsv⟩ :=
    mapM_ident_arr_ident hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "array_var_bool_element")
      [vx, .array vs, vy] := interp_of_hname hname hinterp
  rw [fullInterp_of_extracted_elem "array_var_bool_element"
    (Or.inr (Or.inr rfl))] at h1
  exact ⟨vs, vx, vy, hvs, hsx, hsy, h1⟩

end HoldsBridge

/-- The evaluated values of a coefficient array that produced
    `coeffs` via `linCoeffs` are exactly `intVals coeffs`. -/
theorem linCoeffs_eval {store : Store} :
    ∀ (ks : ArrayLiteral) (coeffs : List Int),
    linCoeffs ks = some coeffs →
    ks.mapM (BasicExpr.eval store) = some (intVals coeffs) := by
  intro ks
  induction ks with
  | nil =>
      intro coeffs hcoeffs
      have hnil : linCoeffs [] = some [] := rfl
      rw [hnil] at hcoeffs
      have hnil' : coeffs = [] := (Option.some.inj hcoeffs).symm
      subst hnil'
      rfl
  | cons e es ih =>
      intro coeffs hcoeffs
      cases he : e with
      | lit l =>
          cases hl : l with
          | int k =>
              simp only [linCoeffs, he, hl] at hcoeffs
              cases hrest : linCoeffs es with
              | none => rw [hrest] at hcoeffs; exact absurd hcoeffs (by simp)
              | some rest =>
                  rw [hrest] at hcoeffs
                  have hcons : k :: rest = coeffs := Option.some.inj hcoeffs
                  subst hcons
                  simp only [List.mapM_cons, BasicExpr.eval,
                    BasicLiteral.denote]
                  rw [ih rest hrest]
                  rfl
          | bool b =>
              simp only [linCoeffs, he, hl] at hcoeffs
              exact absurd hcoeffs (by simp)
          | set sl =>
              simp only [linCoeffs, he, hl] at hcoeffs
              exact absurd hcoeffs (by simp)
      | ident x =>
          simp only [linCoeffs, he] at hcoeffs
          exact absurd hcoeffs (by simp)

/-- The evaluated values of a constant integer array that produced
    `xs` via `intLits` are exactly the integer views of `xs`. -/
theorem intLits_eval {store : Store} :
    ∀ (es : ArrayLiteral) (xs : List Int),
    intLits es = some xs →
    es.mapM (BasicExpr.eval store) = some (xs.map Value.int) := by
  intro es
  induction es with
  | nil =>
      intro xs h
      have hnil : intLits ([] : ArrayLiteral) = some [] := rfl
      rw [hnil] at h
      have hx : xs = [] := (Option.some.inj h).symm
      subst hx
      rfl
  | cons e es ih =>
      intro xs h
      cases he : e with
      | lit l =>
          cases hl : l with
          | int k =>
              simp only [intLits, he, hl] at h
              cases hrest : intLits es with
              | none => rw [hrest] at h; exact absurd h (by simp)
              | some rest =>
                  rw [hrest] at h
                  have hcons : k :: rest = xs := Option.some.inj h
                  subst hcons
                  simp only [List.mapM_cons, BasicExpr.eval,
                    BasicLiteral.denote]
                  rw [ih rest hrest]
                  rfl
          | bool b =>
              simp only [intLits, he, hl] at h
              exact absurd h (by simp)
          | set sl =>
              simp only [intLits, he, hl] at h
              exact absurd h (by simp)
      | ident x =>
          simp only [intLits, he] at h
          exact absurd h (by simp)

/-- Every position produced by `linIndices` is in bounds for
    `names` (the slot-name list it indexes). -/
theorem linIndices_lt {names : List String} :
    ∀ (elems : ArrayLiteral) (is : List Nat),
    linIndices names elems = some is →
    ∀ i, i ∈ is → i < names.length := by
  intro elems
  induction elems with
  | nil =>
      intro is hidx i hi
      have hnil : linIndices names [] = some [] := rfl
      rw [hnil] at hidx
      have his : is = [] := (Option.some.inj hidx).symm
      rw [his] at hi
      exact absurd hi (by simp)
  | cons e es ih =>
      intro is hidx i hi
      cases he : e with
      | lit l =>
          rw [he] at hidx
          exact absurd hidx (by simp [linIndices])
      | ident x =>
          rw [he] at hidx
          simp only [linIndices] at hidx
          cases hn : nameIndex names x.name with
          | none => rw [hn] at hidx; exact absurd hidx (by simp)
          | some n =>
              rw [hn] at hidx
              cases hrest : linIndices names es with
              | none => rw [hrest] at hidx; exact absurd hidx (by simp)
              | some rest =>
                  rw [hrest] at hidx
                  have his : is = n :: rest := by simpa using hidx.symm
                  rw [his] at hi
                  obtain ⟨hxlt, _⟩ := nameIndex_some names x.name n hn
                  cases hi with
                  | head => exact hxlt
                  | tail _ hitl => exact ih rest hrest i hitl

/-- The evaluated values of a slot array that produced `is` via
    `linIndices` are exactly the assignment's values at those
    positions (when the store pins each slot name to the
    assignment's value and every index is in range). -/
theorem linIndices_eval {names : List String} {store : Store}
    {a : List Value}
    (hvals : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
      store (Ident.mk names[i]!) = some v) :
    ∀ (elems : ArrayLiteral) (is : List Nat),
    linIndices names elems = some is →
    (∀ i, i ∈ is → i < a.length) →
    elems.mapM (BasicExpr.eval store) = some (is.map (fun i => a[i]!)) := by
  intro elems
  induction elems with
  | nil =>
      intro is hidx _
      have hnil : linIndices names [] = some [] := rfl
      rw [hnil] at hidx
      have his : is = [] := (Option.some.inj hidx).symm
      subst his
      rfl
  | cons e es ih =>
      intro is hidx hin
      cases he : e with
      | lit l =>
          rw [he] at hidx
          exact absurd hidx (by simp [linIndices])
      | ident x =>
          rw [he] at hidx
          simp only [linIndices] at hidx
          cases hn : nameIndex names x.name with
          | none => rw [hn] at hidx; exact absurd hidx (by simp)
          | some n =>
              rw [hn] at hidx
              cases hrest : linIndices names es with
              | none => rw [hrest] at hidx; exact absurd hidx (by simp)
              | some rest =>
                  rw [hrest] at hidx
                  have his : is = n :: rest := by simpa using hidx.symm
                  subst his
                  -- the store lookup of the element succeeded
                  obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name n hn
                  have hnameq : names[n]! = x.name :=
                    getElem_of_getElem? hxlt hxget
                  have hnlt : n < a.length := hin n (by simp)
                  have hlook : a[n]? = some a[n]! := by
                    rw [List.getElem?_eq_getElem hnlt, getElem!_pos a n hnlt]
                  have hsx : store x = some a[n]! := by
                    rw [show x = Ident.mk x.name from rfl,
                      show Ident.mk x.name = Ident.mk names[n]! from
                      congrArg Ident.mk hnameq.symm]
                    exact hvals n hxlt a[n]! hlook
                  have htl := ih rest hrest (by
                    intro i hi
                    exact hin i (by simp [hi]))
                  simp only [List.mapM_cons, BasicExpr.eval]
                  rw [hsx, htl]
                  rfl

/-- **The all-different index/value agreement**: if every in-bounds
    position of `a` carries the store's value at the slot name, then
    the values an `all_different` array's elements evaluate to (the
    store's reads) are exactly `a`'s reads at the extracted
    positions, in order. -/
theorem allDiff_map_eq {names : List String} {store : Store} {a : List Value}
    (hvals : ∀ (i : Nat), i < names.length →
      ∃ v, a[i]? = some v ∧ store (Ident.mk names[i]!) = some v) :
    ∀ (elems : ArrayLiteral) (vs : List Value) (is : List Nat),
      elems.mapM (BasicExpr.eval store) = some vs →
      allDiffIndices names elems = some is →
      is.map (fun i => a[i]!) = vs := by
  intro elems
  induction elems with
  | nil =>
      intro vs is hvs hidx
      have hnil : allDiffIndices names [] = some [] := rfl
      rw [hnil] at hidx
      have his : is = [] := (Option.some.inj hidx).symm
      subst his
      have hvs' : vs = [] := by simpa using hvs.symm
      subst hvs'
      rfl
  | cons e es ih =>
      intro vs is hvs hidx
      cases he : e with
      | lit l =>
          rw [he] at hidx
          exact absurd hidx (by simp [allDiffIndices])
      | ident x =>
          rw [he] at hidx
          simp only [allDiffIndices] at hidx
          cases hn : nameIndex names x.name with
          | none => rw [hn] at hidx; exact absurd hidx (by simp)
          | some n =>
              rw [hn] at hidx
              cases hrest : allDiffIndices names es with
              | none => rw [hrest] at hidx; exact absurd hidx (by simp)
              | some rest =>
                  rw [hrest] at hidx
                  have his : is = n :: rest := by simpa using hidx.symm
                  subst his
                  -- the store lookup of the element succeeded
                  have hstep : (BasicExpr.ident x :: es).mapM
                      (BasicExpr.eval store) = some vs →
                      ∃ vx vtl, store x = some vx ∧
                        es.mapM (BasicExpr.eval store) = some vtl ∧
                        vs = vx :: vtl := by
                    intro hm
                    simp only [List.mapM_cons, BasicExpr.eval] at hm
                    cases hx : store x with
                    | none =>
                        rw [hx] at hm
                        simp at hm
                    | some vx =>
                        rw [hx] at hm
                        cases hvtl : es.mapM (BasicExpr.eval store) with
                        | none => rw [hvtl] at hm; simp at hm
                        | some vtl =>
                            rw [hvtl] at hm
                            have hreduce : (some vx >>= fun y =>
                                some vtl >>= fun ys => pure (y :: ys)) =
                                  some (vx :: vtl) := rfl
                            rw [hreduce] at hm
                            have hm' : some (vx :: vtl) = some vs := hm
                            injection hm' with hm2
                            exact ⟨vx, vtl, rfl, rfl, hm2.symm⟩
                  rw [he] at hvs
                  obtain ⟨vx, vtl, hx, hvtl, hcons⟩ := hstep hvs
                  -- the element's value agrees with the assignment's read
                  obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name n hn
                  obtain ⟨v', hav, hstore'⟩ := hvals n hxlt
                  have hnamei : names[n]! = x.name :=
                    getElem_of_getElem? hxlt hxget
                  rw [hnamei] at hstore'
                  have hxmk : Ident.mk x.name = x := by obtain ⟨m⟩ := x; rfl
                  rw [hxmk] at hstore'
                  have hvx : v' = vx := Option.some.inj (hstore'.symm.trans hx)
                  -- so a[n]! is the store value
                  have hread : a[n]! = vx := by
                    have hsome : a[n]? = some vx := by rw [hav, hvx]
                    have hnlt : n < a.length :=
                      (List.getElem?_eq_some_iff.mp hsome).choose
                    rw [getElem!_pos a n hnlt]
                    rw [List.getElem?_eq_getElem hnlt] at hsome
                    exact Option.some.inj hsome
                  -- recurse on the tail
                  have htail := ih vtl rest hvtl hrest
                  show (n :: rest).map (fun i => a[i]!) = vs
                  rw [hcons, List.map_cons, hread, htail]

/-- Inversion of argument evaluation for an identifier argument followed
    by an array argument (the `array_int_maximum(m, xs)` argument
    order). -/
theorem mapM_ident_arr {store : Store} {c : ConstraintItem}
    {x : Ident} {elems : ArrayLiteral} {args : List Value}
    (hargs : c.args = [Expr.basic (.ident x), Expr.array elems])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ vx vs, store x = some vx ∧
      elems.mapM (BasicExpr.eval store) = some vs ∧ args = [vx, .array vs] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
  cases h1 : store x with
  | none => rw [h1] at hmap; simp at hmap
  | some vx =>
      rw [h1] at hmap
      cases h2 : elems.mapM (BasicExpr.eval store) with
      | none => rw [h2] at hmap; simp at hmap
      | some vs =>
          rw [h2] at hmap
          exact ⟨vx, vs, rfl, rfl, by simpa using hmap.symm⟩

/-- Inversion of argument evaluation for three general basic arguments
    (the general `int_min`/`int_max`/`int_div`/`int_mod` shapes): each
    argument evaluates and the evaluated list is the three values. -/
theorem mapM_three_basic {store : Store} {c : ConstraintItem}
    {a₀ a₁ a₂ : BasicExpr} {args : List Value}
    (hargs : c.args = [Expr.basic a₀, Expr.basic a₁, Expr.basic a₂])
    (hmap : c.args.mapM (Expr.eval store) = some args) :
    ∃ v₀ v₁ v₂, a₀.eval store = some v₀ ∧ a₁.eval store = some v₁ ∧
      a₂.eval store = some v₂ ∧ args = [v₀, v₁, v₂] := by
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval] at hmap
  cases h0 : a₀.eval store with
  | none => rw [h0] at hmap; simp at hmap
  | some v₀ =>
      rw [h0] at hmap
      cases h1 : a₁.eval store with
      | none => rw [h1] at hmap; simp at hmap
      | some v₁ =>
          rw [h1] at hmap
          cases h2 : a₂.eval store with
          | none => rw [h2] at hmap; simp at hmap
          | some v₂ =>
              rw [h2] at hmap
              exact ⟨v₀, v₁, v₂, rfl, rfl, rfl, by simpa using hmap.symm⟩

/-- **The operand read agrees with the store's evaluation**: when the
    assignment carries the store's values at the slot names, the
    `DomIntArg` operand that `intArgOf` extracted from a source
    expression reads the value the store evaluates that expression to
    (an identifier is the slot's store value, an integer literal
    denotes itself). -/
theorem intArgOf_read {names : List String} {store : Store} {a : List Value}
    {e : BasicExpr} {o : DomIntArg} {v : Value}
    (hvals : ∀ (i : Nat), i < names.length →
      ∃ w, a[i]? = some w ∧ store (Ident.mk names[i]!) = some w)
    (ho : intArgOf names e = some o) (he : BasicExpr.eval store e = some v) :
    DomIntArg.read a o = v := by
  cases e with
  | lit l =>
      cases l with
      | int k =>
          have ho' : o = .lit k :=
            (Option.some.inj (by simpa [intArgOf] using ho)).symm
          subst ho'
          have hv : v = .int k :=
            (Option.some.inj (by
              simpa [BasicExpr.eval, BasicLiteral.denote] using he)).symm
          subst hv
          rfl
      | bool b => exact absurd ho (by simp [intArgOf])
      | set s => exact absurd ho (by simp [intArgOf])
  | ident x =>
      simp only [intArgOf] at ho
      cases hn : nameIndex names x.name with
      | none => rw [hn] at ho; exact absurd ho (by simp)
      | some i =>
          rw [hn] at ho
          have ho' : o = .slot i := (Option.some.inj (by simpa using ho)).symm
          subst ho'
          have hev : store x = some v := by simpa [BasicExpr.eval] using he
          obtain ⟨hilt, higet⟩ := nameIndex_some names x.name i hn
          have hnamei : names[i]! = x.name := getElem_of_getElem? hilt higet
          obtain ⟨w, haw, hsw⟩ := hvals i hilt
          have hx : Ident.mk names[i]! = x := by
            obtain ⟨m⟩ := x
            rw [hnamei]
          rw [hx] at hsw
          have hwv : w = v := Option.some.inj (hsw.symm.trans hev)
          have hsome : a[i]? = some v := by rw [haw, hwv]
          show a[i]! = v
          have hilt' : i < a.length :=
            (List.getElem?_eq_some_iff.mp hsome).choose
          have hbang : a[i]? = some a[i]! := getElem_bang_some hilt'
          rw [hbang] at hsome
          exact Option.some.inj hsome

/-- **Inversion of `Holds` for the general two-operand integer
    arithmetic predicates** (`int_min`/`int_max`/`int_div`/`int_mod`
    on general basic arguments, PLAN C6): the three evaluated arguments
    are integers and satisfy the predicate's arithmetic relation `phi`
    (for `int_min`/`int_max`, that the third IS the min/max; for
    `int_div`/`int_mod`, that the second is nonzero and the third the
    truncated quotient/remainder). -/
theorem holds_int_arith_gen
    (op : String) (phi : Int → Int → Int → Prop)
    (hbridge : fullInterp (Ident.mk op) = stdInterp (Ident.mk op))
    (hsem : ∀ args : List Value,
      stdInterp (Ident.mk op) args =
        (match args with
        | [.int p, .int q, .int r] => phi p q r
        | _ => False))
    {store : Store} {c : ConstraintItem} {a₀ a₁ a₂ : BasicExpr}
    (hname : c.name.name = op)
    (hargs : c.args = [Expr.basic a₀, Expr.basic a₁, Expr.basic a₂])
    (h : c.Holds fullInterp store) :
    ∃ p q r, a₀.eval store = some (.int p) ∧ a₁.eval store = some (.int q) ∧
      a₂.eval store = some (.int r) ∧ phi p q r := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨v₀, v₁, v₂, he₀, he₁, he₂, hargsv⟩ := mapM_three_basic hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk op) [v₀, v₁, v₂] :=
    interp_of_hname hname hinterp
  rw [hbridge] at h1
  rw [hsem [v₀, v₁, v₂]] at h1
  have hmatch : (match [v₀, v₁, v₂] with
    | [.int p, .int q, .int r] => phi p q r
    | _ => False) := h1
  cases v₀ with
  | int p =>
      cases v₁ with
      | int q =>
          cases v₂ with
          | int r => exact ⟨p, q, r, he₀, he₁, he₂, by simpa using hmatch⟩
          | bool w => exact absurd hmatch (by simp)
          | setOfInt w => exact absurd hmatch (by simp)
          | array w => exact absurd hmatch (by simp)
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- **Inversion of `Holds` for the array extreme forms**
    (`array_int_maximum`/`array_int_minimum`, result parameter first):
    the store's value at the result name is an integer and the array's
    evaluated elements have that value as their `maxValue`/`minValue`. -/
theorem holds_array_int_extreme
    (op : String) (hval : List Value → Option Int)
    (hbridge : fullInterp (Ident.mk op) = stdInterp (Ident.mk op))
    (hsem : ∀ args : List Value,
      stdInterp (Ident.mk op) args =
        (match args with
        | [.int m, .array xs] => hval xs = some m
        | _ => False))
    {store : Store} {c : ConstraintItem} {x : Ident} {elems : ArrayLiteral}
    (hname : c.name.name = op)
    (hargs : c.args = [Expr.basic (.ident x), Expr.array elems])
    (h : c.Holds fullInterp store) :
    ∃ m vs, store x = some (.int m) ∧
      elems.mapM (BasicExpr.eval store) = some vs ∧ hval vs = some m := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, vs, hx, hvs, hargsv⟩ := mapM_ident_arr hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk op) [vx, .array vs] :=
    interp_of_hname hname hinterp
  rw [hbridge] at h1
  rw [hsem [vx, .array vs]] at h1
  have hmatch : (match [vx, .array vs] with
    | [.int m, .array xs] => hval xs = some m
    | _ => False) := h1
  cases vx with
  | int m => exact ⟨m, vs, hx, hvs, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- **Extraction inversion**: if `extractConstraint names c`
    produced a constraint, then the model constraint has one of the
    extracted shapes — the name is one of the extracted predicates,
    the arguments are the corresponding identifier/literal/array
    pattern, and the slot names resolve. -/
theorem extractConstraint_inv {names : List String} {c : ConstraintItem}
    {dc : DomConstraint} (hdc : extractConstraint names c = some dc) :
    (∃ x y i j, c.name.name = "int_eq" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧ dc = .eqSlot i j) ∨
    (∃ x k i, c.name.name = "int_eq" ∧
        c.args = [.basic (.ident x), .basic (.lit (.int k))] ∧
        nameIndex names x.name = some i ∧ dc = .constEq i (.int k)) ∨
    (∃ k y i, c.name.name = "int_eq" ∧
        c.args = [.basic (.lit (.int k)), .basic (.ident y)] ∧
        nameIndex names y.name = some i ∧ dc = .constEq i (.int k)) ∨
    (∃ x y i j, c.name.name = "int_ne" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧ dc = .neSlot i j) ∨
    (∃ x y i j, c.name.name = "int_le" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧ dc = .leSlot i j) ∨
    (∃ x k i, c.name.name = "int_le" ∧
        c.args = [.basic (.ident x), .basic (.lit (.int k))] ∧
        nameIndex names x.name = some i ∧ dc = .leConstHi i k) ∨
    (∃ k y i, c.name.name = "int_le" ∧
        c.args = [.basic (.lit (.int k)), .basic (.ident y)] ∧
        nameIndex names y.name = some i ∧ dc = .leConstLo i k) ∨
    (∃ x y z i j k, c.name.name = "int_plus" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident z)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names z.name = some k ∧ dc = .plusSlot i j k) ∨
    (∃ elems is, c.name.name = "all_different" ∧
        c.args = [Expr.array elems] ∧
        allDiffIndices names elems = some is ∧ dc = .allDiff is) ∨
    (∃ ks elems coeffs is b, c.name.name = "int_lin_eq" ∧
        c.args = [Expr.array ks, Expr.array elems,
          Expr.basic (.lit (.int b))] ∧
        linCoeffs ks = some coeffs ∧ linIndices names elems = some is ∧
        (coeffs.length == is.length) = true ∧ dc = .linEq coeffs is b) ∨
    (∃ ks elems coeffs is b, c.name.name = "int_lin_le" ∧
        c.args = [Expr.array ks, Expr.array elems,
          Expr.basic (.lit (.int b))] ∧
        linCoeffs ks = some coeffs ∧ linIndices names elems = some is ∧
        (coeffs.length == is.length) = true ∧ dc = .linLe coeffs is b) ∨
    (∃ x y z i j k, c.name.name = "int_times" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident z)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names z.name = some k ∧ dc = .timesSlot i j k) ∨
    (∃ x y z i j k, c.name.name = "int_min" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident z)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names z.name = some k ∧ dc = .minSlot i j k) ∨
    (∃ x y z i j k, c.name.name = "int_max" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident z)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names z.name = some k ∧ dc = .maxSlot i j k) ∨
    (∃ x y i k, c.name.name = "int_abs" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some k ∧ dc = .absSlot i k) ∨
    (∃ x y i j, c.name.name = "int_lt" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧ dc = .ltSlot i j) ∨
    (∃ x k i, c.name.name = "int_lt" ∧
        c.args = [.basic (.ident x), .basic (.lit (.int k))] ∧
        nameIndex names x.name = some i ∧ dc = .ltConstHi i k) ∨
    (∃ k y i, c.name.name = "int_lt" ∧
        c.args = [.basic (.lit (.int k)), .basic (.ident y)] ∧
        nameIndex names y.name = some i ∧ dc = .ltConstLo i k) ∨
    (∃ x y i j, c.name.name = "bool_not" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧ dc = .boolNotSlot i j) ∨
    (∃ x y z i j k, c.name.name = "bool_and" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident z)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names z.name = some k ∧ dc = .boolAndSlot i j k) ∨
    (∃ x y z i j k, c.name.name = "bool_or" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident z)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names z.name = some k ∧ dc = .boolOrSlot i j k) ∨
    (∃ ks elems coeffs is b, c.name.name = "int_lin_ne" ∧
        c.args = [Expr.array ks, Expr.array elems,
          Expr.basic (.lit (.int b))] ∧
        linCoeffs ks = some coeffs ∧ linIndices names elems = some is ∧
        (coeffs.length == is.length) = true ∧ dc = .linNe coeffs is b) ∨
    (∃ elems1 elems2 ps ns, c.name.name = "bool_clause" ∧
        c.args = [Expr.array elems1, Expr.array elems2] ∧
        linIndices names elems1 = some ps ∧
        linIndices names elems2 = some ns ∧
        dc = .boolClauseSlot ps ns) ∨
    (∃ elems r is k, c.name.name = "array_bool_and" ∧
        c.args = [Expr.array elems, Expr.basic (.ident r)] ∧
        linIndices names elems = some is ∧
        nameIndex names r.name = some k ∧
        dc = .arrayBoolAndSlot is k) ∨
    (∃ x y i k, c.name.name = "bool2int" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some k ∧
        dc = .bool2intSlot i k) ∨
    (∃ x y i j, c.name.name = "bool_eq" ∧
        c.args = [.basic (.ident x), .basic (.ident y)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        dc = .boolEqSlot i j) ∨
    (∃ elems xs x y i k, c.name.name = "array_int_element" ∧
        c.args = [.basic (.ident x), Expr.array elems, .basic (.ident y)] ∧
        intLits elems = some xs ∧ nameIndex names x.name = some i ∧
        nameIndex names y.name = some k ∧
        dc = .arrayIntElementSlot xs i k) ∨
    (∃ elems is x y i k, c.name.name = "array_var_int_element" ∧
        c.args = [.basic (.ident x), Expr.array elems, .basic (.ident y)] ∧
        linIndices names elems = some is ∧ nameIndex names x.name = some i ∧
        nameIndex names y.name = some k ∧
        dc = .arrayVarIntElementSlot is i k) ∨
    (∃ elems is x y i k, c.name.name = "array_var_bool_element" ∧
        c.args = [.basic (.ident x), Expr.array elems, .basic (.ident y)] ∧
        linIndices names elems = some is ∧ nameIndex names x.name = some i ∧
        nameIndex names y.name = some k ∧
        dc = .arrayVarBoolElementSlot is i k) ∨
    (∃ x y r i j k, c.name.name = "int_eq_reif" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident r)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names r.name = some k ∧ dc = .eqReifSlot i j k) ∨
    (∃ x y r i j k, c.name.name = "int_le_reif" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident r)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names r.name = some k ∧ dc = .leReifSlot i j k) ∨
    (∃ x y r i j k, c.name.name = "int_ne_reif" ∧
        c.args = [.basic (.ident x), .basic (.ident y),
          Expr.basic (.ident r)] ∧
        nameIndex names x.name = some i ∧ nameIndex names y.name = some j ∧
        nameIndex names r.name = some k ∧ dc = .neReifSlot i j k) ∨
    (∃ ks elems coeffs is b r k, c.name.name = "int_lin_eq_reif" ∧
        c.args = [Expr.array ks, Expr.array elems,
          Expr.basic (.lit (.int b)), Expr.basic (.ident r)] ∧
        linCoeffs ks = some coeffs ∧ linIndices names elems = some is ∧
        (coeffs.length == is.length) = true ∧
        nameIndex names r.name = some k ∧ dc = .linEqReif coeffs is b k) ∨
    (∃ ks elems coeffs is b r k, c.name.name = "int_lin_le_reif" ∧
        c.args = [Expr.array ks, Expr.array elems,
          Expr.basic (.lit (.int b)), Expr.basic (.ident r)] ∧
        linCoeffs ks = some coeffs ∧ linIndices names elems = some is ∧
        (coeffs.length == is.length) = true ∧
        nameIndex names r.name = some k ∧ dc = .linLeReif coeffs is b k) ∨
    (∃ ks elems coeffs is b r k, c.name.name = "int_lin_ne_reif" ∧
        c.args = [Expr.array ks, Expr.array elems,
          Expr.basic (.lit (.int b)), Expr.basic (.ident r)] ∧
        linCoeffs ks = some coeffs ∧ linIndices names elems = some is ∧
        (coeffs.length == is.length) = true ∧
        nameIndex names r.name = some k ∧ dc = .linNeReif coeffs is b k) ∨
    (∃ a₀ a₁ a₂ o₀ o₁ o₂, c.name.name = "int_min" ∧
        c.args = [.basic a₀, .basic a₁, .basic a₂] ∧
        intArgOf names a₀ = some o₀ ∧ intArgOf names a₁ = some o₁ ∧
        intArgOf names a₂ = some o₂ ∧ dc = .minPair o₀ o₁ o₂) ∨
    (∃ a₀ a₁ a₂ o₀ o₁ o₂, c.name.name = "int_max" ∧
        c.args = [.basic a₀, .basic a₁, .basic a₂] ∧
        intArgOf names a₀ = some o₀ ∧ intArgOf names a₁ = some o₁ ∧
        intArgOf names a₂ = some o₂ ∧ dc = .maxPair o₀ o₁ o₂) ∨
    (∃ a₀ a₁ a₂ o₀ o₁ o₂, c.name.name = "int_div" ∧
        c.args = [.basic a₀, .basic a₁, .basic a₂] ∧
        intArgOf names a₀ = some o₀ ∧ intArgOf names a₁ = some o₁ ∧
        intArgOf names a₂ = some o₂ ∧ dc = .divGen o₀ o₁ o₂) ∨
    (∃ a₀ a₁ a₂ o₀ o₁ o₂, c.name.name = "int_mod" ∧
        c.args = [.basic a₀, .basic a₁, .basic a₂] ∧
        intArgOf names a₀ = some o₀ ∧ intArgOf names a₁ = some o₁ ∧
        intArgOf names a₂ = some o₂ ∧ dc = .modGen o₀ o₁ o₂) ∨
    (∃ x elems is k, c.name.name = "array_int_maximum" ∧
        c.args = [.basic (.ident x), .array elems] ∧
        nameIndex names x.name = some k ∧ linIndices names elems = some is ∧
        dc = .maxGen (is.map DomIntArg.slot) (.slot k)) ∨
    (∃ x elems is k, c.name.name = "array_int_minimum" ∧
        c.args = [.basic (.ident x), .array elems] ∧
        nameIndex names x.name = some k ∧ linIndices names elems = some is ∧
        dc = .minGen (is.map DomIntArg.slot) (.slot k)) := by
  rw [extractConstraint] at hdc
  split at hdc
  case h_1 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i j hxi hyi =>
        exact Or.inl ⟨x, y, i, j, heqname, heqargs, hxi, hyi, by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 x k heqargs =>
      cases hxi : nameIndex names x.name
      case none =>
        rw [hxi] at hdc
        exact absurd hdc (by simp)
      case some i =>
        rw [hxi] at hdc
        exact Or.inr (Or.inl ⟨x, k, i, heqname, heqargs, hxi, by simpa using hdc.symm⟩)
    case h_3 k y heqargs =>
      cases hyi : nameIndex names y.name
      case none =>
        rw [hyi] at hdc
        exact absurd hdc (by simp)
      case some i =>
        rw [hyi] at hdc
        exact Or.inr (Or.inr (Or.inl ⟨k, y, i, heqname, heqargs, hyi, by simpa using hdc.symm⟩))
    case h_4 => exact absurd hdc (by simp)
  case h_2 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i j hxi hyi =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, i, j, heqname, heqargs, hxi, hyi, by simpa using hdc.symm⟩)))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_3 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i j hxi hyi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, i, j, heqname, heqargs, hxi, hyi, by simpa using hdc.symm⟩))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 x k heqargs =>
      cases hxi : nameIndex names x.name
      case none =>
        rw [hxi] at hdc
        exact absurd hdc (by simp)
      case some i =>
        rw [hxi] at hdc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, k, i, heqname, heqargs, hxi, by simpa using hdc.symm⟩)))))
    case h_3 k y heqargs =>
      cases hyi : nameIndex names y.name
      case none =>
        rw [hyi] at hdc
        exact absurd hdc (by simp)
      case some i =>
        rw [hyi] at hdc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, y, i, heqname, heqargs, hyi, by simpa using hdc.symm⟩))))))
    case h_4 => exact absurd hdc (by simp)
  case h_4 heqname =>
    split at hdc
    case h_1 x y z heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hzi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩)))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_5 heqname =>
    split at hdc
    case h_1 elems heqargs =>
      cases hidx : allDiffIndices names elems
      case none =>
        rw [hidx] at hdc
        exact absurd hdc (by simp)
      case some is =>
        rw [hidx] at hdc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨elems, is, heqname, heqargs, hidx, by simpa using hdc.symm⟩))))))))
    case h_2 => exact absurd hdc (by simp)
  case h_6 heqname =>
    split at hdc
    case h_1 ks elems b heqargs =>
      split at hdc
      case h_1 hcoeffs his =>
        split at hdc
        case isTrue hlen =>
          rename_i coeffs is
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ks, elems, coeffs, is, b, heqname, heqargs, hcoeffs, his, hlen,
            by simpa using hdc.symm⟩)))))))))
        case isFalse => exact absurd hdc (by simp)
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_7 heqname =>
    split at hdc
    case h_1 ks elems b heqargs =>
      split at hdc
      case h_1 hcoeffs his =>
        split at hdc
        case isTrue hlen =>
          rename_i coeffs is
          have hdcfin : dc = DomConstraint.linLe coeffs is b :=
            (Option.some.inj hdc).symm
          exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨ks, elems, coeffs, is, b, heqname, heqargs, hcoeffs, his, hlen,
            hdcfin⟩))))))))))
        case isFalse => exact absurd hdc (by simp)
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_8 heqname =>
    split at hdc
    case h_1 x y z heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hzi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩)))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_9 heqname =>
    split at hdc
    case h_1 x y z heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hzi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 a₀ a₁ a₂ hne heqargs =>
      split at hdc
      case h_1 o₀ o₁ o₂ ho₀ ho₁ ho₂ =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨a₀, a₁, a₂, o₀, o₁, o₂, heqname, heqargs, ho₀, ho₁, ho₂,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_3 => exact absurd hdc (by simp)
  case h_10 heqname =>
    split at hdc
    case h_1 x y z heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hzi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩)))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 a₀ a₁ a₂ hne heqargs =>
      split at hdc
      case h_1 o₀ o₁ o₂ ho₀ ho₁ ho₂ =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr
        exact Or.inl ⟨a₀, a₁, a₂, o₀, o₁, o₂, heqname, heqargs, ho₀, ho₁, ho₂,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_3 => exact absurd hdc (by simp)
  case h_11 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i k hxi hyi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, i, k, heqname, heqargs, hxi, hyi,
          by simpa using hdc.symm⟩))))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_12 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i j hxi hyi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, i, j, heqname, heqargs, hxi, hyi,
          by simpa using hdc.symm⟩)))))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 x k heqargs =>
      cases hxi : nameIndex names x.name
      case none =>
        rw [hxi] at hdc
        simp only [Option.map] at hdc
        exact absurd hdc (by simp)
      case some i =>
        rw [hxi] at hdc
        simp only [Option.map] at hdc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, k, i, heqname, heqargs, hxi, by simp at hdc; exact hdc.symm⟩))))))))))))))))
    case h_3 k y heqargs =>
      cases hyi : nameIndex names y.name
      case none =>
        rw [hyi] at hdc
        simp only [Option.map] at hdc
        exact absurd hdc (by simp)
      case some i =>
        rw [hyi] at hdc
        simp only [Option.map] at hdc
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨k, y, i, heqname, heqargs, hyi, by simp at hdc; exact hdc.symm⟩)))))))))))))))))
    case h_4 => exact absurd hdc (by simp)
  case h_13 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i j hxi hyi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, i, j, heqname, heqargs, hxi, hyi,
          by simpa using hdc.symm⟩))))))))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_14 heqname =>
    split at hdc
    case h_1 x y z heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hzi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩)))))))))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_15 heqname =>
    split at hdc
    case h_1 x y z heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hzi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩))))))))))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_16 heqname =>
    split at hdc
    case h_1 ks elems b heqargs =>
      split at hdc
      case h_1 hcoeffs his =>
        split at hdc
        case isTrue hlen =>
          rename_i coeffs is
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inl
          exact ⟨ks, elems, coeffs, is, b, heqname, heqargs, hcoeffs, his, hlen,
            by simpa using hdc.symm⟩
        case isFalse => exact absurd hdc (by simp)
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_17 heqname =>
    split at hdc
    case h_1 elems1 elems2 heqargs =>
      split at hdc
      case h_1 ps ns hps hns =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨elems1, elems2, ps, ns, heqname, heqargs, hps, hns,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_18 heqname =>
    split at hdc
    case h_1 elems r heqargs =>
      split at hdc
      case h_1 is k his hr =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨elems, r, is, k, heqname, heqargs, his, hr,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_19 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i k hxi hyi =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨x, y, i, k, heqname, heqargs, hxi, hyi,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_20 heqname =>
    split at hdc
    case h_1 x y heqargs =>
      split at hdc
      case h_1 i j hxi hyi =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨x, y, i, j, heqname, heqargs, hxi, hyi,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_21 heqname =>
    split at hdc
    case h_1 x elems y heqargs =>
      split at hdc
      case h_1 xs i k hxs hxi hyk =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr
        exact Or.inl ⟨elems, xs, x, y, i, k, heqname, heqargs, hxs, hxi, hyk,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_22 heqname =>
    split at hdc
    case h_1 x elems y heqargs =>
      split at hdc
      case h_1 is i k his hxi hyk =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr
        exact Or.inl ⟨elems, is, x, y, i, k, heqname, heqargs, his, hxi, hyk,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_23 heqname =>
    split at hdc
    case h_1 x elems y heqargs =>
      split at hdc
      case h_1 is i k his hxi hyk =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨elems, is, x, y, i, k, heqname, heqargs, his, hxi, hyk,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_24 heqname =>
    split at hdc
    case h_1 x y r heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hrk =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨x, y, r, i, j, k, heqname, heqargs, hxi, hyi, hrk,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_25 heqname =>
    split at hdc
    case h_1 x y r heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hrk =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨x, y, r, i, j, k, heqname, heqargs, hxi, hyi, hrk,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_26 heqname =>
    split at hdc
    case h_1 x y r heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hrk =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr
        exact Or.inl ⟨x, y, r, i, j, k, heqname, heqargs, hxi, hyi, hrk,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_27 heqname =>
    split at hdc
    case h_1 ks elems b r heqargs =>
      split at hdc
      case h_1 hcoeffs his hrk =>
        split at hdc
        case isTrue hlen =>
          rename_i coeffs is k
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr
          exact Or.inl ⟨ks, elems, coeffs, is, b, r, k, heqname, heqargs,
            hcoeffs, his, hlen, hrk, by simpa using hdc.symm⟩
        case isFalse => exact absurd hdc (by simp)
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_28 heqname =>
    split at hdc
    case h_1 ks elems b r heqargs =>
      split at hdc
      case h_1 hcoeffs his hrk =>
        split at hdc
        case isTrue hlen =>
          rename_i coeffs is k
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr
          exact Or.inl ⟨ks, elems, coeffs, is, b, r, k, heqname, heqargs,
            hcoeffs, his, hlen, hrk, by simpa using hdc.symm⟩
        case isFalse => exact absurd hdc (by simp)
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_29 heqname =>
    split at hdc
    case h_1 ks elems b r heqargs =>
      split at hdc
      case h_1 hcoeffs his hrk =>
        split at hdc
        case isTrue hlen =>
          rename_i coeffs is k
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
          exact Or.inl ⟨ks, elems, coeffs, is, b, r, k, heqname, heqargs,
            hcoeffs, his, hlen, hrk, by simpa using hdc.symm⟩
        case isFalse => exact absurd hdc (by simp)
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_30 heqname =>
    split at hdc
    case h_1 a₀ a₁ a₂ heqargs =>
      split at hdc
      case h_1 o₀ o₁ o₂ ho₀ ho₁ ho₂ =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr
        exact Or.inl ⟨a₀, a₁, a₂, o₀, o₁, o₂, heqname, heqargs, ho₀, ho₁, ho₂,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_31 heqname =>
    split at hdc
    case h_1 a₀ a₁ a₂ heqargs =>
      split at hdc
      case h_1 o₀ o₁ o₂ ho₀ ho₁ ho₂ =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨a₀, a₁, a₂, o₀, o₁, o₂, heqname, heqargs, ho₀, ho₁, ho₂,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_32 heqname =>
    split at hdc
    case h_1 x elems heqargs =>
      split at hdc
      case h_1 k is hk his =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact Or.inl ⟨x, elems, is, k, heqname, heqargs, hk, his,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_33 heqname =>
    split at hdc
    case h_1 x elems heqargs =>
      split at hdc
      case h_1 k is hk his =>
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr; apply Or.inr
        exact ⟨x, elems, is, k, heqname, heqargs, hk, his,
          by simpa using hdc.symm⟩
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_34 => exact absurd hdc (by simp)

/-- **Per-constraint extraction soundness**: if the model constraint
    `c` holds in `store` (under `fullInterp`, the interpretation the
    verified checker certifies), and `extractConstraint names c`
    produced `dc`, then `dc` is `SatisfiedBy` any assignment `a`
    whose slot values agree with the store at the slot names
    (`hvals`: position `i` of `a` is the store's value at the
    slot-`i` name, whenever `i` is in bounds). -/
theorem extractConstraint_holds {names : List String} {c : ConstraintItem}
    {dc : DomConstraint} {store : Store} {a : List Value}
    (hh : c.Holds fullInterp store)
    (hdc : extractConstraint names c = some dc)
    (hvals : ∀ (i : Nat), i < names.length →
      ∃ v, a[i]? = some v ∧ store (Ident.mk names[i]!) = some v) :
    dc.SatisfiedBy a := by
  -- a helper: reading slot i's value as pinned by the store
  have hslot : ∀ (i : Nat) (s : String), i < names.length →
      names[i]! = s → ∃ v, a[i]? = some v ∧ store (Ident.mk s) = some v := by
    intro i s hilt his
    obtain ⟨v, haiv, hstore⟩ := hvals i hilt
    rw [his] at hstore
    exact ⟨v, haiv, hstore⟩
  rcases extractConstraint_inv hdc with
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, k, i, hname, hargs, hxi, hdc'⟩ |
    ⟨k, y, i, hname, hargs, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, k, i, hname, hargs, hxi, hdc'⟩ |
    ⟨k, y, i, hname, hargs, hyi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨elems, is, hname, hargs, hidx, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, hname, hargs, hcoeffs, his, hlen, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, hname, hargs, hcoeffs, his, hlen, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, i, k, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, k, i, hname, hargs, hxi, hdc'⟩ |
    ⟨k, y, i, hname, hargs, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, hname, hargs, hcoeffs, his, hlen, hdc'⟩ |
    ⟨elems1, elems2, ps, ns, hname, hargs, hidx1, hidx2, hdc'⟩ |
    ⟨elems, r, is, k, hname, hargs, his, hr, hdc'⟩ |
    ⟨x, y, i, k, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨elems, xs, x, y, i, k, hname, hargs, hxs, hxi, hyk, hdc'⟩ |
    ⟨elems, is, x, y, i, k, hname, hargs, his, hxi, hyk, hdc'⟩ |
    ⟨elems, is, x, y, i, k, hname, hargs, his, hxi, hyk, hdc'⟩ |
    ⟨x, y, r, i, j, k, hname, hargs, hxi, hyi, hrk, hdc'⟩ |
    ⟨x, y, r, i, j, k, hname, hargs, hxi, hyi, hrk, hdc'⟩ |
    ⟨x, y, r, i, j, k, hname, hargs, hxi, hyi, hrk, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, r, k, hname, hargs, hcoeffs, his, hlen, hrk,
      hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, r, k, hname, hargs, hcoeffs, his, hlen, hrk,
      hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, r, k, hname, hargs, hcoeffs, his, hlen, hrk,
      hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨x, elems, is, k, hname, hargs, hk, his, hdc'⟩ |
    ⟨x, elems, is, k, hname, hargs, hk, his, hdc'⟩
  · -- int_eq on two slots
    subst hdc'
    obtain ⟨vx, vy, hsx, hsy, heq⟩ := holds_int_eq_slot hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    have hvx : vxi = vx := Option.some.inj (hsni.symm.trans hsx)
    have hvy : vyj = vy := Option.some.inj (hsnj.symm.trans hsy)
    refine ⟨vxi, vyj, hai, haj, ?_⟩
    have heq' : vxi = vyj := by rw [hvx, hvy]; exact heq
    exact heq'
  · -- int_eq(x, k)
    subst hdc'
    have hsx := holds_int_eq_const hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    rw [hnamei] at hsni
    have hvx : vxi = .int k := Option.some.inj (hsni.symm.trans hsx)
    rw [← hvx]
    exact hai
  · -- int_eq(k, y)
    subst hdc'
    have hsy := holds_int_eq_const' hname hargs hh
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name i hyi
    obtain ⟨vyi, hai, hsni⟩ := hvals i hylt
    have hnamei : names[i]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    have hvy : vyi = .int k := Option.some.inj (hsni.symm.trans hsy)
    rw [← hvy]
    exact hai
  · -- int_ne on two slots
    subst hdc'
    obtain ⟨vx, vy, hsx, hsy, hne⟩ := holds_int_ne_slot hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    have hvx : vxi = vx := Option.some.inj (hsni.symm.trans hsx)
    have hvy : vyj = vy := Option.some.inj (hsnj.symm.trans hsy)
    refine ⟨vxi, vyj, hai, haj, ?_⟩
    intro hcc
    rw [hvx, hvy] at hcc
    exact hne hcc
  · -- int_le on two slots
    subst hdc'
    obtain ⟨p, q, hsx, hsy, hle⟩ := holds_int_le_slot hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    have hvx : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvy : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    rw [hvx] at hai
    rw [hvy] at haj
    exact ⟨p, q, hai, haj, hle⟩
  · -- int_le(x, c)
    subst hdc'
    obtain ⟨p, hsx, hpc⟩ := holds_int_le_const hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    rw [hnamei] at hsni
    have hvx : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    rw [hvx] at hai
    exact ⟨p, hai, hpc⟩
  · -- int_le(c, x)
    subst hdc'
    obtain ⟨p, hsy, hcp⟩ := holds_int_le_const' hname hargs hh
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name i hyi
    obtain ⟨vyi, hai, hsni⟩ := hvals i hylt
    have hnamei : names[i]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    have hvy : vyi = .int p := Option.some.inj (hsni.symm.trans hsy)
    rw [hvy] at hai
    exact ⟨p, hai, hcp⟩
  · -- int_plus on three slots
    subst hdc'
    obtain ⟨p, q, r, hsx, hsy, hsz, hpqr⟩ := holds_int_plus_slot hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hzlt, hzget⟩ := nameIndex_some names z.name k hzi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vzk, haz, hsnk⟩ := hvals k hzlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = z.name := getElem_of_getElem? hzlt hzget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    have hvr : vzk = .int r := Option.some.inj (hsnk.symm.trans hsz)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvr] at haz
    exact ⟨p, q, r, hai, haj, haz, hpqr⟩
  · -- all_different on an explicit array of slots
    subst hdc'
    obtain ⟨vs, hvs, hall⟩ := holds_all_different hname hargs hh
    -- the extracted indices read exactly the array's values, in order
    have hmap : is.map (fun i => a[i]!) = vs :=
      allDiff_map_eq hvals elems vs is hvs hidx
    -- the read values are pairwise different, as the store's were
    show (is.map (fun i => a[i]!)).Nodup
    rw [hmap]
    exact (valuesAllDifferent_iff_nodup vs).mp hall
  · -- int_lin_eq on slots
    subst hdc'
    obtain ⟨vs1, vs2, hvs1, hvs2, hdot⟩ := holds_int_lin_eq hname hargs hh
    rw [linCoeffs_eval ks coeffs hcoeffs] at hvs1
    -- the option-lookup form of hvals, via the hslot bridge
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    rw [linIndices_eval hlook elems is his (by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose)] at hvs2
    show dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b
    rw [← Option.some.inj hvs1.symm, ← Option.some.inj hvs2.symm]
    exact hdot
  · -- int_lin_le on slots
    subst hdc'
    obtain ⟨vs1, vs2, hvs1, hvs2, hdot⟩ := holds_int_lin_le hname hargs hh
    rw [linCoeffs_eval ks coeffs hcoeffs] at hvs1
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    rw [linIndices_eval hlook elems is his (by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose)] at hvs2
    show dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
    rw [← Option.some.inj hvs1.symm, ← Option.some.inj hvs2.symm]
    exact hdot
  · -- int_times on three slots
    subst hdc'
    obtain ⟨p, q, r, hsx, hsy, hsz, hpqr⟩ :=
      holds_int_ternary_slot "int_times" (fun p q => p * q)
        (Or.inl rfl)
        (fun args => by
          cases args with
          | cons a as =>
              cases as with
              | cons b bs =>
                  cases bs with
                  | cons w ws =>
                      cases a with
                      | int p' =>
                          cases b with
                          | int q' =>
                              cases w with
                              | int w' =>
                                  cases ws with
                                  | nil =>
                                      exact propext (eq_comm (a := p' * q') (b := w'))
                                  | cons v vs => rfl
                              | bool v => rfl
                              | setOfInt v => rfl
                              | array v => rfl
                          | bool v => rfl
                          | setOfInt v => rfl
                          | array v => rfl
                      | bool v => rfl
                      | setOfInt v => rfl
                      | array v => rfl
                  | nil => simp only [stdInterp]
              | nil => simp only [stdInterp]
          | nil => simp only [stdInterp])
        hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hzlt, hzget⟩ := nameIndex_some names z.name k hzi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vzk, haz, hsnk⟩ := hvals k hzlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = z.name := getElem_of_getElem? hzlt hzget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    have hvr : vzk = .int r := Option.some.inj (hsnk.symm.trans hsz)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvr] at haz
    exact ⟨p, q, r, hai, haj, haz, hpqr⟩
  · -- int_min on three slots
    subst hdc'
    obtain ⟨p, q, r, hsx, hsy, hsz, hpqr⟩ :=
      holds_int_ternary_slot "int_min" (fun p q => min p q)
        (Or.inr (Or.inl rfl))
        (fun args => by
          cases args with
          | cons a as =>
              cases as with
              | cons b bs =>
                  cases bs with
                  | cons w ws =>
                      cases a with
                      | int p' =>
                          cases b with
                          | int q' =>
                              cases w with
                              | int w' => rfl
                              | bool v => rfl
                              | setOfInt v => rfl
                              | array v => rfl
                          | bool v => rfl
                          | setOfInt v => rfl
                          | array v => rfl
                      | bool v => rfl
                      | setOfInt v => rfl
                      | array v => rfl
                  | nil => rfl
              | nil => rfl
          | nil => rfl)
        hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hzlt, hzget⟩ := nameIndex_some names z.name k hzi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vzk, haz, hsnk⟩ := hvals k hzlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = z.name := getElem_of_getElem? hzlt hzget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    have hvr : vzk = .int r := Option.some.inj (hsnk.symm.trans hsz)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvr] at haz
    exact ⟨p, q, r, hai, haj, haz, hpqr⟩
  · -- int_max on three slots
    subst hdc'
    obtain ⟨p, q, r, hsx, hsy, hsz, hpqr⟩ :=
      holds_int_ternary_slot "int_max" (fun p q => max p q)
        (Or.inr (Or.inr (Or.inl rfl)))
        (fun args => by
          cases args with
          | cons a as =>
              cases as with
              | cons b bs =>
                  cases bs with
                  | cons w ws =>
                      cases a with
                      | int p' =>
                          cases b with
                          | int q' =>
                              cases w with
                              | int w' => rfl
                              | bool v => rfl
                              | setOfInt v => rfl
                              | array v => rfl
                          | bool v => rfl
                          | setOfInt v => rfl
                          | array v => rfl
                      | bool v => rfl
                      | setOfInt v => rfl
                      | array v => rfl
                  | nil => rfl
              | nil => rfl
          | nil => rfl)
        hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hzlt, hzget⟩ := nameIndex_some names z.name k hzi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vzk, haz, hsnk⟩ := hvals k hzlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = z.name := getElem_of_getElem? hzlt hzget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    have hvr : vzk = .int r := Option.some.inj (hsnk.symm.trans hsz)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvr] at haz
    exact ⟨p, q, r, hai, haj, haz, hpqr⟩
  · -- int_abs on two slots
    subst hdc'
    obtain ⟨p, r, hsx, hsy, hpabs⟩ := holds_int_abs_slot hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name k hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyk, hak, hsnk⟩ := hvals k hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamek : names[k]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvr : vyk = .int r := Option.some.inj (hsnk.symm.trans hsy)
    have habs : absValue p = r := hpabs
    rw [hvp] at hai
    rw [hvr] at hak
    exact ⟨p, r, hai, hak, habs⟩
  · -- int_lt on two slots
    subst hdc'
    obtain ⟨p, q, hsx, hsy, hpq⟩ := holds_int_lt_slot hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    rw [hvp] at hai
    rw [hvq] at haj
    exact ⟨p, q, hai, haj, hpq⟩
  · -- int_lt(x, c)
    subst hdc'
    obtain ⟨p, hsx, hpc⟩ := holds_int_lt_const hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    rw [hnamei] at hsni
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    rw [hvp] at hai
    exact ⟨p, hai, hpc⟩
  · -- int_lt(c, x)
    subst hdc'
    obtain ⟨p, hsy, hcp⟩ := holds_int_lt_const' hname hargs hh
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name i hyi
    obtain ⟨vyi, hai, hsni⟩ := hvals i hylt
    have hnamei : names[i]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    have hvp : vyi = .int p := Option.some.inj (hsni.symm.trans hsy)
    rw [hvp] at hai
    exact ⟨p, hai, hcp⟩
  · -- bool_not on two slots
    subst hdc'
    obtain ⟨p, q, hsx, hsy, hqp⟩ := holds_bool_not_slot hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    have hvp : vxi = .bool p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .bool q := Option.some.inj (hsnj.symm.trans hsy)
    rw [hvp] at hai
    rw [hvq] at haj
    refine ⟨.bool p, .bool q, hai, haj, ?_⟩
    cases p with
    | false =>
        cases q with
        | false => exact absurd hqp (by simp)
        | true => exact Or.inr ⟨rfl, rfl⟩
    | true =>
        cases q with
        | false => exact Or.inl ⟨rfl, rfl⟩
        | true => exact absurd hqp (by simp)
  · -- bool_and on three slots
    subst hdc'
    obtain ⟨p, q, r, hsx, hsy, hsz, hpqr⟩ :=
      holds_bool_ternary_slot "bool_and" (fun p q => p && q)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))))
        (fun args => by
          cases args with
          | cons a as =>
              cases as with
              | cons b bs =>
                  cases bs with
                  | cons w ws =>
                      cases a with
                      | bool p' =>
                          cases b with
                          | bool q' =>
                              cases w with
                              | bool w' => rfl
                              | int v => rfl
                              | setOfInt v => rfl
                              | array v => rfl
                          | int v => rfl
                          | setOfInt v => rfl
                          | array v => rfl
                      | int v => rfl
                      | setOfInt v => rfl
                      | array v => rfl
                  | nil => rfl
              | nil => rfl
          | nil => rfl)
        hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hzlt, hzget⟩ := nameIndex_some names z.name k hzi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vzk, haz, hsnk⟩ := hvals k hzlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = z.name := getElem_of_getElem? hzlt hzget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .bool p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .bool q := Option.some.inj (hsnj.symm.trans hsy)
    have hvr : vzk = .bool r := Option.some.inj (hsnk.symm.trans hsz)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvr] at haz
    exact ⟨p, q, r, hai, haj, haz, hpqr⟩
  · -- bool_or on three slots
    subst hdc'
    obtain ⟨p, q, r, hsx, hsy, hsz, hpqr⟩ :=
      holds_bool_ternary_slot "bool_or" (fun p q => p || q)
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))))
        (fun args => by
          cases args with
          | cons a as =>
              cases as with
              | cons b bs =>
                  cases bs with
                  | cons w ws =>
                      cases a with
                      | bool p' =>
                          cases b with
                          | bool q' =>
                              cases w with
                              | bool w' => rfl
                              | int v => rfl
                              | setOfInt v => rfl
                              | array v => rfl
                          | int v => rfl
                          | setOfInt v => rfl
                          | array v => rfl
                      | int v => rfl
                      | setOfInt v => rfl
                      | array v => rfl
                  | nil => rfl
              | nil => rfl
          | nil => rfl)
        hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hzlt, hzget⟩ := nameIndex_some names z.name k hzi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vzk, haz, hsnk⟩ := hvals k hzlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = z.name := getElem_of_getElem? hzlt hzget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .bool p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .bool q := Option.some.inj (hsnj.symm.trans hsy)
    have hvr : vzk = .bool r := Option.some.inj (hsnk.symm.trans hsz)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvr] at haz
    exact ⟨p, q, r, hai, haj, haz, hpqr⟩
  · -- int_lin_ne on slots
    subst hdc'
    obtain ⟨vs1, vs2, hvs1, hvs2, hdot⟩ := holds_int_lin_ne hname hargs hh
    rw [linCoeffs_eval ks coeffs hcoeffs] at hvs1
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    rw [linIndices_eval hlook elems is his (by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose)] at hvs2
    show dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
    rw [← Option.some.inj hvs1.symm, ← Option.some.inj hvs2.symm]
    exact hdot
  · -- bool_clause on two slot arrays
    subst hdc'
    obtain ⟨vs1, vs2, hvs1, hvs2, hcl⟩ := holds_bool_clause hname hargs hh
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    have hin1 : ∀ i, i ∈ ps → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems1 ps hidx1 i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose
    have hin2 : ∀ j, j ∈ ns → j < a.length := by
      intro j hj
      have hilt := linIndices_lt elems2 ns hidx2 j hj
      obtain ⟨v, hav, _⟩ := hvals j hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose
    rw [linIndices_eval hlook elems1 ps hidx1 hin1] at hvs1
    rw [linIndices_eval hlook elems2 ns hidx2 hin2] at hvs2
    have hv1 : ps.map (fun i => a[i]!) = vs1 := Option.some.inj hvs1
    have hv2 : ns.map (fun j => a[j]!) = vs2 := Option.some.inj hvs2
    rw [← hv1, ← hv2, Bool.or_eq_true] at hcl
    rcases hcl with hcl | hcl
    · exact Or.inl (bang_any_eqB_iff_slotIsBoolB hin1 |>.mp hcl)
    · exact Or.inr (bang_any_eqB_iff_slotIsBoolB hin2 |>.mp hcl)
  · -- array_bool_and on a slot array and a slot target
    subst hdc'
    obtain ⟨vs, vr, hvs, hsr, hvr⟩ := holds_array_bool_and hname hargs hh
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose
    rw [linIndices_eval hlook elems is his hin] at hvs
    have hvm : is.map (fun i => a[i]!) = vs := Option.some.inj hvs
    have hall : vs.all (fun x => x.eqB (.bool true))
        = is.all (fun i => slotIsBoolB a i true) := by
      rw [← hvm]
      rw [show (is.map (fun i => a[i]!)).all (fun v => v.eqB (.bool true))
          = is.all (fun i => (a[i]!).eqB (.bool true)) from List.all_map]
      exact Bool.eq_iff_iff.mpr (bang_all_eqB_iff_slotIsBoolB (b := true) hin)
    rw [hall] at hvr
    obtain ⟨hklt, hkget⟩ := nameIndex_some names r.name k hr
    obtain ⟨vk, hak, hsnk⟩ := hvals k hklt
    have hnk : names[k]! = r.name := getElem_of_getElem? hklt hkget
    rw [hnk] at hsnk
    have hvrk : vk = vr := Option.some.inj (hsnk.symm.trans hsr)
    show a[k]? = some (.bool (is.all (fun i => slotIsBoolB a i true)))
    rw [hak, hvrk, hvr]
  · -- bool2int on two slots
    subst hdc'
    obtain ⟨p, q, hsb, hsi, hkq⟩ := holds_bool2int hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name k hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyk, hak, hsnk⟩ := hvals k hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamek : names[k]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamek] at hsnk
    have hvp : vxi = .bool p := Option.some.inj (hsni.symm.trans hsb)
    have hvq : vyk = .int q := Option.some.inj (hsnk.symm.trans hsi)
    rw [hvp] at hai
    rw [hvq] at hak
    exact ⟨p, hai, by rw [hak, hkq]⟩
  · -- bool_eq on two slots
    subst hdc'
    obtain ⟨p, q, hsx, hsy, hpq⟩ := holds_bool_eq hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    have hvp : vxi = .bool p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .bool q := Option.some.inj (hsnj.symm.trans hsy)
    rw [hvp] at hai
    rw [hvq] at haj
    exact ⟨p, q, hai, haj, hpq⟩
  · -- array_int_element on a constant integer array
    subst hdc'
    obtain ⟨vs, vx, vy, hvs, hsx, hsy, hmatch⟩ :=
      holds_array_int_element hname hargs hh
    rw [intLits_eval elems xs hxs] at hvs
    have hvm : xs.map Value.int = vs := Option.some.inj hvs
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    rw [hnamei] at hsni
    have hvx : vxi = vx := Option.some.inj (hsni.symm.trans hsx)
    obtain ⟨hklt, hkget⟩ := nameIndex_some names y.name k hyk
    obtain ⟨vyk, hak, hsnk⟩ := hvals k hklt
    have hnamek : names[k]! = y.name := getElem_of_getElem? hklt hkget
    rw [hnamek] at hsnk
    have hvy : vyk = vy := Option.some.inj (hsnk.symm.trans hsy)
    cases vx with
    | int idx =>
        cases vy with
        | int e =>
            have hget : valuesGet1 vs idx = some (.int e) := by
              simpa using hmatch
            rw [← hvm] at hget
            rw [hvx] at hai
            rw [hvy] at hak
            exact ⟨idx, e, hai, hak, hget⟩
        | bool w => exact absurd hmatch (by simp)
        | setOfInt w => exact absurd hmatch (by simp)
        | array w => exact absurd hmatch (by simp)
    | bool w => exact absurd hmatch (by simp)
    | setOfInt w => exact absurd hmatch (by simp)
    | array w => exact absurd hmatch (by simp)
  · -- array_var_int_element on an explicit slot array
    subst hdc'
    obtain ⟨vs, vx, vy, hvs, hsx, hsy, hmatch⟩ :=
      holds_array_var_int_element hname hargs hh
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose
    rw [linIndices_eval hlook elems is his hin] at hvs
    have hvm : is.map (fun i => a[i]!) = vs := Option.some.inj hvs
    have hin' : ∀ j ∈ is, ∃ v, a[j]? = some v := by
      intro j hj
      obtain ⟨v, hv, _⟩ := hvals j (linIndices_lt elems is his j hj)
      exact ⟨v, hv⟩
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    rw [hnamei] at hsni
    have hvx : vxi = vx := Option.some.inj (hsni.symm.trans hsx)
    obtain ⟨hklt, hkget⟩ := nameIndex_some names y.name k hyk
    obtain ⟨vyk, hak, hsnk⟩ := hvals k hklt
    have hnamek : names[k]! = y.name := getElem_of_getElem? hklt hkget
    rw [hnamek] at hsnk
    have hvy : vyk = vy := Option.some.inj (hsnk.symm.trans hsy)
    cases vx with
    | int idx =>
        cases vy with
        | int e =>
            have hget : valuesGet1 vs idx = some (.int e) := by
              simpa using hmatch
            rw [← hvm] at hget
            rw [hvx] at hai
            rw [hvy] at hak
            exact ⟨idx, e, hai, hak, hin', hget⟩
        | bool w => exact absurd hmatch (by simp)
        | setOfInt w => exact absurd hmatch (by simp)
        | array w => exact absurd hmatch (by simp)
    | bool w => exact absurd hmatch (by simp)
    | setOfInt w => exact absurd hmatch (by simp)
    | array w => exact absurd hmatch (by simp)
  · -- array_var_bool_element on an explicit slot array
    subst hdc'
    obtain ⟨vs, vx, vy, hvs, hsx, hsy, hmatch⟩ :=
      holds_array_var_bool_element hname hargs hh
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose
    rw [linIndices_eval hlook elems is his hin] at hvs
    have hvm : is.map (fun i => a[i]!) = vs := Option.some.inj hvs
    have hin' : ∀ j ∈ is, ∃ v, a[j]? = some v := by
      intro j hj
      obtain ⟨v, hv, _⟩ := hvals j (linIndices_lt elems is his j hj)
      exact ⟨v, hv⟩
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    rw [hnamei] at hsni
    have hvx : vxi = vx := Option.some.inj (hsni.symm.trans hsx)
    obtain ⟨hklt, hkget⟩ := nameIndex_some names y.name k hyk
    obtain ⟨vyk, hak, hsnk⟩ := hvals k hklt
    have hnamek : names[k]! = y.name := getElem_of_getElem? hklt hkget
    rw [hnamek] at hsnk
    have hvy : vyk = vy := Option.some.inj (hsnk.symm.trans hsy)
    cases vx with
    | int idx =>
        cases vy with
        | bool e =>
            have hget : valuesGet1 vs idx = some (.bool e) := by
              simpa using hmatch
            rw [← hvm] at hget
            rw [hvx] at hai
            rw [hvy] at hak
            exact ⟨idx, e, hai, hak, hin', hget⟩
        | int w => exact absurd hmatch (by simp)
        | setOfInt w => exact absurd hmatch (by simp)
        | array w => exact absurd hmatch (by simp)
    | bool w => exact absurd hmatch (by simp)
    | setOfInt w => exact absurd hmatch (by simp)
    | array w => exact absurd hmatch (by simp)
  · -- int_eq_reif on two slots and a reification slot
    subst hdc'
    obtain ⟨p, q, rb, hsx, hsy, hsr, hiff⟩ :=
      holds_int_eq_reif hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hrlt, hrget⟩ := nameIndex_some names r.name k hrk
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vrk, hak, hsnk⟩ := hvals k hrlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = r.name := getElem_of_getElem? hrlt hrget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    have hvrb : vrk = .bool rb := Option.some.inj (hsnk.symm.trans hsr)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvrb] at hak
    exact ⟨p, q, rb, hai, haj, hak, hiff⟩
  · -- int_le_reif on two slots and a reification slot
    subst hdc'
    obtain ⟨p, q, rb, hsx, hsy, hsr, hiff⟩ :=
      holds_int_le_reif hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hrlt, hrget⟩ := nameIndex_some names r.name k hrk
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vrk, hak, hsnk⟩ := hvals k hrlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = r.name := getElem_of_getElem? hrlt hrget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    have hvrb : vrk = .bool rb := Option.some.inj (hsnk.symm.trans hsr)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvrb] at hak
    exact ⟨p, q, rb, hai, haj, hak, hiff⟩
  · -- int_ne_reif on two slots and a reification slot
    subst hdc'
    obtain ⟨p, q, rb, hsx, hsy, hsr, hiff⟩ :=
      holds_int_ne_reif hname hargs hh
    obtain ⟨hxlt, hxget⟩ := nameIndex_some names x.name i hxi
    obtain ⟨hylt, hyget⟩ := nameIndex_some names y.name j hyi
    obtain ⟨hrlt, hrget⟩ := nameIndex_some names r.name k hrk
    obtain ⟨vxi, hai, hsni⟩ := hvals i hxlt
    obtain ⟨vyj, haj, hsnj⟩ := hvals j hylt
    obtain ⟨vrk, hak, hsnk⟩ := hvals k hrlt
    have hnamei : names[i]! = x.name := getElem_of_getElem? hxlt hxget
    have hnamej : names[j]! = y.name := getElem_of_getElem? hylt hyget
    have hnamek : names[k]! = r.name := getElem_of_getElem? hrlt hrget
    rw [hnamei] at hsni
    rw [hnamej] at hsnj
    rw [hnamek] at hsnk
    have hvp : vxi = .int p := Option.some.inj (hsni.symm.trans hsx)
    have hvq : vyj = .int q := Option.some.inj (hsnj.symm.trans hsy)
    have hvrb : vrk = .bool rb := Option.some.inj (hsnk.symm.trans hsr)
    rw [hvp] at hai
    rw [hvq] at haj
    rw [hvrb] at hak
    exact ⟨p, q, rb, hai, haj, hak, hiff⟩
  · -- int_lin_eq_reif on slots and a reification slot
    subst hdc'
    obtain ⟨vs1, vs2, rb, hvs1, hvs2, hsr, hiff⟩ :=
      holds_int_lin_eq_reif hname hargs hh
    rw [linCoeffs_eval ks coeffs hcoeffs] at hvs1
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    rw [linIndices_eval hlook elems is his (by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose)] at hvs2
    obtain ⟨hrlt, hrget⟩ := nameIndex_some names r.name k hrk
    obtain ⟨vrk, hak, hsnk⟩ := hvals k hrlt
    have hnamek : names[k]! = r.name := getElem_of_getElem? hrlt hrget
    rw [hnamek] at hsnk
    have hvrb : vrk = .bool rb := Option.some.inj (hsnk.symm.trans hsr)
    rw [hvrb] at hak
    show ∃ (rb : Bool), a[k]? = some (.bool rb) ∧
      (rb = true ↔
        dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b)
    refine ⟨rb, hak, ?_⟩
    rw [← Option.some.inj hvs1.symm, ← Option.some.inj hvs2.symm]
    exact hiff
  · -- int_lin_le_reif on slots and a reification slot
    subst hdc'
    obtain ⟨vs1, vs2, rb, hvs1, hvs2, hsr, hiff⟩ :=
      holds_int_lin_le_reif hname hargs hh
    rw [linCoeffs_eval ks coeffs hcoeffs] at hvs1
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    rw [linIndices_eval hlook elems is his (by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose)] at hvs2
    obtain ⟨hrlt, hrget⟩ := nameIndex_some names r.name k hrk
    obtain ⟨vrk, hak, hsnk⟩ := hvals k hrlt
    have hnamek : names[k]! = r.name := getElem_of_getElem? hrlt hrget
    rw [hnamek] at hsnk
    have hvrb : vrk = .bool rb := Option.some.inj (hsnk.symm.trans hsr)
    rw [hvrb] at hak
    show ∃ (rb : Bool), a[k]? = some (.bool rb) ∧
      (rb = true ↔
        dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true)
    refine ⟨rb, hak, ?_⟩
    rw [← Option.some.inj hvs1.symm, ← Option.some.inj hvs2.symm]
    exact hiff
  · -- int_lin_ne_reif on slots and a reification slot
    subst hdc'
    obtain ⟨vs1, vs2, rb, hvs1, hvs2, hsr, hiff⟩ :=
      holds_int_lin_ne_reif hname hargs hh
    rw [linCoeffs_eval ks coeffs hcoeffs] at hvs1
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length :=
        (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    rw [linIndices_eval hlook elems is his (by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      obtain ⟨v, hav, _⟩ := hvals i hilt
      exact (List.getElem?_eq_some_iff.mp hav).choose)] at hvs2
    obtain ⟨hrlt, hrget⟩ := nameIndex_some names r.name k hrk
    obtain ⟨vrk, hak, hsnk⟩ := hvals k hrlt
    have hnamek : names[k]! = r.name := getElem_of_getElem? hrlt hrget
    rw [hnamek] at hsnk
    have hvrb : vrk = .bool rb := Option.some.inj (hsnk.symm.trans hsr)
    rw [hvrb] at hak
    show ∃ (rb : Bool), a[k]? = some (.bool rb) ∧
      (rb = true ↔
        dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true)
    refine ⟨rb, hak, ?_⟩
    rw [← Option.some.inj hvs1.symm, ← Option.some.inj hvs2.symm]
    exact hiff
  · -- int_min in the general three-basic-argument shape
    subst hdc'
    obtain ⟨p, q, r, he₀, he₁, he₂, hmin⟩ :=
      holds_int_arith_gen "int_min" (fun p q r => r = min p q)
        (fullInterp_of_extracted'' "int_min" (Or.inr (Or.inl rfl)))
        (fun args => by
          cases args with
          | nil => rfl
          | cons v₀ rest =>
              cases rest with
              | nil => rfl
              | cons v₁ rest2 =>
                  cases rest2 with
                  | nil => rfl
                  | cons v₂ rest3 =>
                      cases rest3 with
                      | nil => cases v₀ <;> cases v₁ <;> cases v₂ <;> rfl
                      | cons v₃ rest4 => rfl)
        hname hargs hh
    exact ⟨p, q, intArgOf_read hvals ho₀ he₀, intArgOf_read hvals ho₁ he₁,
      by rw [intArgOf_read hvals ho₂ he₂, hmin]⟩
  · -- int_max in the general three-basic-argument shape
    subst hdc'
    obtain ⟨p, q, r, he₀, he₁, he₂, hmax⟩ :=
      holds_int_arith_gen "int_max" (fun p q r => r = max p q)
        (fullInterp_of_extracted'' "int_max" (Or.inr (Or.inr (Or.inl rfl))))
        (fun args => by
          cases args with
          | nil => rfl
          | cons v₀ rest =>
              cases rest with
              | nil => rfl
              | cons v₁ rest2 =>
                  cases rest2 with
                  | nil => rfl
                  | cons v₂ rest3 =>
                      cases rest3 with
                      | nil => cases v₀ <;> cases v₁ <;> cases v₂ <;> rfl
                      | cons v₃ rest4 => rfl)
        hname hargs hh
    exact ⟨p, q, intArgOf_read hvals ho₀ he₀, intArgOf_read hvals ho₁ he₁,
      by rw [intArgOf_read hvals ho₂ he₂, hmax]⟩
  · -- int_div in the general three-basic-argument shape
    subst hdc'
    obtain ⟨p, q, r, he₀, he₁, he₂, hq, hr⟩ :=
      holds_int_arith_gen "int_div" (fun p q r => q ≠ 0 ∧ r = Int.tdiv p q)
        (fullInterp_of_extracted_arith "int_div" (Or.inl rfl))
        (fun args => by
          cases args with
          | nil => rfl
          | cons v₀ rest =>
              cases rest with
              | nil => rfl
              | cons v₁ rest2 =>
                  cases rest2 with
                  | nil => rfl
                  | cons v₂ rest3 =>
                      cases rest3 with
                      | nil => cases v₀ <;> cases v₁ <;> cases v₂ <;> rfl
                      | cons v₃ rest4 => rfl)
        hname hargs hh
    exact ⟨p, q, intArgOf_read hvals ho₀ he₀, intArgOf_read hvals ho₁ he₁, hq,
      by rw [intArgOf_read hvals ho₂ he₂, hr]⟩
  · -- int_mod in the general three-basic-argument shape
    subst hdc'
    obtain ⟨p, q, r, he₀, he₁, he₂, hq, hr⟩ :=
      holds_int_arith_gen "int_mod" (fun p q r => q ≠ 0 ∧ r = Int.tmod p q)
        (fullInterp_of_extracted_arith "int_mod" (Or.inr (Or.inl rfl)))
        (fun args => by
          cases args with
          | nil => rfl
          | cons v₀ rest =>
              cases rest with
              | nil => rfl
              | cons v₁ rest2 =>
                  cases rest2 with
                  | nil => rfl
                  | cons v₂ rest3 =>
                      cases rest3 with
                      | nil => cases v₀ <;> cases v₁ <;> cases v₂ <;> rfl
                      | cons v₃ rest4 => rfl)
        hname hargs hh
    exact ⟨p, q, intArgOf_read hvals ho₀ he₀, intArgOf_read hvals ho₁ he₁, hq,
      by rw [intArgOf_read hvals ho₂ he₂, hr]⟩
  · -- array_int_maximum on a slot array and a slot target
    subst hdc'
    obtain ⟨m, vs, hsm, hvs, hmax⟩ :=
      holds_array_int_extreme "array_int_maximum" maxValue
        (fullInterp_of_extracted_arith "array_int_maximum"
          (Or.inr (Or.inr (Or.inl rfl))))
        (fun args => by
          cases args with
          | nil => rfl
          | cons v₀ rest =>
              cases rest with
              | nil => rfl
              | cons v₁ rest2 =>
                  cases rest2 with
                  | nil => cases v₀ <;> cases v₁ <;> rfl
                  | cons v₂ rest3 => rfl)
        hname hargs hh
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length := (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    have hvs_eq : vs = is.map (fun i => a[i]!) :=
      Option.some.inj (hvs.symm.trans (linIndices_eval hlook elems is his (by
        intro i hi
        have hilt := linIndices_lt elems is his i hi
        obtain ⟨v, hav, _⟩ := hvals i hilt
        exact (List.getElem?_eq_some_iff.mp hav).choose)))
    have ho_k : intArgOf names (.ident x) = some (.slot k) := by
      show (nameIndex names x.name).map DomIntArg.slot = some (.slot k)
      rw [hk]
      rfl
    refine ⟨m, intArgOf_read hvals ho_k hsm, ?_⟩
    show maxValue ((is.map DomIntArg.slot).map (DomIntArg.read a)) = some m
    rw [List.map_map]
    show maxValue (is.map (fun i => a[i]!)) = some m
    rw [← hvs_eq]
    exact hmax
  · -- array_int_minimum on a slot array and a slot target
    subst hdc'
    obtain ⟨m, vs, hsm, hvs, hmin⟩ :=
      holds_array_int_extreme "array_int_minimum" minValue
        (fullInterp_of_extracted_arith "array_int_minimum"
          (Or.inr (Or.inr (Or.inr rfl))))
        (fun args => by
          cases args with
          | nil => rfl
          | cons v₀ rest =>
              cases rest with
              | nil => rfl
              | cons v₁ rest2 =>
                  cases rest2 with
                  | nil => cases v₀ <;> cases v₁ <;> rfl
                  | cons v₂ rest3 => rfl)
        hname hargs hh
    have hlook : ∀ (i : Nat), i < names.length → ∀ (v : Value), a[i]? = some v →
        store (Ident.mk names[i]!) = some v := by
      intro i hlt v hv
      obtain ⟨v', hv', hst⟩ := hvals i hlt
      have hlt' : i < a.length := (List.getElem?_eq_some_iff.mp hv).choose
      rw [List.getElem?_eq_getElem hlt'] at hv
      rw [List.getElem?_eq_getElem hlt'] at hv'
      have hvv : v = v' := Option.some.inj (hv.symm.trans hv')
      rw [← hvv] at hst
      exact hst
    have hvs_eq : vs = is.map (fun i => a[i]!) :=
      Option.some.inj (hvs.symm.trans (linIndices_eval hlook elems is his (by
        intro i hi
        have hilt := linIndices_lt elems is his i hi
        obtain ⟨v, hav, _⟩ := hvals i hilt
        exact (List.getElem?_eq_some_iff.mp hav).choose)))
    have ho_k : intArgOf names (.ident x) = some (.slot k) := by
      show (nameIndex names x.name).map DomIntArg.slot = some (.slot k)
      rw [hk]
      rfl
    refine ⟨m, intArgOf_read hvals ho_k hsm, ?_⟩
    show minValue ((is.map DomIntArg.slot).map (DomIntArg.read a)) = some m
    rw [List.map_map]
    show minValue (is.map (fun i => a[i]!)) = some m
    rw [← hvs_eq]
    exact hmin

end LeanFzn.Compiler
