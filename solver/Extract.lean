/-
File: solver/Extract.lean

Purpose:
Extraction of slot-indexed constraints from a FlatZinc model's
constraint list, for the pruning search of PLAN 6.3
(`solver/Fixpoint.lean`).  Each recognized predicate-argument shape is
translated to a `DomConstraint` over the model's search-slot
positions, so the propagators of `solver/Propagators.lean` can
narrow the slot domains during search.
-/

import LeanFzn
import solver.Domain
import solver.Propagators

/-! ## Slot-name indexing

`nameIndex names s` is the position of `s` in the slot-name list, if
any. -/

namespace LeanFzn.Solver

open LeanFzn LeanFzn.Solution LeanFzn.Globals

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
private theorem getElem_of_getElem? {α : Type} [Inhabited α] {l : List α}
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
(Fixpoint.lean) needs, stated at the store level: if a store
satisfies the model's constraint list under `fullInterp` (the
`SatisfiesDyn` constraint half, the very thing
`checkModelSolution_correct` certifies for accepted solutions) and the
store maps each slot name to the assignment's value at that slot
(the emitter round-trip obligation), then every extracted
`DomConstraint` is `SatisfiedBy` the assignment.

Connecting the store-value hypothesis to the leaf predicate — the
string round trip "the checker accepted the text emitted from `a`,
therefore the completed store assigns the slot names `a`'s values" —
is deliberately *not* proven here: `completedStore` is `opaque` by
design (a compilation safeguard, see `LeanFzn/FznSolution.lean`), so
no lemma can see its content.  The integrated UNSAT theorem
(`solveModelProp_unsat_sound` in `solver/Solve.lean`) therefore
carries that step as an explicit licence. -/

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
      | _ => none
  | "int_max" =>
      match c.args with
      | [.basic (.ident x), .basic (.ident y), .basic (.ident z)] =>
          match nameIndex names x.name, nameIndex names y.name,
            nameIndex names z.name with
          | some i, some j, some k => some (.maxSlot i j k)
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
private theorem fullInterp_of_extracted (n : String)
    (hn : n = "int_eq" ∨ n = "int_ne" ∨ n = "int_le") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The same bridge for the two further standard names extracted in
    this round (`int_plus`, `all_different`). -/
private theorem fullInterp_of_extracted' (n : String)
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
private theorem fullInterp_of_extracted'' (n : String)
    (hn : n = "int_times" ∨ n = "int_min" ∨ n = "int_max" ∨ n = "int_abs"
      ∨ n = "int_lt" ∨ n = "bool_not" ∨ n = "bool_and" ∨ n = "bool_or") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- The interpretation of a holding constraint is about its own
    name: transport `hinterp` to the spelled-out name. -/
private theorem interp_of_hname {c : ConstraintItem}
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
private theorem mapM_two_ident {store : Store} {c : ConstraintItem}
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
private theorem mapM_three_ident {store : Store} {c : ConstraintItem}
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
private theorem mapM_two_const {store : Store} {c : ConstraintItem}
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
private theorem mapM_two_const' {store : Store} {c : ConstraintItem}
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

/-- Inversion of `Holds` for `int_eq(slot, slot)`: the store's values
    at the two names are equal. -/
private theorem holds_int_eq_slot {store : Store} {c : ConstraintItem}
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
private theorem holds_int_eq_const {store : Store} {c : ConstraintItem}
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
private theorem holds_int_eq_const' {store : Store} {c : ConstraintItem}
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
private theorem holds_int_ne_slot {store : Store} {c : ConstraintItem}
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
private theorem holds_int_le_slot {store : Store} {c : ConstraintItem}
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
private theorem holds_int_le_const {store : Store} {c : ConstraintItem}
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
private theorem holds_int_le_const' {store : Store} {c : ConstraintItem}
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
private theorem holds_int_plus_slot {store : Store} {c : ConstraintItem}
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
private theorem holds_int_ternary_slot
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
private theorem holds_int_abs_slot {store : Store} {c : ConstraintItem}
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
private theorem holds_int_lt_slot {store : Store} {c : ConstraintItem}
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
private theorem holds_int_lt_const {store : Store} {c : ConstraintItem}
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
private theorem holds_int_lt_const' {store : Store} {c : ConstraintItem}
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
private theorem holds_bool_not_slot {store : Store} {c : ConstraintItem}
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
private theorem holds_bool_ternary_slot
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
private theorem mapM_lin {store : Store} {c : ConstraintItem}
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

/-- Inversion of `Holds` for an `int_lin_eq` on slots. -/
private theorem holds_int_lin_eq {store : Store} {c : ConstraintItem}
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
private theorem holds_int_lin_le {store : Store} {c : ConstraintItem}
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

/-- Inversion of `Holds` for an explicit-array `all_different`: the
    array's elements all evaluate, and the values are pairwise
    different. -/
private theorem holds_all_different {store : Store} {c : ConstraintItem}
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

end HoldsBridge

/-- The evaluated values of a coefficient array that produced
    `coeffs` via `linCoeffs` are exactly `intVals coeffs`. -/
private theorem linCoeffs_eval {store : Store} :
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

/-- Every position produced by `linIndices` is in bounds for
    `names` (the slot-name list it indexes). -/
private theorem linIndices_lt {names : List String} :
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
private theorem linIndices_eval {names : List String} {store : Store}
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
private theorem allDiff_map_eq {names : List String} {store : Store} {a : List Value}
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

/-- **Extraction inversion**: if `extractConstraint names c`
    produced a constraint, then the model constraint has one of the
    extracted shapes — the name is one of the extracted predicates,
    the arguments are the corresponding identifier/literal/array
    pattern, and the slot names resolve. -/
private theorem extractConstraint_inv {names : List String} {c : ConstraintItem}
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
        nameIndex names z.name = some k ∧ dc = .boolOrSlot i j k) := by
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
    case h_2 => exact absurd hdc (by simp)
  case h_10 heqname =>
    split at hdc
    case h_1 x y z heqargs =>
      split at hdc
      case h_1 i j k hxi hyi hzi =>
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩)))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
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
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (⟨x, y, z, i, j, k, heqname, heqargs, hxi, hyi, hzi,
          by simpa using hdc.symm⟩))))))))))))))))))))
      case h_2 => exact absurd hdc (by simp)
    case h_2 => exact absurd hdc (by simp)
  case h_16 => exact absurd hdc (by simp)

/-- **Per-constraint extraction soundness**: if the model constraint
    `c` holds in `store` (under `fullInterp`, the interpretation the
    verified checker certifies), and `extractConstraint names c`
    produced `dc`, then `dc` is `SatisfiedBy` any assignment `a`
    whose slot values agree with the store at the slot names
    (`hvals`: position `i` of `a` is the store's value at the
    slot-`i` name, whenever `i` is in bounds). -/
private theorem extractConstraint_holds {names : List String} {c : ConstraintItem}
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
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩
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

end LeanFzn.Solver