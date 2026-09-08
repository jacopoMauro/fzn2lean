import LeanFzn.FznSemantics

/-!
# Standard FlatZinc predicate library

Signatures (`stdSig`) and mathematical interpretations (`stdInterp`) for the
standard FlatZinc builtins of the integer/Boolean fragment, following the
MiniZinc 2.10.0 FlatZinc specification's standard-predicate table.

`stdSig` is a `SigEnv`: it can be passed to `wellFormedB` so that models
using standard predicates are statically checked against their official
signatures.  `stdInterp` is a `PredicateInterpretation`: it gives each
predicate its intended mathematical meaning, so `Satisfies stdSig stdInterp
m store` states that `store` solves `m` under the standard semantics.

Interpretations are written to be decidable wherever practical: computable
Boolean helpers (`Value.eqB`, `valuesAllDifferent`, `dotProduct`, …) are
used instead of quantifiers over infinite domains, so the tests in
`Tests/StdLib.lean` can evaluate them with `decide`.  The set predicates
whose meaning is inherently extensional (`set_eq`, `set_subset`,
`set_union`, `set_intersection`, `set_diff`) quantify over all integers and
are therefore only exercised by static signature checking.
-/

namespace LeanFzn

/-! ## Computable helpers -/

/-- Structural equality test on integer sets. -/
def IntSetValue.eqB : IntSetValue → IntSetValue → Bool
  | .enumeration xs, .enumeration ys =>
      xs.length == ys.length &&
        (xs.zip ys).all (fun (a, b) => a == b)
  | .interval lo hi, .interval lo' hi' => lo == lo' && hi == hi'
  | _, _ => false

/- Structural equality test on values, and on lists of values (arrays
   compare elementwise).  Defined mutually so the recursion is
   first-order. -/
mutual
  def Value.eqB : Value → Value → Bool
    | .bool a, .bool b => a == b
    | .int a, .int b => a == b
    | .setOfInt a, .setOfInt b => a.eqB b
    | .array xs, .array ys => valuesEqB xs ys
    | _, _ => false

  def valuesEqB : List Value → List Value → Bool
    | [], [] => true
    | x :: xs, y :: ys => x.eqB y && valuesEqB xs ys
    | _, _ => false
end

/-- Cardinality of an integer set: number of elements of an enumeration,
    size of an interval (zero when the bounds are reversed, R1). -/
def IntSetValue.card : IntSetValue → Nat
  | .enumeration xs => xs.length
  | .interval lo hi => if hi < lo then 0 else (hi - lo + 1).toNat

/-- Membership in an integer set is decidable. -/
instance : DecidablePred (IntSetValue.Contains s) := by
  cases s with
  | enumeration xs =>
      intro a
      show Decidable (a ∈ xs)
      infer_instance
  | interval lo hi =>
      intro a
      show Decidable (lo ≤ a ∧ a ≤ hi)
      infer_instance

/-- Are all elements of the value list pairwise distinct? -/
def valuesAllDifferent : List Value → Bool
  | [] => true
  | x :: xs => !(xs.any (fun y => x.eqB y)) && valuesAllDifferent xs

/-- Pairwise distinctness ignoring zeros: two elements may be equal only
    when at least one of them is zero. -/
def valuesAllDifferentExcept0 : List Value → Bool
  | [] => true
  | x :: xs =>
      !(xs.any (fun y => !(x.eqB (.int 0)) && !(y.eqB (.int 0)) && x.eqB y))
        && valuesAllDifferentExcept0 xs

/-- Dot product of an integer list and a value list; `none` on shape or
    length mismatch. -/
def dotProduct : List Value → List Value → Option Int
  | .int a :: as_, .int x :: xs =>
      match dotProduct as_ xs with
      | some s => some (a * x + s)
      | none => none
  | [], [] => some 0
  | _, _ => none

/-- `dotProduct as_ xs` exists and is at most `b`. -/
def dotLe (as_ xs : List Value) (b : Int) : Bool :=
  match dotProduct as_ xs with
  | some d => decide (d ≤ b)
  | none => false

/-- `dotProduct as_ xs` exists and differs from `b`. -/
def dotNe (as_ xs : List Value) (b : Int) : Bool :=
  match dotProduct as_ xs with
  | some d => decide (d ≠ b)
  | none => false

/-- Maximum of the integers in a value list; `none` if empty or any
    element is not an integer. -/
def maxValue : List Value → Option Int
  | [] => none
  | .int x :: xs => match maxValue xs with
    | some m => some (max x m)
    | none => some x
  | _ :: _ => none

/-- Minimum of the integers in a value list; `none` if empty or any
    element is not an integer. -/
def minValue : List Value → Option Int
  | [] => none
  | .int x :: xs => match minValue xs with
    | some m => some (min x m)
    | none => some x
  | _ :: _ => none

/-! ## Standard signatures -/

/-- Signature environment for the standard FlatZinc predicates of the
    integer/Boolean fragment.  Parameter types follow the MiniZinc 2.10.0
    FlatZinc specification. -/
def stdSig : SigEnv := fun x =>
  match x.name with
  | "int_eq" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_ne" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_le" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_lt" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_ge" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_gt" => some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "int_eq_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_ne_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_le_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_lt_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_ge_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "int_gt_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))]
  | "bool_eq" => some [.basic (.var (.par .bool)), .basic (.var (.par .bool))]
  | "bool_not" => some [.basic (.var (.par .bool)), .basic (.var (.par .bool))]
  | "bool_and" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_or" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_xor" =>
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))]
  | "bool_clause" =>
      some [.array .int (.var (.par .bool)), .array .int (.var (.par .bool))]
  | "int_plus" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_minus" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_times" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_div" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_mod" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_min" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_max" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_abs" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .int))]
  | "set_in" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt))]
  | "set_in_reif" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))]
  | "set_eq" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_subset" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt))]
  | "set_card" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .int))]
  | "set_union" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "set_intersection" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "set_diff" =>
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))]
  | "all_different" => some [.array .int (.var (.par .int))]
  | "all_different_except_0" => some [.array .int (.var (.par .int))]
  | "int_lin_eq" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_lin_le" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "int_lin_ne" =>
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))]
  | "array_int_maximum" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int))]
  | "array_int_minimum" =>
      some [.basic (.var (.par .int)), .array .int (.var (.par .int))]
  | "true" => some []
  | "dom" =>
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt))]
  | _ => none

/-- Convenience: static well-formedness under the standard signatures. -/
def stdWellFormed (m : Model) : Bool := wellFormedB stdSig m

/-! ## Standard interpretations -/

/-- Mathematical interpretations of the standard FlatZinc predicates.
    Each case matches the argument list; a wrong shape yields `False`.
    Quantifier-free cases are decidable; the extensional set predicates
    (`set_eq`, `set_subset`, `set_union`, `set_intersection`, `set_diff`)
    quantify over all integers and are not decidable. -/
def stdInterp : PredicateInterpretation := fun x =>
  match x.name with
  | "int_eq" => fun args =>
    match args with
    | [.int a, .int b] => a = b
    | _ => False
  | "int_ne" => fun args =>
    match args with
    | [.int a, .int b] => a ≠ b
    | _ => False
  | "int_le" => fun args =>
    match args with
    | [.int a, .int b] => a ≤ b
    | _ => False
  | "int_lt" => fun args =>
    match args with
    | [.int a, .int b] => a < b
    | _ => False
  | "int_ge" => fun args =>
    match args with
    | [.int a, .int b] => a ≥ b
    | _ => False
  | "int_gt" => fun args =>
    match args with
    | [.int a, .int b] => a > b
    | _ => False
  | "int_eq_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a = b) ∨ (r = false ∧ a ≠ b)
    | _ => False
  | "int_ne_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a ≠ b) ∨ (r = false ∧ a = b)
    | _ => False
  | "int_le_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a ≤ b) ∨ (r = false ∧ a > b)
    | _ => False
  | "int_lt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a < b) ∨ (r = false ∧ a ≥ b)
    | _ => False
  | "int_ge_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a ≥ b) ∨ (r = false ∧ a < b)
    | _ => False
  | "int_gt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] => (r = true ∧ a > b) ∨ (r = false ∧ a ≤ b)
    | _ => False
  | "bool_eq" => fun args =>
    match args with
    | [.bool a, .bool b] => a = b
    | _ => False
  | "bool_not" => fun args =>
    match args with
    | [.bool a, .bool b] => b = !a
    | _ => False
  | "bool_and" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => c = (a && b)
    | _ => False
  | "bool_or" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => c = (a || b)
    | _ => False
  | "bool_xor" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => c = (a ^^ b)
    | _ => False
  | "bool_clause" => fun args =>
    match args with
    | [.array xs, .array ys] =>
        ((xs.any (fun x => x.eqB (.bool true))) ||
          (ys.any (fun y => y.eqB (.bool true)))) = true
    | _ => False
  | "int_plus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => a + b = c
    | _ => False
  | "int_minus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => a - b = c
    | _ => False
  | "int_times" => fun args =>
    match args with
    | [.int a, .int b, .int c] => a * b = c
    | _ => False
  | "int_div" => fun args =>
    match args with
    | [.int a, .int b, .int c] => b ≠ 0 ∧ c = a / b
    | _ => False
  | "int_mod" => fun args =>
    match args with
    | [.int a, .int b, .int c] => b ≠ 0 ∧ c = a % b
    | _ => False
  | "int_min" => fun args =>
    match args with
    | [.int a, .int b, .int c] => c = min a b
    | _ => False
  | "int_max" => fun args =>
    match args with
    | [.int a, .int b, .int c] => c = max a b
    | _ => False
  | "int_abs" => fun args =>
    match args with
    | [.int a, .int b] => b = if a < 0 then -a else a
    | _ => False
  | "set_in" => fun args =>
    match args with
    | [.int a, .setOfInt s] => s.Contains a
    | _ => False
  | "set_in_reif" => fun args =>
    match args with
    | [.int a, .setOfInt s, .bool r] =>
        (r = true ∧ s.Contains a) ∨ (r = false ∧ ¬ s.Contains a)
    | _ => False
  | "dom" => fun args =>
    match args with
    | [.int a, .setOfInt s] => s.Contains a
    | _ => False
  | "set_card" => fun args =>
    match args with
    | [.setOfInt s, .int n] => n = s.card
    | _ => False
  | "set_eq" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => ∀ i, a.Contains i ↔ b.Contains i
    | _ => False
  | "set_subset" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b] => ∀ i, a.Contains i → b.Contains i
    | _ => False
  | "set_union" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        ∀ i, c.Contains i ↔ a.Contains i ∨ b.Contains i
    | _ => False
  | "set_intersection" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        ∀ i, c.Contains i ↔ a.Contains i ∧ b.Contains i
    | _ => False
  | "set_diff" => fun args =>
    match args with
    | [.setOfInt a, .setOfInt b, .setOfInt c] =>
        ∀ i, c.Contains i ↔ a.Contains i ∧ ¬ b.Contains i
    | _ => False
  | "all_different" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferent xs
    | _ => False
  | "all_different_except_0" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferentExcept0 xs
    | _ => False
  | "int_lin_eq" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotProduct as_ xs = some b
    | _ => False
  | "int_lin_le" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotLe as_ xs b = true
    | _ => False
  | "int_lin_ne" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotNe as_ xs b = true
    | _ => False
  | "array_int_maximum" => fun args =>
    match args with
    | [.int m, .array xs] => maxValue xs = some m
    | _ => False
  | "array_int_minimum" => fun args =>
    match args with
    | [.int m, .array xs] => minValue xs = some m
    | _ => False
  | "true" => fun args =>
    match args with
    | [] => True
    | _ => False
  | _ => fun _ => False

/-- **Executable twin of `stdInterp`**: computes the truth of the decidable
    standard-predicate interpretations.  Mirrors `stdInterp` case by case;
    the extensional set predicates (`set_eq`, `set_subset`, `set_union`,
    `set_intersection`, `set_diff`) quantify over all integers, are not
    computable, and return `false` here — use `stdInterp` for their
    mathematical meaning.  The equivalence with `stdInterp` on the
    decidable fragment is left as future work (the `wellFormedB_iff`
    pattern). -/
def stdInterpB : Ident → List Value → Bool := fun x =>
  match x.name with
  | "int_eq" => fun args =>
    match args with
    | [.int a, .int b] => decide (a = b)
    | _ => false
  | "int_ne" => fun args =>
    match args with
    | [.int a, .int b] => decide (a ≠ b)
    | _ => false
  | "int_le" => fun args =>
    match args with
    | [.int a, .int b] => decide (a ≤ b)
    | _ => false
  | "int_lt" => fun args =>
    match args with
    | [.int a, .int b] => decide (a < b)
    | _ => false
  | "int_ge" => fun args =>
    match args with
    | [.int a, .int b] => decide (a ≥ b)
    | _ => false
  | "int_gt" => fun args =>
    match args with
    | [.int a, .int b] => decide (a > b)
    | _ => false
  | "int_eq_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a = b) ∨ (r = false ∧ a ≠ b))
    | _ => false
  | "int_ne_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a ≠ b) ∨ (r = false ∧ a = b))
    | _ => false
  | "int_le_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a ≤ b) ∨ (r = false ∧ a > b))
    | _ => false
  | "int_lt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a < b) ∨ (r = false ∧ a ≥ b))
    | _ => false
  | "int_ge_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a ≥ b) ∨ (r = false ∧ a < b))
    | _ => false
  | "int_gt_reif" => fun args =>
    match args with
    | [.int a, .int b, .bool r] =>
        decide ((r = true ∧ a > b) ∨ (r = false ∧ a ≤ b))
    | _ => false
  | "bool_eq" => fun args =>
    match args with
    | [.bool a, .bool b] => decide (a = b)
    | _ => false
  | "bool_not" => fun args =>
    match args with
    | [.bool a, .bool b] => decide (b = !a)
    | _ => false
  | "bool_and" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => decide (c = (a && b))
    | _ => false
  | "bool_or" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => decide (c = (a || b))
    | _ => false
  | "bool_xor" => fun args =>
    match args with
    | [.bool a, .bool b, .bool c] => decide (c = (a ^^ b))
    | _ => false
  | "bool_clause" => fun args =>
    match args with
    | [.array xs, .array ys] =>
        (xs.any (fun x => x.eqB (.bool true))) ||
          (ys.any (fun y => y.eqB (.bool true)))
    | _ => false
  | "int_plus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (a + b = c)
    | _ => false
  | "int_minus" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (a - b = c)
    | _ => false
  | "int_times" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (a * b = c)
    | _ => false
  | "int_div" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (b ≠ 0 ∧ c = a / b)
    | _ => false
  | "int_mod" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (b ≠ 0 ∧ c = a % b)
    | _ => false
  | "int_min" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (c = min a b)
    | _ => false
  | "int_max" => fun args =>
    match args with
    | [.int a, .int b, .int c] => decide (c = max a b)
    | _ => false
  | "int_abs" => fun args =>
    match args with
    | [.int a, .int b] => decide (b = if a < 0 then -a else a)
    | _ => false
  | "set_in" => fun args =>
    match args with
    | [.int a, .setOfInt s] => decide (s.Contains a)
    | _ => false
  | "set_in_reif" => fun args =>
    match args with
    | [.int a, .setOfInt s, .bool r] =>
        decide ((r = true ∧ s.Contains a) ∨ (r = false ∧ ¬ s.Contains a))
    | _ => false
  | "dom" => fun args =>
    match args with
    | [.int a, .setOfInt s] => decide (s.Contains a)
    | _ => false
  | "set_card" => fun args =>
    match args with
    | [.setOfInt s, .int n] => decide (n = s.card)
    | _ => false
  | "all_different" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferent xs
    | _ => false
  | "all_different_except_0" => fun args =>
    match args with
    | [.array xs] => valuesAllDifferentExcept0 xs
    | _ => false
  | "int_lin_eq" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotProduct as_ xs == some b
    | _ => false
  | "int_lin_le" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotLe as_ xs b
    | _ => false
  | "int_lin_ne" => fun args =>
    match args with
    | [.array as_, .array xs, .int b] => dotNe as_ xs b
    | _ => false
  | "array_int_maximum" => fun args =>
    match args with
    | [.int m, .array xs] => maxValue xs == some m
    | _ => false
  | "array_int_minimum" => fun args =>
    match args with
    | [.int m, .array xs] => minValue xs == some m
    | _ => false
  | "true" => fun args =>
    match args with
    | [] => true
    | _ => false
  | _ => fun _ => false

end LeanFzn
