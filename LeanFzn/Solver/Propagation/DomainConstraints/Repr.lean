import LeanFzn.Solver.Propagation.DomainConstraints.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Solver.Core
open LeanFzn LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core List
open LeanFzn.Solver.Propagation.DomainFiltering.Internal

namespace LeanFzn.Solver.Propagation.DomainFiltering

/-! ## Constraint representation -/

/-- An integer operand of a GENERAL arithmetic constraint: a slot
    position or an integer literal. The general shapes of `int_max` /
    `int_min` / `int_div` / `int_mod` accept either, and the array
    forms `array_int_maximum(m, xs)` / `array_int_minimum(m, xs)`
    (result slot `m` first) are the all-slot special case. -/
inductive DomIntArg where
  /-- The value at a slot position. -/
  | slot (i : Nat)
  /-- An integer literal. -/
  | lit (k : Int)
  deriving DecidableEq, Repr

namespace DomIntArg

/-- The value an operand reads from an assignment: the slot's value (the
    bang read, matching the `linEq`/`allDiff` convention) or the
    literal's integer. -/
def read (a : List Value) : DomIntArg → Value
  | .slot i => a[i]!
  | .lit k => .int k

/-- Array-assignment read: identical to `read`, with O(1) slot lookup. -/
def readA (a : Array Value) : DomIntArg → Value
  | .slot i => a[i]!
  | .lit k => .int k

/-- `readA` on the array mirror is `read` on the list. -/
theorem readA_toArray_eq (a : List Value) :
    readA a.toArray = read a := by
  funext x
  cases x <;> simp [readA, read]

/-- The slot positions an operand names. -/
def slots : DomIntArg → List Nat
  | .slot i => [i]
  | .lit _ => []

/-- `read` unfolded at a slot. -/
theorem read_slot (a : List Value) (i : Nat) :
    read a (.slot i) = a[i]! := rfl

/-- `read` unfolded at a literal. -/
theorem read_lit (a : List Value) (k : Int) :
    read a (.lit k) = .int k := rfl

end DomIntArg

/-- A constraint over slot positions: the declarative representation a
    propagator narrows domains for.  The positions index the search
    slots of `LeanFzn/Compiler/Domain.lean`; each constructor matches the
    corresponding FlatZinc predicate on scalar values (`int_eq`,
    `int_eq(x, c)` after constant propagation, `int_plus` on three
    slots, `int_le(x, c)` / `int_le(c, x)` against a constant, and
    `all_different` over an explicit array of slots).  The arithmetic
    predicates extend it: `timesSlot i j k` (slot `i` times slot `j`
    equals slot `k` — `int_times` style), `minSlot i j k` / `maxSlot i
    j k` (slot `k` carries the minimum / maximum of slots `i` and `j`
    — `int_min` / `int_max` style), and `absSlot i k` (slot `k`
    carries the absolute value of slot `i` — `int_abs` style). -/
inductive DomConstraint where
  /-- Slots `i` and `j` must carry equal values (`int_eq` style). -/
  | eqSlot (i j : Nat)
  /-- Slots `i` and `j` must carry different values (`int_ne` style). -/
  | neSlot (i j : Nat)
  /-- Slot `i`'s value must be at most slot `j`'s (`int_le` style). -/
  | leSlot (i j : Nat)
  /-- Slot `i` must carry the constant `v`. -/
  | constEq (i : Nat) (v : Value)
  /-- Slot `i`'s value plus slot `j`'s must equal slot `k`'s
      (`int_plus` style). -/
  | plusSlot (i j k : Nat)
  /-- Slot `i`'s value must be at most the integer `c`
      (`int_le(x, c)` style). -/
  | leConstHi (i : Nat) (c : Int)
  /-- Slot `i`'s value must be at least the integer `c`
      (`int_le(c, x)` style). -/
  | leConstLo (i : Nat) (c : Int)
  /-- The slots at the positions of `is` must carry pairwise
      different values (`all_different` style). -/
  | allDiff (is : List Nat)
  /-- Slot `i`'s value times slot `j`'s must equal slot `k`'s
      (`int_times` style). -/
  | timesSlot (i j k : Nat)
  /-- Slot `k`'s value must be the minimum of slots `i`'s and `j`'s
      (`int_min` style). -/
  | minSlot (i j k : Nat)
  /-- Slot `k`'s value must be the maximum of slots `i`'s and `j`'s
      (`int_max` style). -/
  | maxSlot (i j k : Nat)
  /-- Slot `k`'s value must be the absolute value of slot `i`'s
      (`int_abs` style). -/
  | absSlot (i k : Nat)
  /-- Linear equality: the dot product of `coeffs` and the values at
      the slot positions `is` equals `b` (`int_lin_eq` style). -/
  | linEq (coeffs : List Int) (is : List Nat) (b : Int)
  /-- Linear inequality: the dot product of `coeffs` and the values at
      the slot positions `is` is at most `b` (`int_lin_le` style). -/
  | linLe (coeffs : List Int) (is : List Nat) (b : Int)
  /-- Linear disequality: the dot product of `coeffs` and the values at
      the slot positions `is` differs from `b` (`int_lin_ne` style). -/
  | linNe (coeffs : List Int) (is : List Nat) (b : Int)
  /-- Slot `i`'s value must be strictly below slot `j`'s
      (`int_lt` style). -/
  | ltSlot (i j : Nat)
  /-- Slot `i`'s value must be strictly below the integer `c`
      (`int_lt(x, c)` style). -/
  | ltConstHi (i : Nat) (c : Int)
  /-- Slot `i`'s value must be strictly above the integer `c`
      (`int_lt(c, x)` style). -/
  | ltConstLo (i : Nat) (c : Int)
  /-- Slot `j`'s value must be the negation of slot `i`'s Boolean
      (`bool_not` style). -/
  | boolNotSlot (i j : Nat)
  /-- Slot `k`'s value must be the conjunction of slots `i`'s and
      `j`'s Booleans (`bool_and` style). -/
  | boolAndSlot (i j k : Nat)
  /-- Slot `k`'s value must be the disjunction of slots `i`'s and
      `j`'s Booleans (`bool_or` style). -/
  | boolOrSlot (i j k : Nat)
  /-- The Boolean clause "some slot of `ps` is true, or some slot of
      `ns` is false" (`bool_clause` style: the positive argument
      array `ps`, the negated argument array `ns`). The constraint is
      enforced at the leaf (no propagator is registered); the
      compiler additionally seeds the corresponding original clause
      `∨ ps ∨ ¬ns` into the clause database (see `SeedClauses` and
      `Integration.Lcg`) so the LCG engine can propagate it. -/
  | boolClauseSlot (ps ns : List Nat)
  /-- Slot `k`'s Boolean must be the conjunction of the Booleans at
      the listed slots (`array_bool_and` style: the source form
      `array_bool_and(array of var bool, var bool)`). The target's
      truth value IS the `all` of the source slots' `= true` reads,
      so the EMPTY list forces the target to `true` (the `all` of an
      empty source array). -/
  | arrayBoolAndSlot (is : List Nat) (k : Nat)
  /-- Slot `k`'s integer must be the 0/1 view of slot `i`'s Boolean
      (`bool2int` style: `i = (if b then 1 else 0)`). -/
  | bool2intSlot (i : Nat) (k : Nat)
  /-- Slots `i` and `j` must carry equal Booleans (`bool_eq` style). -/
  | boolEqSlot (i j : Nat)
  /-- Slot `i`'s value is an integer index into the constant integer
      array `xs`, and slot `k` holds the 1-based element read at that
      index (`array_int_element` style: `xs[i] = k`, FlatZinc arrays
      are 1-based, and an out-of-range index is unsatisfiable). -/
  | arrayIntElementSlot (xs : List Int) (i : Nat) (k : Nat)
  /-- Slot `i`'s value is an integer index into the variable integer
      array at the slots `is`, and slot `k` holds the 1-based element
      read at that index (`array_var_int_element` style). -/
  | arrayVarIntElementSlot (is : List Nat) (i : Nat) (k : Nat)
  /-- Slot `i`'s value is an integer index into the variable Boolean
      array at the slots `is`, and slot `k` holds the 1-based element
      read at that index (`array_var_bool_element` style). -/
  | arrayVarBoolElementSlot (is : List Nat) (i : Nat) (k : Nat)
  /-- Slot `r`'s Boolean holds the truth value of "slot `i`'s value
      equals slot `j`'s" (`int_eq_reif` style: `R ↔ x = y`, the
      reification slot `r` is `true` exactly when the relation
      holds). -/
  | eqReifSlot (i j r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of "slot `i`'s integer
      is at most slot `j`'s" (`int_le_reif` style: `R ↔ x ≤ y`). -/
  | leReifSlot (i j r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of "slot `i`'s value
      differs from slot `j`'s" (`int_ne_reif` style: `R ↔ x ≠ y`). -/
  | neReifSlot (i j r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of the linear equality
      "the dot product of `coeffs` and the values at `is` equals
      `b`" (`int_lin_eq_reif` style:
      `R ↔ dotProduct coeffs xs = some b`). -/
  | linEqReif (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of the linear
      inequality "the dot product of `coeffs` and the values at `is`
      is at most `b`" (`int_lin_le_reif` style:
      `R ↔ dotLe coeffs xs b`). -/
  | linLeReif (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
  /-- Slot `r`'s Boolean holds the truth value of the linear
      disequality "the dot product of `coeffs` and the values at `is`
      differs from `b`" (`int_lin_ne_reif` style:
      `R ↔ dotNe coeffs xs b`). -/
  | linNeReif (coeffs : List Int) (is : List Nat) (b : Int) (r : Nat)
  /-- The `array_int_maximum(m, xs)` array form (result slot first in
      the source): the result operand `r` carries the maximum of the
      operand list `os` — `maxValue` of the operand VALUES in the
      source predicate's exact reading (operands may be slots or
      integer literals; the empty list is unsatisfiable, as in the
      source). -/
  | maxGen (os : List DomIntArg) (r : DomIntArg)
  /-- The `array_int_minimum(m, xs)` array form: the result operand
      `r` carries the minimum of the operand list `os` (`minValue` of
      the operand values, empty list unsatisfiable). -/
  | minGen (os : List DomIntArg) (r : DomIntArg)
  /-- The GENERAL `int_div` shape: the result operand is the
      TRUNCATED quotient `Int.tdiv` of the two operands, and a zero
      divisor is unsatisfiable (the source predicate's exact
      `b ≠ 0 ∧ c = Int.tdiv a b` reading, so negative operands
      truncate towards zero). -/
  | divGen (o₁ o₂ r : DomIntArg)
  /-- The GENERAL `int_mod` shape: the result operand is the
      TRUNCATED remainder `Int.tmod` of the two operands, and a zero
      divisor is unsatisfiable (the source predicate's exact
      `b ≠ 0 ∧ c = Int.tmod a b` reading, so the remainder's sign
      follows the dividend). -/
  | modGen (o₁ o₂ r : DomIntArg)
  /-- The GENERAL two-operand `int_min` shape: the result operand `r`
      carries the minimum of the two operands, and all THREE operands
      must be integers — the source predicate's exact
      `[.int a, .int b, .int c] ↦ c = min a b` reading, so a
      non-integer operand is unsatisfiable in either reading (unlike
      `array_int_minimum`'s `minValue` reading, which ignores a
      non-integer tail element). -/
  | minPair (o₀ o₁ r : DomIntArg)
  /-- The GENERAL two-operand `int_max` shape, the `max` twin of
      `minPair`: `c = max a b` with all three operands integers. -/
  | maxPair (o₀ o₁ r : DomIntArg)
  /-- Slot `i`'s integer must be a member of the CONSTANT set `s`
      (`set_in(x, S)` with a literal or parameter set: no set value
      flows through a slot — the set rides the constraint as a
      payload).  Leaf-enforced (no propagator), like `boolClauseSlot`;
      the FlatZinc-fragment models never carry the set through a
      variable. -/
  | setInSlot (i : Nat) (s : IntSetValue)
  /-- Slot `r`'s Boolean holds the truth value of "slot `i`'s integer
      is a member of the constant set `s`" (`set_in_reif(x, S, r)`
      style: `R ↔ x ∈ S`, the set again a constant payload).
      Leaf-enforced, like `setInSlot`. -/
  | setInReifSlot (i : Nat) (s : IntSetValue) (r : Nat)
  deriving DecidableEq, Repr

/-- The read of slot `i` is the Boolean `b` (false when the slot is
    absent or holds a non-Boolean value). -/
def slotIsBoolB (a : List Value) (i : Nat) (b : Bool) : Bool :=
  match a[i]? with
  | some v => v.eqB (.bool b)
  | none => false

/-- Array-assignment variant of `slotIsBoolB`. -/
def slotIsBoolBA (a : Array Value) (i : Nat) (b : Bool) : Bool :=
  match a[i]? with
  | some v => v.eqB (.bool b)
  | none => false

/-- The declarative semantics of a slot constraint: what it means, in
    `Prop`, for a complete assignment (one value per slot, in slot
    order — the shape of `allAssigns`) to satisfy the constraint. -/
def DomConstraint.SatisfiedBy : DomConstraint → List Value → Prop
  | .eqSlot i j, a => ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧ x = y
  | .neSlot i j, a => ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧ x ≠ y
  | .leSlot i j, a => ∃ p q, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧ p ≤ q
  | .constEq i v, a => a[i]? = some v
  | .plusSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ p + q = r
  | .leConstHi i c, a => ∃ p, a[i]? = some (.int p) ∧ p ≤ c
  | .leConstLo i c, a => ∃ p, a[i]? = some (.int p) ∧ c ≤ p
  | .allDiff is, a => (is.map (fun i => a[i]!)).Nodup
  | .timesSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ p * q = r
  | .minSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ min p q = r
  | .maxSlot i j k, a =>
      ∃ p q r, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧
        a[k]? = some (.int r) ∧ max p q = r
  | .absSlot i k, a =>
      ∃ p r, a[i]? = some (.int p) ∧ a[k]? = some (.int r) ∧
        absValue p = r
  | .linEq coeffs is b, a =>
      dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b
  | .linLe coeffs is b, a =>
      dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
  | .linNe coeffs is b, a =>
      dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
  | .ltSlot i j, a =>
      ∃ p q, a[i]? = some (.int p) ∧ a[j]? = some (.int q) ∧ p < q
  | .ltConstHi i c, a => ∃ p, a[i]? = some (.int p) ∧ p < c
  | .ltConstLo i c, a => ∃ p, a[i]? = some (.int p) ∧ c < p
  | .boolNotSlot i j, a =>
      ∃ x y, a[i]? = some x ∧ a[j]? = some y ∧
        (x = .bool true ∧ y = .bool false ∨
          x = .bool false ∧ y = .bool true)
  | .boolAndSlot i j k, a =>
      ∃ p q r, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧
        a[k]? = some (.bool r) ∧ (p && q) = r
  | .boolOrSlot i j k, a =>
      ∃ p q r, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧
        a[k]? = some (.bool r) ∧ (p || q) = r
  | .boolClauseSlot ps ns, a =>
      (ps.any (fun i => slotIsBoolB a i true)) = true ∨
      (ns.any (fun j => slotIsBoolB a j false)) = true
  | .arrayBoolAndSlot is k, a =>
      a[k]? = some (.bool (is.all (fun i => slotIsBoolB a i true)))
  | .bool2intSlot i k, a =>
      ∃ b : Bool, a[i]? = some (.bool b) ∧
        a[k]? = some (.int (if b then 1 else 0))
  | .boolEqSlot i j, a =>
      ∃ p q : Bool, a[i]? = some (.bool p) ∧ a[j]? = some (.bool q) ∧ p = q
  | .arrayIntElementSlot xs i k, a =>
      ∃ idx e, a[i]? = some (.int idx) ∧ a[k]? = some (.int e) ∧
        valuesGet1 (xs.map Value.int) idx = some (.int e)
  | .arrayVarIntElementSlot is i k, a =>
      ∃ idx e, a[i]? = some (.int idx) ∧ a[k]? = some (.int e) ∧
        (∀ j ∈ is, ∃ v, a[j]? = some v) ∧
        valuesGet1 (is.map (fun j => a[j]!)) idx = some (.int e)
  | .arrayVarBoolElementSlot is i k, a =>
      ∃ idx e, a[i]? = some (.int idx) ∧ a[k]? = some (.bool e) ∧
        (∀ j ∈ is, ∃ v, a[j]? = some v) ∧
        valuesGet1 (is.map (fun j => a[j]!)) idx = some (.bool e)
  | .eqReifSlot i j r, a =>
      ∃ (p : Int) (q : Int) (rb : Bool), a[i]? = some (.int p) ∧
        a[j]? = some (.int q) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ p = q)
  | .leReifSlot i j r, a =>
      ∃ (p : Int) (q : Int) (rb : Bool), a[i]? = some (.int p) ∧
        a[j]? = some (.int q) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ p ≤ q)
  | .neReifSlot i j r, a =>
      ∃ (p : Int) (q : Int) (rb : Bool), a[i]? = some (.int p) ∧
        a[j]? = some (.int q) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ p ≠ q)
  | .linEqReif coeffs is b r, a =>
      ∃ (rb : Bool), a[r]? = some (.bool rb) ∧
        (rb = true ↔
          dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) = some b)
  | .linLeReif coeffs is b r, a =>
      ∃ (rb : Bool), a[r]? = some (.bool rb) ∧
        (rb = true ↔
          dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true)
  | .linNeReif coeffs is b r, a =>
      ∃ (rb : Bool), a[r]? = some (.bool rb) ∧
        (rb = true ↔
          dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true)
  | .maxGen os r, a =>
      ∃ m : Int, DomIntArg.read a r = .int m ∧
        maxValue (os.map (DomIntArg.read a)) = some m
  | .minGen os r, a =>
      ∃ m : Int, DomIntArg.read a r = .int m ∧
        minValue (os.map (DomIntArg.read a)) = some m
  | .divGen o₁ o₂ r, a =>
      ∃ p q : Int, DomIntArg.read a o₁ = .int p ∧
        DomIntArg.read a o₂ = .int q ∧ q ≠ 0 ∧
        DomIntArg.read a r = .int (Int.tdiv p q)
  | .modGen o₁ o₂ r, a =>
      ∃ p q : Int, DomIntArg.read a o₁ = .int p ∧
        DomIntArg.read a o₂ = .int q ∧ q ≠ 0 ∧
        DomIntArg.read a r = .int (Int.tmod p q)
  | .minPair o₀ o₁ r, a =>
      ∃ p q : Int, DomIntArg.read a o₀ = .int p ∧
        DomIntArg.read a o₁ = .int q ∧
        DomIntArg.read a r = .int (min p q)
  | .maxPair o₀ o₁ r, a =>
      ∃ p q : Int, DomIntArg.read a o₀ = .int p ∧
        DomIntArg.read a o₁ = .int q ∧
        DomIntArg.read a r = .int (max p q)
  | .setInSlot i s, a =>
      ∃ p, a[i]? = some (.int p) ∧ s.Contains p
  | .setInReifSlot i s r, a =>
      ∃ (p : Int) (rb : Bool), a[i]? = some (.int p) ∧
        a[r]? = some (.bool rb) ∧ (rb = true ↔ s.Contains p)

/-- The executable Boolean twin of `SatisfiedBy`, for testing and for
    a pruning search's leaf integration. -/
def DomConstraint.satisfiedB (c : DomConstraint) (a : List Value) : Bool :=
  match c with
  | .eqSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => x.eqB y
      | _, _ => false
  | .neSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => !x.eqB y
      | _, _ => false
  | .leSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => intLEB x y
      | _, _ => false
  | .constEq i v =>
      match a[i]? with
      | some x => x.eqB v
      | none => false
  | .plusSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (p + q = r)
      | _, _, _ => false
  | .leConstHi i c =>
      match a[i]? with
      | some (.int p) => decide (p ≤ c)
      | _ => false
  | .leConstLo i c =>
      match a[i]? with
      | some (.int p) => decide (c ≤ p)
      | _ => false
  | .allDiff is => valuesAllDifferent (is.map (fun i => a[i]!))
  | .timesSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (p * q = r)
      | _, _, _ => false
  | .minSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (min p q = r)
      | _, _, _ => false
  | .maxSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (max p q = r)
      | _, _, _ => false
  | .absSlot i k =>
      match a[i]?, a[k]? with
      | some (.int p), some (.int r) => decide (absValue p = r)
      | _, _ => false
  | .linEq coeffs is b =>
      match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
      | some d => decide (d = b)
      | none => false
  | .linLe coeffs is b =>
      dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b
  | .linNe coeffs is b =>
      dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b
  | .ltSlot i j =>
      match a[i]?, a[j]? with
      | some (.int p), some (.int q) => decide (p < q)
      | _, _ => false
  | .ltConstHi i c =>
      match a[i]? with
      | some (.int p) => decide (p < c)
      | _ => false
  | .ltConstLo i c =>
      match a[i]? with
      | some (.int p) => decide (c < p)
      | _ => false
  | .boolNotSlot i j =>
      match a[i]?, a[j]? with
      | some (.bool p), some (.bool q) => decide (q = !p)
      | _, _ => false
  | .boolAndSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.bool p), some (.bool q), some (.bool r) =>
          decide ((p && q) = r)
      | _, _, _ => false
  | .boolOrSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.bool p), some (.bool q), some (.bool r) =>
          decide ((p || q) = r)
      | _, _, _ => false
  | .boolClauseSlot ps ns =>
      (ps.any (fun i => slotIsBoolB a i true)) ||
      (ns.any (fun j => slotIsBoolB a j false))
  | .arrayBoolAndSlot is k =>
      match a[k]? with
      | some (.bool b) => decide (b = is.all (fun i => slotIsBoolB a i true))
      | _ => false
  | .bool2intSlot i k =>
      match a[i]?, a[k]? with
      | some (.bool b), some (.int p) => decide (p = (if b then 1 else 0))
      | _, _ => false
  | .boolEqSlot i j =>
      match a[i]?, a[j]? with
      | some (.bool p), some (.bool q) => decide (p = q)
      | _, _ => false
  | .arrayIntElementSlot xs i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.int e) =>
          match valuesGet1 (xs.map Value.int) idx with
          | some v => v.eqB (.int e)
          | none => false
      | _, _ => false
  | .arrayVarIntElementSlot is i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.int e) =>
          is.all (fun j => (a[j]?).isSome) &&
            (match valuesGet1 (is.map (fun j => a[j]!)) idx with
             | some v => v.eqB (.int e)
             | none => false)
      | _, _ => false
  | .arrayVarBoolElementSlot is i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.bool e) =>
          is.all (fun j => (a[j]?).isSome) &&
            (match valuesGet1 (is.map (fun j => a[j]!)) idx with
             | some v => v.eqB (.bool e)
             | none => false)
      | _, _ => false
  | .eqReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p = q))
      | _, _, _ => false
  | .leReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p ≤ q))
      | _, _, _ => false
  | .neReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p ≠ q))
      | _, _, _ => false
  | .linEqReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = (match dotProduct (intVals coeffs)
              (is.map (fun i => a[i]!)) with
            | some d => decide (d = b)
            | none => false))
      | _ => false
  | .linLeReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b)
      | _ => false
  | .linNeReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b)
      | _ => false
  | .maxGen os r =>
      match DomIntArg.read a r with
      | .int m => decide (maxValue (os.map (DomIntArg.read a)) = some m)
      | _ => false
  | .minGen os r =>
      match DomIntArg.read a r with
      | .int m => decide (minValue (os.map (DomIntArg.read a)) = some m)
      | _ => false
  | .divGen o₁ o₂ r =>
      match DomIntArg.read a o₁, DomIntArg.read a o₂ with
      | .int p, .int q =>
          decide (q ≠ 0) && (DomIntArg.read a r).eqB (.int (Int.tdiv p q))
      | _, _ => false
  | .modGen o₁ o₂ r =>
      match DomIntArg.read a o₁, DomIntArg.read a o₂ with
      | .int p, .int q =>
          decide (q ≠ 0) && (DomIntArg.read a r).eqB (.int (Int.tmod p q))
      | _, _ => false
  | .minPair o₀ o₁ r =>
      match DomIntArg.read a o₀, DomIntArg.read a o₁ with
      | .int p, .int q => (DomIntArg.read a r).eqB (.int (min p q))
      | _, _ => false
  | .maxPair o₀ o₁ r =>
      match DomIntArg.read a o₀, DomIntArg.read a o₁ with
      | .int p, .int q => (DomIntArg.read a r).eqB (.int (max p q))
      | _, _ => false
  | .setInSlot i s =>
      match a[i]? with
      | some (.int p) => decide (s.Contains p)
      | _ => false
  | .setInReifSlot i s r =>
      match a[i]?, a[r]? with
      | some (.int p), some (.bool rb) => decide (rb = decide (s.Contains p))
      | _, _ => false

/-- Array-assignment twin of `satisfiedB`: slot reads are `O(1)` instead of
    `List` walks.  Used at the search leaf and by `acceptsFast`. -/
def DomConstraint.satisfiedBA (c : DomConstraint) (a : Array Value) : Bool :=
  match c with
  | .eqSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => x.eqB y
      | _, _ => false
  | .neSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => !x.eqB y
      | _, _ => false
  | .leSlot i j =>
      match a[i]?, a[j]? with
      | some x, some y => intLEB x y
      | _, _ => false
  | .constEq i v =>
      match a[i]? with
      | some x => x.eqB v
      | none => false
  | .plusSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (p + q = r)
      | _, _, _ => false
  | .leConstHi i c =>
      match a[i]? with
      | some (.int p) => decide (p ≤ c)
      | _ => false
  | .leConstLo i c =>
      match a[i]? with
      | some (.int p) => decide (c ≤ p)
      | _ => false
  | .allDiff is => valuesAllDifferent (is.map (fun i => a[i]!))
  | .timesSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (p * q = r)
      | _, _, _ => false
  | .minSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (min p q = r)
      | _, _, _ => false
  | .maxSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.int p), some (.int q), some (.int r) => decide (max p q = r)
      | _, _, _ => false
  | .absSlot i k =>
      match a[i]?, a[k]? with
      | some (.int p), some (.int r) => decide (absValue p = r)
      | _, _ => false
  | .linEq coeffs is b =>
      match dotProduct (intVals coeffs) (is.map (fun i => a[i]!)) with
      | some d => decide (d = b)
      | none => false
  | .linLe coeffs is b =>
      dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b
  | .linNe coeffs is b =>
      dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b
  | .ltSlot i j =>
      match a[i]?, a[j]? with
      | some (.int p), some (.int q) => decide (p < q)
      | _, _ => false
  | .ltConstHi i c =>
      match a[i]? with
      | some (.int p) => decide (p < c)
      | _ => false
  | .ltConstLo i c =>
      match a[i]? with
      | some (.int p) => decide (c < p)
      | _ => false
  | .boolNotSlot i j =>
      match a[i]?, a[j]? with
      | some (.bool p), some (.bool q) => decide (q = !p)
      | _, _ => false
  | .boolAndSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.bool p), some (.bool q), some (.bool r) =>
          decide ((p && q) = r)
      | _, _, _ => false
  | .boolOrSlot i j k =>
      match a[i]?, a[j]?, a[k]? with
      | some (.bool p), some (.bool q), some (.bool r) =>
          decide ((p || q) = r)
      | _, _, _ => false
  | .boolClauseSlot ps ns =>
      (ps.any (fun i => slotIsBoolBA a i true)) ||
      (ns.any (fun j => slotIsBoolBA a j false))
  | .arrayBoolAndSlot is k =>
      match a[k]? with
      | some (.bool b) => decide (b = is.all (fun i => slotIsBoolBA a i true))
      | _ => false
  | .bool2intSlot i k =>
      match a[i]?, a[k]? with
      | some (.bool b), some (.int p) => decide (p = (if b then 1 else 0))
      | _, _ => false
  | .boolEqSlot i j =>
      match a[i]?, a[j]? with
      | some (.bool p), some (.bool q) => decide (p = q)
      | _, _ => false
  | .arrayIntElementSlot xs i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.int e) =>
          match valuesGet1 (xs.map Value.int) idx with
          | some v => v.eqB (.int e)
          | none => false
      | _, _ => false
  | .arrayVarIntElementSlot is i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.int e) =>
          is.all (fun j => (a[j]?).isSome) &&
            (match valuesGet1 (is.map (fun j => a[j]!)) idx with
             | some v => v.eqB (.int e)
             | none => false)
      | _, _ => false
  | .arrayVarBoolElementSlot is i k =>
      match a[i]?, a[k]? with
      | some (.int idx), some (.bool e) =>
          is.all (fun j => (a[j]?).isSome) &&
            (match valuesGet1 (is.map (fun j => a[j]!)) idx with
             | some v => v.eqB (.bool e)
             | none => false)
      | _, _ => false
  | .eqReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p = q))
      | _, _, _ => false
  | .leReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p ≤ q))
      | _, _, _ => false
  | .neReifSlot i j r =>
      match a[i]?, a[j]?, a[r]? with
      | some (.int p), some (.int q), some (.bool rb) =>
          decide (rb = decide (p ≠ q))
      | _, _, _ => false
  | .linEqReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = (match dotProduct (intVals coeffs)
              (is.map (fun i => a[i]!)) with
            | some d => decide (d = b)
            | none => false))
      | _ => false
  | .linLeReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b)
      | _ => false
  | .linNeReif coeffs is b r =>
      match a[r]? with
      | some (.bool rb) =>
          decide (rb = dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b)
      | _ => false
  | .maxGen os r =>
      match DomIntArg.readA a r with
      | .int m => decide (maxValue (os.map (DomIntArg.readA a)) = some m)
      | _ => false
  | .minGen os r =>
      match DomIntArg.readA a r with
      | .int m => decide (minValue (os.map (DomIntArg.readA a)) = some m)
      | _ => false
  | .divGen o₁ o₂ r =>
      match DomIntArg.readA a o₁, DomIntArg.readA a o₂ with
      | .int p, .int q =>
          decide (q ≠ 0) && (DomIntArg.readA a r).eqB (.int (Int.tdiv p q))
      | _, _ => false
  | .modGen o₁ o₂ r =>
      match DomIntArg.readA a o₁, DomIntArg.readA a o₂ with
      | .int p, .int q =>
          decide (q ≠ 0) && (DomIntArg.readA a r).eqB (.int (Int.tmod p q))
      | _, _ => false
  | .minPair o₀ o₁ r =>
      match DomIntArg.readA a o₀, DomIntArg.readA a o₁ with
      | .int p, .int q => (DomIntArg.readA a r).eqB (.int (min p q))
      | _, _ => false
  | .maxPair o₀ o₁ r =>
      match DomIntArg.readA a o₀, DomIntArg.readA a o₁ with
      | .int p, .int q => (DomIntArg.readA a r).eqB (.int (max p q))
      | _, _ => false
  | .setInSlot i s =>
      match a[i]? with
      | some (.int p) => decide (s.Contains p)
      | _ => false
  | .setInReifSlot i s r =>
      match a[i]?, a[r]? with
      | some (.int p), some (.bool rb) => decide (rb = decide (s.Contains p))
      | _, _ => false

/-- The array twin agrees with `satisfiedB` on the list assignment. -/
theorem DomConstraint.satisfiedBA_eq (c : DomConstraint) (a : List Value) :
    c.satisfiedBA a.toArray = c.satisfiedB a := by
  cases c <;>
    simp [DomConstraint.satisfiedBA, DomConstraint.satisfiedB,
      DomIntArg.readA, DomIntArg.read, DomIntArg.readA_toArray_eq,
      slotIsBoolBA, slotIsBoolB] <;>
    rfl

/-- A `valuesGet1` read of an all-integer value list realizes the
    chosen element with `eqB` exactly when it IS that integer. -/
private theorem valuesGet1_intEqB_iff (idx : Int) (ys : List Value)
    (e : Int) :
    ((match valuesGet1 ys idx with
      | some v => v.eqB (.int e)
      | none => false) = true) ↔ valuesGet1 ys idx = some (.int e) := by
  cases h : valuesGet1 ys idx with
  | none => simp
  | some v =>
      cases v <;> simp [value_eqB_iff]

/-- The Bool twin of `valuesGet1_intEqB_iff`. -/
private theorem valuesGet1_boolEqB_iff (idx : Int) (ys : List Value)
    (e : Bool) :
    ((match valuesGet1 ys idx with
      | some v => v.eqB (.bool e)
      | none => false) = true) ↔ valuesGet1 ys idx = some (.bool e) := by
  cases h : valuesGet1 ys idx with
  | none => simp
  | some v =>
      cases v <;> simp [value_eqB_iff]

/-- An `all` of `Option.isSome` reads is the pointwise existence of the
    reads. -/
private theorem all_isSome_iff {a : List Value} {is : List Nat} :
    (is.all (fun j => (a[j]?).isSome) = true) ↔
      ∀ j ∈ is, ∃ v, a[j]? = some v := by
  rw [List.all_eq_true]
  constructor
  · intro h j hj
    exact Option.isSome_iff_exists.mp (h j hj)
  · intro h j hj
    obtain ⟨v, hv⟩ := h j hj
    rw [hv]
    rfl

private theorem dotProduct_match_eq_some (xs ys : List Value) (b : Int) :
    (match dotProduct xs ys with
     | some d => decide (d = b)
     | none => false) = true ↔ dotProduct xs ys = some b := by
  cases h : dotProduct xs ys with
  | none => simp
  | some d => simp

/-- A reification-slot decision IS the truth-value agreement it
    represents: `decide (rb = t)` holds exactly when `rb` is `true`
    precisely if `t` is. -/
private theorem decide_eq_bool_iff (rb t : Bool) :
    decide (rb = t) = true ↔ (rb = true ↔ t = true) := by
  cases rb <;> cases t <;> simp

/-- The source form of a reified constraint — the disjunction "the
    reification slot is `true` and the relation holds, or it is
    `false` and the relation fails" — IS the truth-value agreement
    `R ↔ P`.  This is the bridge between the FlatZinc `*_reif`
    disjunction and the slot-agreement form of the `DomConstraint`
    semantics. -/
theorem reif_disj_iff (P : Prop) (rb : Bool) :
    ((rb = true ∧ P) ∨ (rb = false ∧ ¬ P)) ↔ (rb = true ↔ P) := by
  constructor
  · rintro (⟨hrb, hP⟩ | ⟨hrb, hnP⟩)
    · subst hrb
      exact ⟨fun _ => hP, fun _ => rfl⟩
    · subst hrb
      exact ⟨fun hfalse => absurd hfalse (by simp), fun hP => absurd hP hnP⟩
  · intro h
    cases rb with
    | true => exact Or.inl ⟨rfl, h.mp rfl⟩
    | false =>
        exact Or.inr ⟨rfl, fun hP => absurd (h.mpr hP) (by simp)⟩

/-- `dotNe` unfolds to a decision on the dot product. -/
theorem dotNe_eq (as_ xs : List Value) (b : Int) :
    dotNe as_ xs b = true ↔ ∃ d, dotProduct as_ xs = some d ∧ d ≠ b := by
  unfold dotNe
  cases h : dotProduct as_ xs with
  | none => simp
  | some d =>
      simp only [decide_eq_true_eq]
      constructor
      · intro hd
        exact ⟨d, rfl, hd⟩
      · rintro ⟨d', hd', hne⟩
        have : d' = d := (Option.some.inj hd').symm
        subst this
        exact hne

/-- `dotLe` unfolds to a decision on the dot product. -/
theorem dotLe_eq (as_ xs : List Value) (b : Int) :
    dotLe as_ xs b = true ↔ ∃ d, dotProduct as_ xs = some d ∧ d ≤ b := by
  unfold dotLe
  cases h : dotProduct as_ xs with
  | none => simp
  | some d =>
      simp only [decide_eq_true_eq]
      constructor
      · intro hd
        exact ⟨d, rfl, hd⟩
      · rintro ⟨d', hd', hle⟩
        have : d' = d := (Option.some.inj hd').symm
        subst this
        exact hle

/-- **Agreement** between the declarative semantics and the Boolean
    twin of `SatisfiedBy`. -/
theorem DomConstraint.satisfiedB_iff (c : DomConstraint) (a : List Value) :
    c.satisfiedB a = true ↔ c.SatisfiedBy a := by
  cases c with
  | eqSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              simp only []
              simp only [value_eqB_iff, Option.some.injEq]
              refine ⟨fun h => ⟨x, y, rfl, rfl, h⟩, ?_⟩
              rintro ⟨w, z, rfl, rfl, h⟩
              exact h
  | neSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              simp only []
              rw [Bool.not_eq_true', eqB_false_iff_ne]
              simp only [Option.some.injEq]
              refine ⟨fun h => ⟨x, y, rfl, rfl, h⟩, ?_⟩
              rintro ⟨w, z, rfl, rfl, h⟩
              exact h
  | leSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              simp only []
              rw [intLEB_iff]
              refine ⟨fun ⟨p, q, hpx, hqy, hle⟩ => ⟨p, q, ?_, ?_, hle⟩, ?_⟩
              · simp [hpx]
              · simp [hqy]
              · rintro ⟨p, q, hpx, hqy, hle⟩
                simp only [Option.some.injEq] at hpx hqy
                exact ⟨p, q, hpx, hqy, hle⟩
  | constEq i v =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          simp only []
          rw [value_eqB_iff]
          simp only [Option.some.injEq]
  | plusSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hsum⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hsum
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | leConstHi i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | leConstLo i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | allDiff is =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      exact valuesAllDifferent_iff_nodup _
  | timesSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hprod⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hprod
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | minSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hmin⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hmin
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | maxSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | int p =>
                      cases y with
                      | int q =>
                          cases z with
                          | int r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hmax⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hmax
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
  | absSlot i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int p =>
                  cases z with
                  | int r =>
                      simp only [decide_eq_true_eq]
                      refine ⟨fun h => ⟨p, r, rfl, rfl, h⟩, ?_⟩
                      rintro ⟨p', r', hp, hr, habs⟩
                      have h1 : p = p' := by
                        injection Option.some.inj hp
                      have h2 : r = r' := by
                        injection Option.some.inj hr
                      subst h1; subst h2
                      exact habs
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | linEq coeffs is b =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      exact dotProduct_match_eq_some (intVals coeffs) (is.map (fun i => a[i]!)) b
  | linLe coeffs is b =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
  | linNe coeffs is b =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
  | ltSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases x with
              | int p =>
                  cases y with
                  | int q =>
                      simp only [decide_eq_true_eq]
                      refine ⟨fun h => ⟨p, q, rfl, rfl, h⟩, ?_⟩
                      rintro ⟨p', q', hp, hq, hlt⟩
                      have h1 : p = p' := by injection Option.some.inj hp
                      have h2 : q = q' := by injection Option.some.inj hq
                      subst h1; subst h2
                      exact hlt
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | ltConstHi i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | ltConstLo i c =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              refine ⟨fun h => ⟨p, rfl, h⟩, ?_⟩
              rintro ⟨p', hp, h⟩
              simp only [Option.some.injEq, Value.int.injEq] at hp
              omega
          | bool w => simp
          | setOfInt w => simp
          | array w => simp
  | boolNotSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases x with
              | bool p =>
                  cases y with
                  | bool q =>
                      cases p <;> cases q <;> simp_all
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
              | int w => simp
              | setOfInt w => simp
              | array w => simp
  | boolAndSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | bool p =>
                      cases y with
                      | bool q =>
                          cases z with
                          | bool r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hand⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hand
                          | int w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | int w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | boolOrSlot i j k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hz : a[k]? with
              | none => simp
              | some z =>
                  cases x with
                  | bool p =>
                      cases y with
                      | bool q =>
                          cases z with
                          | bool r =>
                              simp only [decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, r, rfl, rfl, rfl, h⟩, ?_⟩
                              rintro ⟨p', q', r', hp, hq, hr, hor⟩
                              have h1 : p = p' := by
                                injection Option.some.inj hp
                              have h2 : q = q' := by
                                injection Option.some.inj hq
                              have h3 : r = r' := by
                                injection Option.some.inj hr
                              subst h1; subst h2; subst h3
                              exact hor
                          | int w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | int w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | boolClauseSlot ps ns =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy,
        Bool.or_eq_true]
  | arrayBoolAndSlot is k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hz : a[k]? with
      | none => simp
      | some z =>
          cases z with
          | bool b =>
              simp only [decide_eq_true_eq, Option.some.injEq, Value.bool.injEq]
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | bool2intSlot i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | bool p =>
                  cases z with
                  | int q => cases p <;> simp_all
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | int w => simp
              | setOfInt w => simp
              | array w => simp
  | boolEqSlot i j =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases x with
              | bool p =>
                  cases y with
                  | bool q => cases p <;> cases q <;> simp_all
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
              | int w => simp
              | setOfInt w => simp
              | array w => simp
  | arrayIntElementSlot xs i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int idx =>
                  cases z with
                  | int e =>
                      rw [valuesGet1_intEqB_iff]
                      refine ⟨fun h => ⟨idx, e, rfl, rfl, h⟩, ?_⟩
                      rintro ⟨idx', e', h1, h2, hget⟩
                      cases h1; cases h2
                      exact hget
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | arrayVarIntElementSlot is i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int idx =>
                  cases z with
                  | int e =>
                      simp only [all_isSome_iff, valuesGet1_intEqB_iff,
                        Bool.and_eq_true, Option.some.injEq]
                      refine ⟨fun ⟨hin, hget⟩ =>
                        ⟨idx, e, rfl, rfl, hin, hget⟩, ?_⟩
                      rintro ⟨idx', e', h1, h2, hin, hget⟩
                      injection h1 with h1'; injection h2 with h2'
                      subst h1'; subst h2'
                      exact ⟨hin, hget⟩
                  | bool w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | arrayVarBoolElementSlot is i k =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hz : a[k]? with
          | none => simp
          | some z =>
              cases x with
              | int idx =>
                  cases z with
                  | bool e =>
                      simp only [all_isSome_iff, valuesGet1_boolEqB_iff,
                        Bool.and_eq_true, Option.some.injEq]
                      refine ⟨fun ⟨hin, hget⟩ =>
                        ⟨idx, e, rfl, rfl, hin, hget⟩, ?_⟩
                      rintro ⟨idx', e', h1, h2, hin, hget⟩
                      injection h1 with h1'; injection h2 with h2'
                      subst h1'; subst h2'
                      exact ⟨hin, hget⟩
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
              | bool w => simp
              | setOfInt w => simp
              | array w => simp
  | eqReifSlot i j r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hr : a[r]? with
              | none => simp
              | some rv =>
                  cases rv with
                  | bool rb =>
                      cases x with
                      | int p =>
                          cases y with
                          | int q =>
                              rw [decide_eq_bool_iff, decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, rb, rfl, rfl, rfl, h⟩,
                                ?_⟩
                              rintro ⟨p', q', rb', h1, h2, h3, h⟩
                              cases h1; cases h2; cases h3
                              exact h
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | leReifSlot i j r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hr : a[r]? with
              | none => simp
              | some rv =>
                  cases rv with
                  | bool rb =>
                      cases x with
                      | int p =>
                          cases y with
                          | int q =>
                              rw [decide_eq_bool_iff, decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, rb, rfl, rfl, rfl, h⟩,
                                ?_⟩
                              rintro ⟨p', q', rb', h1, h2, h3, h⟩
                              cases h1; cases h2; cases h3
                              exact h
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | neReifSlot i j r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases hy : a[j]? with
          | none => simp
          | some y =>
              cases hr : a[r]? with
              | none => simp
              | some rv =>
                  cases rv with
                  | bool rb =>
                      cases x with
                      | int p =>
                          cases y with
                          | int q =>
                              rw [decide_eq_bool_iff, decide_eq_true_eq]
                              refine ⟨fun h => ⟨p, q, rb, rfl, rfl, rfl, h⟩,
                                ?_⟩
                              rintro ⟨p', q', rb', h1, h2, h3, h⟩
                              cases h1; cases h2; cases h3
                              exact h
                          | bool w => simp
                          | setOfInt w => simp
                          | array w => simp
                      | bool w => simp
                      | setOfInt w => simp
                      | array w => simp
                  | int w => simp
                  | setOfInt w => simp
                  | array w => simp
  | linEqReif coeffs is b r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : a[r]? with
      | none => simp
      | some rv =>
          cases rv with
          | bool rb =>
              rw [decide_eq_bool_iff, dotProduct_match_eq_some]
              refine ⟨fun h => ⟨rb, rfl, h⟩, ?_⟩
              rintro ⟨rb', h1, h⟩
              cases h1
              exact h
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | linLeReif coeffs is b r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : a[r]? with
      | none => simp
      | some rv =>
          cases rv with
          | bool rb =>
              rw [decide_eq_bool_iff]
              refine ⟨fun h => ⟨rb, rfl, h⟩, ?_⟩
              rintro ⟨rb', h1, h⟩
              cases h1
              exact h
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | linNeReif coeffs is b r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : a[r]? with
      | none => simp
      | some rv =>
          cases rv with
          | bool rb =>
              rw [decide_eq_bool_iff]
              refine ⟨fun h => ⟨rb, rfl, h⟩, ?_⟩
              rintro ⟨rb', h1, h⟩
              cases h1
              exact h
          | int w => simp
          | setOfInt w => simp
          | array w => simp
  | maxGen os r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : DomIntArg.read a r with
      | int m =>
          rw [decide_eq_true_eq]
          constructor
          · intro h
            exact ⟨m, rfl, h⟩
          · rintro ⟨m', hm', h⟩
            have hm : m = m' := by injection hm' with hmi
            subst hm
            exact h
      | bool w => simp [hr]
      | setOfInt w => simp [hr]
      | array w => simp [hr]
  | minGen os r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hr : DomIntArg.read a r with
      | int m =>
          rw [decide_eq_true_eq]
          constructor
          · intro h
            exact ⟨m, rfl, h⟩
          · rintro ⟨m', hm', h⟩
            have hm : m = m' := by injection hm' with hmi
            subst hm
            exact h
      | bool w => simp [hr]
      | setOfInt w => simp [hr]
      | array w => simp [hr]
  | divGen o₁ o₂ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₁ with
      | int p =>
          cases h₂ : DomIntArg.read a o₂ with
          | int q =>
              rw [Bool.and_eq_true, decide_eq_true_eq, value_eqB_iff]
              constructor
              · rintro ⟨hq, hr⟩
                exact ⟨p, q, rfl, rfl, hq, hr⟩
              · rintro ⟨p', q', hp', hq'', hq, hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hqv] at hq
                rw [hpv, hqv] at hr
                exact ⟨hq, hr⟩
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]
  | modGen o₁ o₂ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₁ with
      | int p =>
          cases h₂ : DomIntArg.read a o₂ with
          | int q =>
              rw [Bool.and_eq_true, decide_eq_true_eq, value_eqB_iff]
              constructor
              · rintro ⟨hq, hr⟩
                exact ⟨p, q, rfl, rfl, hq, hr⟩
              · rintro ⟨p', q', hp', hq'', hq, hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hqv] at hq
                rw [hpv, hqv] at hr
                exact ⟨hq, hr⟩
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]
  | minPair o₀ o₁ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₀ with
      | int p =>
          cases h₂ : DomIntArg.read a o₁ with
          | int q =>
              rw [value_eqB_iff]
              constructor
              · intro hr
                exact ⟨p, q, rfl, rfl, hr⟩
              · rintro ⟨p', q', hp', hq'', hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hpv, hqv] at hr
                exact hr
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]
  | maxPair o₀ o₁ r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases h₁ : DomIntArg.read a o₀ with
      | int p =>
          cases h₂ : DomIntArg.read a o₁ with
          | int q =>
              rw [value_eqB_iff]
              constructor
              · intro hr
                exact ⟨p, q, rfl, rfl, hr⟩
              · rintro ⟨p', q', hp', hq'', hr⟩
                have hpv : p' = p := by injection hp' with hpi; exact hpi.symm
                have hqv : q' = q := by injection hq'' with hqi; exact hqi.symm
                rw [hpv, hqv] at hr
                exact hr
          | bool w => simp [h₁, h₂]
          | setOfInt w => simp [h₁, h₂]
          | array w => simp [h₁, h₂]
      | bool w => simp [h₁]
      | setOfInt w => simp [h₁]
      | array w => simp [h₁]
  | setInSlot i s =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              simp only [decide_eq_true_eq]
              constructor
              · intro h; exact ⟨p, rfl, h⟩
              · rintro ⟨p', hp', h⟩
                have hve : Value.int p = Value.int p' := by injection hp'
                have : p = p' := by injection hve
                subst this
                exact h
          | bool w => simp [hx]
          | setOfInt w => simp [hx]
          | array w => simp [hx]
  | setInReifSlot i s r =>
      simp only [DomConstraint.satisfiedB, DomConstraint.SatisfiedBy]
      cases hx : a[i]? with
      | none => simp
      | some x =>
          cases x with
          | int p =>
              cases hr : a[r]? with
              | none => simp
              | some y =>
                  cases y with
                  | bool rb =>
                      rw [decide_eq_bool_iff, decide_eq_true_eq]
                      constructor
                      · intro h; exact ⟨p, rb, rfl, rfl, h⟩
                      · rintro ⟨p', rb', hp', hr', h⟩
                        have hve : Value.int p = Value.int p' := by injection hp'
                        have hpe : p = p' := by injection hve
                        subst hpe
                        have hve2 : Value.bool rb = Value.bool rb' := by injection hr'
                        have : rb = rb' := by injection hve2
                        subst this
                        exact h
                  | int w => simp [hr]
                  | setOfInt w => simp [hr]
                  | array w => simp [hr]
          | bool w => simp [hx]
          | setOfInt w => simp [hx]
          | array w => simp [hx]
/-- `neSlot` is symmetric in its two positions. -/

theorem DomConstraint.satisfiedBy_neSlot_comm (i j : Nat) (a : List Value) :
    DomConstraint.SatisfiedBy (DomConstraint.neSlot i j) a ↔
      DomConstraint.SatisfiedBy (DomConstraint.neSlot j i) a := by
  simp only [DomConstraint.SatisfiedBy]
  constructor
  · rintro ⟨x, y, hx, hy, hne⟩
    exact ⟨y, x, hy, hx, hne.symm⟩
  · rintro ⟨x, y, hx, hy, hne⟩
    exact ⟨y, x, hy, hx, hne.symm⟩

/-! ## The propagation contract -/

/-- The result of a propagator: a certified contradiction, or the
    narrowed slot domains (one finite value list per slot, the shape of
    `LeanFzn/Compiler/Domain.lean`'s search slots). -/
inductive PropResult where
  /-- The propagator certifies that no assignment of the current
      domains can satisfy its constraint. -/
  | contradiction
  /-- The narrowed domains: every satisfying assignment compatible
      with the input domains is still compatible with them. -/
  | narrowed (doms : List (List Value))
  deriving Repr

/-- Structural equality of propagation results (for testing):
    results are equal when both are contradictions, or both narrow to
    pointwise structurally-equal domain lists. -/
def domsEqB (a b : List (List Value)) : Bool :=
  a.length == b.length && (a.zip b).all (fun p => valuesEqB p.1 p.2)

instance : BEq PropResult where
  beq
    | .contradiction, .contradiction => true
    | .narrowed a, .narrowed b => domsEqB a b
    | _, _ => false

/-- **The propagation contract** (PLAN 6.3's local preservation
    theorem, packaged).  A propagator `p` for constraint `c` meets the
    contract when:

    * on `narrowed doms'`, every assignment of the input domains that
      satisfies `c` is still an assignment of `doms'` — "every
      satisfying assignment compatible with the input domains remains
      compatible with the output domains" — and `doms'` is
      pointwise-subset the input domains (no slot grows, none is
      added or removed);
    * on `contradiction`, no assignment of the input domains
      satisfies `c`. -/
structure Preserves (c : DomConstraint)
    (p : List (List Value) → PropResult) : Prop where
  /-- **Narrowing soundness**: satisfying assignments of the input
      domains remain assignments of the output domains. -/
  narrowed {doms doms' : List (List Value)}
      (h : p doms = .narrowed doms') :
    ∀ a ∈ allAssigns doms, c.SatisfiedBy a → a ∈ allAssigns doms'
  /-- The output domains only shrank: pointwise subsetting, same slot
      count. -/
  subset {doms doms' : List (List Value)}
      (h : p doms = .narrowed doms') : DomPointwiseSub doms' doms
  /-- **Contradiction soundness**: no satisfying assignment
      remains. -/
  contradicts {doms : List (List Value)}
      (h : p doms = .contradiction) :
    ∀ a ∈ allAssigns doms, ¬ c.SatisfiedBy a


end LeanFzn.Solver.Propagation.DomainFiltering
