/-
File: LeanFzn/Compiler/SetIn.lean

Purpose:
  The constant-set membership normalization of the certified compiler
  front end (PLAN.md §3.0 item 2).  FlatZinc's `set_in(x, S)` and its
  literal-reified forms constrain a variable to a CONSTANT set.  When
  `x` is a plain, initializer-free declared scalar `var int` with a
  finite declared domain, the constraint is exactly a restriction of
  that domain:

  * `set_in(x, S)` and `set_in_reif(x, S, true)`: keep `dom(x) ∩ S`;
  * `set_in_reif(x, S, false)`: keep `dom(x) \ S`, which is finite
    because the declared domain is finite (the form the C0 coverage
    table §11.5 recorded as blocked by the "infinite complement" of a
    finite set).

  `restrictSetInModel m` rewrites the declaration and DROPS the
  subsumed constraint; `compileModelFull` then runs the unchanged
  `compileModel` on the rewritten model, so search never branches on
  an excluded value.  Every other shape (literal subjects, aliases,
  parameter/variable set arguments, and any variable whose declaration
  is not a finite int range/enumeration) keeps its
  `setInSlot`/`setInReifSlot` leaf constraint unchanged.

  The correctness theorems are in `Proofs/SetIn`.

Dependencies:
  - LeanFzn.Compiler.Compile: `compileModel`, `CompiledProblem`.
-/

import LeanFzn.Compiler.Compile

namespace LeanFzn.Compiler
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation

/-- The denoted value of a constant set argument: a set literal only.
    Parameter and variable set arguments are not constant and keep
    their leaf constraint. -/
def setArgDenote : BasicExpr → Option IntSetValue
  | .lit (.set s) => some s.denote
  | _ => none

/-- A variable type is a finite integer domain (range or enumeration),
    the only shape the restriction rewrites. -/
def isFiniteIntType : BasicVarType → Bool
  | .intRange _ _ => true
  | .intSet _ => true
  | _ => false

theorem isFiniteIntType_iff {ty : BasicVarType} :
    isFiniteIntType ty = true ↔
      (∃ lo hi, ty = .intRange lo hi) ∨ (∃ xs, ty = .intSet xs) := by
  cases ty <;> simp [isFiniteIntType]

/-- A variable is a plain, initializer-free scalar with a finite
    integer domain (the only shape the domain restriction rewrites). -/
def plainFiniteIntVar (m : Model) (x : String) : Bool :=
  m.variables.any fun d =>
    match d with
    | .basic ty n _ none => n.name == x && isFiniteIntType ty
    | _ => false

/-- One constant-set restriction: the set and whether membership is
    required (`true`) or forbidden (`false`). -/
abbrev SetInRestriction := IntSetValue × Bool

/-- The droppable constant-set membership shape: subject variable,
    set argument and membership polarity (a literal `set_in_reif`
    reification or `true` for the unreified form). -/
def setInShape (c : ConstraintItem) :
    Option (Ident × BasicExpr × Bool) :=
  match c.name.name, c.args with
  | "set_in", [.basic (.ident y), .basic s] => some (y, s, true)
  | "set_in_reif", [.basic (.ident y), .basic s, .basic (.lit (.bool b))] =>
      some (y, s, b)
  | _, _ => none

/-- The constant-set restrictions a constraint imposes on the variable
    named `x`, if the constraint has an accepted `set_in` shape and a
    literal (or absent) reification. -/
def setInCondOf (x : String) (c : ConstraintItem) :
    Option SetInRestriction :=
  match setInShape c with
  | some (y, s, b) =>
      if y.name = x then (setArgDenote s).map (fun sv => (sv, b))
      else none
  | none => none

/-- The restrictions the constraints of `m` impose on the variable
    named `x` (all of them are dropped from the normalized model when
    `x` is a plain finite int variable). -/
def setInConds (m : Model) (x : String) : List SetInRestriction :=
  m.constraints.filterMap (setInCondOf x)

/-- One restriction accepts an integer value. -/
def setInCondAccepts (sv : IntSetValue) (pos : Bool) (v : Int) : Bool :=
  if pos then decide (sv.Contains v) else !decide (sv.Contains v)

/-- All restrictions of a variable accept an integer value. -/
def setInAccepts (conds : List SetInRestriction) (v : Int) : Bool :=
  conds.all (fun q => setInCondAccepts q.1 q.2 v)

/-- The subject variable of a constant-set membership constraint, if
    the constraint has one of the droppable shapes. -/
def setInSubject (c : ConstraintItem) : Option String :=
  (setInShape c).map (fun p => p.1.name)

/-- The constraint is a constant-set membership that the domain
    restriction subsumes: plain finite scalar subject and a constant
    set argument. -/
def setInRestricts (m : Model) (c : ConstraintItem) : Bool :=
  match setInSubject c with
  | some x => plainFiniteIntVar m x && (setInCondOf x c).isSome
  | none => false

/-- The declared type restricted by the constant-set membership
    conditions on its name.  Types outside the finite integer fragment
    are left untouched. -/
def restrictVarType (m : Model) (name : String) : BasicVarType → BasicVarType
  | .intRange lo hi =>
      match setInConds m name with
      | [] => .intRange lo hi
      | conds => .intSet ((setElems (.interval lo hi)).filter (setInAccepts conds))
  | .intSet xs =>
      match setInConds m name with
      | [] => .intSet xs
      | conds => .intSet (xs.filter (setInAccepts conds))
  | ty => ty

/-- The declaration with its finite int domain restricted by the
    constant-set membership conditions on its name. -/
def restrictVarDecl (m : Model) : VarDeclItem → VarDeclItem
  | .basic ty n anns none => .basic (restrictVarType m n.name ty) n anns none
  | d => d

/-- **The constant-set domain restriction**: intersect every plain
    finite scalar variable's declared domain with the constant sets of
    its `set_in` / literal-reified `set_in_reif` constraints and drop
    those constraints.  All other declarations and constraints are
    unchanged. -/
def restrictSetInModel (m : Model) : Model :=
  { m with
    variables := m.variables.map (restrictVarDecl m)
    constraints := m.constraints.filter (fun c => !setInRestricts m c) }

end LeanFzn.Compiler
