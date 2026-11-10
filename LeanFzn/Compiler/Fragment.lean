/-
File: LeanFzn/Compiler/Fragment.lean

Purpose:
  Fragment sweep for the certified compiler (PLAN.md task L4).

  Two model-to-model passes close declaration and argument gaps that are
  legal FlatZinc but outside the scalar compiler's fragment:

  * `substParamsModel` replaces a scalar `int`/`bool` parameter identifier
    in a constraint argument or variable initializer by its declared
    literal value (through `parEnv`).  The parameter declarations remain,
    so the model's value namespace and `ParamHonest` condition are
    unchanged; only the syntactic use of the name changes.
  * `expandInitModel` rewrites a scalar variable initializer into the
    equivalent fixed-value constraint and removes the initializer.  An
    `int` literal initializer becomes `int_eq(x, k)`, and a `bool` literal
    becomes `bool_not(x, !b)`.  Identifier initializers, set initializers
    and set-valued variables stay on the declaration and therefore remain
    an explicit unsupported outcome; scalar parameters are substituted
    before this pass, so `x = p` is covered when `p` is scalar.

  Both passes change only `constraints` (and, for the initializer pass,
  the initializer field of scalar declarations).  Variables, arrays,
  parameters, domains and `solveAnn` are otherwise untouched.  The
  composite `fragmentModel` runs parameter substitution before initializer
  expansion, so an initializer that names a scalar parameter is first
  turned into a literal.

  `normalizeFull` runs `fragmentModel` after array inlining and before the
  literal folds.  The correctness proofs are in `Proofs/Fragment`; the
  public `solveModel_*` statements are unchanged.

Dependencies:
  - LeanFzn.Compiler.Compile: `compileModel`, `parEnv`.
-/

import LeanFzn.Compiler.Compile

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics

/-! ## Scalar parameter substitution -/

/-- A scalar value as the corresponding basic literal. -/
def scalarLiteral : Value → Option BasicLiteral
  | .int i => some (.int i)
  | .bool b => some (.bool b)
  | _ => none

/-- Replace a scalar parameter identifier by its declared literal value.
    A name outside `parEnv` (a variable or an unsupported parameter) is
    kept unchanged. -/
def substParamBasic (env : Store) : BasicExpr → BasicExpr
  | .ident x =>
      match env x with
      | some v =>
          match scalarLiteral v with
          | some l => .lit l
          | none => .ident x
      | none => .ident x
  | b => b

/-- Substitute scalar parameters in an expression (including every element
    of an explicit array). -/
def substParamExpr (env : Store) : Expr → Expr
  | .basic b => .basic (substParamBasic env b)
  | .array es => .array (es.map (substParamBasic env))

/-- Substitute scalar parameters in one constraint's arguments. -/
def substParamConstraint (env : Store) (c : ConstraintItem) : ConstraintItem :=
  { c with args := c.args.map (substParamExpr env) }

/-- Substitute scalar parameters in a variable declaration's initializer. -/
def substParamVarDecl (env : Store) : VarDeclItem → VarDeclItem
  | .basic ty n anns (some e) => .basic ty n anns (some (substParamBasic env e))
  | d => d

/-- The scalar-parameter substitution pass.  Parameters themselves stay
    declared, so `ParamHonest` is unchanged. -/
def substParamsModel (m : Model) : Model :=
  let env := parEnv m
  { m with
    variables := m.variables.map (substParamVarDecl env)
    constraints := m.constraints.map (substParamConstraint env) }

/-! ## Variable initializers -/

/-- The fixed-value constraint equivalent to a scalar initializer, when the
    initializer shape is supported.  The Boolean literal case uses
    `bool_not(x, !b)`, which the compiler already accepts with a literal
    second argument. -/
def initConstraint : VarDeclItem → Option ConstraintItem
  | .basic ty n _ (some (.lit (.int k))) =>
      if ty.base = .int then
        some { name := Ident.mk "int_eq"
               args := [.basic (.ident n), .basic (.lit (.int k))]
               anns := [] }
      else none
  | .basic ty n _ (some (.lit (.bool b))) =>
      if ty.base = .bool then
        some { name := Ident.mk "bool_not"
               args := [.basic (.ident n), .basic (.lit (.bool (!b)))]
               anns := [] }
      else none
  | _ => none

/-- One declaration after initializer expansion: the initializer-free
    declaration and the constraints that replace it. -/
def expandInitDecl (d : VarDeclItem) : VarDeclItem × List ConstraintItem :=
  match d with
  | .basic ty n anns (some _) =>
      match initConstraint d with
      | some c => (.basic ty n anns none, [c])
      | none => (d, [])
  | _ => (d, [])

/-- The initializer-expansion pass.  Only scalar declarations are touched;
    unsupported initializers are kept verbatim and stay unsupported. -/
def expandInitModel (m : Model) : Model :=
  let ds := m.variables.map expandInitDecl
  { m with
    variables := ds.map Prod.fst
    constraints := m.constraints ++ ds.flatMap Prod.snd }

/-- The composite L4 fragment pass: substitute scalar parameters first, then
    move supported scalar initializers into constraints. -/
def fragmentModel (m : Model) : Model :=
  expandInitModel (substParamsModel m)

end LeanFzn.Compiler
