/-
File: LeanFzn/Compiler/Normalize.lean

Purpose:
  The array front end of the certified compiler (PLAN.md task X1).
  FlatZinc models routinely declare parameter arrays
  (`array [1..n] of int: a = [..];`) and variable arrays that are pure
  aliases of declared scalar variables
  (`array [1..n] of var int: x :: output_array(..) = [v1,..,vn];`).
  `compileModel` handles scalar declarations only; this module reduces
  the array declarations to that fragment by SOURCE-LEVEL INLINING.
  It also runs the constant-set membership domain restriction
  (`SetIn.restrictSetInModel`) before compilation, so `set_in` over a
  plain declared scalar is a domain restriction rather than a leaf
  constraint.  The array part:

  * `arrayDefs m` lists, for every array declaration of `m`, the
    element expressions the array denotes (a parameter array: its
    literals; a variable array: its initializer);
  * `normalizeModel m` drops the array declarations and replaces every
    constraint argument that is the bare NAME of an array by the
    corresponding explicit array literal, which the unchanged
    `compileConstraints` already handles;
  * `compileModelFull m` runs `compileModel` on the normalized model
    and re-attaches the original model as `source` and a `toStore` that
    additionally gives every array name its (element-wise) value, so the
    produced store is a store of the ORIGINAL model.

  The variable-array alias gate (`arraysOkB`) is deliberately narrow so
  that the array's declared element type is automatically satisfied:
  the element type must be unrestricted `var int` / `var bool`, every
  element must be a literal of that base type or the name of a declared
  initializer-free scalar variable of that base type, and array names
  must not be reused as element or explicit-array identifiers.

  `compileModel` and all its theorems are UNCHANGED; the correctness
  theorems for `compileModelFull` are in `Proofs/Normalize` (array
  inlining) and `Proofs/SetIn` (the constant-set domain restriction).

Dependencies:
  - LeanFzn.Compiler.Compile: `compileModel`, `CompiledProblem`.
  - LeanFzn.Compiler.SetIn: the constant-set domain restriction.
-/

import LeanFzn.Compiler.Compile
import LeanFzn.Compiler.SetIn

namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation

/-- A parameter array's definition: its literals as expressions. -/
def parArrayDef : ParDeclItem → Option (Ident × List BasicExpr)
  | .array _ _ n lits => some (n, lits.map BasicExpr.lit)
  | _ => none

/-- A variable array's definition: its initializer. -/
def varArrayDef : VarDeclItem → Option (Ident × List BasicExpr)
  | .array _ n _ es => some (n, es)
  | _ => none

/-- Every array declaration's element expressions, keyed by name
    (parameter arrays first). -/
def arrayDefs (m : Model) : List (Ident × List BasicExpr) :=
  m.parameters.filterMap parArrayDef ++ m.variables.filterMap varArrayDef

def isArrayPar : ParDeclItem → Bool
  | .array .. => true
  | _ => false

def isBasicVar : VarDeclItem → Bool
  | .basic .. => true
  | _ => false

/-- Inline a bare array name by its element list. -/
def inlineExpr (defs : List (Ident × List BasicExpr)) : Expr → Expr
  | .basic (.ident x) =>
      match lookupIdent x defs with
      | some es => .array es
      | none => .basic (.ident x)
  | e => e

def inlineConstraint (defs : List (Ident × List BasicExpr))
    (c : ConstraintItem) : ConstraintItem :=
  { c with args := c.args.map (inlineExpr defs) }

/-- The model without its array declarations, constraint array names
    inlined. -/
def normalizeModel (m : Model) : Model :=
  let defs := arrayDefs m
  { m with
    parameters := m.parameters.filter (fun d => !isArrayPar d)
    variables := m.variables.filter isBasicVar
    constraints := m.constraints.map (inlineConstraint defs) }

/-- The full source normalization: array inlining, then the
    constant-set membership domain restriction. -/
def normalizeFull (m : Model) : Model :=
  restrictSetInModel (normalizeModel m)

/-- A variable-array element is acceptable: a literal of the array's
    base type, or the name of a declared initializer-free scalar
    variable of that base type that is not itself an array name. -/
def elemOkB (m : Model) (defs : List (Ident × List BasicExpr))
    (b : BaseType) : BasicExpr → Bool
  | .lit (.int _) => decide (b = .int)
  | .lit (.bool _) => decide (b = .bool)
  | .lit (.set _) => false
  | .ident x =>
      (lookupIdent x defs).isNone &&
      m.variables.any (fun d => match d with
        | .basic ty n _ none => n.name == x.name && decide (ty.base = b)
        | _ => false)

/-- A variable declaration passes the array gate: scalar declarations
    always; arrays only as unrestricted int/bool aliases of acceptable
    elements. -/
def varArrayOkB (m : Model) (defs : List (Ident × List BasicExpr)) :
    VarDeclItem → Bool
  | .array ty _ _ es =>
      match ty.elem with
      | .par .int => es.all (elemOkB m defs .int)
      | .par .bool => es.all (elemOkB m defs .bool)
      | _ => false
  | _ => true

/-- A constraint argument passes the array gate: an explicit array
    literal must not mention an array name. -/
def explicitOkB (defs : List (Ident × List BasicExpr)) : Expr → Bool
  | .array es => es.all (fun b => match b with
      | .ident x => (lookupIdent x defs).isNone
      | _ => true)
  | _ => true

/-- The array gate.  The array-definition table is computed ONCE per
    model: the previous body recomputed it at every constraint (the
    partial application `explicitOkB (arrayDefs m)` was rebuilt inside
    the `List.all` lambda), which dominated the 1HZ5 compile time. -/
def arraysOkB (m : Model) : Bool :=
  let defs := arrayDefs m
  m.variables.all (varArrayOkB m defs) &&
  m.constraints.all (fun c => c.args.all (explicitOkB defs))

/-- The value of an array name under a store: its elements evaluated. -/
def arrayValue (defs : List (Ident × List BasicExpr)) (s : Store)
    (x : Ident) : Option Value :=
  (lookupIdent x defs).bind (fun es =>
    (es.mapM (BasicExpr.eval s)).map Value.array)

/-- The store extended with the array names' values (array names take
    precedence). -/
def fullStore (defs : List (Ident × List BasicExpr)) (s : Store) : Store :=
  fun x =>
    match arrayValue defs s x with
    | some v => some v
    | none => s x

/-- Re-attach the original model and the array-extended store. -/
def relabel (m : Model) (p : CompiledProblem DomConstraint) :
    CompiledProblem DomConstraint :=
  let defs := arrayDefs m
  { p with
    source := m
    toStore := (fun a => fullStore defs (p.toStore a)) }

/-- Compile a model with parameter arrays, variable-array aliases and
    constant-set membership: `compileModel` on the fully normalized
    model, with the original model as `source` and the array-extended
    `toStore`. -/
def compileModelFull (m : Model) :
    Except String (CompiledProblem DomConstraint) :=
  if arraysOkB m then
    match compileModel (normalizeFull m) with
    | .error e => .error e
    | .ok p => .ok (relabel m p)
  else .error "unsupported array declaration or array argument"

end LeanFzn.Compiler
