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
  Between array inlining and compilation it runs the L4 fragment sweep
  (`Fragment.fragmentModel`: scalar parameter substitution and
  supported scalar-initializer expansion), the L1/L2/L3 literal folds,
  and the constant-set membership domain restriction
  (`SetIn.restrictSetInModel`), so `set_in` over a plain declared scalar
  is a domain restriction rather than a leaf constraint.  The array part:

  * `arrayDefs m` lists, for every array declaration of `m`, the
    element expressions the array denotes (a parameter array: its
    literals; a variable array: its initializer);
  * `normalizeModel m` drops the array declarations and replaces every
    constraint argument that is the bare NAME of an array by the
    corresponding explicit array literal, which the unchanged
    `compileConstraints` already handles;
  * `compileModelFull m` runs the U1 bounds pass (`boundsModel`, which
    narrows unbounded `var int` declarations to intervals forced by the
    constraints, or rejects the model) and then `compileModel` on the
    normalized model, re-attaching the original model as `source` and a
    `toStore` that additionally gives every array name its (element-wise)
    value, so the produced store is a store of the ORIGINAL model.

  The variable-array alias gate (`arraysOkB`) is deliberately narrow so
  that the array's declared element type is automatically satisfied:
  the element type must be unrestricted `var int` / `var bool` / set,
  every element must be a literal of that base type or the name of a
  declared initializer-free scalar variable of that base type, and array
  names must not be reused as element or explicit-array identifiers.

  Set-valued variable arrays get one extra restriction (`setArrayUseOkB`):
  a set-array name may occur only as the array argument of the three
  set-element constraints.  This keeps the S5 shape pass complete: every
  surviving use of a variable set array is an element selection, whose
  semantics is extensional in the selected set value.

  `compileModel` and all its theorems are UNCHANGED; the correctness
  theorems for `compileModelFull` are in `Proofs/Normalize` (array
  inlining) and `Proofs/SetIn` (the constant-set domain restriction).

Dependencies:
  - LeanFzn.Compiler.Compile: `compileModel`, `CompiledProblem`.
  - LeanFzn.Compiler.SetIn: the constant-set domain restriction.
-/

import LeanFzn.Compiler.Compile
import LeanFzn.Compiler.Bounds
import LeanFzn.Compiler.Fragment
import LeanFzn.Compiler.LiteralFold
import LeanFzn.Compiler.SetIn
import LeanFzn.Compiler.SetExpand
import LeanFzn.Compiler.SetShape
import Std.Data.HashSet.Lemmas

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

/-- One step of the `basicNamesOf` fold. -/
def basicNameStep (p : BasicVarType → Bool) (s : Std.HashSet String)
    (d : VarDeclItem) : Std.HashSet String :=
  match d with
  | .basic ty n _ none => cond (p ty) (s.insert n.name) s
  | _ => s

/-- The fold behind `basicNamesOf`; shared with the correctness lemma so
    the generated match auxiliary is the same term. -/
def basicNamesFold (ds : List VarDeclItem) (s : Std.HashSet String)
    (p : BasicVarType → Bool) : Std.HashSet String :=
  ds.foldl (basicNameStep p) s

/-- The names of the initializer-free basic variables whose type satisfies
    `p`, computed once per model.  This is the lookup table that makes the
    array gate linear in the number of elements; the naive form rescanned
    every variable for every array element. -/
def basicNamesOf (m : Model) (p : BasicVarType → Bool) : Std.HashSet String :=
  basicNamesFold m.variables ∅ p

/-- The precomputed array-gate lookup tables.  `allSets` covers every
    set-typed basic variable; `sets` keeps the finite-universe ones that
    the set-array element gate requires. -/
structure ArrayGate where
  ints : Std.HashSet String
  bools : Std.HashSet String
  allSets : Std.HashSet String
  sets : Std.HashSet String

/-- Build the array-gate tables in one pass over the variable declarations. -/
def arrayGate (m : Model) : ArrayGate :=
  { ints := basicNamesOf m (fun ty => decide (ty.base = .int)),
    bools := basicNamesOf m (fun ty => decide (ty.base = .bool)),
    allSets := basicNamesOf m (fun ty => decide (ty.base = .setOfInt)),
    sets := basicNamesOf m (fun ty => (setUniverse? ty).isSome) }

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

/-- Fast twin of `SetIn.restrictSetInModel`: collect the tagged
    constant-set restrictions once, gate the variable rewrite by the
    subject-name hash set, and gate the drop test by the hash set of
    plain finite integer variable names.  The equality with the scanning
    definition is `restrictSetInModelFast_eq` in `Proofs/Normalize`. -/
def restrictSetInModelFast (m : Model) : Model :=
  let rs := setInRestrictionList m
  let subjects := setInSubjectNames rs
  let finites := basicNamesOf m (fun ty => isFiniteIntType ty)
  { m with
    variables := m.variables.map (restrictVarDeclOf rs subjects)
    constraints := m.constraints.filter (fun c => !setInRestrictsOf finites c) }

/-- The full source normalization: array inlining, the L4 fragment pass
    (scalar-parameter substitution and initializer expansion), literal
    folding, then the constant-set membership domain restriction. -/
def normalizeFull (m : Model) : Model :=
  restrictSetInModelFast (foldLiteralsModel (fragmentModel (normalizeModel m)))

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

/-- A set-valued variable-array element is acceptable: a set literal, or
    the name of a declared initializer-free basic set variable with a
    finite universe (and not itself an array name). -/
def setElemOkB (m : Model) (defs : List (Ident × List BasicExpr)) :
    BasicExpr → Bool
  | .lit (.set _) => true
  | .ident x =>
      (lookupIdent x defs).isNone &&
      m.variables.any (fun d => match d with
        | .basic ty n _ none => n.name == x.name && (setUniverse? ty).isSome
        | _ => false)
  | _ => false

/-- A variable declaration passes the array gate: scalar declarations
    always; arrays only as unrestricted int/bool/set aliases of
    acceptable elements. -/
def varArrayOkB (m : Model) (defs : List (Ident × List BasicExpr)) :
    VarDeclItem → Bool
  | .array ty _ _ es =>
      match ty.elem with
      | .par .int => es.all (elemOkB m defs .int)
      | .par .bool => es.all (elemOkB m defs .bool)
      | .par .setOfInt => es.all (setElemOkB m defs)
      | _ => false
  | _ => true

/-- Fast twin of `elemOkB`: the per-type name tables replace the scan of
    the whole variable list for every array element. -/
def elemOkBFast (g : ArrayGate) (defs : List (Ident × List BasicExpr))
    (b : BaseType) : BasicExpr → Bool
  | .lit (.int _) => decide (b = .int)
  | .lit (.bool _) => decide (b = .bool)
  | .lit (.set _) => false
  | .ident x =>
      (lookupIdent x defs).isNone &&
      match b with
      | .int => g.ints.contains x.name
      | .bool => g.bools.contains x.name
      | .setOfInt => g.allSets.contains x.name

/-- Fast twin of `setElemOkB`. -/
def setElemOkBFast (g : ArrayGate) (defs : List (Ident × List BasicExpr)) :
    BasicExpr → Bool
  | .lit (.set _) => true
  | .ident x => (lookupIdent x defs).isNone && g.sets.contains x.name
  | _ => false

/-- Fast twin of `varArrayOkB`. -/
def varArrayOkBFast (g : ArrayGate) (defs : List (Ident × List BasicExpr)) :
    VarDeclItem → Bool
  | .array ty _ _ es =>
      match ty.elem with
      | .par .int => es.all (elemOkBFast g defs .int)
      | .par .bool => es.all (elemOkBFast g defs .bool)
      | .par .setOfInt => es.all (setElemOkBFast g defs)
      | _ => false
  | _ => true

/-- A scalar initializer may not mention an array name: array definitions
    are inlined into constraints only. -/
def initializerOkB (defs : List (Ident × List BasicExpr)) :
    VarDeclItem → Bool
  | .basic _ _ _ (some b) =>
      match b with
      | .ident x => (lookupIdent x defs).isNone
      | .lit _ => true
  | _ => true

/-- A constraint argument passes the array gate: an explicit array
    literal must not mention an array name. -/
def explicitOkB (defs : List (Ident × List BasicExpr)) : Expr → Bool
  | .array es => es.all (fun b => match b with
      | .ident x => (lookupIdent x defs).isNone
      | _ => true)
  | _ => true

/-- The names of the variable arrays whose elements are sets. -/
def setArrayNames (m : Model) : List String :=
  m.variables.filterMap fun d =>
    match d with
    | .array ty n _ _ =>
        match ty.elem with
        | .par .setOfInt => some n.name
        | _ => none
    | .basic .. => none

/-- Does this basic expression mention one of the given names? -/
def mentionsName (names : List String) : BasicExpr → Bool
  | .ident x => names.contains x.name
  | _ => false

/-- Does this expression mention one of the given names? -/
def exprMentionsName (names : List String) : Expr → Bool
  | .basic b => mentionsName names b
  | .array es => es.any (mentionsName names)

/-- The array argument of a set-element constraint may be a bare array
    name or an explicit array whose elements mention no set-array name. -/
def elemArrayArgOkB (names : List String) : Expr → Bool
  | .array es => es.all (fun b => !mentionsName names b)
  | _ => true

/-- A set-array name may occur only as the array argument of the three
    set-element constraints; every other occurrence rejects the model.
    The index and target arguments must not mention a set-array name. -/
def setArrayUseOkB (names : List String) (c : ConstraintItem) : Bool :=
  match c.name.name, c.args with
  | "array_var_set_element", [a0, a1, a2] =>
      !exprMentionsName names a0 && elemArrayArgOkB names a1 &&
        !exprMentionsName names a2
  | "array_set_element", [a0, a1, a2] =>
      !exprMentionsName names a0 && elemArrayArgOkB names a1 &&
        !exprMentionsName names a2
  | "array_var_set_element_nonshifted", [a0, a1, a2] =>
      !exprMentionsName names a0 && elemArrayArgOkB names a1 &&
        !exprMentionsName names a2
  | _, _ => c.args.all (fun e => !exprMentionsName names e)

/-- The array gate.  The array-definition table is computed ONCE per
    model: the previous body recomputed it at every constraint (the
    partial application `explicitOkB (arrayDefs m)` was rebuilt inside
    the `List.all` lambda), which dominated the 1HZ5 compile time. -/
def arraysOkB (m : Model) : Bool :=
  let defs := arrayDefs m
  let snames := setArrayNames m
  let gate := arrayGate m
  m.variables.all (varArrayOkBFast gate defs) &&
  m.variables.all (initializerOkB defs) &&
  m.constraints.all (fun c =>
    c.args.all (explicitOkB defs) && setArrayUseOkB snames c)

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

/-- Re-attach the original model, the array-extended store, and the
    reconstruction of the expanded set variables from their fresh
    Booleans. -/
def relabel (m : Model) (se : SetExpansion)
    (p : CompiledProblem DomConstraint) : CompiledProblem DomConstraint :=
  let defs := arrayDefs m
  { p with
    source := m
    toStore := fun a => fullStore defs (setStore se (p.toStore a)) }

/-- Compile a model with parameter arrays, variable-array aliases, constant-set
    membership and scalar set variables: expand the declared set variables
    (with the original model's names taken, so the fresh Booleans also avoid
    the array names normalization removed), run the U1 bounds pass, then
    `compileModel`, with the original model as `source` and a `toStore` that
    reconstructs arrays and set values. -/
def compileModelFull (m : Model) :
    Except String (CompiledProblem DomConstraint) :=
  if arraysOkB m then
    match shapeExpandModel (normalizeFull m) with
    | none => .error "unsupported set shape"
    | some sh =>
        match setExpandModel sh.model with
        | none => .error "unsupported set variable shape"
        | some se =>
            match boundsModel se.model with
            | none => .error "unbounded integer variable without certified bounds"
            | some mb =>
                match compileModel mb with
                | .error e => .error e
                | .ok p => .ok (relabel m se p)
  else .error "unsupported array declaration or array argument"

end LeanFzn.Compiler
