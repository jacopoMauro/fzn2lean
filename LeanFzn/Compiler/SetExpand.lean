/-
File: LeanFzn/Compiler/SetExpand.lean

Purpose:
  Verified expansion of scalar `var set of lo..hi` / `var set of {..}`
  declarations (PLAN.md task S3).  Each declared set variable becomes one
  fresh Boolean per universe value, and the S3 membership shapes are
  rewritten to Boolean rows:

  * `set_in(k, S)` pins the Boolean of `k` (or becomes the always-false
    row when `k` is outside the declared universe);
  * `set_in_reif(k, S, r)` equates the Boolean of `k` with `r`, with the
    literal-result cases reduced to a pin, a drop, or the false row.

  Every other constraint is kept, but the pass returns `none` if it still
  mentions a removed set variable.  The expansion also carries a
  `SetExpansion` table so the store of the rewritten problem can be
  rebuilt as a set value (`setStore`).  A set-valued initializer, a bare
  `var set of int`, a set array, and any unrewritten shape are rejected;
  they remain honest unsupported outcomes.

  The correctness theorems are in `Proofs/SetExpand`.

Dependencies:
  - LeanFzn.Compiler.LiteralFold (the accepted always-false row).
-/

import LeanFzn.Compiler.LiteralFold
import Std.Data.HashSet.Lemmas

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation

/-- One expanded set variable: its source name and declared type, and the
    fresh Boolean name attached to each universe value.  The universe list
    is ascending and duplicate-free. -/
structure SetInfo where
  name : String
  ty : BasicVarType
  bools : List (String × Int)
  deriving Repr

/-- The result of the set-expansion pass: the rewritten model and the
    table used to rebuild source set values from Boolean stores. -/
structure SetExpansion where
  model : Model
  sets : List SetInfo
  deriving Repr

/-- The universe of a declared set type: the ascending, duplicate-free
    list of values the declaration admits.  `setUniverse?` is `none` for
    non-set types and for the unbounded `var set of int`. -/
def setUniverse? : BasicVarType → Option (List Int)
  | .setOfIntRange lo hi => some (setElems (.interval lo hi))
  | .setOfIntSet xs => some ((IntSetValue.enumeration xs).sortElems)
  | _ => none

/-- The fresh Boolean name of each universe value, numbered from `start`
    in the globally fresh `auxName` family. -/
def freshPairs (taken : List String) : Nat → List Int → List (String × Int)
  | _, [] => []
  | start, v :: vs => (auxName taken start, v) :: freshPairs taken (start + 1) vs

/-- The counter after a `freshPairs` run. -/
def freshPairsNext (start : Nat) (us : List Int) : Nat := start + us.length

/-- `auxName` with the length bound already computed.  `auxName` calls
    `maxStrLength taken` at every slot; on the post-shape models the taken
    list has over a million names, so allocating twelve thousand slots that
    way is quadratic. -/
def auxNameAt (bound : Nat) (n : Nat) : String :=
  "_aux_" ++ dollarRun (bound + 1 + n)

/-- `freshPairs` with the length bound already computed. -/
def freshPairsAt (bound : Nat) : Nat → List Int → List (String × Int)
  | _, [] => []
  | start, v :: vs => (auxNameAt bound start, v) :: freshPairsAt bound (start + 1) vs

/-- The bounded allocator agrees with `auxName` at its bound. -/
theorem auxNameAt_eq (taken : List String) (n : Nat) :
    auxNameAt (maxStrLength taken) n = auxName taken n := rfl

/-- The bounded allocator agrees with `freshPairs` at its bound. -/
theorem freshPairsAt_eq (taken : List String) (start : Nat) (us : List Int) :
    freshPairsAt (maxStrLength taken) start us = freshPairs taken start us := by
  induction us generalizing start with
  | nil => rfl
  | cons v vs ih =>
      simp only [freshPairsAt, freshPairs, auxNameAt_eq, ih]

/-- The names a model can mention (parameters and variables).  Fresh
    auxiliary names are disjoint from this list. -/
def setTaken (m : Model) : List String :=
  m.parameters.map (fun d => d.name.name) ++
    m.variables.map (fun d => d.name.name)

/-- Expand the variable declarations: a declared set variable is replaced
    by its fresh Booleans; every other declaration is kept.  A set-typed
    declaration outside the accepted shapes rejects the whole model. -/
def expandVarDecls (taken : List String) (n : Nat) :
    List VarDeclItem → Option (List SetInfo × Nat × List VarDeclItem)
  | [] => some ([], n, [])
  | d :: ds =>
      match d with
      | .basic ty x _anns none =>
          match setUniverse? ty with
          | some us =>
              let pairs := freshPairs taken n us
              let info : SetInfo := { name := x.name, ty := ty, bools := pairs }
              let bds := pairs.map fun p =>
                (VarDeclItem.basic (.par .bool) (Ident.mk p.1) [] none)
              match expandVarDecls taken (n + us.length) ds with
              | none => none
              | some (infos, n', rest) =>
                  some (info :: infos, n', bds ++ rest)
          | none =>
              if ty.base = .setOfInt then none
              else
                match expandVarDecls taken n ds with
                | none => none
                | some (infos, n', rest) => some (infos, n', d :: rest)
      | .basic ty _ _ (some _) =>
          if ty.base = .setOfInt then none
          else
            match expandVarDecls taken n ds with
            | none => none
            | some (infos, n', rest) => some (infos, n', d :: rest)
      | .array ty _ _ _ =>
          if ty.elem.base = .setOfInt then none
          else
            match expandVarDecls taken n ds with
            | none => none
            | some (infos, n', rest) => some (infos, n', d :: rest)

/-- The width-bounded twin of `expandVarDecls`: identical, but the fresh
    names are allocated with the already computed `maxStrLength taken`
    bound instead of recomputing it per slot. -/
def expandVarDeclsAt (bound : Nat) (n : Nat) :
    List VarDeclItem → Option (List SetInfo × Nat × List VarDeclItem)
  | [] => some ([], n, [])
  | d :: ds =>
      match d with
      | .basic ty x _anns none =>
          match setUniverse? ty with
          | some us =>
              let pairs := freshPairsAt bound n us
              let info : SetInfo := { name := x.name, ty := ty, bools := pairs }
              let bds := pairs.map fun p =>
                (VarDeclItem.basic (.par .bool) (Ident.mk p.1) [] none)
              match expandVarDeclsAt bound (n + us.length) ds with
              | none => none
              | some (infos, n', rest) =>
                  some (info :: infos, n', bds ++ rest)
          | none =>
              if ty.base = .setOfInt then none
              else
                match expandVarDeclsAt bound n ds with
                | none => none
                | some (infos, n', rest) => some (infos, n', d :: rest)
      | .basic ty _ _ (some _) =>
          if ty.base = .setOfInt then none
          else
            match expandVarDeclsAt bound n ds with
            | none => none
            | some (infos, n', rest) => some (infos, n', d :: rest)
      | .array ty _ _ _ =>
          if ty.elem.base = .setOfInt then none
          else
            match expandVarDeclsAt bound n ds with
            | none => none
            | some (infos, n', rest) => some (infos, n', d :: rest)

/-- The set table entry for a name, if the name is a removed set
    variable. -/
def SetExpansion.infoOf (se : SetExpansion) (x : Ident) : Option SetInfo :=
  se.sets.find? fun i => i.name = x.name

/-- Is this a removed set-variable name? -/
def SetExpansion.isSetName (se : SetExpansion) (x : Ident) : Bool :=
  (se.infoOf x).isSome

/-- The fresh Boolean attached to one universe value. -/
def SetInfo.boolAt (i : SetInfo) (v : Int) : Option String :=
  (i.bools.find? fun p => p.2 = v).map Prod.fst

/-- The universe value attached to one fresh Boolean name. -/
def SetInfo.boolValueOf (i : SetInfo) (x : Ident) : Option Int :=
  (i.bools.find? fun p => p.1 = x.name).map Prod.snd

/-- The set whose fresh Booleans include this name. -/
def SetExpansion.boolInfoOf (se : SetExpansion) (x : Ident) : Option SetInfo :=
  se.sets.find? fun i => i.bools.any fun p => p.1 = x.name

/-- The source set value of a set variable, if the store has one. -/
def SetInfo.sourceSet? (i : SetInfo) (s : Store) : Option IntSetValue :=
  match s (Ident.mk i.name) with
  | some (.setOfInt sv) => some sv
  | _ => none

/-- `Contains` of the source set value, as a Boolean. -/
def SetInfo.sourceContainsB (i : SetInfo) (s : Store) (v : Int) : Bool :=
  match i.sourceSet? s with
  | some sv => decide (sv.Contains v)
  | none => false

/-- The set rebuilt from a Boolean store: the universe values whose
    Boolean is true. -/
def SetInfo.rebuilt (i : SetInfo) (s : Store) : IntSetValue :=
  .enumeration
    (i.bools.filterMap fun p =>
      match s (Ident.mk p.1) with
      | some (.bool true) => some p.2
      | _ => none)

/-- The universe of a set info: the values of its Boolean slots. -/
def SetInfo.values (i : SetInfo) : List Int := i.bools.map Prod.snd

/-- The names of the set variables removed by the expansion. -/
def SetExpansion.setNames (se : SetExpansion) : List String :=
  se.sets.map (fun i => i.name)

/-- The names of all fresh Boolean slots. -/
def SetExpansion.boolNames (se : SetExpansion) : List String :=
  se.sets.flatMap (fun i => i.bools.map Prod.fst)

/-- Insert every removed set-variable name into a hash set. -/
def insertSetNames (is : List SetInfo) (s : Std.HashSet String) :
    Std.HashSet String :=
  is.foldl (fun s i => s.insert i.name) s

/-- The removed set-variable names as a hash set.  This is the lookup
    table that keeps `rewriteConstraintFast` linear; `isSetName` rescans
    the whole table for every identifier, which is quadratic on the large
    normalized models. -/
def SetExpansion.setNameSet (se : SetExpansion) : Std.HashSet String :=
  insertSetNames se.sets ∅

/-- Does a basic expression mention a removed set-variable name? -/
def basicMentionsSet (se : SetExpansion) : BasicExpr → Bool
  | .ident x => se.isSetName x
  | .lit _ => false

/-- Does an expression mention a removed set-variable name? -/
def exprMentionsSet (se : SetExpansion) : Expr → Bool
  | .basic b => basicMentionsSet se b
  | .array es => es.any (basicMentionsSet se)

/-- A constraint argument mentions a removed set-variable name. -/
def constraintMentionsSet (se : SetExpansion) (c : ConstraintItem) : Bool :=
  c.args.any (exprMentionsSet se)

/-! ### Hash-set fast twins

`isSetName` scans `se.sets` for every identifier, so `constraintMentionsSet`
is quadratic on the millions of constraints produced by the shape pass.
The twins below use the precomputed `setNameSet`; the correctness lemmas in
`Proofs/SetExpand` show they agree pointwise with the scanning definitions. -/

/-- Does a basic expression mention a name in the precomputed table? -/
def basicMentionsSetFast (names : Std.HashSet String) : BasicExpr → Bool
  | .ident x => names.contains x.name
  | .lit _ => false

/-- Does an expression mention a name in the precomputed table? -/
def exprMentionsSetFast (names : Std.HashSet String) : Expr → Bool
  | .basic b => basicMentionsSetFast names b
  | .array es => es.any (basicMentionsSetFast names)

/-- A constraint argument mentions a name in the precomputed table. -/
def constraintMentionsSetFast (names : Std.HashSet String)
    (c : ConstraintItem) : Bool :=
  c.args.any (exprMentionsSetFast names)

/-- Pin a Boolean to a value: `bool_not(b, !v)` means `b = v`. -/
def pinBoolConstraint (b : String) (v : Bool) : ConstraintItem :=
  { name := Ident.mk "bool_not"
    args := [.basic (.ident (Ident.mk b)), .basic (.lit (.bool (!v)))]
    anns := [] }

/-- Equate two Boolean variables. -/
def boolEqConstraint (b r : String) : ConstraintItem :=
  { name := Ident.mk "bool_eq"
    args := [.basic (.ident (Ident.mk b)), .basic (.ident (Ident.mk r))]
    anns := [] }

/-- Rewrite one constraint.  The `set_in`/`set_in_reif` shapes with a
    declared set variable become Boolean rows; any other shape mentioning
    a removed set name is rejected.  Annotations are dropped because they
    are inert in `SatisfiesDyn`. -/
def rewriteConstraint (se : SetExpansion) (c : ConstraintItem) :
    Option (List ConstraintItem) :=
  match c.name.name, c.args with
  | "set_in", [.basic (.lit (.int k)), .basic (.ident s)] =>
      match se.infoOf s with
      | some i =>
          match i.boolAt k with
          | some b => some [pinBoolConstraint b true]
          | none => some [falseConstraint]
      | none =>
          if constraintMentionsSet se c then none else some [c]
  | "set_in_reif", [.basic (.lit (.int k)), .basic (.ident s), r] =>
      match se.infoOf s with
      | some i =>
          match i.boolAt k with
          | some b =>
              match r with
              | .basic (.ident z) =>
                  if se.isSetName z then none
                  else some [boolEqConstraint b z.name]
              | .basic (.lit (.bool true)) => some [pinBoolConstraint b true]
              | .basic (.lit (.bool false)) => some [pinBoolConstraint b false]
              | _ => none
          | none =>
              match r with
              | .basic (.ident z) =>
                  if se.isSetName z then none
                  else some [pinBoolConstraint z.name false]
              | .basic (.lit (.bool true)) => some [falseConstraint]
              | .basic (.lit (.bool false)) => some []
              | _ => none
      | none =>
          if constraintMentionsSet se c then none else some [c]
  | _, _ =>
      if constraintMentionsSet se c then none else some [c]

/-- The hash-set twin of `rewriteConstraint`: identical except that set
    names are looked up in the precomputed table.  The pass below uses this
    version; `rewriteConstraintFast_eq` proves it agrees with the scanning
    specification on every constraint. -/
def rewriteConstraintFast (names : Std.HashSet String) (se : SetExpansion)
    (c : ConstraintItem) : Option (List ConstraintItem) :=
  match c.name.name, c.args with
  | "set_in", [.basic (.lit (.int k)), .basic (.ident s)] =>
      match se.infoOf s with
      | some i =>
          match i.boolAt k with
          | some b => some [pinBoolConstraint b true]
          | none => some [falseConstraint]
      | none =>
          if constraintMentionsSetFast names c then none else some [c]
  | "set_in_reif", [.basic (.lit (.int k)), .basic (.ident s), r] =>
      match se.infoOf s with
      | some i =>
          match i.boolAt k with
          | some b =>
              match r with
              | .basic (.ident z) =>
                  if names.contains z.name then none
                  else some [boolEqConstraint b z.name]
              | .basic (.lit (.bool true)) => some [pinBoolConstraint b true]
              | .basic (.lit (.bool false)) => some [pinBoolConstraint b false]
              | _ => none
          | none =>
              match r with
              | .basic (.ident z) =>
                  if names.contains z.name then none
                  else some [pinBoolConstraint z.name false]
              | .basic (.lit (.bool true)) => some [falseConstraint]
              | .basic (.lit (.bool false)) => some []
              | _ => none
      | none =>
          if constraintMentionsSetFast names c then none else some [c]
  | _, _ =>
      if constraintMentionsSetFast names c then none else some [c]

/-- **The set-expansion pass**, with the list of names the fresh Boolean
    slots must avoid.  Declared scalar set variables become fresh
    Booleans; the two S3 membership shapes are rewritten; every remaining
    reference to a removed set name rejects the model.  The caller that
    expands a NORMALIZED model passes the original model's names, so the
    fresh slots also avoid the array names that normalization removed. -/
def setExpandModelWith (taken : List String) (m : Model) : Option SetExpansion :=
  match expandVarDeclsAt (maxStrLength taken) 0 m.variables with
  | none => none
  | some (infos, _, vars) =>
      let se : SetExpansion := { model := { m with variables := vars }, sets := infos }
      match m.constraints.mapM (rewriteConstraintFast se.setNameSet se) with
      | none => none
      | some css => some { se with model := { se.model with constraints := css.flatten } }

/-- The set-expansion pass avoiding the model's own declared names. -/
def setExpandModel (m : Model) : Option SetExpansion :=
  setExpandModelWith (setTaken m) m

/-- Rebuild a source set value from the fresh Booleans: the ascending
    enumeration of the universe values whose Boolean is true.  Names that
    are not set variables are read from the underlying store unchanged. -/
def setStore (se : SetExpansion) (s : Store) : Store :=
  fun x =>
    match se.infoOf x with
    | some i => some (.setOfInt (i.rebuilt s))
    | none => s x

/-- The completeness store: fresh Booleans are set from the source set
    value's `Contains`; every other name is read from the source store. -/
def encodeStore (se : SetExpansion) (s : Store) : Store :=
  fun x =>
    match se.boolInfoOf x with
    | some i =>
        match i.boolValueOf x with
        | some v => some (.bool (i.sourceContainsB s v))
        | none => s x
    | none => s x

end LeanFzn.Compiler
