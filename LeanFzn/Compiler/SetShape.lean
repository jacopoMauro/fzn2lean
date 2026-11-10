/-
File: LeanFzn/Compiler/SetShape.lean

Purpose:
  Pre-pass for the set-shape tasks S4–S7.  It runs after `normalizeFull`
  and before the verified S3 expansion.  Set constraints that S3 does not
  handle are rewritten into ordinary scalar constraints plus the literal
  `set_in`/`set_in_reif` shapes S3 already proves.  Set declarations are
  left in place for S3.

  S4 shapes:
  * `set_in_reif(x, S, b)` with a variable integer `x`: an equality bit
    per value of `x`'s finite domain, a membership bit per value, a
    conjunction, and a Boolean clause linking the conjunctions to `b`.
  * `set_card(S, k)`: a membership bit per universe value, a `bool2int`
    alias, and one linear equality.
  * `set_union(A, B, C)`: one Boolean relation per value in the union of
    the three declared universes; values outside a universe contribute a
    pinned `false`, and a value outside `C`'s universe forces the
    corresponding `A`/`B` bits false.

  Every auxiliary is a fresh ordinary scalar variable with a functional
  definition recorded in `ShapeExpansion.aux` for the completeness proof.
  The pass is the identity on constraints it does not recognize; a later
  unsupported shape is still rejected by S3's set-reference gate.

Dependencies:
  - LeanFzn.Compiler.SetExpand (auxiliary naming and set universes).
-/

import LeanFzn.Compiler.SetExpand

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation

/-- The functional definition of one shape auxiliary. -/
inductive ShapeKind where
  /-- A membership bit for `v ∈ S`: `set_in_reif(v,S,a)`. -/
  | member (setName : String) (v : Int)
  /-- An equality bit for `x = v`: `int_eq_reif(x,v,e)`. -/
  | eq (x : String) (v : Int)
  /-- A Boolean conjunction of two identifiers: `bool_and(a,b,c)`. -/
  | and (a b : String)
  /-- A `bool2int` alias for a Boolean identifier: `bool2int(a,c)`. -/
  | bit (a : String)
  /-- A fresh Boolean pinned to a literal: `bool_not(a,!v)`. -/
  | const (v : Bool)
  deriving Repr

/-- One fresh auxiliary declaration and its definition. -/
structure ShapeAux where
  name : String
  ty : BasicVarType
  kind : ShapeKind
  deriving Repr

/-- Accumulator for one pass over the constraint list.  `decls` and
    `cons` are stored in reverse allocation/emission order.

    `maxLen` caches `maxStrLength taken` so that fresh names do not
    rescan the taken list at every allocation (the S4–S6 passes allocate
    hundreds of thousands of auxiliaries on the larger warehouse models).
    -/
structure ShapeState where
  next : Nat
  aux : List ShapeAux
  decls : List VarDeclItem
  cons : List ConstraintItem
  maxLen : Nat
  deriving Repr

/-- The result of the shape pre-pass. -/
structure ShapeExpansion where
  model : Model
  aux : List ShapeAux
  deriving Repr

/-- A Boolean literal term. -/
def shapeBool (b : Bool) : BasicExpr := .lit (.bool b)

/-- A variable-name term. -/
def shapeName (x : String) : BasicExpr := .ident (Ident.mk x)

/-- An integer literal term. -/
def shapeInt (k : Int) : BasicExpr := .lit (.int k)

/-- The variable name of a term, if any. -/
def shapeName? : BasicExpr → Option String
  | .ident x => some x.name
  | _ => none

/-- A standard constraint with no annotations. -/
def shapeE (b : BasicExpr) : Expr := .basic b

/-- A standard constraint with no annotations. -/
def shapeConstraint (n : String) (args : List Expr) : ConstraintItem :=
  { name := Ident.mk n, args := args, anns := [] }

/-- An `int_lin_eq` row. -/
def shapeLinEq (coeffs : List Int) (vars : List String) (rhs : Int) : ConstraintItem :=
  shapeConstraint "int_lin_eq"
    [.array (coeffs.map fun k => shapeInt k),
     .array (vars.map fun x => shapeName x),
     shapeE (shapeInt rhs)]

/-- The defining constraint emitted for an auxiliary. -/
def ShapeAux.definition : ShapeAux → ConstraintItem
  | ⟨n, _, .member S v⟩ =>
      shapeConstraint "set_in_reif"
        [shapeE (shapeInt v), shapeE (shapeName S), shapeE (shapeName n)]
  | ⟨n, _, .eq x v⟩ =>
      shapeConstraint "int_eq_reif"
        [shapeE (shapeName x), shapeE (shapeInt v), shapeE (shapeName n)]
  | ⟨n, _, .and x y⟩ =>
      shapeConstraint "bool_and"
        [shapeE (shapeName x), shapeE (shapeName y), shapeE (shapeName n)]
  | ⟨n, _, .bit x⟩ =>
      shapeConstraint "bool2int"
        [shapeE (shapeName x), shapeE (shapeName n)]
  | ⟨n, _, .const v⟩ => pinBoolConstraint n v

/-- The fresh-name family of the shape pre-pass.  The `$`-run makes the
    name strictly longer than every taken name, so it is fresh even
    against hand-built models; the decimal counter keeps the name short
    (unlike the older unary `auxName` family, whose name length grew with
    the allocation counter). -/
def shapeAuxName (bound n : Nat) : String :=
  "_aux_" ++ dollarRun (bound + 1) ++ Nat.repr n

/-- Add a declaration and advance the auxiliary counter. -/
def ShapeState.freshDecl (taken : List String) (st : ShapeState)
    (ty : BasicVarType) : String × ShapeState :=
  let n := shapeAuxName st.maxLen st.next
  (n, { st with
        next := st.next + 1
        decls := .basic ty (Ident.mk n) [] none :: st.decls })

/-- Allocate a fresh Boolean auxiliary, emitting its defining constraint. -/
def ShapeState.freshBool (taken : List String) (st : ShapeState)
    (kind : ShapeKind) : String × ShapeState :=
  let (n, st') := st.freshDecl taken (.par .bool)
  let a : ShapeAux := { name := n, ty := .par .bool, kind := kind }
  (n, { st' with aux := a :: st'.aux, cons := a.definition :: st'.cons })

/-- Allocate a fresh `0..1` integer auxiliary, emitting its defining
    constraint. -/
def ShapeState.freshInt01 (taken : List String) (st : ShapeState)
    (kind : ShapeKind) : String × ShapeState :=
  let (n, st') := st.freshDecl taken (.intRange 0 1)
  let a : ShapeAux := { name := n, ty := .intRange 0 1, kind := kind }
  (n, { st' with aux := a :: st'.aux, cons := a.definition :: st'.cons })

/-- Emit one constraint. -/
def ShapeState.emit (st : ShapeState) (c : ConstraintItem) : ShapeState :=
  { st with cons := c :: st.cons }

/-- Emit a list of constraints in order. -/
def ShapeState.emitList (st : ShapeState) (cs : List ConstraintItem) : ShapeState :=
  { st with cons := cs.reverse ++ st.cons }

/-- The declared set universe of a variable name. -/
def modelSetUniverse? (m : Model) (name : String) : Option (List Int) :=
  let rec go : List VarDeclItem → Option (List Int)
    | [] => none
    | .basic ty x _ _ :: ds =>
        if x.name = name then setUniverse? ty else go ds
    | .array _ _ _ _ :: ds => go ds
  go m.variables

/-- The finite declared integer values of a variable name. -/
def modelIntValues? (m : Model) (name : String) : Option (List Int) :=
  let rec go : List VarDeclItem → Option (List Int)
    | [] => none
    | .basic ty x _ _ :: ds =>
        if x.name = name then
          match ty with
          | .intRange lo hi => some (setElems (.interval lo hi))
          | .intSet xs => some ((IntSetValue.enumeration xs).sortElems)
          | _ => none
        else go ds
    | .array _ _ _ _ :: ds => go ds
  go m.variables

/-- Is this name a declared set variable? -/
def modelIsSetName (m : Model) (name : String) : Bool :=
  (modelSetUniverse? m name).isSome

/-- The finite values of a set argument: a declared set variable's
    universe, or a literal set's elements.  `none` means the argument is
    not one of those finite set shapes. -/
def setArgValues? (m : Model) : Expr → Option (List Int)
  | .basic (.ident s) => modelSetUniverse? m s.name
  | .basic (.lit (.set l)) =>
      match l with
      | .intSet xs => some ((IntSetValue.enumeration xs).sortElems)
      | .intRange lo hi => some (setElems (.interval lo hi))
  | _ => none

/-- A membership term for `v ∈ S`.  A declared set variable introduces
    the literal S3 shape `set_in_reif(v,S,a)`; a literal set and a value
    outside a declared universe are pinned with `bool_not`. -/
def memberTerm (taken : List String) (m : Model) (st : ShapeState)
    (s : Expr) (v : Int) : Option (String × ShapeState) :=
  match s with
  | .basic (.ident S) =>
      match modelSetUniverse? m S.name with
      | none => none
      | some us =>
          if v ∈ us then
            some (st.freshBool taken (.member S.name v))
          else
            some (st.freshBool taken (.const false))
  | .basic (.lit (.set l)) =>
      let b := decide (l.denote.Contains v)
      some (st.freshBool taken (.const b))
  | _ => none

/-- A Boolean result identifier.  A literal result is represented by a
    fresh Boolean pinned to that literal, so the clause encoding always
    sees identifiers. -/
def resultTarget (taken : List String) (st : ShapeState) :
    BasicExpr → Option (String × ShapeState)
  | .ident b => some (b.name, st)
  | .lit (.bool true) => some (st.freshBool taken (.const true))
  | .lit (.bool false) => some (st.freshBool taken (.const false))
  | _ => none

/-- Link a target Boolean to the disjunction of the terms with
    `bool_clause`: `target → OR terms` and every `term → target`. -/
def linkOr (st : ShapeState) (terms : List String) (target : String) : ShapeState :=
  match terms with
  | [] => st.emit (pinBoolConstraint target false)
  | _ =>
      let positives := terms.map shapeName
      let clause := shapeConstraint "bool_clause"
        [.array positives, .array [shapeName target]]
      let links := terms.map fun t =>
        shapeConstraint "bool_clause"
          [.array [shapeName target], .array [shapeName t]]
      st.emitList (clause :: links)

/-- The per-value terms of a variable membership `x ∈ S`, together with
    the state after emitting their definitions. -/
def varMemberTerms (taken : List String) (m : Model) (x s : String) :
    ShapeState → List Int → Option (List String × ShapeState)
  | st, [] => some ([], st)
  | st, v :: vs =>
      match st.freshBool taken (.eq x v) with
      | (e, st1) =>
        match memberTerm taken m st1 (.basic (.ident (Ident.mk s))) v with
        | none => none
        | some (a, st2) =>
          match st2.freshBool taken (.and e a) with
          | (t, st3) =>
            match varMemberTerms taken m x s st3 vs with
            | none => none
            | some (ts, st4) => some (t :: ts, st4)

/-- Rewrite `set_in_reif(x,S,b)` for a variable integer `x`. -/
def rewriteVarMember (taken : List String) (m : Model) (st : ShapeState)
    (x s : String) (vals : List Int) (r : BasicExpr) :
    Option (ShapeState × List ConstraintItem) :=
  match varMemberTerms taken m x s st vals with
  | none => none
  | some (terms, st1) =>
      match resultTarget taken st1 r with
      | none => none
      | some (target, st2) => some (linkOr st2 terms target, [])

/-- The `bool2int` aliases for the universe of a cardinality constraint. -/
def cardBits (taken : List String) (m : Model) (s : String) :
    ShapeState → List Int → Option (List String × ShapeState)
  | st, [] => some ([], st)
  | st, v :: vs =>
      match memberTerm taken m st (.basic (.ident (Ident.mk s))) v with
      | none => none
      | some (a, st1) =>
        match st1.freshInt01 taken (.bit a) with
        | (c, st2) =>
          match cardBits taken m s st2 vs with
          | none => none
          | some (cs, st3) => some (c :: cs, st3)

/-- Rewrite `set_card(S,k)` for a declared set variable `S`. -/
def rewriteCard (taken : List String) (m : Model) (st : ShapeState)
    (s : String) (k : BasicExpr) : Option (ShapeState × List ConstraintItem) :=
  let us := (modelSetUniverse? m s).getD []
  if us.isEmpty then
    match k with
    | .ident kn =>
        some (st.emit (shapeConstraint "int_eq" [shapeE (shapeName kn.name), shapeE (shapeInt 0)]), [])
    | .lit (.int n) =>
        if n = 0 then some (st, []) else some (st.emit falseConstraint, [])
    | _ => none
  else
    match cardBits taken m s st us with
    | none => none
    | some (cs, st1) =>
        match k with
        | .ident kn =>
            let coeffs := cs.map (fun _ => 1) ++ [-1]
            some (st1.emit (shapeLinEq coeffs (cs ++ [kn.name]) 0), [])
        | .lit (.int n) =>
            let coeffs := cs.map (fun _ => 1)
            some (st1.emit (shapeLinEq coeffs cs n), [])
        | _ => none

/-- The per-value rows of a set union. -/
def unionRows (taken : List String) (m : Model) (a b c : Expr) :
    ShapeState → List Int → Option ShapeState
  | st, [] => some st
  | st, v :: vs =>
      match memberTerm taken m st a v with
      | none => none
      | some (av, st1) =>
        match memberTerm taken m st1 b v with
        | none => none
        | some (bv, st2) =>
          match memberTerm taken m st2 c v with
          | none => none
          | some (cv, st3) =>
            let st4 := st3.emit
              (shapeConstraint "bool_or"
                [shapeE (shapeName av), shapeE (shapeName bv), shapeE (shapeName cv)])
            unionRows taken m a b c st4 vs

/-- Rewrite `set_union(A,B,C)` for finite set arguments. -/
def rewriteUnion (taken : List String) (m : Model) (st : ShapeState)
    (a b c : Expr) (ua ub uc : List Int) :
    Option (ShapeState × List ConstraintItem) :=
  match unionRows taken m a b c st (ua ++ ub ++ uc) with
  | none => none
  | some st' => some (st', [])

/-! ## S6: set intersection -/

/-- The per-value rows of a set intersection.  The value list is the
    sorted duplicate-free union of the three argument universes, so a
    shared universe value allocates its membership bits only once. -/
def intersectRows (taken : List String) (m : Model) (a b c : Expr) :
    ShapeState → List Int → Option ShapeState
  | st, [] => some st
  | st, v :: vs =>
      match memberTerm taken m st a v with
      | none => none
      | some (av, st1) =>
        match memberTerm taken m st1 b v with
        | none => none
        | some (bv, st2) =>
          match memberTerm taken m st2 c v with
          | none => none
          | some (cv, st3) =>
            let st4 := st3.emit
              (shapeConstraint "bool_and"
                [shapeE (shapeName av), shapeE (shapeName bv), shapeE (shapeName cv)])
            intersectRows taken m a b c st4 vs

/-- Rewrite `set_intersect(A,B,C)` for finite set arguments. -/
def rewriteIntersect (taken : List String) (m : Model) (st : ShapeState)
    (a b c : Expr) (ua ub uc : List Int) :
    Option (ShapeState × List ConstraintItem) :=
  match intersectRows taken m a b c st
      ((IntSetValue.enumeration (ua ++ ub ++ uc)).sortElems) with
  | none => none
  | some st' => some (st', [])

/-! ## S5: set membership of a variable integer and set-array element -/

/-- The concatenation of the declared universes of the element set
    expressions, in array order. -/
def arrayElemUnion (m : Model) : List BasicExpr → Option (List Int)
  | [] => some []
  | e :: rest =>
      match setArgValues? m (.basic e) with
      | none => none
      | some us =>
          match arrayElemUnion m rest with
          | none => none
          | some union => some (us ++ union)

/-- The sorted, duplicate-free union of the declared universes of the
    element set expressions and of the target set variable.  The target
    must be a declared set variable with a finite universe; every
    element must be a literal set or such a variable. -/
def arrayElemValues (m : Model) (es : List BasicExpr) (T : String) :
    Option (List Int) :=
  match modelSetUniverse? m T with
  | none => none
  | some ut =>
      match arrayElemUnion m es with
      | none => none
      | some union =>
          some (IntSetValue.enumeration (ut ++ union)).sortElems

/-- The range checks of an element constraint: the index must be
    between 1 and the array length.  A literal index is decided now, so
    an out-of-range literal becomes the always-false row. -/
def shapeRangeChecks (i : BasicExpr) (n : Nat) : List ConstraintItem :=
  match i with
  | .lit (.int k) =>
      if 1 ≤ k ∧ k ≤ (n : Int) then [] else [falseConstraint]
  | _ =>
      [shapeConstraint "int_le" [shapeE (shapeInt 1), shapeE i],
       shapeConstraint "int_le" [shapeE i, shapeE (shapeInt (n : Int))]]

/-- Membership terms for one value in every element set expression. -/
def arrayElemBits (taken : List String) (m : Model) :
    List BasicExpr → ShapeState → Int → Option (List String × ShapeState)
  | [], st, _ => some ([], st)
  | e :: rest, st, v =>
      match memberTerm taken m st (.basic e) v with
      | none => none
      | some (b, st1) =>
          match arrayElemBits taken m rest st1 v with
          | none => none
          | some (bs, st2) => some (b :: bs, st2)

/-- One Boolean element row: `array_var_bool_element(i, bits, tv)`. -/
def arrayElemRow (i : BasicExpr) (bits : List String) (tv : String) :
    ConstraintItem :=
  shapeConstraint "array_var_bool_element"
    [shapeE i, .array (bits.map shapeName), shapeE (shapeName tv)]

/-- The per-value rows of a set-array element constraint: one
    `array_var_bool_element` over the membership bits for every value of
    the union of universes.  The allocated `(value, bits, target)` triples
    are returned for the correctness proof. -/
def arrayElemRows (taken : List String) (m : Model) (i : BasicExpr)
    (es : List BasicExpr) (T : String) :
    ShapeState → List Int →
      Option (List (Int × List String × String) × ShapeState)
  | st, [] => some ([], st)
  | st, v :: vs =>
      match arrayElemBits taken m es st v with
      | none => none
      | some (bits, st1) =>
          match memberTerm taken m st1
              (.basic (.ident (Ident.mk T))) v with
          | none => none
          | some (tv, st2) =>
              match arrayElemRows taken m i es T st2 vs with
              | none => none
              | some (rows, st3) => some ((v, bits, tv) :: rows, st3)

/-- The rows emitted for the allocated per-value triples. -/
def arrayElemRowList (i : BasicExpr) :
    List (Int × List String × String) → List ConstraintItem
  | [] => []
  | r :: rs => arrayElemRow i r.2.1 r.2.2 :: arrayElemRowList i rs

/-- Rewrite `array_var_set_element(i, [S...], T)` for an explicit set
    array and a declared finite target set: one Boolean element row per
    value in the union of the element universes and the target universe.
    The emitted range checks make an out-of-range index false even when
    that union (and hence the row set) is empty. -/
def rewriteArrayElem (taken : List String) (m : Model) (st : ShapeState)
    (i : BasicExpr) (es : List BasicExpr) (T : String) :
    Option (ShapeState × List ConstraintItem) :=
  match arrayElemValues m es T with
  | none => none
  | some vals =>
      match arrayElemRows taken m i es T st vals with
      | none => none
      | some (rows, st') =>
          some (st', arrayElemRowList i rows ++ shapeRangeChecks i es.length)

/-- Rewrite one constraint.  Recognized finite set shapes are replaced by
    their scalar encoding; other constraints are kept verbatim. -/
def shapeRewriteConstraint (taken : List String) (m : Model) (st : ShapeState)
    (c : ConstraintItem) : Option (ShapeState × List ConstraintItem) :=
  match c.name.name, c.args with
  | "set_in_reif", [.basic xarg, .basic sarg, .basic rarg] =>
      match sarg with
      | .ident S =>
          match modelSetUniverse? m S.name with
          | none => some (st, [c])
          | some _ =>
              match xarg with
              | .ident x =>
                  match modelIntValues? m x.name with
                  | some vals => rewriteVarMember taken m st x.name S.name vals rarg
                  | none => none
              | .lit (.int _) => some (st, [c])
              | _ => none
      | .lit (.set _) => some (st, [c])
      | _ => none
  | "set_in", [.basic xarg, .basic sarg] =>
      match sarg with
      | .ident S =>
          match modelSetUniverse? m S.name with
          | none => some (st, [c])
          | some _ =>
              match xarg with
              | .ident x =>
                  match modelIntValues? m x.name with
                  | some vals =>
                      rewriteVarMember taken m st x.name S.name vals (shapeBool true)
                  | none => none
              | .lit (.int _) => some (st, [c])
              | _ => none
      | .lit (.set _) => some (st, [c])
      | _ => none
  | "set_card", [.basic sarg, .basic karg] =>
      match sarg with
      | .ident S =>
          match modelSetUniverse? m S.name with
          | none => some (st, [c])
          | some _ => rewriteCard taken m st S.name karg
      | .lit (.set _) => some (st, [c])
      | _ => none
  | "set_union", [sa, sb, sc] =>
      match setArgValues? m sa, setArgValues? m sb, setArgValues? m sc with
      | some ua, some ub, some uc => rewriteUnion taken m st sa sb sc ua ub uc
      | _, _, _ => some (st, [c])
  | "array_var_set_element", [.basic iarg, .array es, .basic targ] =>
      match targ with
      | .ident T =>
          match iarg with
          | .lit (.int _) =>
              match arrayElemValues m es T.name with
              | none => some (st, [c])
              | some _ => rewriteArrayElem taken m st iarg es T.name
          | .ident x =>
              match modelIntValues? m x.name with
              | some _ =>
                  match arrayElemValues m es T.name with
                  | none => some (st, [c])
                  | some _ => rewriteArrayElem taken m st iarg es T.name
              | none => some (st, [c])
          | _ => some (st, [c])
      | _ => some (st, [c])
  | "set_intersect", [sa, sb, sc] =>
      match setArgValues? m sa, setArgValues? m sb, setArgValues? m sc with
      | some ua, some ub, some uc => rewriteIntersect taken m st sa sb sc ua ub uc
      | _, _, _ => some (st, [c])
  | _, _ => some (st, [c])

/-- The shape pre-pass over a constraint list. -/
def shapeExpandConstraints (taken : List String) (m : Model) :
    List ConstraintItem → ShapeState → Option ShapeState
  | [], st => some st
  | c :: cs, st =>
      match shapeRewriteConstraint taken m st c with
      | none => none
      | some (st1, cs') => shapeExpandConstraints taken m cs (st1.emitList cs')

/-- **The set-shape pre-pass**, avoiding the model's own declared names. -/
def shapeExpandModelWith (taken : List String) (m : Model) : Option ShapeExpansion := do
  let st ← shapeExpandConstraints taken m m.constraints
    { next := 0, aux := [], decls := [], cons := [], maxLen := maxStrLength taken }
  some { model := { m with
           variables := st.decls.reverse ++ m.variables,
           constraints := st.cons.reverse },
         aux := st.aux.reverse }

/-- The shape pre-pass avoiding the model's own names. -/
def shapeExpandModel (m : Model) : Option ShapeExpansion :=
  shapeExpandModelWith (setTaken m) m

end LeanFzn.Compiler
