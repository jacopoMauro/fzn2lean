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
import Std.Data.HashMap.Lemmas

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
  deriving Repr, DecidableEq

/-- Comparison by structural equality.  The cache relies on this `BEq`
    being lawful so a lookup hit returns the canonical auxiliary. -/
instance : BEq ShapeKind := ⟨fun a b => decide (a = b)⟩

instance : ReflBEq ShapeKind where
  rfl := by intro a; simp

instance : LawfulBEq ShapeKind where
  eq_of_beq := by intro a b h; simpa using h

/- The cache is keyed by `ShapeKind`; the hash only needs to agree with
    the lawful `BEq`, which `LawfulHashable` derives from `LawfulBEq`. -/
deriving instance Hashable for ShapeKind

/-- The declared type dictated by a shape kind.  `bool2int` aliases are
    the only `0..1` integer auxiliaries; every other shape is Boolean. -/
def ShapeKind.ty : ShapeKind → BasicVarType
  | .bit _ => .intRange 0 1
  | _ => .par .bool

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
  /-- Canonical name for every shape kind already emitted.  A hit returns
      the existing auxiliary instead of allocating a duplicate. -/
  cache : Std.HashMap ShapeKind String
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

/-- Add a declaration and advance the auxiliary counter. -/
def ShapeState.freshDecl (taken : List String) (st : ShapeState)
    (ty : BasicVarType) : String × ShapeState :=
  let n := shapeAuxName st.maxLen st.next
  (n, { st with
        next := st.next + 1
        decls := .basic ty (Ident.mk n) [] none :: st.decls })

/-- Allocate a fresh auxiliary for `kind`, unconditionally.  The cache
    bookkeeping is separate so the proofs can reason about allocation and
    reuse with one case split. -/
def ShapeState.allocAux (taken : List String) (st : ShapeState)
    (kind : ShapeKind) : String × ShapeState :=
  let (n, st') := st.freshDecl taken kind.ty
  let a : ShapeAux := { name := n, ty := kind.ty, kind := kind }
  (n, { st' with
        aux := a :: st'.aux
        cons := a.definition :: st'.cons
        cache := st'.cache.insert kind n })

/-- Allocate an auxiliary for `kind`, or return the canonical auxiliary
    already recorded for that kind.  The type is fixed by the kind, so a
    cache hit is always type-correct. -/
def ShapeState.freshAux (taken : List String) (st : ShapeState)
    (kind : ShapeKind) : String × ShapeState :=
  match st.cache.get? kind with
  | some n => (n, st)
  | none => st.allocAux taken kind

/-- The initial shape state. -/
def ShapeState.initial (taken : List String) : ShapeState :=
  { next := 0, aux := [], decls := [], cons := [], maxLen := maxStrLength taken,
    cache := {} }

/-- Allocate a fresh Boolean auxiliary, emitting its defining constraint
    (or reuse the canonical one for the same kind). -/
abbrev ShapeState.freshBool (taken : List String) (st : ShapeState)
    (kind : ShapeKind) : String × ShapeState :=
  st.freshAux taken kind

/-- Allocate a fresh `0..1` integer auxiliary, emitting its defining
    constraint (or reuse the canonical one for the same kind). -/
abbrev ShapeState.freshInt01 (taken : List String) (st : ShapeState)
    (kind : ShapeKind) : String × ShapeState :=
  st.freshAux taken kind

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
  let st ← shapeExpandConstraints taken m m.constraints (ShapeState.initial taken)
  some { model := { m with
           variables := st.decls.reverse ++ m.variables,
           constraints := st.cons.reverse },
         aux := st.aux.reverse }

/-! ## Indexed twin of the pass

The specification above finds a name's declared type with
`modelSetUniverse?`/`modelIntValues?`, a linear scan of `m.variables`, once
per constraint and once per universe value.  On large set models (gt-sort:
70k declarations, 87k constraints) that scan dominates the whole compile.
The twin below is the same pass with both lookups abstracted into a
`ShapeLookup`; `ShapeLookup.ofModel` answers them from a hash map built
once.  `shapeExpandModelWith_eq_fast` proves the twin equal to the
specification, and `@[csimp]` installs it as the compiled code, so every
proof keeps reasoning about the scanning definition. -/

/-- The two declaration lookups the pass performs. -/
structure ShapeLookup where
  setU : String → Option (List Int)
  intV : String → Option (List Int)

/-- The finite integer values of a declared type (the body of
    `modelIntValues?`). -/
def tyIntValues? : BasicVarType → Option (List Int)
  | .intRange lo hi => some (setElems (.interval lo hi))
  | .intSet xs => some ((IntSetValue.enumeration xs).sortElems)
  | _ => none

/-- Declared type of every scalar name; the first declaration wins. -/
def declTypeIndex (ds : List VarDeclItem) : Std.HashMap String BasicVarType :=
  ds.foldr (fun d acc =>
    match d with
    | .basic ty x _ _ => acc.insert x.name ty
    | .array _ _ _ _ => acc) {}

/-- The scanning lookups of the specification. -/
def ShapeLookup.spec (m : Model) : ShapeLookup :=
  ⟨modelSetUniverse? m, modelIntValues? m⟩

/-- The hash-map lookups used by the compiled pass. -/
def ShapeLookup.ofModel (m : Model) : ShapeLookup :=
  let idx := declTypeIndex m.variables
  ⟨fun n => idx[n]?.bind setUniverse?, fun n => idx[n]?.bind tyIntValues?⟩

def memberTermL (L : ShapeLookup) (taken : List String) (st : ShapeState)
    (s : Expr) (v : Int) : Option (String × ShapeState) :=
  match s with
  | .basic (.ident S) =>
      match L.setU S.name with
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

def setArgValuesL (L : ShapeLookup) : Expr → Option (List Int)
  | .basic (.ident s) => L.setU s.name
  | .basic (.lit (.set l)) =>
      match l with
      | .intSet xs => some ((IntSetValue.enumeration xs).sortElems)
      | .intRange lo hi => some (setElems (.interval lo hi))
  | _ => none

def varMemberTermsL (L : ShapeLookup) (taken : List String) (x s : String) :
    ShapeState → List Int → Option (List String × ShapeState)
  | st, [] => some ([], st)
  | st, v :: vs =>
      match st.freshBool taken (.eq x v) with
      | (e, st1) =>
        match memberTermL L taken st1 (.basic (.ident (Ident.mk s))) v with
        | none => none
        | some (a, st2) =>
          match st2.freshBool taken (.and e a) with
          | (t, st3) =>
            match varMemberTermsL L taken x s st3 vs with
            | none => none
            | some (ts, st4) => some (t :: ts, st4)

def rewriteVarMemberL (L : ShapeLookup) (taken : List String) (st : ShapeState)
    (x s : String) (vals : List Int) (r : BasicExpr) :
    Option (ShapeState × List ConstraintItem) :=
  match varMemberTermsL L taken x s st vals with
  | none => none
  | some (terms, st1) =>
      match resultTarget taken st1 r with
      | none => none
      | some (target, st2) => some (linkOr st2 terms target, [])

def cardBitsL (L : ShapeLookup) (taken : List String) (s : String) :
    ShapeState → List Int → Option (List String × ShapeState)
  | st, [] => some ([], st)
  | st, v :: vs =>
      match memberTermL L taken st (.basic (.ident (Ident.mk s))) v with
      | none => none
      | some (a, st1) =>
        match st1.freshInt01 taken (.bit a) with
        | (c, st2) =>
          match cardBitsL L taken s st2 vs with
          | none => none
          | some (cs, st3) => some (c :: cs, st3)

def rewriteCardL (L : ShapeLookup) (taken : List String) (st : ShapeState)
    (s : String) (k : BasicExpr) : Option (ShapeState × List ConstraintItem) :=
  let us := (L.setU s).getD []
  if us.isEmpty then
    match k with
    | .ident kn =>
        some (st.emit (shapeConstraint "int_eq" [shapeE (shapeName kn.name), shapeE (shapeInt 0)]), [])
    | .lit (.int n) =>
        if n = 0 then some (st, []) else some (st.emit falseConstraint, [])
    | _ => none
  else
    match cardBitsL L taken s st us with
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

def unionRowsL (L : ShapeLookup) (taken : List String) (a b c : Expr) :
    ShapeState → List Int → Option ShapeState
  | st, [] => some st
  | st, v :: vs =>
      match memberTermL L taken st a v with
      | none => none
      | some (av, st1) =>
        match memberTermL L taken st1 b v with
        | none => none
        | some (bv, st2) =>
          match memberTermL L taken st2 c v with
          | none => none
          | some (cv, st3) =>
            let st4 := st3.emit
              (shapeConstraint "bool_or"
                [shapeE (shapeName av), shapeE (shapeName bv), shapeE (shapeName cv)])
            unionRowsL L taken a b c st4 vs

def intersectRowsL (L : ShapeLookup) (taken : List String) (a b c : Expr) :
    ShapeState → List Int → Option ShapeState
  | st, [] => some st
  | st, v :: vs =>
      match memberTermL L taken st a v with
      | none => none
      | some (av, st1) =>
        match memberTermL L taken st1 b v with
        | none => none
        | some (bv, st2) =>
          match memberTermL L taken st2 c v with
          | none => none
          | some (cv, st3) =>
            let st4 := st3.emit
              (shapeConstraint "bool_and"
                [shapeE (shapeName av), shapeE (shapeName bv), shapeE (shapeName cv)])
            intersectRowsL L taken a b c st4 vs

def arrayElemUnionL (L : ShapeLookup) : List BasicExpr → Option (List Int)
  | [] => some []
  | e :: rest =>
      match setArgValuesL L (.basic e) with
      | none => none
      | some us =>
          match arrayElemUnionL L rest with
          | none => none
          | some union => some (us ++ union)

def arrayElemValuesL (L : ShapeLookup) (es : List BasicExpr) (T : String) :
    Option (List Int) :=
  match L.setU T with
  | none => none
  | some ut =>
      match arrayElemUnionL L es with
      | none => none
      | some union =>
          some (IntSetValue.enumeration (ut ++ union)).sortElems

def arrayElemBitsL (L : ShapeLookup) (taken : List String) :
    List BasicExpr → ShapeState → Int → Option (List String × ShapeState)
  | [], st, _ => some ([], st)
  | e :: rest, st, v =>
      match memberTermL L taken st (.basic e) v with
      | none => none
      | some (b, st1) =>
          match arrayElemBitsL L taken rest st1 v with
          | none => none
          | some (bs, st2) => some (b :: bs, st2)

def arrayElemRowsL (L : ShapeLookup) (taken : List String) (i : BasicExpr)
    (es : List BasicExpr) (T : String) :
    ShapeState → List Int →
      Option (List (Int × List String × String) × ShapeState)
  | st, [] => some ([], st)
  | st, v :: vs =>
      match arrayElemBitsL L taken es st v with
      | none => none
      | some (bits, st1) =>
          match memberTermL L taken st1
              (.basic (.ident (Ident.mk T))) v with
          | none => none
          | some (tv, st2) =>
              match arrayElemRowsL L taken i es T st2 vs with
              | none => none
              | some (rows, st3) => some ((v, bits, tv) :: rows, st3)

def rewriteArrayElemL (L : ShapeLookup) (taken : List String) (st : ShapeState)
    (i : BasicExpr) (es : List BasicExpr) (T : String) :
    Option (ShapeState × List ConstraintItem) :=
  match arrayElemValuesL L es T with
  | none => none
  | some vals =>
      match arrayElemRowsL L taken i es T st vals with
      | none => none
      | some (rows, st') =>
          some (st', arrayElemRowList i rows ++ shapeRangeChecks i es.length)

def shapeRewriteConstraintL (L : ShapeLookup) (taken : List String) (st : ShapeState)
    (c : ConstraintItem) : Option (ShapeState × List ConstraintItem) :=
  match c.name.name, c.args with
  | "set_in_reif", [.basic xarg, .basic sarg, .basic rarg] =>
      match sarg with
      | .ident S =>
          match L.setU S.name with
          | none => some (st, [c])
          | some _ =>
              match xarg with
              | .ident x =>
                  match L.intV x.name with
                  | some vals => rewriteVarMemberL L taken st x.name S.name vals rarg
                  | none => none
              | .lit (.int _) => some (st, [c])
              | _ => none
      | .lit (.set _) => some (st, [c])
      | _ => none
  | "set_in", [.basic xarg, .basic sarg] =>
      match sarg with
      | .ident S =>
          match L.setU S.name with
          | none => some (st, [c])
          | some _ =>
              match xarg with
              | .ident x =>
                  match L.intV x.name with
                  | some vals =>
                      rewriteVarMemberL L taken st x.name S.name vals (shapeBool true)
                  | none => none
              | .lit (.int _) => some (st, [c])
              | _ => none
      | .lit (.set _) => some (st, [c])
      | _ => none
  | "set_card", [.basic sarg, .basic karg] =>
      match sarg with
      | .ident S =>
          match L.setU S.name with
          | none => some (st, [c])
          | some _ => rewriteCardL L taken st S.name karg
      | .lit (.set _) => some (st, [c])
      | _ => none
  | "set_union", [sa, sb, sc] =>
      match setArgValuesL L sa, setArgValuesL L sb, setArgValuesL L sc with
      | some ua, some ub, some uc =>
          match unionRowsL L taken sa sb sc st (ua ++ ub ++ uc) with
          | none => none
          | some st' => some (st', [])
      | _, _, _ => some (st, [c])
  | "array_var_set_element", [.basic iarg, .array es, .basic targ] =>
      match targ with
      | .ident T =>
          match iarg with
          | .lit (.int _) =>
              match arrayElemValuesL L es T.name with
              | none => some (st, [c])
              | some _ => rewriteArrayElemL L taken st iarg es T.name
          | .ident x =>
              match L.intV x.name with
              | some _ =>
                  match arrayElemValuesL L es T.name with
                  | none => some (st, [c])
                  | some _ => rewriteArrayElemL L taken st iarg es T.name
              | none => some (st, [c])
          | _ => some (st, [c])
      | _ => some (st, [c])
  | "set_intersect", [sa, sb, sc] =>
      match setArgValuesL L sa, setArgValuesL L sb, setArgValuesL L sc with
      | some ua, some ub, some uc =>
          match intersectRowsL L taken sa sb sc st
              ((IntSetValue.enumeration (ua ++ ub ++ uc)).sortElems) with
          | none => none
          | some st' => some (st', [])
      | _, _, _ => some (st, [c])
  | _, _ => some (st, [c])

def shapeExpandConstraintsL (L : ShapeLookup) (taken : List String) :
    List ConstraintItem → ShapeState → Option ShapeState
  | [], st => some st
  | c :: cs, st =>
      match shapeRewriteConstraintL L taken st c with
      | none => none
      | some (st1, cs') => shapeExpandConstraintsL L taken cs (st1.emitList cs')

/-- The compiled form of `shapeExpandModelWith`: the same pass answering
    declaration lookups from `ShapeLookup.ofModel`. -/
def shapeExpandModelWithFast (taken : List String) (m : Model) : Option ShapeExpansion := do
  let st ← shapeExpandConstraintsL (ShapeLookup.ofModel m) taken m.constraints
    (ShapeState.initial taken)
  some { model := { m with
           variables := st.decls.reverse ++ m.variables,
           constraints := st.cons.reverse },
         aux := st.aux.reverse }

/-! ### The twin computes the specification -/

theorem declTypeIndex_setU (ds : List VarDeclItem) (n : String) :
    (declTypeIndex ds)[n]?.bind setUniverse? = modelSetUniverse?.go n ds := by
  induction ds with
  | nil => simp [declTypeIndex, modelSetUniverse?.go]
  | cons d ds ih =>
      cases d with
      | basic ty x _ _ =>
          simp only [declTypeIndex, List.foldr_cons, modelSetUniverse?.go] at ih ⊢
          rw [Std.HashMap.getElem?_insert]
          by_cases h : x.name = n
          · simp [h]
          · simp [h, ih]
      | array _ _ _ _ =>
          simpa [declTypeIndex, modelSetUniverse?.go] using ih

theorem declTypeIndex_intV (ds : List VarDeclItem) (n : String) :
    (declTypeIndex ds)[n]?.bind tyIntValues? = modelIntValues?.go n ds := by
  induction ds with
  | nil => simp [declTypeIndex, modelIntValues?.go]
  | cons d ds ih =>
      cases d with
      | basic ty x _ _ =>
          simp only [declTypeIndex, List.foldr_cons, modelIntValues?.go] at ih ⊢
          rw [Std.HashMap.getElem?_insert]
          by_cases h : x.name = n
          · cases ty <;> simp [h, tyIntValues?]
          · simp [h, ih]
      | array _ _ _ _ =>
          simpa [declTypeIndex, modelIntValues?.go] using ih

theorem ShapeLookup.ofModel_eq_spec (m : Model) :
    ShapeLookup.ofModel m = ShapeLookup.spec m := by
  simp only [ShapeLookup.ofModel, ShapeLookup.spec, ShapeLookup.mk.injEq]
  constructor
  · funext n; exact (declTypeIndex_setU m.variables n).trans rfl
  · funext n; exact (declTypeIndex_intV m.variables n).trans rfl

section SpecEq
variable (m : Model) (taken : List String)

theorem memberTermL_spec (st : ShapeState) (s : Expr) (v : Int) :
    memberTermL (ShapeLookup.spec m) taken st s v = memberTerm taken m st s v := rfl

theorem setArgValuesL_spec (e : Expr) :
    setArgValuesL (ShapeLookup.spec m) e = setArgValues? m e := rfl

theorem varMemberTermsL_spec (x s : String) :
    ∀ st vals, varMemberTermsL (ShapeLookup.spec m) taken x s st vals =
      varMemberTerms taken m x s st vals
  | _, [] => rfl
  | st, v :: vs => by
      simp only [varMemberTermsL, varMemberTerms, memberTermL_spec,
        varMemberTermsL_spec x s _ vs]

theorem cardBitsL_spec (s : String) :
    ∀ st vals, cardBitsL (ShapeLookup.spec m) taken s st vals = cardBits taken m s st vals
  | _, [] => rfl
  | st, v :: vs => by
      simp only [cardBitsL, cardBits, memberTermL_spec, cardBitsL_spec s _ vs]

theorem unionRowsL_spec (a b c : Expr) :
    ∀ st vals, unionRowsL (ShapeLookup.spec m) taken a b c st vals =
      unionRows taken m a b c st vals
  | _, [] => rfl
  | st, v :: vs => by
      simp only [unionRowsL, unionRows, memberTermL_spec, unionRowsL_spec a b c _ vs]

theorem intersectRowsL_spec (a b c : Expr) :
    ∀ st vals, intersectRowsL (ShapeLookup.spec m) taken a b c st vals =
      intersectRows taken m a b c st vals
  | _, [] => rfl
  | st, v :: vs => by
      simp only [intersectRowsL, intersectRows, memberTermL_spec,
        intersectRowsL_spec a b c _ vs]

theorem arrayElemUnionL_spec :
    ∀ es, arrayElemUnionL (ShapeLookup.spec m) es = arrayElemUnion m es
  | [] => rfl
  | e :: es => by
      simp only [arrayElemUnionL, arrayElemUnion, setArgValuesL_spec, arrayElemUnionL_spec es]

theorem arrayElemValuesL_spec (es : List BasicExpr) (T : String) :
    arrayElemValuesL (ShapeLookup.spec m) es T = arrayElemValues m es T := by
  simp only [arrayElemValuesL, arrayElemValues, arrayElemUnionL_spec]; rfl

theorem arrayElemBitsL_spec :
    ∀ es st v, arrayElemBitsL (ShapeLookup.spec m) taken es st v =
      arrayElemBits taken m es st v
  | [], _, _ => rfl
  | e :: es, st, v => by
      simp only [arrayElemBitsL, arrayElemBits, memberTermL_spec, arrayElemBitsL_spec es]

theorem arrayElemRowsL_spec (i : BasicExpr) (es : List BasicExpr) (T : String) :
    ∀ st vals, arrayElemRowsL (ShapeLookup.spec m) taken i es T st vals =
      arrayElemRows taken m i es T st vals
  | _, [] => rfl
  | st, v :: vs => by
      simp only [arrayElemRowsL, arrayElemRows, arrayElemBitsL_spec, memberTermL_spec,
        arrayElemRowsL_spec i es T _ vs]

theorem shapeRewriteConstraintL_spec (st : ShapeState) (c : ConstraintItem) :
    shapeRewriteConstraintL (ShapeLookup.spec m) taken st c =
      shapeRewriteConstraint taken m st c := by
  unfold shapeRewriteConstraintL shapeRewriteConstraint
  simp only [rewriteVarMemberL, rewriteVarMember, varMemberTermsL_spec, rewriteCardL,
    rewriteCard, cardBitsL_spec, setArgValuesL_spec, unionRowsL_spec, rewriteUnion,
    intersectRowsL_spec, rewriteIntersect, arrayElemValuesL_spec, rewriteArrayElemL,
    rewriteArrayElem, arrayElemRowsL_spec]
  rfl

theorem shapeExpandConstraintsL_spec :
    ∀ cs st, shapeExpandConstraintsL (ShapeLookup.spec m) taken cs st =
      shapeExpandConstraints taken m cs st
  | [], _ => rfl
  | c :: cs, st => by
      simp only [shapeExpandConstraintsL, shapeExpandConstraints,
        shapeRewriteConstraintL_spec]
      split <;> simp only [shapeExpandConstraintsL_spec cs]

end SpecEq

/-- The indexed pass is the specification; the compiler runs the former. -/
@[csimp] theorem shapeExpandModelWith_eq_fast :
    @shapeExpandModelWith = @shapeExpandModelWithFast := by
  funext taken m
  simp only [shapeExpandModelWith, shapeExpandModelWithFast, ShapeLookup.ofModel_eq_spec,
    shapeExpandConstraintsL_spec]

/-- The shape pre-pass avoiding the model's own names.  Defined after
    `shapeExpandModelWith_eq_fast` so its compiled code already calls the
    indexed pass (`@[csimp]` only rewrites code compiled after it). -/
def shapeExpandModel (m : Model) : Option ShapeExpansion :=
  shapeExpandModelWith (setTaken m) m

end LeanFzn.Compiler
