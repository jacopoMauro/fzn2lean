import LeanFzn.Syntax.AST



/-!
# Static and denotational semantics for non-float FlatZinc

Dynamic semantics is parameterised by an interpretation of predicate names,
since FlatZinc delegates standard and solver-specific predicates to the target
LeanFzn.Solver. Annotations are intentionally semantically inert suggestions.
-/

namespace LeanFzn.Semantics

open LeanFzn

inductive BaseType where
  | bool | int | setOfInt
  deriving Repr, DecidableEq, Inhabited

inductive FznType where
  | base (t : BaseType)
  | array (length : Nat) (elem : BaseType)
  deriving Repr, DecidableEq, Inhabited

inductive IntSetValue where
  | enumeration (values : List Int)
  | interval (lo hi : Int)
  deriving Repr, DecidableEq, Inhabited

inductive Value where
  | bool (value : Bool)
  | int (value : Int)
  | setOfInt (value : IntSetValue)
  | array (value : List Value)
  deriving Repr, Inhabited, BEq

/-! ## Argument shape

Decodability of a global constraint depends only on the constructor tags and
array lengths of the evaluated arguments, plus the concrete values at the
`par` positions (which the model's parameters fix).  The relations below
record exactly that information. -/

/-- Pointwise shape agreement of two `Value` lists, relative to a value
relation `R`.  This is a standalone inductive rather than a
`Forall2 SameShape`: `Value.SameShape` nests through it, whereas a direct
`Forall2 SameShape` argument is rejected by the strict-positivity checker and
a mutual pair of inductives blocks the `induction` tactic. -/
inductive ListSameShape (R : Value → Value → Prop) : List Value → List Value → Prop
  | nil : ListSameShape R [] []
  | cons {x y : Value} {xs ys : List Value} :
      R x y → ListSameShape R xs ys → ListSameShape R (x :: xs) (y :: ys)

namespace Value

/-- Constructor shape of two values: equal constructor tags, and for arrays
pointwise shape agreement.  This preserves exactly what the decoders inspect:
constructor tags and array lengths, recursively. -/
inductive SameShape : Value → Value → Prop
  | bool (b b' : Bool) : SameShape (.bool b) (.bool b')
  | int (i i' : Int) : SameShape (.int i) (.int i')
  | setOfInt (s s' : IntSetValue) : SameShape (.setOfInt s) (.setOfInt s')
  | array {xs ys : List Value} :
      ListSameShape SameShape xs ys → SameShape (.array xs) (.array ys)

/-- Pointwise `SameShape` on two value lists. -/
abbrev SameShapeList : List Value → List Value → Prop :=
  ListSameShape SameShape

/-- Agreement at a predicate parameter: definitional equality at a `par`
position, constructor shape at a variable position. -/
def Agree (par : Bool) (a b : Value) : Prop :=
  match par with
  | true => a = b
  | false => a.SameShape b

mutual
  /-- `SameShape` is reflexive. -/
  theorem SameShape.refl : ∀ v : Value, SameShape v v
    | .bool _ => .bool _ _
    | .int _ => .int _ _
    | .setOfInt _ => .setOfInt _ _
    | .array xs => .array (SameShapeList.refl xs)

  /-- `SameShapeList` is reflexive. -/
  theorem SameShapeList.refl : ∀ xs : List Value, SameShapeList xs xs
    | [] => .nil
    | x :: xs => .cons (SameShape.refl x) (SameShapeList.refl xs)
end

end Value

namespace ListSameShape

/-- Shape agreement preserves list length. -/
theorem length_eq {R : Value → Value → Prop} {xs ys : List Value}
    (h : ListSameShape R xs ys) : xs.length = ys.length := by
  induction h with
  | nil => rfl
  | cons _ _ ih => simp [ih]

end ListSameShape

def IntSetValue.Contains (s : IntSetValue) (x : Int) : Prop :=
  match s with
  | .enumeration xs => x ∈ xs
  | .interval lo hi => lo ≤ x ∧ x ≤ hi

abbrev Store := Ident → Option Value

def _root_.LeanFzn.SetLiteral.denote : SetLiteral → IntSetValue
  | .intSet xs => .enumeration xs
  | .intRange lo hi => .interval lo hi

def _root_.LeanFzn.BasicLiteral.denote : BasicLiteral → Value
  | .bool b => .bool b
  | .int i => .int i
  | .set s => .setOfInt s.denote

def _root_.LeanFzn.BasicLiteral.type : BasicLiteral → BaseType
  | .bool _ => .bool
  | .int _ => .int
  | .set _ => .setOfInt

def _root_.LeanFzn.BasicParType.base : BasicParType → BaseType
  | .bool => .bool
  | .int => .int
  | .setOfInt => .setOfInt

/-- The cardinality of `1..hi` (zero when `hi < 1`). -/
def _root_.LeanFzn.IndexSet.length (i : IndexSet) : Nat := i.hi.toNat

def _root_.LeanFzn.BasicExpr.eval (store : Store) : BasicExpr → Option Value
  | .lit l => some l.denote
  | .ident x => store x

def _root_.LeanFzn.Expr.eval (store : Store) : Expr → Option Value
  | .basic e => e.eval store
  | .array es => (es.mapM (BasicExpr.eval store)).map Value.array

def _root_.LeanFzn.BasicVarType.base : BasicVarType → BaseType
  | .par t => t.base
  | .intRange _ _ | .intSet _ => .int
  | .setOfIntRange _ _ | .setOfIntSet _ => .setOfInt

def _root_.LeanFzn.BasicVarType.contains : BasicVarType → Value → Prop
  | .par .bool, .bool _ => True
  | .par .int, .int _ => True
  | .par .setOfInt, .setOfInt _ => True
  | .intRange lo hi, .int x => lo ≤ x ∧ x ≤ hi
  | .intSet xs, .int x => x ∈ xs
  | .setOfIntRange lo hi, .setOfInt xs => ∀ x, xs.Contains x → lo ≤ x ∧ x ≤ hi
  | .setOfIntSet allowed, .setOfInt xs => ∀ x, xs.Contains x → x ∈ allowed
  | _, _ => False

/-- Meanings of built-in and solver-specific predicate symbols. -/
abbrev PredicateInterpretation := Ident → List Value → Prop

def _root_.LeanFzn.ConstraintItem.Holds (pred : PredicateInterpretation) (store : Store)
    (c : ConstraintItem) : Prop :=
  ∃ args, c.args.mapM (Expr.eval store) = some args ∧ pred c.name args

def _root_.LeanFzn.SolveItem.objective (store : Store) : SolveItem → Option Int
  | .satisfy _ => none
  | .minimize _ e | .maximize _ e =>
      match e.eval store with
      | some (.int i) => some i
      | _ => none

/-! ## Static well-formedness

The context-sensitive rules of the supported fragment, as resolved in
`specification/flatzinc_specification_assumptions.md` (R1-R12, A1-A5).
Static checking is parameterized by a predicate-signature environment
(R8, A3): model-declared predicates take precedence, and the external
environment supplies the standard and solver-specific predicates. -/

/-- Look up a name in an association list (first match wins). -/
def lookupIdent {β : Type} (x : Ident) : List (Ident × β) → Option β
  | [] => none
  | (y, v) :: rest => if x.name = y.name then some v else lookupIdent x rest

/-- Predicate signature environment (R8, A3): maps a predicate name to
    the *list* of its accepted parameter-type lists; `[]` if the
    predicate is not available.  The theorems quantify over this
    environment.

    The list has more than one element exactly for the predicates where
    upstream ships several same-named FlatZinc overloads, e.g.
    `fzn_reachable_int` (`N, E, from, to, root, ns, es`) and
    `fzn_reachable_enum` (`from, to, root, ns, es`).  A constraint is
    well formed when its argument list matches *some* entry. -/
abbrev SigEnv := Ident → List (List PredParamType)

/-- The first (`primary`) signature of a name, `none` when the name is
    unavailable.  Consumers that only need "the" signature — the
    compiler's exact-fragment proofs — go through this projection, so
    their shapes are unchanged by the move to several signatures. -/
def SigEnv.primary (sig : SigEnv) (x : Ident) : Option (List PredParamType) :=
  (sig x).head?

/-- A name whose signature environment is the singleton list `[p]`
    accepts `p` in the `List.mem` sense used by
    `WellFormed.constraintsChecked`.  This bridges the residual
    `… = [p]` form of the signature lemmas to the membership form. -/
theorem SigEnv.mem_of_eq_singleton {sig : SigEnv} {x : Ident}
    {p : List PredParamType} (h : sig x = [p]) : p ∈ sig x := by
  rw [h]
  exact List.mem_singleton.mpr rfl

/-- The converse direction: a name with the singleton signature list
    `[p]` accepts nothing else.  This replaces the old
    `Option.some.inj (hsig.symm.trans …)` steps of the `some`-valued
    signature environment. -/
theorem SigEnv.eq_of_mem_eq_singleton {sig : SigEnv} {x : Ident}
    {p q : List PredParamType} (hmem : p ∈ sig x) (h : sig x = [q]) :
    p = q := by
  rw [h] at hmem
  exact List.mem_singleton.mp hmem

/-- The static environment: for each declared name, its type and whether
    it is a decision variable (`true`) or a parameter (`false`). -/
abbrev StaticEnv := Ident → Option (FznType × Bool)

/-- The declared name of a parameter declaration. -/
def _root_.LeanFzn.ParDeclItem.name : ParDeclItem → Ident
  | .basic _ n _ | .array _ _ n _ => n

/-- The declared type of a parameter declaration. -/
def _root_.LeanFzn.ParDeclItem.type : ParDeclItem → FznType
  | .basic t _ _ => .base t.base
  | .array idx t _ _ => .array idx.length t.base

/-- The declared name of a variable declaration. -/
def _root_.LeanFzn.VarDeclItem.name : VarDeclItem → Ident
  | .basic _ n _ _ | .array _ n _ _ => n

/-- The declared type of a variable declaration. -/
def _root_.LeanFzn.VarDeclItem.type : VarDeclItem → FznType
  | .basic t _ _ _ => .base t.base
  | .array ty _ _ _ => .array ty.idx.length ty.elem.base

/-- The model's global static environment (R5): parameters and variables
    are resolved against the completed model, so forward references are
    permitted.  Parameters are par (`false`), variables var (`true`). -/
def _root_.LeanFzn.Model.staticEnv (m : Model) : StaticEnv :=
  fun x =>
    match lookupIdent x (m.parameters.map (fun d => (d.name, (d.type, false)))) with
    | some info => some info
    | none => lookupIdent x (m.variables.map (fun d => (d.name, (d.type, true))))

/-- The signatures declared by the model's predicate items.  A
    user-declared predicate contributes exactly one signature. -/
def _root_.LeanFzn.Model.declaredSigs (m : Model) : SigEnv :=
  fun x =>
    match lookupIdent x (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) with
    | some params => [params]
    | none => []

/-- Combined signature lookup (R8): model declarations first, then the
    external environment. -/
def _root_.LeanFzn.Model.sigEnv (m : Model) (ext : SigEnv) : SigEnv :=
  fun x =>
    match m.declaredSigs x with
    | [] => ext x
    | sigs => sigs

/-- The base type a predicate parameter expects. -/
def _root_.LeanFzn.BasicPredParamType.baseType : BasicPredParamType → BaseType
  | .par t => t.base
  | .var t => t.base
  | .intRange _ _ | .intSet _ => .int
  | .setOfIntRange _ _ | .setOfIntSet _ => .setOfInt

/-- Is the predicate parameter a fixed (par) parameter?  Par parameters
    do not accept variable arguments: par-to-var coercion is allowed,
    var-to-par is not (spec, "Parameter types"). -/
def _root_.LeanFzn.BasicPredParamType.isPar : BasicPredParamType → Bool
  | .par _ => true
  | _ => false

/-- Is the predicate parameter a `par` parameter?  Array parameters are
    classified by their element type. -/
def _root_.LeanFzn.PredParamType.isPar : PredParamType → Bool
  | .basic bt => bt.isPar
  | .array _ bt => bt.isPar

/-- Agreement of two evaluated argument lists with a predicate signature:
    at a `par` position the values are equal, at a variable position they
    only need the same constructor shape.  `False` when the lengths
    differ.  This is the information a decoder may rely on: par arguments
    are literals or parameter identifiers (fixed by `Model.parameters`),
    variable arguments only contribute their declared type. -/
def ArgsAgree : List PredParamType → List Value → List Value → Prop
  | [], [], [] => True
  | pt :: pts, a :: as, b :: bs =>
      Value.Agree pt.isPar a b ∧ ArgsAgree pts as bs
  | _, _, _ => False

/-- `Agree` at any par/var flag implies constructor-shape agreement. -/
theorem Value.sameShape_of_agree {par : Bool} {a b : Value}
    (h : Value.Agree par a b) : a.SameShape b := by
  cases par with
  | false => exact h
  | true =>
      have hab : a = b := h
      rw [hab]
      exact Value.SameShape.refl b

/-- Signature agreement implies pointwise constructor shape. -/
theorem ArgsAgree.sameShape {params : List PredParamType} {vs ws : List Value}
    (h : ArgsAgree params vs ws) : Value.SameShapeList vs ws := by
  induction vs generalizing params ws with
  | nil =>
      cases params with
      | nil =>
          cases ws with
          | nil => exact .nil
          | cons w ws => cases h
      | cons pt pts => cases h
  | cons v vs ih =>
      cases params with
      | nil => cases h
      | cons pt pts =>
          cases ws with
          | nil => cases h
          | cons w ws =>
              obtain ⟨h0, h1⟩ := h
              exact .cons (Value.sameShape_of_agree h0) (ih h1)

/-- When every parameter is `par`, agreement forces the argument lists to be
    equal. -/
theorem ArgsAgree.eq_of_all_par {params : List PredParamType} {vs ws : List Value}
    (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ params, pt.isPar = true) : vs = ws := by
  induction vs generalizing params ws with
  | nil =>
      cases params with
      | nil =>
          cases ws with
          | nil => rfl
          | cons w ws => cases h
      | cons pt pts => cases h
  | cons v vs ih =>
      cases params with
      | nil => cases h
      | cons pt pts =>
          cases ws with
          | nil => cases h
          | cons w ws =>
              obtain ⟨h0, h1⟩ := h
              have hp : pt.isPar = true := hpar pt (by simp)
              have hvw : v = w := by simpa [Value.Agree, hp] using h0
              rw [hvw]
              rw [ih h1 (fun q hq => hpar q (by simp [hq]))]

/-- With every parameter after the first one `par`, agreement of the
    argument lists forces their tails to be equal: only the (possibly
    variable) first argument may differ in value. -/
theorem ArgsAgree.drop_one_eq {params : List PredParamType} {vs ws : List Value}
    (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ params.drop 1, pt.isPar = true) :
    vs.drop 1 = ws.drop 1 := by
  cases vs with
  | nil =>
      cases ws with
      | nil => rfl
      | cons w ws =>
          cases params with
          | nil => cases h
          | cons pt pts => cases h
  | cons v vs =>
      cases ws with
      | nil =>
          cases params with
          | nil => cases h
          | cons pt pts => cases h
      | cons w ws =>
          cases params with
          | nil => cases h
          | cons pt pts =>
              obtain ⟨h0, h1⟩ := h
              have htail : vs = ws := ArgsAgree.eq_of_all_par h1 (by
                intro q hq
                exact hpar q (by simpa using hq))
              rw [htail]
              rfl

/-- With every parameter except the last one `par`, agreement of the
    argument lists decomposes them as a common prefix followed by one
    possibly different last value of the same shape. -/
theorem ArgsAgree.eq_init_lastShape {params : List PredParamType}
    {vs ws : List Value} (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ params.dropLast, pt.isPar = true)
    (hvs : vs ≠ []) (hws : ws ≠ []) :
    ∃ pre a b, vs = pre ++ [a] ∧ ws = pre ++ [b] ∧ a.SameShape b := by
  induction vs generalizing params ws with
  | nil => exact (hvs rfl).elim
  | cons v vs' ih =>
      cases params with
      | nil => cases h
      | cons pt pts =>
          cases ws with
          | nil => exact (hws rfl).elim
          | cons w ws' =>
              obtain ⟨hagree, htail⟩ := h
              cases vs' with
              | nil =>
                  cases ws' with
                  | nil =>
                      exact ⟨[], v, w, rfl, rfl,
                        Value.sameShape_of_agree hagree⟩
                  | cons _ _ => simp [ArgsAgree] at htail
              | cons v' vs'' =>
                  cases ws' with
                  | nil => simp [ArgsAgree] at htail
                  | cons w' ws'' =>
                      cases pts with
                      | nil => simp [ArgsAgree] at htail
                      | cons pt' pts' =>
                          have hp : pt.isPar = true := by
                            apply hpar pt
                            simp [List.dropLast]
                          have hvw : v = w := by
                            simpa [Value.Agree, hp] using hagree
                          subst hvw
                          obtain ⟨pre, a, b, hvs', hws', hshape⟩ :=
                            ih htail (fun q hq => by
                              apply hpar q
                              simp [List.dropLast, hq]) (by simp) (by simp)
                          exact ⟨v :: pre, a, b, by simp [hvs'],
                            by simp [hws'], hshape⟩

/-- The `drop 1` version of `ArgsAgree.eq_init_lastShape`: only the last
    argument of the tail may differ, and then only in value. -/
theorem ArgsAgree.drop_one_eq_init_lastShape
    {params : List PredParamType} {vs ws : List Value}
    (h : ArgsAgree params vs ws)
    (hpar : ∀ pt ∈ (params.drop 1).dropLast, pt.isPar = true)
    (hvs : vs.drop 1 ≠ []) (hws : ws.drop 1 ≠ []) :
    ∃ pre a b, vs.drop 1 = pre ++ [a] ∧ ws.drop 1 = pre ++ [b] ∧
      a.SameShape b := by
  rcases vs with _ | ⟨v, vs1⟩ <;> rcases ws with _ | ⟨w, ws1⟩
  · exact (hvs rfl).elim
  · cases params with
    | nil => simp [ArgsAgree] at h
    | cons _ _ => simp [ArgsAgree] at h
  · cases params with
    | nil => simp [ArgsAgree] at h
    | cons _ _ => simp [ArgsAgree] at h
  · cases params with
    | nil => simp [ArgsAgree] at h
    | cons pt pts =>
        have htail : ArgsAgree pts vs1 ws1 := h.2
        have hpar' : ∀ q ∈ pts.dropLast, q.isPar = true := by
          intro q hq
          apply hpar q
          simpa using hq
        exact ArgsAgree.eq_init_lastShape htail hpar'
          (by simpa using hvs) (by simpa using hws)

/-- Does a scalar argument of type `t` and par/var status `isVar` match
    the predicate parameter type `bt`? -/
def _root_.LeanFzn.BasicPredParamType.accepts (bt : BasicPredParamType) (t : BaseType)
    (isVar : Bool) : Prop :=
  bt.baseType = t ∧ (bt.isPar = true → isVar = false)

/-- Does a predicate array parameter with index set `idx` accept an
    array of length `n`?  `int` accepts any length; `1..hi` accepts
    exactly the index set's cardinality (R3). -/
def _root_.LeanFzn.PredIndexSet.acceptsLength (idx : PredIndexSet) (n : Nat) : Prop :=
  match idx with
  | .int => True
  | .range i => n = i.length

/-- Does the basic expression have exactly the base type `t`?  Used for
    variable initializers (R26) and objectives (R7).  References to
    undeclared names fail (R5/R12). -/
def _root_.LeanFzn.BasicExpr.hasBaseType (env : StaticEnv) (b : BasicExpr) (t : BaseType) : Prop :=
  match b with
  | .lit l => l.type = t
  | .ident x => match env x with
    | some (.base t', _) => t' = t
    | _ => False

/-- Does the basic expression check against the predicate parameter type
    `bt`?  Literals are par; identifiers carry their declared status.
    Par-to-var coercion is allowed, var-to-par is not. -/
def _root_.LeanFzn.BasicExpr.checkBase (env : StaticEnv) (b : BasicExpr)
    (bt : BasicPredParamType) : Prop :=
  match b with
  | .lit l => bt.accepts l.type false
  | .ident x => match env x with
    | some (.base t, isVar) => bt.accepts t isVar
    | _ => False

/-- Does the expression check against the predicate parameter type?
    A scalar argument cannot fill an array parameter and vice versa, but
    the *name* of an array variable or parameter can fill an array
    parameter (spec, "Values and expressions"). -/
def _root_.LeanFzn.Expr.checkArg (env : StaticEnv) (e : Expr) (pt : PredParamType) : Prop :=
  match pt with
  | .basic bt => match e with
    | .basic b => b.checkBase env bt
    | .array _ => False
  | .array idx bt => match e with
    | .basic (.ident x) =>
      match env x with
      | some (.array n t, isVar) => idx.acceptsLength n ∧ bt.accepts t isVar
      | _ => False
    | .basic (.lit _) => False
    | .array es => idx.acceptsLength es.length ∧ ∀ b ∈ es, b.checkBase env bt

/-- Pairwise relation between two lists; `False` when the lengths differ. -/
def Forall2 {α β : Type} (R : α → β → Prop) : List α → List β → Prop
  | [], [] => True
  | a :: as, b :: bs => R a b ∧ Forall2 R as bs
  | _, _ => False

/-! ## An executable static checker

The helpers below are used by `wellFormedB`, which, together with
`WellFormed`, lives in `LeanFzn.Semantics.Globals`: the decodability
conjunct of `WellFormed` refers to the global-constraint decoders, which
are downstream of this module. -/

/-- Boolean identifier membership, comparing names. -/
def memIdentB (x : Ident) : List Ident → Bool
  | [] => false
  | y :: ys => decide (x.name = y.name) || memIdentB x ys

/-- Boolean no-duplicates for identifier lists. -/
def nodupIdentB : List Ident → Bool
  | [] => true
  | x :: xs => (!memIdentB x xs) && nodupIdentB xs

/-- Names determine identifiers. -/
theorem _root_.LeanFzn.Ident.eq_of_name_eq {x y : Ident} (h : x.name = y.name) : x = y := by
  cases x
  cases y
  simpa using h

theorem memIdentB_iff {x : Ident} {l : List Ident} :
    memIdentB x l = true ↔ x ∈ l := by
  induction l with
  | nil => simp [memIdentB]
  | cons y ys ih =>
    simp only [memIdentB, Bool.or_eq_true, decide_eq_true_iff, List.mem_cons, ih]
    constructor
    · rintro (h | h)
      · exact Or.inl (Ident.eq_of_name_eq h)
      · exact Or.inr h
    · rintro (h | h)
      · exact Or.inl (congrArg Ident.name h)
      · exact Or.inr h

theorem nodupIdentB_iff {l : List Ident} : nodupIdentB l = true ↔ l.Nodup := by
  induction l with
  | nil => simp [nodupIdentB]
  | cons x xs ih =>
    have hmem : memIdentB x xs = false ↔ ¬ (x ∈ xs) := by
      constructor
      · intro hf hin
        rw [memIdentB_iff.mpr hin] at hf
        simp at hf
      · intro hin
        cases hb : memIdentB x xs with
        | false => rfl
        | true => exact absurd (memIdentB_iff.mp hb) hin
    simp only [nodupIdentB, Bool.and_eq_true, Bool.not_eq_true', List.nodup_cons,
      ih, hmem]

/-- Boolean counterpart of `PredIndexSet.acceptsLength`. -/
def acceptsLengthB (idx : PredIndexSet) (n : Nat) : Bool :=
  match idx with
  | .int => true
  | .range i => decide (n = i.length)

theorem acceptsLengthB_iff {idx : PredIndexSet} {n : Nat} :
    acceptsLengthB idx n = true ↔ idx.acceptsLength n := by
  cases idx with
  | int => simp [acceptsLengthB, PredIndexSet.acceptsLength]
  | range i => simp [acceptsLengthB, PredIndexSet.acceptsLength]

/-- Boolean counterpart of `BasicPredParamType.accepts`. -/
def acceptsB (bt : BasicPredParamType) (t : BaseType) (isVar : Bool) : Bool :=
  decide (bt.baseType = t) && !(bt.isPar && isVar)

theorem acceptsB_iff {bt : BasicPredParamType} {t : BaseType} {isVar : Bool} :
    acceptsB bt t isVar = true ↔ bt.accepts t isVar := by
  unfold acceptsB BasicPredParamType.accepts
  rw [Bool.and_eq_true, decide_eq_true_iff, Bool.not_eq_true']
  cases hb : bt.isPar with
  | false => simp
  | true => simp

/-- Boolean counterpart of `BasicExpr.hasBaseType`. -/
def hasBaseTypeB (env : StaticEnv) (b : BasicExpr) (t : BaseType) : Bool :=
  match b with
  | .lit l => decide (l.type = t)
  | .ident x =>
    match env x with
    | some (.base t', _) => decide (t' = t)
    | _ => false

theorem hasBaseTypeB_iff {env : StaticEnv} {b : BasicExpr} {t : BaseType} :
    hasBaseTypeB env b t = true ↔ b.hasBaseType env t := by
  cases b with
  | lit l => simp only [hasBaseTypeB, BasicExpr.hasBaseType, decide_eq_true_iff]
  | ident x =>
    simp only [hasBaseTypeB, BasicExpr.hasBaseType]
    cases h : env x with
    | none => simp
    | some p =>
      obtain ⟨ft, isVar⟩ := p
      cases ft with
      | base t' => simp
      | array n te => simp

/-- Boolean counterpart of `BasicExpr.checkBase`. -/
def checkBaseB (env : StaticEnv) (b : BasicExpr)
    (bt : BasicPredParamType) : Bool :=
  match b with
  | .lit l => acceptsB bt l.type false
  | .ident x =>
    match env x with
    | some (.base t, isVar) => acceptsB bt t isVar
    | _ => false

theorem checkBaseB_iff {env : StaticEnv} {b : BasicExpr}
    {bt : BasicPredParamType} :
    checkBaseB env b bt = true ↔ b.checkBase env bt := by
  cases b with
  | lit l => simpa [checkBaseB, BasicExpr.checkBase] using acceptsB_iff
  | ident x =>
    simp only [checkBaseB, BasicExpr.checkBase]
    cases h : env x with
    | none => simp
    | some p =>
      obtain ⟨ft, isVar⟩ := p
      cases ft with
      | base t => simpa using acceptsB_iff
      | array n te => simp

/-- Boolean counterpart of `Expr.checkArg`. -/
def checkArgB (env : StaticEnv) (e : Expr) (pt : PredParamType) : Bool :=
  match pt with
  | .basic bt =>
    match e with
    | .basic b => checkBaseB env b bt
    | .array _ => false
  | .array idx bt =>
    match e with
    | .basic (.ident x) =>
      match env x with
      | some (.array n t, isVar) => acceptsLengthB idx n && acceptsB bt t isVar
      | _ => false
    | .basic (.lit _) => false
    | .array es =>
      acceptsLengthB idx es.length && es.all (fun b => checkBaseB env b bt)

theorem checkArgB_iff {env : StaticEnv} {e : Expr} {pt : PredParamType} :
    checkArgB env e pt = true ↔ e.checkArg env pt := by
  cases pt with
  | basic bt =>
    cases e with
    | basic b => exact checkBaseB_iff
    | array es => simp [checkArgB, Expr.checkArg]
  | array idx bt =>
    cases e with
    | basic b =>
      cases b with
      | lit l => simp [checkArgB, Expr.checkArg]
      | ident x =>
        simp only [checkArgB, Expr.checkArg]
        cases h : env x with
        | none => simp
        | some p =>
          obtain ⟨ft, isVar⟩ := p
          cases ft with
          | base t => simp
          | array n te =>
            simp only [Bool.and_eq_true, acceptsLengthB_iff, acceptsB_iff]
    | array es =>
      simp only [checkArgB, Expr.checkArg, Bool.and_eq_true, acceptsLengthB_iff,
        List.all_eq_true, checkBaseB_iff]

/-- Boolean counterpart of `Forall2 (Expr.checkArg env)`. -/
def checkArgsB (env : StaticEnv) : List Expr → List PredParamType → Bool
  | [], [] => true
  | e :: es, pt :: pts => checkArgB env e pt && checkArgsB env es pts
  | _, _ => false

theorem checkArgsB_iff {env : StaticEnv} {args : List Expr}
    {params : List PredParamType} :
    checkArgsB env args params = true ↔
      Forall2 (Expr.checkArg env) args params := by
  induction args generalizing params with
  | nil => cases params <;> simp [checkArgsB, Forall2]
  | cons e es ih =>
    cases params with
    | nil => simp [checkArgsB, Forall2]
    | cons pt pts =>
      simp only [checkArgsB, Forall2, Bool.and_eq_true]
      rw [checkArgB_iff, ih]

/-- Does the argument list match one of the accepted signatures? -/
def SigEnv.matches (sig : SigEnv) (env : StaticEnv) (x : Ident)
    (args : List Expr) : Bool :=
  (sig x).any fun params => checkArgsB env args params

/-- `matches` is true exactly when some accepted signature type-checks. -/
theorem SigEnv.matches_iff (sig : SigEnv) (env : StaticEnv) (x : Ident)
    (args : List Expr) :
    sig.matches env x args = true ↔
      ∃ params ∈ sig x, Forall2 (Expr.checkArg env) args params := by
  unfold SigEnv.matches
  rw [List.any_eq_true]
  constructor
  · rintro ⟨params, hmem, hchk⟩
    exact ⟨params, hmem, checkArgsB_iff.mp hchk⟩
  · rintro ⟨params, hmem, hchk⟩
    exact ⟨params, hmem, checkArgsB_iff.mpr hchk⟩

/-- Check a constraint's arguments against a resolved signature. -/
def checkConstraintB (env : StaticEnv) (args : List Expr) :
    Option (List PredParamType) → Bool
  | none => false
  | some params => checkArgsB env args params

theorem checkConstraintB_iff {env : StaticEnv} {args : List Expr}
    {o : Option (List PredParamType)} :
    checkConstraintB env args o = true ↔
    ∃ params, o = some params ∧ Forall2 (Expr.checkArg env) args params := by
  cases o with
  | none => simp [checkConstraintB]
  | some params =>
    simp only [checkConstraintB]
    constructor
    · intro h
      exact ⟨params, rfl, checkArgsB_iff.mp h⟩
    · rintro ⟨params', heq, hfor⟩
      have hpp : params = params' := by simpa using heq
      rw [hpp]
      exact checkArgsB_iff.mpr hfor

/-- Boolean counterpart of the objective-type check (R7). -/
def solveObjB (env : StaticEnv) : SolveItem → Bool
  | .satisfy _ => true
  | .minimize _ e | .maximize _ e => hasBaseTypeB env e .int

theorem solveObjB_iff {env : StaticEnv} {si : SolveItem} :
    solveObjB env si = true ↔
    (match si with
     | .satisfy _ => True
     | .minimize _ e | .maximize _ e => e.hasBaseType env .int) := by
  cases si with
  | satisfy a => simp [solveObjB]
  | minimize a e => simpa [solveObjB] using hasBaseTypeB_iff
  | maximize a e => simpa [solveObjB] using hasBaseTypeB_iff

/-- Boolean counterpart of the parameter-declaration check (R18/R20). -/
def parDeclCheckB : ParDeclItem → Bool
  | .basic t _ v => decide (v.type = t.base)
  | .array idx t _ vs =>
      decide (vs.length = idx.length) && vs.all (fun v => decide (v.type = t.base))

theorem parDeclCheckB_iff {d : ParDeclItem} :
    parDeclCheckB d = true ↔
    (match d with
     | .basic t _ v => v.type = t.base
     | .array idx t _ vs =>
         vs.length = idx.length ∧ ∀ v ∈ vs, v.type = t.base) := by
  cases d with
  | basic t n v => simp [parDeclCheckB]
  | array idx t n vs =>
    simp only [parDeclCheckB, Bool.and_eq_true, decide_eq_true_iff,
      List.all_eq_true]

/-- Boolean counterpart of the variable-array-length check (R22). -/
def varDeclArrayLenB : VarDeclItem → Bool
  | .array ty _ _ values => decide (values.length = ty.idx.length)
  | _ => true

theorem varDeclArrayLenB_iff {d : VarDeclItem} :
    varDeclArrayLenB d = true ↔
    (match d with
     | .array ty _ _ values => values.length = ty.idx.length
     | _ => True) := by
  cases d <;> simp [varDeclArrayLenB]

/-- Boolean counterpart of the variable-initializer check (R26/R6). -/
def varDeclInitB (env : StaticEnv) : VarDeclItem → Bool
  | .basic t _ _ (some v) => hasBaseTypeB env v t.base
  | .array ty _ _ values => values.all (fun v => hasBaseTypeB env v ty.elem.base)
  | _ => true

theorem varDeclInitB_iff {env : StaticEnv} {d : VarDeclItem} :
    varDeclInitB env d = true ↔
    (match d with
     | .basic t _ _ (some v) => v.hasBaseType env t.base
     | .array ty _ _ values => ∀ v ∈ values, v.hasBaseType env ty.elem.base
     | _ => True) := by
  cases d with
  | basic t n a v =>
    cases v with
    | none => simp [varDeclInitB]
    | some e => simpa [varDeclInitB] using hasBaseTypeB_iff
  | array ty n a values =>
    simp only [varDeclInitB, List.all_eq_true, hasBaseTypeB_iff]

/-! ## Solution semantics -/

/-- Semantic equality of scalar values (R6): Booleans and integers are
    equal as values, integer sets are equal when they have the same
    elements — `1..3`, `{1,2,3}` and `{3,2,1,1}` all denote the same
    set.  Arrays are compared elementwise by `initializerHolds`, so a
    scalar is never `SemEq` to an array. -/
def Value.SemEq : Value → Value → Prop
  | .bool a, .bool b => a = b
  | .int a, .int b => a = b
  | .setOfInt a, .setOfInt b => ∀ x, a.Contains x ↔ b.Contains x
  | _, _ => False

/-- R6: a variable declaration with an initializer imposes equality
    between the declared variable and the initializer's value in every
    solution.  Array initializers define the whole array, elementwise.
    Equality is semantic (`Value.SemEq`): set values with different
    representations of the same set are equal. -/
def _root_.LeanFzn.VarDeclItem.initializerHolds (store : Store) : VarDeclItem → Prop
  | .basic _ _ _ none => True
  | .basic _ n _ (some v) =>
      ∃ val val', v.eval store = some val ∧ store n = some val' ∧ val.SemEq val'
  | .array _ n _ es =>
      ∃ vs ws, es.mapM (fun e => e.eval store) = some vs ∧
        store n = some (.array ws) ∧ Forall2 Value.SemEq vs ws

/-- The dynamic conditions of satisfaction: constraints, variable
    domains, and initializers (everything but static well-formedness). -/
def SatisfiesDyn (pred : PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  (∀ c ∈ m.constraints, c.Holds pred store) ∧
  (∀ d ∈ m.variables, match d with
    | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
    | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
        vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v) ∧
  (∀ d ∈ m.variables, d.initializerHolds store)

/-- The value a parameter declaration fixes. -/
def _root_.LeanFzn.ParDeclItem.value : ParDeclItem → Value
  | .basic _ _ v => v.denote
  | .array _ _ _ vs => .array (vs.map (·.denote))

/-- Canonical dummy value of a base type, used by the shape store. -/
def _root_.LeanFzn.BaseType.dummy : BaseType → Value
  | .bool => .bool false
  | .int => .int 0
  | .setOfInt => .setOfInt (.enumeration [])

/-- Canonical dummy value of an (unfixed) variable type: the dummy of the
    underlying base type, `0` for integer domains and the empty set for set
    domains. -/
def _root_.LeanFzn.BasicVarType.dummy : BasicVarType → Value
  | .par t => _root_.LeanFzn.BaseType.dummy t.base
  | .intRange _ _ | .intSet _ => .int 0
  | .setOfIntRange _ _ | .setOfIntSet _ => .setOfInt (.enumeration [])

/-- The shape value of a variable declaration: the canonical dummy of its
    declared base type, or an array dummy of the declared length. -/
def _root_.LeanFzn.VarDeclItem.shapeValue : VarDeclItem → Value
  | .basic ty _ _ _ => ty.dummy
  | .array ty _ _ _ => .array (List.replicate ty.idx.length ty.elem.dummy)

/-- The shape store: a parameter name takes the value its declaration fixes,
    a variable name takes the canonical dummy of its declared type.  Every
    store whose parameters are honest and whose variables respect their
    domains has the same decoder-relevant structure as `m.shapeStore`. -/
def _root_.LeanFzn.Model.shapeStore (m : Model) : Store := fun x =>
  match lookupIdent x (m.parameters.map (fun d => (d.name, d.value))) with
  | some v => some v
  | none => lookupIdent x (m.variables.map (fun d => (d.name, d.shapeValue)))

/-- The store gives every parameter the value its declaration fixes. -/
def ParamHonest (m : Model) (store : Store) : Prop :=
  ∀ d ∈ m.parameters, store d.name = some d.value

/-! ## `lookupIdent` facts needed by the shape store -/

theorem shapeLookup_cons_eq {β : Type} {y : Ident} {v : β}
    {rest : List (Ident × β)} :
    lookupIdent y ((y, v) :: rest) = some v := by
  simp only [lookupIdent, reduceIte]

theorem shapeLookup_cons_ne {β : Type} {x y : Ident} {v : β}
    {rest : List (Ident × β)} (hne : x.name ≠ y.name) :
    lookupIdent x ((y, v) :: rest) = lookupIdent x rest := by
  simp only [lookupIdent, if_neg hne]

theorem shapeLookup_of_mem {β : Type} {x : Ident} {v : β}
    {l : List (Ident × β)} (hnu : (l.map Prod.fst).Nodup)
    (hmem : (x, v) ∈ l) :
    lookupIdent x l = some v := by
  induction l with
  | nil => cases hmem
  | cons ab rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnu
      rcases List.mem_cons.mp hmem with heq | htl
      · have hxa : x = ab.1 := (Prod.mk.injEq .. ▸ heq).1
        have hva : v = ab.2 := (Prod.mk.injEq .. ▸ heq).2
        rw [hxa, hva]
        exact shapeLookup_cons_eq
      · obtain ⟨y', v'⟩ := ab
        by_cases hname : x.name = y'.name
        · exfalso
          have hxmem : x ∈ rest.map Prod.fst :=
            List.mem_map.mpr ⟨(x, v), htl, rfl⟩
          have hyx : x = y' := Ident.eq_of_name_eq hname
          rw [hyx] at hxmem
          exact hnu.1 hxmem
        · rw [shapeLookup_cons_ne hname]
          exact ih hnu.2 htl

theorem shapeLookup_inv_mem {β : Type} (x : Ident) (l : List (Ident × β))
    (v : β) (h : lookupIdent x l = some v) :
    ∃ y, (y, v) ∈ l ∧ y.name = x.name := by
  induction l with
  | nil => simp [lookupIdent] at h
  | cons ab rest ih =>
      simp only [lookupIdent] at h
      by_cases hab : x.name = ab.1.name
      · rw [if_pos hab] at h
        have hvv : ab.2 = v := (Option.some.inj h)
        subst hvv
        exact ⟨ab.1, List.mem_cons_self, hab.symm⟩
      · rw [if_neg hab] at h
        obtain ⟨y, hy, hname⟩ := ih h
        exact ⟨y, by simp [hy], hname⟩

theorem shapeLookup_none_of_forall {β : Type} {x : Ident} {l : List (Ident × β)}
    (h : ∀ y v, (y, v) ∈ l → y.name ≠ x.name) :
    lookupIdent x l = none := by
  induction l with
  | nil => rfl
  | cons ab rest ih =>
      obtain ⟨y, v⟩ := ab
      by_cases hname : x.name = y.name
      · exact absurd hname.symm (h y v List.mem_cons_self)
      · rw [shapeLookup_cons_ne hname]
        exact ih (fun y' v' hmem => h y' v' (List.mem_cons_of_mem _ hmem))

/-! ## Inversions of `staticEnv` -/

theorem staticEnv_param {m : Model} {x : Ident} {ft : FznType}
    (h : m.staticEnv x = some (ft, false)) :
    ∃ d ∈ m.parameters, d.name = x ∧ d.type = ft := by
  unfold Model.staticEnv at h
  cases hp : lookupIdent x (m.parameters.map (fun d => (d.name, (d.type, false)))) with
  | some info =>
      obtain ⟨ft', isVar⟩ := info
      rw [hp] at h
      have hpair : (ft', isVar) = (ft, false) := Option.some.inj h
      have hft : ft' = ft := congrArg Prod.fst hpair
      have hfalse : isVar = false := congrArg Prod.snd hpair
      subst ft'
      subst isVar
      obtain ⟨y, hy, hname⟩ := shapeLookup_inv_mem x _ (ft, false) hp
      obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hy
      have hdname : d.name = y := congrArg Prod.fst hdeq
      have hdtype : d.type = ft := by
        have := congrArg (fun p : Ident × (FznType × Bool) => p.2.1) hdeq
        simpa using this
      exact ⟨d, hd, hdname.trans (Ident.eq_of_name_eq hname), hdtype⟩
  | none =>
      rw [hp] at h
      obtain ⟨y, hy, hname⟩ := shapeLookup_inv_mem x _ (ft, false) h
      obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hy
      have hsnd : (true : Bool) = false := by
        have := congrArg (fun p : Ident × (FznType × Bool) => p.2.2) hdeq
        simpa using this.symm
      exact absurd hsnd (by simp)

theorem staticEnv_var {m : Model} {x : Ident} {ft : FznType}
    (h : m.staticEnv x = some (ft, true)) :
    ∃ d ∈ m.variables, d.name = x ∧ d.type = ft := by
  unfold Model.staticEnv at h
  cases hp : lookupIdent x (m.parameters.map (fun d => (d.name, (d.type, false)))) with
  | some info =>
      obtain ⟨ft', isVar⟩ := info
      rw [hp] at h
      have hpair : (ft', isVar) = (ft, true) := Option.some.inj h
      have htrue : isVar = true := congrArg Prod.snd hpair
      obtain ⟨y, hy, _⟩ := shapeLookup_inv_mem x _ (ft', isVar) hp
      obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hy
      have hfalse : isVar = false := by
        have := congrArg (fun p : Ident × (FznType × Bool) => p.2.2) hdeq
        simpa using this
      exact absurd (htrue.symm.trans hfalse) (by simp)
  | none =>
      rw [hp] at h
      obtain ⟨y, hy, hname⟩ := shapeLookup_inv_mem x _ (ft, true) h
      obtain ⟨d, hd, hdeq⟩ := List.mem_map.mp hy
      have hdname : d.name = y := congrArg Prod.fst hdeq
      have hdtype : d.type = ft := by
        have := congrArg (fun p : Ident × (FznType × Bool) => p.2.1) hdeq
        simpa using this
      exact ⟨d, hd, hdname.trans (Ident.eq_of_name_eq hname), hdtype⟩

/-! ## `shapeStore` lookups -/

theorem shapeStore_param {m : Model}
    (hnd : (m.parameters.map (·.name)).Nodup)
    {d : ParDeclItem} (hd : d ∈ m.parameters) :
    m.shapeStore d.name = some d.value := by
  unfold Model.shapeStore
  have hmem : (d.name, d.value) ∈
      m.parameters.map (fun d => (d.name, d.value)) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  have hnu : ((m.parameters.map (fun d => (d.name, d.value))).map Prod.fst).Nodup := by
    rw [List.map_map]
    simpa [Function.comp_def] using hnd
  have hlookup := shapeLookup_of_mem hnu hmem
  simp only [Model.shapeStore, hlookup]

theorem shapeStore_var {m : Model}
    (hnd : (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup)
    {d : VarDeclItem} (hd : d ∈ m.variables) :
    m.shapeStore d.name = some d.shapeValue := by
  unfold Model.shapeStore
  have hsplit := List.nodup_append.mp hnd
  obtain ⟨_, hndVar, hdisj⟩ := hsplit
  have hnone : lookupIdent d.name
      (m.parameters.map (fun d => (d.name, d.value))) = none := by
    apply shapeLookup_none_of_forall
    intro y v hmem heq
    obtain ⟨p, hp, hp_eq⟩ := List.mem_map.mp hmem
    have hy : p.name = y := congrArg Prod.fst hp_eq
    have hpmem : p.name ∈ m.parameters.map (·.name) :=
      List.mem_map.mpr ⟨p, hp, rfl⟩
    have hdmem : d.name ∈ m.variables.map (·.name) :=
      List.mem_map.mpr ⟨d, hd, rfl⟩
    have hpname : p.name = d.name := by
      rw [hy]
      exact Ident.eq_of_name_eq heq
    have hdmem' : p.name ∈ m.variables.map (·.name) := by
      rw [hpname]; exact hdmem
    exact (hdisj p.name hpmem p.name hdmem') rfl
  rw [hnone]
  have hmem : (d.name, d.shapeValue) ∈
      m.variables.map (fun d => (d.name, d.shapeValue)) :=
    List.mem_map.mpr ⟨d, hd, rfl⟩
  have hnu : ((m.variables.map (fun d => (d.name, d.shapeValue))).map Prod.fst).Nodup := by
    rw [List.map_map]
    simpa [Function.comp_def] using hndVar
  exact shapeLookup_of_mem hnu hmem


/-! ## Dummy shapes and variable domain respect -/

/-- The variable-domain conjunct of `SatisfiesDyn`. -/
def VarsRespect (m : Model) (store : Store) : Prop :=
  ∀ d ∈ m.variables, match d with
    | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
    | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
        vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v

theorem BasicVarType.sameShape_dummy {ty : BasicVarType} {v : Value}
    (h : ty.contains v) : v.SameShape ty.dummy := by
  cases ty with
  | par t =>
      cases t with
      | bool => cases v with
        | bool b => exact .bool b false
        | int i => exact h.elim
        | setOfInt s => exact h.elim
        | array xs => exact h.elim
      | int => cases v with
        | bool b => exact h.elim
        | int i => exact .int i 0
        | setOfInt s => exact h.elim
        | array xs => exact h.elim
      | setOfInt => cases v with
        | bool b => exact h.elim
        | int i => exact h.elim
        | setOfInt s => exact .setOfInt s (.enumeration [])
        | array xs => exact h.elim
  | intRange lo hi =>
      cases v with
      | bool b => exact h.elim
      | int i => exact .int i 0
      | setOfInt s => exact h.elim
      | array xs => exact h.elim
  | intSet xs =>
      cases v with
      | bool b => exact h.elim
      | int i => exact .int i 0
      | setOfInt s => exact h.elim
      | array xs => exact h.elim
  | setOfIntRange lo hi =>
      cases v with
      | bool b => exact h.elim
      | int i => exact h.elim
      | setOfInt s => exact .setOfInt s (.enumeration [])
      | array xs => exact h.elim
  | setOfIntSet xs =>
      cases v with
      | bool b => exact h.elim
      | int i => exact h.elim
      | setOfInt s => exact .setOfInt s (.enumeration [])
      | array xs => exact h.elim

theorem ListSameShape.replicate {R : Value → Value → Prop} {x : Value} :
    ∀ (xs : List Value) (n : Nat), xs.length = n →
      (∀ y ∈ xs, R y x) → ListSameShape R xs (List.replicate n x)
  | [], n, hn, _ => by
      cases n with
      | zero => exact .nil
      | succ n => simp at hn
  | y :: ys, n, hn, hx => by
      cases n with
      | zero => simp at hn
      | succ n =>
          have hlen : ys.length = n := by simpa using hn
          exact .cons (hx y List.mem_cons_self)
            (ListSameShape.replicate ys n hlen (fun z hz => hx z (List.mem_cons_of_mem _ hz)))



theorem _root_.LeanFzn.BasicVarType.dummy_eq_base_dummy (ty : BasicVarType) :
    ty.dummy = LeanFzn.BaseType.dummy ty.base := by
  cases ty <;> rfl

theorem _root_.LeanFzn.BasicVarType.dummy_eq_of_base_eq {ty ty' : BasicVarType}
    (h : ty.base = ty'.base) : ty.dummy = ty'.dummy := by
  rw [BasicVarType.dummy_eq_base_dummy, BasicVarType.dummy_eq_base_dummy, h]

theorem _root_.LeanFzn.VarDeclItem.shapeValue_eq_of_type_eq {d d' : VarDeclItem}
    (h : d.type = d'.type) : d.shapeValue = d'.shapeValue := by
  cases d with
  | basic ty n anns v =>
      cases d' with
      | basic ty' n' anns' v' =>
          simp only [VarDeclItem.type, FznType.base.injEq] at h
          simp only [VarDeclItem.shapeValue]
          exact BasicVarType.dummy_eq_of_base_eq h
      | array ty' n' anns' es' =>
          simp only [VarDeclItem.type] at h
          cases h
  | array ty n anns es =>
      cases d' with
      | basic ty' n' anns' v' =>
          simp only [VarDeclItem.type] at h
          cases h
      | array ty' n' anns' es' =>
          simp only [VarDeclItem.type, FznType.array.injEq] at h
          obtain ⟨hlen, hbase⟩ := h
          simp only [VarDeclItem.shapeValue, hlen]
          rw [BasicVarType.dummy_eq_of_base_eq hbase]

theorem _root_.LeanFzn.Model.shapeStore_eq_of {m m' : Model}
    (hp : m'.parameters = m.parameters)
    (hv : m'.variables.map (fun d => (d.name, d.shapeValue)) =
      m.variables.map (fun d => (d.name, d.shapeValue))) :
    m'.shapeStore = m.shapeStore := by
  unfold Model.shapeStore
  rw [hp, hv]

theorem _root_.LeanFzn.Model.shapeStore_eq_of_map {m : Model}
    {f : VarDeclItem → VarDeclItem}
    (hf : ∀ d, (f d).name = d.name ∧ (f d).shapeValue = d.shapeValue) :
    ({ m with variables := m.variables.map f } : Model).shapeStore = m.shapeStore := by
  exact Model.shapeStore_eq_of (m := m)
    (m' := { m with variables := m.variables.map f }) rfl (by
      rw [List.map_map]
      exact List.map_congr_left (fun d _ => by simp [hf d]))
/-- Inversion for `List.mapM` on a cons. -/
theorem mapM_cons_inv {α : Type} {f : α → Option Value} {a : α} {l : List α}
    {vs : List Value} (h : (a :: l).mapM f = some vs) :
    ∃ v vs', f a = some v ∧ l.mapM f = some vs' ∧ vs = v :: vs' := by
  simp only [List.mapM_cons, Option.pure_def] at h
  cases hfa : f a with
  | none => rw [hfa] at h; simp at h
  | some v =>
      cases hfl : l.mapM f with
      | none => rw [hfa, hfl] at h; simp at h
      | some vs' =>
          rw [hfa, hfl] at h
          change some (v :: vs') = some vs at h
          exact ⟨v, vs', rfl, rfl, (Option.some.inj h).symm⟩

theorem mapM_cons_some {α : Type} {f : α → Option Value} {a : α} {l : List α}
    {v : Value} {vs : List Value} (hfa : f a = some v)
    (hfl : l.mapM f = some vs) :
    (a :: l).mapM f = some (v :: vs) := by
  rw [List.mapM_cons, hfa, hfl]
  rfl

theorem mapM_isSome {α : Type} {f : α → Option Value} {l : List α}
    (h : ∀ a ∈ l, (f a).isSome = true) : (l.mapM f).isSome = true := by
  have hex : ∃ vs, l.mapM f = some vs := by
    induction l with
    | nil => exact ⟨[], rfl⟩
    | cons a as ih =>
        have hfa : (f a).isSome = true := h a List.mem_cons_self
        obtain ⟨v, hfv⟩ := Option.isSome_iff_exists.mp hfa
        obtain ⟨vs, hvs⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
        exact ⟨v :: vs, mapM_cons_some hfv hvs⟩
  obtain ⟨vs, hvs⟩ := hex
  rw [hvs]
  rfl

theorem shapeStore_exists_of_staticEnv {m : Model}
    (hnd : (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup)
    {x : Ident} {ft : FznType} {isVar : Bool}
    (henv : m.staticEnv x = some (ft, isVar)) :
    ∃ v, m.shapeStore x = some v := by
  cases isVar with
  | false =>
      obtain ⟨d, hd, hdname, _⟩ := staticEnv_param henv
      have hndp : (m.parameters.map (·.name)).Nodup :=
        (List.nodup_append.mp hnd).1
      have hs : m.shapeStore d.name = some d.value := by
        unfold Model.shapeStore
        have hmem : (d.name, d.value) ∈
            m.parameters.map (fun d => (d.name, d.value)) :=
          List.mem_map.mpr ⟨d, hd, rfl⟩
        have hnu : ((m.parameters.map (fun d => (d.name, d.value))).map Prod.fst).Nodup := by
          rw [List.map_map]
          simpa [Function.comp_def] using hndp
        have hlookup := shapeLookup_of_mem hnu hmem
        simp only [Model.shapeStore, hlookup]
      rw [hdname] at hs
      exact ⟨_, hs⟩
  | true =>
      obtain ⟨d, hd, hdname, _⟩ := staticEnv_var henv
      have hs : m.shapeStore d.name = some d.shapeValue :=
        shapeStore_var hnd hd
      rw [hdname] at hs
      exact ⟨_, hs⟩

theorem eval_isSome_of_checkBase {m : Model}
    (hnd : (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup)
    {b : BasicExpr} {bt : BasicPredParamType} (hb : b.checkBase m.staticEnv bt) :
    (b.eval m.shapeStore).isSome = true := by
  cases b with
  | lit l => rfl
  | ident x =>
      simp only [BasicExpr.eval]
      simp only [BasicExpr.checkBase] at hb
      cases henv : m.staticEnv x with
      | none => rw [henv] at hb; exact hb.elim
      | some info =>
          obtain ⟨ft, isVar⟩ := info
          rw [henv] at hb
          obtain ⟨v, hv⟩ := shapeStore_exists_of_staticEnv hnd henv
          rw [hv]
          rfl

theorem eval_isSome_of_checkArg {m : Model}
    (hnd : (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup)
    {e : Expr} {pt : PredParamType} (hc : e.checkArg m.staticEnv pt) :
    (e.eval m.shapeStore).isSome = true := by
  cases e with
  | basic b =>
      cases pt with
      | basic bt =>
          simp only [Expr.checkArg, Expr.eval] at hc ⊢
          exact eval_isSome_of_checkBase hnd hc
      | array idx bt =>
          cases b with
          | lit l => simp [Expr.checkArg] at hc
          | ident x =>
              simp only [Expr.checkArg, Expr.eval] at hc ⊢
              cases henv : m.staticEnv x with
              | none => rw [henv] at hc; exact hc.elim
              | some info =>
                  obtain ⟨ft, isVar⟩ := info
                  rw [henv] at hc
                  cases ft with
                  | base t => exact hc.elim
                  | array n t =>
                      change (m.shapeStore x).isSome = true
                      obtain ⟨v, hv⟩ := shapeStore_exists_of_staticEnv hnd henv
                      rw [hv]
                      rfl
  | array es =>
      cases pt with
      | basic bt => simp [Expr.checkArg] at hc
      | array idx bt =>
          simp only [Expr.checkArg, Expr.eval] at hc ⊢
          obtain ⟨hlen, hcheck⟩ := hc
          rw [Option.isSome_map]
          exact mapM_isSome (fun b hb => eval_isSome_of_checkBase hnd (hcheck b hb))

def ObjectiveAttained (m : Model) (store : Store) : Prop :=
  match m.solve with
  | .satisfy _ => True
  | .minimize _ _ | .maximize _ _ => ∃ i, m.solve.objective store = some i

end LeanFzn.Semantics
