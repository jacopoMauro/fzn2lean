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
    the parameter types of its signature; `none` if the predicate is not
    available.  The theorems quantify over this environment. -/
abbrev SigEnv := Ident → Option (List PredParamType)

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

/-- The signatures declared by the model's predicate items. -/
def _root_.LeanFzn.Model.declaredSigs (m : Model) : SigEnv :=
  fun x => lookupIdent x (m.predicates.map (fun p => (p.name, p.params.map (·.type))))

/-- Combined signature lookup (R8): model declarations first, then the
    external environment. -/
def _root_.LeanFzn.Model.sigEnv (m : Model) (ext : SigEnv) : SigEnv :=
  fun x =>
    match m.declaredSigs x with
    | some params => some params
    | none => ext x

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

/-- **Static well-formedness** of a model under the external signature
    environment `sig` (R8, A3).  Captures the context-sensitive rules of
    the supported fragment:

    * R4: predicate names are distinct; parameters and variables share
      one value namespace and are distinct; predicate formals are distinct.
    * R18/R20: parameter initializers are literals of the declared type,
      and parameter array lengths match the index set.
    * R22: variable array lengths match the index set.
    * R26/R6: variable initializers (fixings and aliases) have the
      declared type.
    * R7: `minimize`/`maximize` objectives have type `int`.
    * R8/R13-R15: every constraint's predicate is available (declared
      in the model or in `sig`) and its arguments match the signature,
      with par-to-var coercion.

    Reversed ranges are deliberately *not* rejected: they denote the
    empty set (R1).  Fixed values outside a variable's domain make a
    model unsatisfiable rather than ill-formed, and parameter data
    outside its type is an instance error (A5), so neither is checked
    here. -/
structure WellFormed (sig : SigEnv) (m : Model) : Prop where
  /-- R4: no duplicate predicate declarations. -/
  predNamesUnique : (m.predicates.map (·.name)).Nodup
  /-- R4: parameters and variables share one value namespace. -/
  valueNamesUnique :
    (m.parameters.map (·.name) ++ m.variables.map (·.name)).Nodup
  /-- R4: predicate formal parameter names are distinct. -/
  predParamsUnique : ∀ p ∈ m.predicates, (p.params.map (·.name)).Nodup
  /-- R18/R20: parameter types and array lengths. -/
  parameterTypes : ∀ d ∈ m.parameters, match d with
    | .basic t _ v => v.type = t.base
    | .array idx t _ vs => vs.length = idx.length ∧ ∀ v ∈ vs, v.type = t.base
  /-- R22: variable array lengths match the declared index set. -/
  variableArrayLengths : ∀ d ∈ m.variables, match d with
    | .array ty _ _ values => values.length = ty.idx.length
    | _ => True
  /-- R26/R6: variable initializers have the declared type. -/
  variableInitializers : ∀ d ∈ m.variables, match d with
    | .basic t _ _ (some v) => v.hasBaseType m.staticEnv t.base
    | .array ty _ _ values =>
        ∀ v ∈ values, v.hasBaseType m.staticEnv ty.elem.base
    | _ => True
  /-- R7: optimization objectives have type `int`. -/
  objectiveType : match m.solve with
    | .satisfy _ => True
    | .minimize _ e | .maximize _ e => e.hasBaseType m.staticEnv .int
  /-- R8/R13-R15: constraints match available signatures. -/
  constraintsChecked : ∀ c ∈ m.constraints, ∃ params,
    m.sigEnv sig c.name = some params ∧
    Forall2 (Expr.checkArg m.staticEnv) c.args params

/-! ## An executable static checker

A boolean-valued function `wellFormedB` mirroring `WellFormed`, proved
equivalent to it by `wellFormedB_iff`.  All comparisons go through
`decide`, so the checker computes on parsed models; the tests in
`Tests/Semantics/WellFormed.lean` run it. -/

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

/-- **Executable static checker**: `wellFormedB sig m` computes the static
    well-formedness of `m` under the signature environment `sig`.
    `wellFormedB_iff` proves it equivalent to the `WellFormed`
    predicate. -/
def wellFormedB (sig : SigEnv) (m : Model) : Bool :=
  nodupIdentB (m.predicates.map (·.name)) &&
  nodupIdentB (m.parameters.map (·.name) ++ m.variables.map (·.name)) &&
  m.predicates.all (fun p => nodupIdentB (p.params.map (·.name))) &&
  m.parameters.all (fun d => parDeclCheckB d) &&
  m.variables.all (fun d => varDeclArrayLenB d) &&
  m.variables.all (fun d => varDeclInitB m.staticEnv d) &&
  solveObjB m.staticEnv m.solve &&
  m.constraints.all (fun c =>
    checkConstraintB m.staticEnv c.args (m.sigEnv sig c.name))

theorem wellFormedB_iff (sig : SigEnv) (m : Model) :
    wellFormedB sig m = true ↔ WellFormed sig m := by
  unfold wellFormedB
  simp only [Bool.and_eq_true, List.all_eq_true]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    refine ⟨nodupIdentB_iff.mp h1, nodupIdentB_iff.mp h2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro p hp; exact nodupIdentB_iff.mp (h3 p hp)
    · intro d hd; exact parDeclCheckB_iff.mp (h4 d hd)
    · intro d hd; exact varDeclArrayLenB_iff.mp (h5 d hd)
    · intro d hd; exact varDeclInitB_iff.mp (h6 d hd)
    · exact solveObjB_iff.mp h7
    · intro c hc; exact checkConstraintB_iff.mp (h8 c hc)
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    refine ⟨⟨⟨⟨⟨⟨⟨nodupIdentB_iff.mpr h1, nodupIdentB_iff.mpr h2⟩,
      fun p hp => nodupIdentB_iff.mpr (h3 p hp)⟩,
      fun d hd => parDeclCheckB_iff.mpr (h4 d hd)⟩,
      fun d hd => varDeclArrayLenB_iff.mpr (h5 d hd)⟩,
      fun d hd => varDeclInitB_iff.mpr (h6 d hd)⟩,
      solveObjB_iff.mpr h7⟩,
      fun c hc => checkConstraintB_iff.mpr (h8 c hc)⟩
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

/-- `store` satisfies the well-formed model `m` under the predicate
    interpretation `pred`.

    `Satisfies` constrains the store on the model's *variables* only:
    it does not require the store to give each parameter its declared
    value.  A store that rebinds a parameter can therefore satisfy
    constraints that the model's actual parameter values violate.
    Statements about solutions of a FlatZinc instance must add
    `ParamHonest m store` (as `IsSolution` does); the solution checker
    guarantees it for the stores it accepts. -/
def Satisfies (sig : SigEnv) (pred : PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  WellFormed sig m ∧ SatisfiesDyn pred m store

/-- The value a parameter declaration fixes. -/
def _root_.LeanFzn.ParDeclItem.value : ParDeclItem → Value
  | .basic _ _ v => v.denote
  | .array _ _ _ vs => .array (vs.map (·.denote))

/-- The store gives every parameter the value its declaration fixes. -/
def ParamHonest (m : Model) (store : Store) : Prop :=
  ∀ d ∈ m.parameters, store d.name = some d.value

def ObjectiveAttained (m : Model) (store : Store) : Prop :=
  match m.solve with
  | .satisfy _ => True
  | .minimize _ _ | .maximize _ _ => ∃ i, m.solve.objective store = some i

/-- Optimality among the instance's solutions.  The competing stores
    must be parameter-honest: otherwise a store rebinding a parameter
    could beat the true optimum. -/
def IsOptimal (sig : SigEnv) (pred : PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  match m.solve with
  | .satisfy _ => True
  | .minimize _ _ => ∀ other i j, Satisfies sig pred m other → ParamHonest m other →
      m.solve.objective store = some i → m.solve.objective other = some j → i ≤ j
  | .maximize _ _ => ∀ other i j, Satisfies sig pred m other → ParamHonest m other →
      m.solve.objective store = some i → m.solve.objective other = some j → j ≤ i

/-- A complete, parameter-honest satisfying assignment which also
    realizes the solve goal. -/
def IsSolution (sig : SigEnv) (pred : PredicateInterpretation) (m : Model)
    (store : Store) : Prop :=
  Satisfies sig pred m store ∧ ParamHonest m store ∧ ObjectiveAttained m store ∧
    IsOptimal sig pred m store

end LeanFzn.Semantics
