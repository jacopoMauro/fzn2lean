/-
File: LeanFzn/Compiler/Proofs/Fragment.lean

Purpose:
  Correctness of the L4 fragment passes (`Compiler/Fragment.lean`,
  PLAN.md task L4).

  * `substParamsModel`: every constraint and scalar initializer evaluates
    identically before and after scalar-parameter substitution, provided
    the store agrees with `parEnv` on every parameter name.  Well-formedness
    is preserved because a scalar parameter identifier is replaced by a
    literal of the same base type.
  * `expandInitModel`: a scalar initializer holds exactly when the
    initializer-free declaration holds together with the emitted
    fixed-value constraint.  Both directions are proved, including the
    `bool_not` encoding for Boolean literals.
  * `fragmentModel` composes the two passes.  `fragment_covers` and
    `fragment_exact` expose the composite as an equivalence of
    `SatisfiesDyn`; `wf_fragment` carries static well-formedness.

  `Proofs/Normalize` inserts `fragmentModel` between array inlining and
  literal folding.  No public `solveModel_*` statement changes.

Dependencies:
  - LeanFzn.Compiler.Fragment (the definitions).
-/

import LeanFzn.Compiler.Fragment
import LeanFzn.Compiler.Proofs.LiteralFold
import LeanFzn.Compiler.Proofs.CompileCore

namespace LeanFzn.Compiler
open LeanFzn Semantics LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Semantics.Globals

/-! ## Generic map lemmas -/

theorem mapM_congr' {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem mapM_map_eq {α β γ : Type} {f : α → β} {g : β → Option γ}
    (l : List α) : (l.map f).mapM g = l.mapM (fun a => g (f a)) := by
  induction l with
  | nil => rfl
  | cons a rest ih => rw [List.map_cons, List.mapM_cons, List.mapM_cons, ih]

theorem mapM_mapM_eq {α β γ : Type} {f : α → β} {g : β → Option γ} :
    ∀ {l : List α} {vs : List γ},
    (l.mapM (fun a => g (f a))) = some vs → (l.map f).mapM g = some vs := by
  intro l
  induction l with
  | nil =>
      intro vs h
      simpa using h
  | cons a rest ih =>
      intro vs h
      rw [List.mapM_cons] at h
      cases hg : g (f a) with
      | none => rw [hg] at h; simp at h
      | some v =>
          rw [hg] at h
          cases hr : rest.mapM (fun a => g (f a)) with
          | none => rw [hr] at h; simp at h
          | some ws =>
              rw [hr] at h
              simp at h
              subst h
              rw [List.map_cons, List.mapM_cons, hg, ih hr]
              rfl

/-! ## Scalar parameter substitution -/

/-- A scalar literal denotes the value it was decoded from. -/
theorem scalarLiteral_denote {v : Value} {l : BasicLiteral}
    (h : scalarLiteral v = some l) : l.denote = v := by
  cases v with
  | int i => simp [scalarLiteral] at h; subst h; rfl
  | bool b => simp [scalarLiteral] at h; subst h; rfl
  | setOfInt s => simp [scalarLiteral] at h
  | array vs => simp [scalarLiteral] at h

/-- Evaluation is unchanged by scalar-parameter substitution when the store
    agrees with the environment on every name it resolves. -/
theorem substParamBasic_eval {env : Store} {s : Store}
    (henv : ∀ x v, env x = some v → s x = some v) (b : BasicExpr) :
    BasicExpr.eval s (substParamBasic env b) = BasicExpr.eval s b := by
  cases b with
  | lit l => rfl
  | ident x =>
      simp only [substParamBasic]
      split
      · rename_i v hv
        cases hv' : scalarLiteral v with
        | some l =>
            simp only [hv']
            show some l.denote = s x
            rw [scalarLiteral_denote hv', henv x v hv]
        | none =>
            rfl
      · rfl

theorem substParamExpr_eval {env : Store} {s : Store}
    (henv : ∀ x v, env x = some v → s x = some v) (e : Expr) :
    Expr.eval s (substParamExpr env e) = Expr.eval s e := by
  cases e with
  | basic b => exact substParamBasic_eval henv b
  | array es =>
      simp only [substParamExpr, Expr.eval]
      rw [mapM_map_eq, mapM_congr' (f := fun b => BasicExpr.eval s (substParamBasic env b))
        (g := fun b => BasicExpr.eval s b)
        (fun b _ => substParamBasic_eval henv b)]

/-- A constraint holds in exactly the same stores after scalar-parameter
    substitution. -/
theorem substParamConstraint_holds {env : Store} {s : Store}
    (henv : ∀ x v, env x = some v → s x = some v) (c : ConstraintItem) :
    c.Holds fullInterp s ↔ (substParamConstraint env c).Holds fullInterp s := by
  unfold ConstraintItem.Holds substParamConstraint
  simp only
  have hargs : ∀ {vs : List Value},
      (List.map (substParamExpr env) c.args).mapM (Expr.eval s) = some vs →
        c.args.mapM (Expr.eval s) = some vs := by
    intro vs h
    rw [mapM_map_eq, mapM_congr' (f := fun e => Expr.eval s (substParamExpr env e))
      (g := fun e => Expr.eval s e)
      (fun e _ => substParamExpr_eval henv e)] at h
    exact h
  constructor
  · rintro ⟨args, hmap, hpred⟩
    refine ⟨args, ?_, hpred⟩
    rw [mapM_map_eq, mapM_congr' (f := fun e => Expr.eval s (substParamExpr env e))
      (g := fun e => Expr.eval s e)
      (fun e _ => substParamExpr_eval henv e)]
    exact hmap
  · rintro ⟨args, hmap, hpred⟩
    exact ⟨args, hargs hmap, hpred⟩

/-- A variable declaration's initializer condition is unchanged by
    scalar-parameter substitution. -/
theorem substParamVarDecl_initializer {env : Store} {s : Store}
    (henv : ∀ x v, env x = some v → s x = some v) (d : VarDeclItem) :
    d.initializerHolds s ↔ (substParamVarDecl env d).initializerHolds s := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => simp [VarDeclItem.initializerHolds, substParamVarDecl]
      | some e =>
          simp only [VarDeclItem.initializerHolds, substParamVarDecl]
          rw [substParamBasic_eval henv e]
  | array ty n anns es => rfl

/-- `SatisfiesDyn` is unchanged by scalar-parameter substitution. -/
theorem substParams_satisfiesDyn {m : Model} {s : Store}
    (henv : ∀ x v, parEnv m x = some v → s x = some v) :
    SatisfiesDyn fullInterp m s ↔ SatisfiesDyn fullInterp (substParamsModel m) s := by
  unfold SatisfiesDyn substParamsModel
  simp only
  constructor
  · rintro ⟨hcons, hvars, hinit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc
      exact (substParamConstraint_holds henv c0).mp (hcons c0 hc0)
    · intro d hd
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
      cases d0 with
      | basic ty n anns init =>
          cases init <;> simpa [substParamVarDecl] using
            hvars (.basic ty n anns _) hd0
      | array ty n anns es =>
          simpa [substParamVarDecl] using hvars (.array ty n anns es) hd0
    · intro d hd
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
      exact (substParamVarDecl_initializer henv d0).mp (hinit d0 hd0)
  · rintro ⟨hcons, hvars, hinit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      exact (substParamConstraint_holds henv c).mpr
        (hcons _ (List.mem_map.mpr ⟨c, hc, rfl⟩))
    · intro d hd
      cases d with
      | basic ty n anns init =>
          cases init <;> simpa [substParamVarDecl] using
            hvars (.basic ty n anns _) (List.mem_map.mpr ⟨_, hd, rfl⟩)
      | array ty n anns es =>
          simpa [substParamVarDecl] using
            hvars (.array ty n anns es) (List.mem_map.mpr ⟨_, hd, rfl⟩)
    · intro d hd
      exact (substParamVarDecl_initializer henv d).mpr
        (hinit _ (List.mem_map.mpr ⟨d, hd, rfl⟩))

/-! ## Initializer expansion -/

/-- The fixed-value row for an integer literal initializer. -/
def intEqConstraint (n : Ident) (k : Int) : ConstraintItem :=
  { name := Ident.mk "int_eq"
    args := [.basic (.ident n), .basic (.lit (.int k))]
    anns := [] }

/-- The fixed-value row for a Boolean literal initializer.  `bool_not(x, b)`
    means `x = !b`, so passing `!b` forces `x = b`. -/
def boolNotConstraint (n : Ident) (b : Bool) : ConstraintItem :=
  { name := Ident.mk "bool_not"
    args := [.basic (.ident n), .basic (.lit (.bool (!b)))]
    anns := [] }

theorem bool_not_not_globals : "bool_not" ∉ globalsNames := by decide

theorem stdInterp_int_eq_apply (args : List Value) :
    stdInterp (Ident.mk "int_eq") args =
      match args with
      | [.int a, .int b] => a = b
      | _ => False := rfl

theorem stdInterp_bool_not_apply (args : List Value) :
    stdInterp (Ident.mk "bool_not") args =
      match args with
      | [.bool a, .bool b] => b = !a
      | _ => False := rfl

theorem intEqConstraint_holds {s : Store} {n : Ident} {k : Int} :
    ({ name := Ident.mk "int_eq"
       args := [.basic (.ident n), .basic (.lit (.int k))]
       anns := [] } : ConstraintItem).Holds fullInterp s ↔ s n = some (.int k) := by
  unfold ConstraintItem.Holds
  constructor
  · rintro ⟨args, hmap, hinterp⟩
    simp [List.mapM_cons, List.mapM_nil, Option.bind_eq_some_iff] at hmap
    rcases hmap with ⟨a1, h1, a2, h2, rfl⟩
    simp only [fullInterp_std_of_not_mem (n := "int_eq") int_eq_not_globals,
      stdInterp_int_eq_apply] at hinterp
    simp [Expr.eval, BasicExpr.eval, BasicLiteral.denote] at h1 h2
    subst h2
    cases a1 <;> simp_all
  · intro hn
    refine ⟨[.int k, .int k], ?_, ?_⟩
    · simp [List.mapM_cons, List.mapM_nil, Option.bind_eq_some_iff,
        Expr.eval, BasicExpr.eval, BasicLiteral.denote, hn]
    · simp only [fullInterp_std_of_not_mem (n := "int_eq") int_eq_not_globals,
        stdInterp_int_eq_apply]

theorem boolNotConstraint_holds {s : Store} {n : Ident} {b : Bool} :
    ({ name := Ident.mk "bool_not"
       args := [.basic (.ident n), .basic (.lit (.bool (!b)))]
       anns := [] } : ConstraintItem).Holds fullInterp s ↔ s n = some (.bool b) := by
  unfold ConstraintItem.Holds
  constructor
  · rintro ⟨args, hmap, hinterp⟩
    simp [List.mapM_cons, List.mapM_nil, Option.bind_eq_some_iff] at hmap
    rcases hmap with ⟨a1, h1, a2, h2, rfl⟩
    simp only [fullInterp_std_of_not_mem (n := "bool_not") bool_not_not_globals,
      stdInterp_bool_not_apply] at hinterp
    simp [Expr.eval, BasicExpr.eval, BasicLiteral.denote] at h1 h2
    subst h2
    cases a1 <;> simp_all
  · intro hn
    refine ⟨[.bool b, .bool (!b)], ?_, ?_⟩
    · simp [List.mapM_cons, List.mapM_nil,
        Expr.eval, BasicExpr.eval, BasicLiteral.denote, hn]
    · simp only [fullInterp_std_of_not_mem (n := "bool_not") bool_not_not_globals,
        stdInterp_bool_not_apply]

/-- The initializer condition of one declaration is exactly its
    initializer-free form plus the constraints emitted by `expandInitDecl`. -/
theorem expandInitDecl_holds (d : VarDeclItem) (s : Store) :
    d.initializerHolds s ↔
      (expandInitDecl d).1.initializerHolds s ∧
        ∀ c ∈ (expandInitDecl d).2, c.Holds fullInterp s := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => simp [VarDeclItem.initializerHolds, expandInitDecl]
      | some e =>
          cases e with
          | lit l =>
              cases l with
              | int k =>
                  by_cases hty : ty.base = .int
                  · simp only [expandInitDecl, initConstraint, hty,
                      if_true, VarDeclItem.initializerHolds, true_and,
                      List.mem_singleton, forall_eq]
                    rw [intEqConstraint_holds]
                    constructor
                    · rintro ⟨val, val', hlit, hn, hsem⟩
                      simp [BasicExpr.eval, BasicLiteral.denote] at hlit
                      subst hlit
                      cases val' <;> simp_all [Value.SemEq]
                    · intro hn
                      refine ⟨.int k, .int k, ?_, hn, ?_⟩
                      · rfl
                      · simp [Value.SemEq]
                  · simp [expandInitDecl, initConstraint, hty,
                      VarDeclItem.initializerHolds]
              | bool b =>
                  by_cases hty : ty.base = .bool
                  · simp only [expandInitDecl, initConstraint, hty,
                      if_true, VarDeclItem.initializerHolds, true_and,
                      List.mem_singleton, forall_eq]
                    rw [boolNotConstraint_holds]
                    constructor
                    · rintro ⟨val, val', hlit, hn, hsem⟩
                      simp [BasicExpr.eval, BasicLiteral.denote] at hlit
                      subst hlit
                      cases val' <;> simp_all [Value.SemEq]
                    · intro hn
                      refine ⟨.bool b, .bool b, ?_, hn, ?_⟩
                      · rfl
                      · simp [Value.SemEq]
                  · simp [expandInitDecl, initConstraint, hty,
                      VarDeclItem.initializerHolds]
              | set sl =>
                  simp [expandInitDecl, initConstraint,
                    VarDeclItem.initializerHolds]
          | ident x =>
              simp [expandInitDecl, initConstraint, VarDeclItem.initializerHolds]
  | array ty n anns es => simp [VarDeclItem.initializerHolds, expandInitDecl]

/-! ## Shape preservation -/

theorem substParamVarDecl_name (env : Store) (d : VarDeclItem) :
    (substParamVarDecl env d).name = d.name := by
  cases d with
  | basic ty n anns init => cases init <;> rfl
  | array ty n anns es => rfl

theorem substParamVarDecl_type (env : Store) (d : VarDeclItem) :
    (substParamVarDecl env d).type = d.type := by
  cases d with
  | basic ty n anns init => cases init <;> rfl
  | array ty n anns es => rfl

theorem expandInitDecl_fst_name (d : VarDeclItem) :
    (expandInitDecl d).1.name = d.name := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => rfl
      | some e =>
          cases hc : initConstraint (.basic ty n anns (some e)) with
          | none => simp [expandInitDecl, hc]
          | some c =>
              simp only [expandInitDecl, hc, Prod.fst]
              rfl
  | array ty n anns es => rfl

theorem expandInitDecl_fst_type (d : VarDeclItem) :
    (expandInitDecl d).1.type = d.type := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => rfl
      | some e =>
          cases hc : initConstraint (.basic ty n anns (some e)) with
          | none => simp [expandInitDecl, hc]
          | some c =>
              simp only [expandInitDecl, hc, Prod.fst]
              rfl
  | array ty n anns es => rfl

theorem fragment_variables_eq (m : Model) :
    (fragmentModel m).variables =
      m.variables.map
        (fun d => (expandInitDecl (substParamVarDecl (parEnv m) d)).1) := by
  simp [fragmentModel, expandInitModel, substParamsModel, List.map_map]

theorem substParams_variables_eq (m : Model) :
    (substParamsModel m).variables =
      m.variables.map (substParamVarDecl (parEnv m)) := rfl

theorem expandInit_variables_eq (m : Model) :
    (expandInitModel m).variables =
      m.variables.map (fun d => (expandInitDecl d).1) := by
  simp [expandInitModel, List.map_map]

theorem fragment_variables_names (m : Model) :
    (fragmentModel m).variables.map VarDeclItem.name =
      m.variables.map VarDeclItem.name := by
  rw [fragment_variables_eq, List.map_map]
  apply List.map_congr_left
  intro d _
  exact (expandInitDecl_fst_name _).trans (substParamVarDecl_name _ _)

theorem fragment_variables_static (m : Model) :
    (fragmentModel m).variables.map (fun d => (d.name, (d.type, true))) =
      m.variables.map (fun d => (d.name, (d.type, true))) := by
  rw [fragment_variables_eq, List.map_map]
  apply List.map_congr_left
  intro d _
  simp [expandInitDecl_fst_name, expandInitDecl_fst_type,
    substParamVarDecl_name, substParamVarDecl_type]

theorem staticEnv_fragment (m : Model) :
    (fragmentModel m).staticEnv = m.staticEnv := by
  unfold Model.staticEnv
  rw [show (fragmentModel m).parameters = m.parameters from rfl,
    fragment_variables_static]

theorem substParams_variables_static (m : Model) :
    (substParamsModel m).variables.map (fun d => (d.name, (d.type, true))) =
      m.variables.map (fun d => (d.name, (d.type, true))) := by
  rw [substParams_variables_eq, List.map_map]
  apply List.map_congr_left
  intro d _
  simp [substParamVarDecl_name, substParamVarDecl_type]

theorem staticEnv_substParams (m : Model) :
    (substParamsModel m).staticEnv = m.staticEnv := by
  unfold Model.staticEnv
  rw [show (substParamsModel m).parameters = m.parameters from rfl,
    substParams_variables_static]

theorem expandInit_variables_static (m : Model) :
    (expandInitModel m).variables.map (fun d => (d.name, (d.type, true))) =
      m.variables.map (fun d => (d.name, (d.type, true))) := by
  rw [expandInit_variables_eq, List.map_map]
  apply List.map_congr_left
  intro d _
  simp [expandInitDecl_fst_name, expandInitDecl_fst_type]

theorem staticEnv_expandInit (m : Model) :
    (expandInitModel m).staticEnv = m.staticEnv := by
  unfold Model.staticEnv
  rw [show (expandInitModel m).parameters = m.parameters from rfl,
    expandInit_variables_static]

/-! ## Domains are untouched -/

/-- The dynamic domain condition of one declaration. -/
def varDomainOK (s : Store) : VarDeclItem → Prop
  | .basic ty n _ _ => ∃ v, s n = some v ∧ ty.contains v
  | .array ty n _ _ => ∃ vs, s n = some (.array vs) ∧
      vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v

theorem satisfiesDyn_iff_varDomainOK (pred : PredicateInterpretation)
    (m : Model) (s : Store) :
    SatisfiesDyn pred m s ↔
      (∀ c ∈ m.constraints, c.Holds pred s) ∧
      (∀ d ∈ m.variables, varDomainOK s d) ∧
      (∀ d ∈ m.variables, d.initializerHolds s) := by
  unfold SatisfiesDyn
  constructor
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩
  · rintro ⟨h1, h2, h3⟩
    exact ⟨h1, h2, h3⟩

theorem substParamVarDecl_domain (env : Store) (s : Store) (d : VarDeclItem) :
    varDomainOK s (substParamVarDecl env d) ↔ varDomainOK s d := by
  cases d with
  | basic ty n anns init => cases init <;> rfl
  | array ty n anns es => rfl

theorem expandInitDecl_domain (s : Store) (d : VarDeclItem) :
    varDomainOK s (expandInitDecl d).1 ↔ varDomainOK s d := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => rfl
      | some e =>
          cases hc : initConstraint (.basic ty n anns (some e)) with
          | none => simp [expandInitDecl, hc]
          | some c =>
              simp only [expandInitDecl, hc, Prod.fst]
              rfl
  | array ty n anns es => rfl

/-! ## Scalar parameter typing -/

/-- The environment resolves each name it substitutes to a literal whose
    type is the statically declared parameter type. -/
def EnvStaticTyped (m : Model) (env : Store) : Prop :=
  ∀ x v, env x = some v → ∀ l, scalarLiteral v = some l →
    m.staticEnv x = some (.base l.type, false)

theorem parDeclValue_value {d : ParDeclItem} {v : Value}
    (h : parDeclValue d = some v) : d.value = v := by
  cases d with
  | basic t n l =>
      cases t <;> cases l <;>
        simp_all [parDeclValue, ParDeclItem.value, BasicLiteral.denote]
  | array idx t n lits => simp [parDeclValue] at h

theorem parDeclValue_spec {d : ParDeclItem} {v : Value}
    (h : parDeclValue d = some v) :
    ∃ (t : BasicParType) (n : Ident) (l : BasicLiteral),
      d = .basic t n l ∧ v = l.denote ∧ l.type = t.base := by
  cases d with
  | basic t n lit =>
      cases t <;> cases lit <;> simp [parDeclValue] at h
      · subst h
        exact ⟨.bool, n, .bool _, rfl, rfl, rfl⟩
      · subst h
        exact ⟨.int, n, .int _, rfl, rfl, rfl⟩
  | array idx t n lits => simp [parDeclValue] at h

theorem nodup_append_left' {α : Type} {l1 l2 : List α}
    (h : (l1 ++ l2).Nodup) : l1.Nodup :=
  (List.nodup_append.mp h).1

theorem parEnv_agrees_static {m : Model}
    (hnu : (m.parameters.map ParDeclItem.name ++
      m.variables.map VarDeclItem.name).Nodup) :
    EnvStaticTyped m (parEnv m) := by
  intro x v hv l hl
  unfold parEnv at hv
  split at hv
  · rename_i wl hwl
    have hwlv : wl = v := Option.some.inj hv
    obtain ⟨y, hy, hyname⟩ := lookupIdent_inv_mem x _ wl hwl
    obtain ⟨d, hd, hdmap⟩ := List.mem_filterMap.mp hy
    cases hpd : parDeclValue d with
    | none => rw [hpd] at hdmap; simp at hdmap
    | some w =>
        rw [hpd] at hdmap
        have hpair : (ParDeclItem.name d, w) = (y, wl) := Option.some.inj hdmap
        have hdn : ParDeclItem.name d = y := congrArg Prod.fst hpair
        have hw : w = wl := congrArg Prod.snd hpair
        obtain ⟨t, n, lit, rfl, hwv, htype⟩ := parDeclValue_spec hpd
        -- the store value is the literal's denotation
        have hvlit : v = lit.denote := by
          rw [← hwlv, ← hw, hwv]
        -- scalarLiteral fixes the literal
        have hlit : l = lit := by
          rw [hvlit] at hl
          cases lit with
          | bool b =>
              simpa [scalarLiteral, BasicLiteral.denote] using (Option.some.inj hl).symm
          | int i =>
              simpa [scalarLiteral, BasicLiteral.denote] using (Option.some.inj hl).symm
          | set sl => simp [scalarLiteral, BasicLiteral.denote] at hl
        have hdn' : n = y := by simpa [ParDeclItem.name] using hdn
        have hnx : n = x := ident_eq_of_name (by
          rw [congrArg Ident.name hdn', hyname])
        have hparnu : ((m.parameters.map
            (fun d => (d.name, (d.type, false)))).map Prod.fst).Nodup := by
          rw [List.map_map]
          exact nodup_append_left' hnu
        have hmem : (x, ((FznType.base lit.type), false)) ∈
            m.parameters.map (fun d => (d.name, (d.type, false))) := by
          rw [List.mem_map]
          refine ⟨.basic t n lit, hd, ?_⟩
          simp [hnx, htype, ParDeclItem.name, ParDeclItem.type]
        unfold Model.staticEnv
        rw [hlit]
        rw [lookupIdent_of_mem hparnu hmem]
  · simp at hv

theorem substParamBasic_hasBaseType {m : Model} {env : Store}
    (henv : EnvStaticTyped m env) {b : BasicExpr} {t : BaseType}
    (hb : b.hasBaseType m.staticEnv t) :
    (substParamBasic env b).hasBaseType m.staticEnv t := by
  cases b with
  | lit l => exact hb
  | ident x =>
      simp only [BasicExpr.hasBaseType] at hb ⊢
      cases hx : env x with
      | none =>
          simp only [substParamBasic, hx]
          exact hb
      | some v =>
          cases hsl : scalarLiteral v with
          | none =>
              simp only [substParamBasic, hx, hsl]
              exact hb
          | some l =>
              simp only [substParamBasic, hx, hsl]
              rw [henv x v hx l hsl] at hb
              exact hb

theorem substParamBasic_checkBase {m : Model} {env : Store}
    (henv : EnvStaticTyped m env) {b : BasicExpr} {bt : BasicPredParamType}
    (hb : b.checkBase m.staticEnv bt) :
    (substParamBasic env b).checkBase m.staticEnv bt := by
  cases b with
  | lit l => exact hb
  | ident x =>
      simp only [BasicExpr.checkBase] at hb ⊢
      cases hx : env x with
      | none =>
          simp only [substParamBasic, hx]
          exact hb
      | some v =>
          cases hsl : scalarLiteral v with
          | none =>
              simp only [substParamBasic, hx, hsl]
              exact hb
          | some l =>
              simp only [substParamBasic, hx, hsl]
              rw [henv x v hx l hsl] at hb
              exact hb

theorem substParamBasic_checkArg_array {m : Model} {env : Store}
    (henv : EnvStaticTyped m env) {b : BasicExpr} {idx : PredIndexSet}
    {bt : BasicPredParamType}
    (he : Expr.checkArg m.staticEnv (.basic b) (.array idx bt)) :
    Expr.checkArg m.staticEnv (.basic (substParamBasic env b)) (.array idx bt) := by
  cases b with
  | lit l => simpa [substParamBasic] using he
  | ident x =>
      cases hx : env x with
      | none => simpa [substParamBasic, hx] using he
      | some v =>
          cases hsl : scalarLiteral v with
          | none => simpa [substParamBasic, hx, hsl] using he
          | some l =>
              have hstat := henv x v hx l hsl
              simp only [substParamBasic, hx, hsl]
              simp only [Expr.checkArg] at he
              rw [hstat] at he
              simpa [Expr.checkArg] using he

theorem substParamExpr_checkArg {m : Model} {env : Store}
    (henv : EnvStaticTyped m env) {e : Expr} {pt : PredParamType}
    (he : e.checkArg m.staticEnv pt) :
    (substParamExpr env e).checkArg m.staticEnv pt := by
  cases e with
  | basic b =>
      cases pt with
      | basic bt => exact substParamBasic_checkBase henv he
      | array idx bt => exact substParamBasic_checkArg_array henv he
  | array es =>
      cases pt with
      | basic bt => exact he.elim
      | array idx bt =>
          obtain ⟨hlen, hall⟩ := he
          refine ⟨?_, ?_⟩
          · simpa [substParamExpr] using hlen
          · intro b hb
            obtain ⟨b0, hb0, rfl⟩ := List.mem_map.mp hb
            exact substParamBasic_checkBase henv (hall b0 hb0)

theorem substParamExpr_checkArg_static {m : Model} {env : Store}
    (henv : EnvStaticTyped m env) {e : Expr} {pt : PredParamType}
    (he : e.checkArg (substParamsModel m).staticEnv pt) :
    (substParamExpr env e).checkArg (substParamsModel m).staticEnv pt := by
  rw [staticEnv_substParams] at he ⊢
  exact substParamExpr_checkArg henv he

theorem forall2_substParamExpr_checkArg {m : Model} {env : Store}
    (henv : EnvStaticTyped m env) :
    ∀ (es : List Expr) (ps : List PredParamType),
      Forall2 (Expr.checkArg m.staticEnv) es ps →
      Forall2 (Expr.checkArg (substParamsModel m).staticEnv)
        (es.map (substParamExpr env)) ps := by
  intro es
  induction es with
  | nil =>
      intro ps h
      cases ps with
      | nil => exact trivial
      | cons p ps => exact h.elim
  | cons e rest ih =>
      intro ps h
      cases ps with
      | nil => exact h.elim
      | cons p ps =>
          have h1 : Expr.checkArg (substParamsModel m).staticEnv e p := by
            rw [staticEnv_substParams]
            exact h.1
          exact ⟨substParamExpr_checkArg_static henv h1, ih ps h.2⟩

theorem substParams_constraints_eq (m : Model) :
    (substParamsModel m).constraints =
      m.constraints.map (substParamConstraint (parEnv m)) := rfl

theorem expandInit_constraints_eq (m : Model) :
    (expandInitModel m).constraints =
      m.constraints ++ (m.variables.map expandInitDecl).flatMap Prod.snd := by
  simp [expandInitModel]

theorem fragment_constraints_eq (m : Model) :
    (fragmentModel m).constraints =
      m.constraints.map (substParamConstraint (parEnv m)) ++
        ((m.variables.map (substParamVarDecl (parEnv m))).map
          expandInitDecl).flatMap Prod.snd := by
  rw [fragmentModel, expandInit_constraints_eq, substParams_constraints_eq,
    substParams_variables_eq]

/-! ## Parameter honesty implies `parEnv` agreement -/

theorem parEnv_sound {m : Model} {s : Store} (h : ParamHonest m s) :
    ∀ x v, parEnv m x = some v → s x = some v := by
  intro x v hv
  unfold parEnv at hv
  split at hv
  · rename_i wl hwl
    have hwlv : wl = v := Option.some.inj hv
    obtain ⟨y, hy, hyname⟩ := lookupIdent_inv_mem x _ wl hwl
    obtain ⟨d, hd, hdmap⟩ := List.mem_filterMap.mp hy
    cases hpd : parDeclValue d with
    | none => rw [hpd] at hdmap; simp at hdmap
    | some w =>
        rw [hpd] at hdmap
        have hpair : (ParDeclItem.name d, w) = (y, wl) := Option.some.inj hdmap
        have hdn : ParDeclItem.name d = y := congrArg Prod.fst hpair
        have hw : w = wl := congrArg Prod.snd hpair
        have hstore : s (ParDeclItem.name d) = some w := by
          have h' := h d hd
          rw [parDeclValue_value hpd] at h'
          exact h'
        have hyx : y = x := ident_eq_of_name hyname
        rw [hdn, hyx, hw, hwlv] at hstore
        exact hstore
  · simp at hv

/-! ## Model-level equivalence -/

theorem fragment_satisfiesDyn {m : Model} {s : Store}
    (henv : ∀ x v, parEnv m x = some v → s x = some v) :
    SatisfiesDyn fullInterp m s ↔
      SatisfiesDyn fullInterp (fragmentModel m) s := by
  rw [satisfiesDyn_iff_varDomainOK, satisfiesDyn_iff_varDomainOK]
  constructor
  · rintro ⟨hcons, hvars, hinit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      rw [fragment_constraints_eq] at hc
      rcases List.mem_append.mp hc with hc1 | hc2
      · obtain ⟨c0, hc0, rfl⟩ := List.mem_map.mp hc1
        exact (substParamConstraint_holds henv c0).mp (hcons c0 hc0)
      · obtain ⟨p, hp, hpc⟩ := List.mem_flatMap.mp hc2
        obtain ⟨dsub, hdsub, rfl⟩ := List.mem_map.mp hp
        obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hdsub
        have hsub : (substParamVarDecl (parEnv m) d).initializerHolds s :=
          (substParamVarDecl_initializer henv d).mp (hinit d hd)
        exact ((expandInitDecl_holds (substParamVarDecl (parEnv m) d) s).mp hsub).2
          c hpc
    · intro d' hd'
      rw [fragment_variables_eq] at hd'
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
      exact (expandInitDecl_domain s _).mpr
        ((substParamVarDecl_domain (parEnv m) s d).mpr (hvars d hd))
    · intro d' hd'
      rw [fragment_variables_eq] at hd'
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
      have hsub : (substParamVarDecl (parEnv m) d).initializerHolds s :=
        (substParamVarDecl_initializer henv d).mp (hinit d hd)
      exact ((expandInitDecl_holds (substParamVarDecl (parEnv m) d) s).mp hsub).1
  · rintro ⟨hcons, hvars, hinit⟩
    refine ⟨?_, ?_, ?_⟩
    · intro c hc
      have hc1 : substParamConstraint (parEnv m) c ∈
          (substParamsModel m).constraints :=
        List.mem_map.mpr ⟨c, hc, rfl⟩
      have hc2 : substParamConstraint (parEnv m) c ∈
          (fragmentModel m).constraints := by
        rw [fragment_constraints_eq]
        exact List.mem_append.mpr (Or.inl hc1)
      exact (substParamConstraint_holds henv c).mpr (hcons _ hc2)
    · intro d hd
      have hd'mem : (expandInitDecl (substParamVarDecl (parEnv m) d)).1 ∈
          (fragmentModel m).variables := by
        rw [fragment_variables_eq]
        exact List.mem_map.mpr ⟨d, hd, rfl⟩
      exact (substParamVarDecl_domain (parEnv m) s d).mp
        ((expandInitDecl_domain s _).mp (hvars _ hd'mem))
    · intro d hd
      have hdsub : substParamVarDecl (parEnv m) d ∈
          (substParamsModel m).variables :=
        List.mem_map.mpr ⟨d, hd, rfl⟩
      have hd'mem : (expandInitDecl (substParamVarDecl (parEnv m) d)).1 ∈
          (fragmentModel m).variables := by
        rw [fragment_variables_eq]
        exact List.mem_map.mpr ⟨d, hd, rfl⟩
      have hinit' :
          (expandInitDecl (substParamVarDecl (parEnv m) d)).1.initializerHolds s :=
        hinit _ hd'mem
      have hem : ∀ c ∈ (expandInitDecl (substParamVarDecl (parEnv m) d)).2,
          c.Holds fullInterp s := by
        intro c hc
        apply hcons c
        rw [fragment_constraints_eq]
        exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr
          ⟨expandInitDecl (substParamVarDecl (parEnv m) d),
            List.mem_map.mpr ⟨substParamVarDecl (parEnv m) d, hdsub, rfl⟩, hc⟩))
      exact (substParamVarDecl_initializer henv d).mpr
        ((expandInitDecl_holds (substParamVarDecl (parEnv m) d) s).mpr
          ⟨hinit', hem⟩)

theorem fragment_covers {m : Model} {s : Store}
    (henv : ∀ x v, parEnv m x = some v → s x = some v)
    (hsat : SatisfiesDyn fullInterp m s) :
    SatisfiesDyn fullInterp (fragmentModel m) s :=
  (fragment_satisfiesDyn henv).mp hsat

theorem fragment_exact {m : Model} {s : Store}
    (henv : ∀ x v, parEnv m x = some v → s x = some v)
    (hsat : SatisfiesDyn fullInterp (fragmentModel m) s) :
    SatisfiesDyn fullInterp m s :=
  (fragment_satisfiesDyn henv).mpr hsat

/-! ## Well-formedness -/

theorem lookupIdent_none_of_forall {β : Type} {x : Ident} :
    ∀ {l : List (Ident × β)},
    (∀ p ∈ l, p.1.name ≠ x.name) → lookupIdent x l = none := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons ab rest ih =>
      intro h
      obtain ⟨y', v'⟩ := ab
      have hne : x.name ≠ y'.name := fun e => h (y', v') List.mem_cons_self e.symm
      rw [lookupIdent_cons_ne hne]
      exact ih (fun p hp => h p (List.mem_cons_of_mem _ hp))

theorem staticEnv_var_of_mem {sig : SigEnv} {m : Model} (hwf : WellFormed sig m)
    {d : VarDeclItem} (hd : d ∈ m.variables) :
    m.staticEnv d.name = some (d.type, true) := by
  have hnu := hwf.valueNamesUnique
  unfold Model.staticEnv
  have hk : ((m.variables.map (fun d => (d.name, (d.type, true)))).map
      Prod.fst).Nodup := by
    rw [List.map_map]
    exact (List.nodup_append.mp hnu).2.1
  have hnone : lookupIdent d.name (m.parameters.map
      (fun d => (d.name, (d.type, false)))) = none := by
    apply lookupIdent_none_of_forall
    intro p hp hpn
    obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hp
    exact (List.nodup_append.mp hnu).2.2 _
      (List.mem_map.mpr ⟨d', hd', rfl⟩) _
      (List.mem_map.mpr ⟨d, hd, rfl⟩) (ident_eq_of_name hpn)
  rw [hnone]
  exact lookupIdent_of_mem hk (List.mem_map.mpr ⟨d, hd, rfl⟩)

theorem expandInit_variables_names (m : Model) :
    (expandInitModel m).variables.map VarDeclItem.name =
      m.variables.map VarDeclItem.name := by
  rw [expandInit_variables_eq, List.map_map]
  apply List.map_congr_left
  intro d _
  exact expandInitDecl_fst_name d

theorem intEq_sig : fullSig (Ident.mk "int_eq") =
    some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  simp [fullSig, globalsSig, stdSig]

theorem boolNot_sig : fullSig (Ident.mk "bool_not") =
    some [.basic (.var (.par .bool)), .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

theorem intEqConstraint_checkArg {m : Model} {ty : BasicVarType} {n : Ident}
    {anns : List Annotation} {k : Int}
    (hwf : WellFormed fullSig m)
    (hd : (.basic ty n anns (some (.lit (.int k))) : VarDeclItem) ∈ m.variables)
    (hty : ty.base = .int) :
    Forall2 (Expr.checkArg m.staticEnv) (intEqConstraint n k).args
      [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  have hstatic := staticEnv_var_of_mem hwf hd
  have hst : m.staticEnv n = some (.base .int, true) := by
    simpa [VarDeclItem.name, VarDeclItem.type, hty] using hstatic
  change Expr.checkArg m.staticEnv (.basic (.ident n))
      (.basic (.var (.par .int))) ∧
    Expr.checkArg m.staticEnv (.basic (.lit (.int k)))
      (.basic (.var (.par .int))) ∧ True
  refine ⟨?_, ?_, trivial⟩
  · simp [Expr.checkArg, BasicExpr.checkBase, BasicPredParamType.accepts,
      BasicPredParamType.baseType, BasicVarType.base, BasicPredParamType.isPar,
      BasicParType.base, hst]
  · simp [Expr.checkArg, BasicExpr.checkBase, BasicPredParamType.accepts,
      BasicPredParamType.baseType, BasicVarType.base, BasicPredParamType.isPar,
      BasicParType.base, BasicLiteral.type]

theorem boolNotConstraint_checkArg {m : Model} {ty : BasicVarType}
    {n : Ident} {anns : List Annotation} {b : Bool}
    (hwf : WellFormed fullSig m)
    (hd : (.basic ty n anns (some (.lit (.bool b))) : VarDeclItem) ∈ m.variables)
    (hty : ty.base = .bool) :
    Forall2 (Expr.checkArg m.staticEnv) (boolNotConstraint n b).args
      [.basic (.var (.par .bool)), .basic (.var (.par .bool))] := by
  have hstatic := staticEnv_var_of_mem hwf hd
  have hst : m.staticEnv n = some (.base .bool, true) := by
    simpa [VarDeclItem.name, VarDeclItem.type, hty] using hstatic
  change Expr.checkArg m.staticEnv (.basic (.ident n))
      (.basic (.var (.par .bool))) ∧
    Expr.checkArg m.staticEnv (.basic (.lit (.bool (!b))))
      (.basic (.var (.par .bool))) ∧ True
  refine ⟨?_, ?_, trivial⟩
  · simp [Expr.checkArg, BasicExpr.checkBase, BasicPredParamType.accepts,
      BasicPredParamType.baseType, BasicVarType.base, BasicPredParamType.isPar,
      BasicParType.base, hst]
  · simp [Expr.checkArg, BasicExpr.checkBase, BasicPredParamType.accepts,
      BasicPredParamType.baseType, BasicVarType.base, BasicPredParamType.isPar,
      BasicParType.base, BasicLiteral.type]

theorem wf_substParams {m : Model} (hwf : WellFormed fullSig m) :
    WellFormed fullSig (substParamsModel m) := by
  have htyped : EnvStaticTyped m (parEnv m) :=
    parEnv_agrees_static hwf.valueNamesUnique
  refine
    { predNamesUnique := hwf.predNamesUnique
      valueNamesUnique := ?_
      predParamsUnique := hwf.predParamsUnique
      parameterTypes := hwf.parameterTypes
      variableArrayLengths := ?_
      variableInitializers := ?_
      objectiveType := ?_
      constraintsChecked := ?_ }
  · rw [substParams_variables_eq, List.map_map]
    simpa [substParamsModel, Function.comp_def, substParamVarDecl_name] using
      hwf.valueNamesUnique
  · intro d hd
    rw [substParams_variables_eq] at hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    cases d0 with
    | basic ty n anns init =>
        cases init with
        | none => simp [substParamVarDecl]
        | some e => simp [substParamVarDecl]
    | array ty n anns es =>
        simpa [substParamVarDecl] using hwf.variableArrayLengths _ hd0
  · intro d hd
    rw [substParams_variables_eq] at hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    cases d0 with
    | array ty n anns es =>
        intro v hv
        rw [staticEnv_substParams]
        exact hwf.variableInitializers _ hd0 v hv
    | basic ty n anns init =>
        cases init with
        | none => trivial
        | some e =>
            rw [staticEnv_substParams]
            exact substParamBasic_hasBaseType htyped
              (hwf.variableInitializers _ hd0)
  · have h := hwf.objectiveType
    rw [← staticEnv_substParams m] at h
    simpa [substParamsModel] using h
  · intro c' hc'
    rw [substParams_constraints_eq] at hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨params, hsig, hF⟩ := hwf.constraintsChecked c hc
    exact ⟨params, hsig, forall2_substParamExpr_checkArg htyped c.args params hF⟩

theorem wf_expandInit {m : Model} (hwf : WellFormed fullSig m)
    (hpred : m.predicates = []) :
    WellFormed fullSig (expandInitModel m) := by
  refine
    { predNamesUnique := hwf.predNamesUnique
      valueNamesUnique := ?_
      predParamsUnique := hwf.predParamsUnique
      parameterTypes := hwf.parameterTypes
      variableArrayLengths := ?_
      variableInitializers := ?_
      objectiveType := ?_
      constraintsChecked := ?_ }
  · rw [expandInit_variables_names]
    exact hwf.valueNamesUnique
  · intro d' hd'
    rw [expandInit_variables_eq] at hd'
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd'
    cases d0 with
    | basic ty n anns init =>
        cases init with
        | none => simp [expandInitDecl]
        | some e =>
            cases hc : initConstraint (.basic ty n anns (some e)) <;>
              simp [expandInitDecl, hc]
    | array ty n anns es =>
        simpa [expandInitDecl] using hwf.variableArrayLengths _ hd0
  · intro d' hd'
    rw [expandInit_variables_eq] at hd'
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd'
    cases d0 with
    | array ty n anns es =>
        intro v hv
        rw [staticEnv_expandInit]
        exact hwf.variableInitializers _ hd0 v hv
    | basic ty n anns init =>
        cases init with
        | none => trivial
        | some e =>
            cases hc : initConstraint (.basic ty n anns (some e)) with
            | some c =>
                simp only [expandInitDecl, hc]
            | none =>
                simp only [expandInitDecl, hc]
                rw [staticEnv_expandInit]
                exact hwf.variableInitializers _ hd0
  · have h := hwf.objectiveType
    rw [← staticEnv_expandInit m] at h
    simpa [expandInitModel] using h
  · intro c' hc'
    rw [expandInit_constraints_eq] at hc'
    rcases List.mem_append.mp hc' with hc1 | hc2
    · obtain ⟨params, hsig, hF⟩ := hwf.constraintsChecked c' hc1
      exact ⟨params, hsig, by simpa [staticEnv_expandInit] using hF⟩
    · obtain ⟨p, hp, hpc⟩ := List.mem_flatMap.mp hc2
      obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hp
      cases d0 with
      | array ty n anns es => simp [expandInitDecl] at hpc
      | basic ty n anns init =>
          cases init with
          | none => simp [expandInitDecl] at hpc
          | some e =>
              cases e with
              | ident x => simp [expandInitDecl, initConstraint] at hpc
              | lit l =>
                  cases l with
                  | set sl => simp [expandInitDecl, initConstraint] at hpc
                  | int k =>
                      by_cases hty : ty.base = .int
                      · have hpc' : c' ∈ [intEqConstraint n k] := by
                          simpa [expandInitDecl, initConstraint, hty,
                            intEqConstraint] using hpc
                        simp only [List.mem_singleton] at hpc'
                        subst hpc'
                        refine ⟨[.basic (.var (.par .int)),
                          .basic (.var (.par .int))], ?_, ?_⟩
                        · have hpred' : (expandInitModel m).predicates = [] := by
                            simpa [expandInitModel] using hpred
                          simpa [expandInitModel, intEqConstraint] using
                            sigEnv_int_eq hpred'
                        · simpa [staticEnv_expandInit] using
                            intEqConstraint_checkArg hwf hd0 hty
                      · simp [expandInitDecl, initConstraint, hty] at hpc
                  | bool b =>
                      by_cases hty : ty.base = .bool
                      · have hpc' : c' ∈ [boolNotConstraint n b] := by
                          simpa [expandInitDecl, initConstraint, hty,
                            boolNotConstraint] using hpc
                        simp only [List.mem_singleton] at hpc'
                        subst hpc'
                        refine ⟨[.basic (.var (.par .bool)),
                          .basic (.var (.par .bool))], ?_, ?_⟩
                        · have hpred' : (expandInitModel m).predicates = [] := by
                            simpa [expandInitModel] using hpred
                          simpa [expandInitModel, boolNotConstraint] using
                            sigEnv_bool_not hpred'
                        · simpa [staticEnv_expandInit] using
                            boolNotConstraint_checkArg hwf hd0 hty
                      · simp [expandInitDecl, initConstraint, hty] at hpc

theorem wf_fragment {m : Model} (hwf : WellFormed fullSig m)
    (hpred : m.predicates = []) :
    WellFormed fullSig (fragmentModel m) := by
  rw [fragmentModel]
  exact wf_expandInit (wf_substParams hwf)
    (by simpa [substParamsModel] using hpred)

end LeanFzn.Compiler
