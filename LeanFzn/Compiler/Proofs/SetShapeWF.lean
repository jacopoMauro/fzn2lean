/-
File: LeanFzn/Compiler/Proofs/SetShapeWF.lean

Purpose:
  Static well-formedness of the set-shape pre-pass (S4–S7).  The pass
  introduces ordinary scalar auxiliary variables and rewrites finite set
  shapes into rows whose signatures are checked against `fullSig`.  This
  file proves that a well-formed source model with no predicate items
  yields a well-formed shape-expanded model.

  The main theorem is `wf_shapeExpand`.  It is used by
  `LeanFzn/Compiler/Proofs/Normalize.lean` to keep the whole compilation
  pipeline statically well-formed.

Dependencies:
  - LeanFzn.Compiler.Proofs.SetShape (shape pass and its semantic proofs).
-/

import LeanFzn.Compiler.Proofs.SetShape

set_option maxHeartbeats 1000000

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Semantics.Globals
open LeanFzn.Solver.Propagation.DomainFiltering

/-! ## Static environment of a shape state -/

/-- The static environment determined by a shape state's declarations. -/
def ShapeState.env (m : Model) (st : ShapeState) : StaticEnv :=
  Model.staticEnv { m with variables := st.decls.reverse ++ m.variables }

/-- `lookupIdent` splits over an append. -/
theorem lookupIdent_append {β : Type} (x : Ident) :
    ∀ (l1 l2 : List (Ident × β)),
      lookupIdent x (l1 ++ l2) =
        (match lookupIdent x l1 with
         | some v => some v
         | none => lookupIdent x l2) := by
  intro l1
  induction l1 with
  | nil => intro l2; rfl
  | cons p rest ih =>
      intro l2
      obtain ⟨y, v⟩ := p
      by_cases h : x.name = y.name
      · simp [lookupIdent, h]
      · simp [lookupIdent, h, ih]

/-- `lookupIdent` skips an appended prefix that does not contain the
    name. -/
theorem lookupIdent_append_of_none {β : Type} {x : Ident}
    {l1 l2 : List (Ident × β)} (h : lookupIdent x l1 = none) :
    lookupIdent x (l1 ++ l2) = lookupIdent x l2 := by
  rw [lookupIdent_append, h]

/-- Skipping a middle block with no matching name. -/
theorem lookupIdent_append_skip {β : Type} {x : Ident}
    {l1 l2 l3 : List (Ident × β)} (h : lookupIdent x l2 = none) :
    lookupIdent x (l1 ++ (l2 ++ l3)) = lookupIdent x (l1 ++ l3) := by
  rw [lookupIdent_append, lookupIdent_append]
  simp only [h]
  rw [← lookupIdent_append]

/-- Duplicate-freeness is invariant under reversal. -/
theorem nodup_reverse_iff {α : Type} {l : List α} : l.reverse.Nodup ↔ l.Nodup := by
  constructor
  · induction l with
    | nil => simp
    | cons a as ih =>
        rw [List.reverse_cons, List.nodup_append]
        rintro ⟨h1, _, h3⟩
        rw [List.nodup_cons]
        refine ⟨?_, ih h1⟩
        intro ha
        exact h3 a (List.mem_reverse.mpr ha) a (by simp) rfl
  · induction l with
    | nil => simp
    | cons a as ih =>
        intro h
        rw [List.reverse_cons, List.nodup_append]
        rw [List.nodup_cons] at h
        refine ⟨ih h.2, by simp, ?_⟩
        intro x hx y hy hxy
        have hx' : x ∈ as := List.mem_reverse.mp hx
        have hy' : y = a := by simpa using hy
        have hxa : x = a := hxy.trans hy'
        exact h.1 (hxa ▸ hx')

/-- A name that is not a parameter name has no parameter lookup. -/
theorem lookupIdent_param_none {m : Model} {n : String}
    (h : ∀ d ∈ m.parameters, d.name.name ≠ n) :
    lookupIdent (Ident.mk n) (m.parameters.map (fun d => (d.name, (d.type, false)))) =
      none := by
  apply lookupIdent_none_of_forall
  intro p hp hpn
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
  exact h d hd (by simpa using hpn)

/-- A declaration list made of auxiliary declarations has duplicate-free
    identifier names. -/
theorem ShapeState.decls_names_nodup {taken : List String} {m : Model}
    {st : ShapeState} (hwf : st.WF taken m) :
    (st.decls.map (fun d => d.name)).Nodup := by
  have h := hwf.auxNodup
  simp only [ShapeState.AuxNodup] at h
  have haux : (st.aux.map (fun a => Ident.mk a.name)).Nodup := by
    have heq : st.aux.map (fun a => Ident.mk a.name) =
        (st.aux.map (fun a => a.name)).map Ident.mk := by
      rw [List.map_map]
      rfl
    rw [heq]
    exact List.Pairwise.map Ident.mk (fun a b hab hf => hab (by simpa using hf)) h
  rw [hwf.auxDecls]
  simpa [List.map_map, Function.comp_def, VarDeclItem.name] using haux

/-- A taken source name reads the same in a well-formed state's static
    environment and in the source model. -/
theorem ShapeState.env_source {taken : List String} {m : Model} {st : ShapeState}
    (hwf : st.WF taken m) {x : Ident} (hx : x.name ∈ taken) :
    st.env m x = m.staticEnv x := by
  have hd : ∀ p ∈ st.decls.reverse.map (fun d => (d.name, (d.type, true))),
      p.1.name ≠ x.name := by
    intro p hp
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    have hdt : d.name.name ∉ taken := by
      rw [hwf.auxDecls] at hd
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hd)
      simpa [VarDeclItem.name] using hwf.namesAvoid a ha
    intro hpn
    exact hdt (hpn ▸ hx)
  unfold ShapeState.env Model.staticEnv
  cases hp : lookupIdent x (m.parameters.map (fun d => (d.name, (d.type, false)))) with
  | some info => rfl
  | none =>
      show lookupIdent x ((st.decls.reverse ++ m.variables).map
          (fun d => (d.name, (d.type, true)))) =
        lookupIdent x (m.variables.map (fun d => (d.name, (d.type, true))))
      rw [List.map_append, lookupIdent_append, lookupIdent_none_of_forall hd]

/-- An auxiliary name has its declared type in a well-formed state's
    static environment. -/
theorem ShapeState.env_aux {taken : List String} {m : Model} {st : ShapeState}
    (hwf : st.WF taken m) (hmwf : WellFormed fullSig m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken) {a : ShapeAux} (ha : a ∈ st.aux) :
    st.env m (Ident.mk a.name) = some (.base a.ty.base, true) := by
  have hname : a.name ∉ taken := hwf.namesAvoid a ha
  have hpar : lookupIdent (Ident.mk a.name)
      (m.parameters.map (fun d => (d.name, (d.type, false)))) = none :=
    lookupIdent_param_none (by
      intro d hd hdn
      have hmem : d.name.name ∈ setTaken m :=
        List.mem_append_left _ (List.mem_map.mpr ⟨d, hd, rfl⟩)
      exact hname (by simpa [hdn] using hsup d.name.name hmem))
  have hdecls_ident : (st.decls.map (fun d => d.name)).Nodup :=
    ShapeState.decls_names_nodup hwf
  have hvars_ident : (m.variables.map (fun d => d.name)).Nodup :=
    (List.nodup_append.mp hmwf.valueNamesUnique).2.1
  have hdisj : ∀ x ∈ st.decls.map (fun d => d.name),
      x ∉ m.variables.map (fun d => d.name) := by
    intro x hx hx'
    obtain ⟨d, hd, hdn⟩ := List.mem_map.mp hx
    have hdt : d.name.name ∉ taken := by
      rw [hwf.auxDecls] at hd
      obtain ⟨a', ha', rfl⟩ := List.mem_map.mp hd
      simpa [VarDeclItem.name] using hwf.namesAvoid a' ha'
    obtain ⟨e, he, hen⟩ := List.mem_map.mp hx'
    exact hdt (by
      rw [hdn]
      exact hen ▸ hsup e.name.name
        (List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)))
  have hnu : (((st.decls.reverse ++ m.variables).map
      (fun d => (d.name, (d.type, true)))).map Prod.fst).Nodup := by
    have heq : ((st.decls.reverse ++ m.variables).map
        (fun d => (d.name, (d.type, true)))).map Prod.fst =
        (st.decls.reverse.map (fun d => d.name)) ++
          (m.variables.map (fun d => d.name)) := by
      simp only [List.map_append, List.map_map, Function.comp_def]
    rw [heq, List.nodup_append]
    refine ⟨?_, hvars_ident, ?_⟩
    · rw [List.map_reverse]
      exact nodup_reverse_iff.mpr hdecls_ident
    · intro x hx y hy hxy
      rw [List.map_reverse, List.mem_reverse] at hx
      exact hdisj x hx (hxy.symm ▸ hy)
  have hdeclmem : (VarDeclItem.basic a.ty (Ident.mk a.name) [] none) ∈ st.decls := by
    rw [hwf.auxDecls]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  have hmem : (Ident.mk a.name, ((.base a.ty.base : FznType), true)) ∈
      (st.decls.reverse ++ m.variables).map
        (fun d => (d.name, (d.type, true))) := by
    rw [List.map_append]
    apply List.mem_append_left
    exact List.mem_map.mpr
      ⟨_, List.mem_reverse.mpr hdeclmem, by simp [VarDeclItem.name, VarDeclItem.type]⟩
  unfold ShapeState.env Model.staticEnv
  rw [hpar]
  exact lookupIdent_of_mem hnu hmem

/-- The static environment of a state is unchanged at a taken name or an
    older auxiliary name when extra newer auxiliaries are added. -/
theorem ShapeState.env_extends {taken : List String} {m : Model}
    {st st' : ShapeState} (hwf : st.WF taken m) (hwf' : st'.WF taken m)
    (haux : ∃ extra, st'.aux = extra ++ st.aux) {x : Ident}
    (hx : x.name ∈ taken ∨ x.name ∈ st.aux.map (fun a => a.name)) :
    st'.env m x = st.env m x := by
  obtain ⟨extra, hextra⟩ := haux
  have hdecl : st'.decls =
      extra.map (fun a => VarDeclItem.basic a.ty (Ident.mk a.name) [] none) ++
        st.decls := by
    rw [hwf'.auxDecls, hwf.auxDecls, hextra, List.map_append]
  have hnone : lookupIdent x
      ((extra.map
        (fun a => VarDeclItem.basic a.ty (Ident.mk a.name) [] none)).reverse.map
        (fun d => (d.name, (d.type, true)))) = none := by
    apply lookupIdent_none_of_forall
    intro p hp hpn
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hd)
    have hpn' : a.name = x.name := by simpa [VarDeclItem.name] using hpn
    rcases hx with htake | hold
    · exact hwf'.namesAvoid a (by rw [hextra]; exact List.mem_append_left _ ha)
        (by rw [hpn']; exact htake)
    · have hnd := hwf'.auxNodup
      simp only [ShapeState.AuxNodup] at hnd
      rw [hextra, List.map_append, List.nodup_append] at hnd
      exact (hnd.2.2 a.name (List.mem_map.mpr ⟨a, ha, rfl⟩) x.name hold) hpn'
  unfold ShapeState.env Model.staticEnv
  cases hp : lookupIdent x (m.parameters.map (fun d => (d.name, (d.type, false)))) with
  | some info => rfl
  | none =>
      show lookupIdent x ((st'.decls.reverse ++ m.variables).map
          (fun d => (d.name, (d.type, true)))) =
        lookupIdent x ((st.decls.reverse ++ m.variables).map
          (fun d => (d.name, (d.type, true))))
      have hmap : (st'.decls.reverse ++ m.variables).map
          (fun d => (d.name, (d.type, true))) =
          (st.decls.reverse.map (fun d => (d.name, (d.type, true)))) ++
            (((extra.map
              (fun a => VarDeclItem.basic a.ty (Ident.mk a.name) [] none)).reverse.map
                (fun d => (d.name, (d.type, true)))) ++
              m.variables.map (fun d => (d.name, (d.type, true)))) := by
        rw [hdecl, List.reverse_append, List.append_assoc, List.map_append,
          List.map_append]
      rw [hmap, lookupIdent_append_skip hnone, List.map_append]

/-! ## Signature checks for emitted rows -/

theorem fullSig_bool_clause :
    fullSig (Ident.mk "bool_clause") =
      some [.array .int (.var (.par .bool)), .array .int (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_bool_or :
    fullSig (Ident.mk "bool_or") =
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_int_lin_eq :
    fullSig (Ident.mk "int_lin_eq") =
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_int_eq :
    fullSig (Ident.mk "int_eq") =
      some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_int_eq_reif :
    fullSig (Ident.mk "int_eq_reif") =
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_bool_and :
    fullSig (Ident.mk "bool_and") =
      some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_bool2int :
    fullSig (Ident.mk "bool2int") =
      some [.basic (.var (.par .bool)), .basic (.var (.par .int))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_set_in_reif :
    fullSig (Ident.mk "set_in_reif") =
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_set_in :
    fullSig (Ident.mk "set_in") =
      some [.basic (.var (.par .int)), .basic (.var (.par .setOfInt))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_int_le :
    fullSig (Ident.mk "int_le") =
      some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_array_var_bool_element :
    fullSig (Ident.mk "array_var_bool_element") =
      some [.basic (.var (.par .int)), .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_array_var_set_element :
    fullSig (Ident.mk "array_var_set_element") =
      some [.basic (.var (.par .int)), .array .int (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))] := by
  simp [fullSig, globalsSig, stdSig]

/-! ## Argument checks -/

theorem checkArg_bool_name {env : StaticEnv} {x : String}
    (h : ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar)) :
    Expr.checkArg env (shapeE (shapeName x)) (.basic (.var (.par .bool))) := by
  obtain ⟨isVar, hiv⟩ := h
  cases isVar <;>
    simp [shapeE, shapeName, Expr.checkArg, BasicExpr.checkBase, hiv,
      BasicPredParamType.accepts, BasicPredParamType.isPar,
      BasicPredParamType.baseType, BasicVarType.base, BasicParType.base]

theorem checkArg_int_name {env : StaticEnv} {x : String}
    (h : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar)) :
    Expr.checkArg env (shapeE (shapeName x)) (.basic (.var (.par .int))) := by
  obtain ⟨isVar, hiv⟩ := h
  cases isVar <;>
    simp [shapeE, shapeName, Expr.checkArg, BasicExpr.checkBase, hiv,
      BasicPredParamType.accepts, BasicPredParamType.isPar,
      BasicPredParamType.baseType, BasicVarType.base, BasicParType.base]

theorem checkArg_set_name {env : StaticEnv} {x : String}
    (h : ∃ isVar, env (Ident.mk x) = some (.base .setOfInt, isVar)) :
    Expr.checkArg env (shapeE (shapeName x)) (.basic (.var (.par .setOfInt))) := by
  obtain ⟨isVar, hiv⟩ := h
  cases isVar <;>
    simp [shapeE, shapeName, Expr.checkArg, BasicExpr.checkBase, hiv,
      BasicPredParamType.accepts, BasicPredParamType.isPar,
      BasicPredParamType.baseType, BasicVarType.base, BasicParType.base]

theorem checkArg_shape_int_lit {env : StaticEnv} (k : Int) :
    Expr.checkArg env (shapeE (shapeInt k)) (.basic (.var (.par .int))) := by
  simp [shapeE, shapeInt, Expr.checkArg, BasicExpr.checkBase,
    BasicPredParamType.accepts, BasicPredParamType.isPar,
    BasicPredParamType.baseType, BasicLiteral.type, BasicParType.base,
    BasicVarType.base]

theorem checkArg_shape_bool_lit {env : StaticEnv} (b : Bool) :
    Expr.checkArg env (shapeE (shapeBool b)) (.basic (.var (.par .bool))) := by
  simp [shapeE, shapeBool, Expr.checkArg, BasicExpr.checkBase,
    BasicPredParamType.accepts, BasicPredParamType.isPar,
    BasicPredParamType.baseType, BasicLiteral.type, BasicParType.base,
    BasicVarType.base]

theorem checkArg_array_int_lits {env : StaticEnv} (ks : List Int) :
    Expr.checkArg env (.array (ks.map shapeInt)) (.array .int (.par .int)) := by
  simp [Expr.checkArg, PredIndexSet.acceptsLength, BasicExpr.checkBase,
    BasicPredParamType.accepts, BasicPredParamType.isPar,
    BasicPredParamType.baseType, BasicLiteral.type, BasicParType.base,
    BasicVarType.base, shapeInt]

theorem checkArg_array_bool_names {env : StaticEnv} (xs : List String)
    (h : ∀ x ∈ xs, ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar)) :
    Expr.checkArg env (.array (xs.map shapeName)) (.array .int (.var (.par .bool))) := by
  simp only [Expr.checkArg, PredIndexSet.acceptsLength, List.length_map, true_and]
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact checkArg_bool_name (h x hx)

theorem checkArg_array_int_names {env : StaticEnv} (xs : List String)
    (h : ∀ x ∈ xs, ∃ isVar, env (Ident.mk x) = some (.base .int, isVar)) :
    Expr.checkArg env (.array (xs.map shapeName)) (.array .int (.var (.par .int))) := by
  simp only [Expr.checkArg, PredIndexSet.acceptsLength, List.length_map, true_and]
  intro b hb
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hb
  exact checkArg_int_name (h x hx)

/-! ## Row checks -/

theorem boolClause_check {env : StaticEnv} {terms : List String} {target : String}
    (h : ∀ x ∈ terms ++ [target],
      ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env)
      [.array (terms.map shapeName), .array [shapeName target]]
      [.array .int (.var (.par .bool)), .array .int (.var (.par .bool))] := by
  refine ⟨checkArg_array_bool_names _ (fun x hx => h x (List.mem_append_left _ hx)),
    ?_, trivial⟩
  simpa [shapeName] using
    checkArg_array_bool_names [target] (fun x hx => h x (by
      rw [List.mem_singleton] at hx
      subst hx
      exact List.mem_append_right _ (List.mem_singleton_self _)))

theorem boolOr_check {env : StaticEnv} {a b c : String}
    (ha : ∃ isVar, env (Ident.mk a) = some (.base .bool, isVar))
    (hb : ∃ isVar, env (Ident.mk b) = some (.base .bool, isVar))
    (hc : ∃ isVar, env (Ident.mk c) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeName a), shapeE (shapeName b), shapeE (shapeName c)]
      [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))] :=
  ⟨checkArg_bool_name ha, checkArg_bool_name hb, checkArg_bool_name hc, trivial⟩

theorem intLinEq_check {env : StaticEnv} {coeffs : List Int} {vars : List String}
    {rhs : Int} (h : ∀ x ∈ vars, ∃ isVar, env (Ident.mk x) = some (.base .int, isVar)) :
    Forall2 (Expr.checkArg env) (shapeLinEq coeffs vars rhs).args
      [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))] := by
  refine ⟨checkArg_array_int_lits _, checkArg_array_int_names _ h,
    checkArg_shape_int_lit _, trivial⟩

theorem intEq_check {env : StaticEnv} {x : String} {k : Int}
    (h : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeName x), shapeE (shapeInt k)]
      [.basic (.var (.par .int)), .basic (.var (.par .int))] :=
  ⟨checkArg_int_name h, checkArg_shape_int_lit _, trivial⟩

theorem intEqReif_check {env : StaticEnv} {x : String} {k : Int} {n : String}
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeName x), shapeE (shapeInt k), shapeE (shapeName n)]
      [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] :=
  ⟨checkArg_int_name hx, checkArg_shape_int_lit _, checkArg_bool_name hn, trivial⟩

theorem boolAnd_check {env : StaticEnv} {x y n : String}
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar))
    (hy : ∃ isVar, env (Ident.mk y) = some (.base .bool, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeName x), shapeE (shapeName y), shapeE (shapeName n)]
      [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))] :=
  ⟨checkArg_bool_name hx, checkArg_bool_name hy, checkArg_bool_name hn, trivial⟩

theorem bool2int_check {env : StaticEnv} {x n : String}
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .int, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeName x), shapeE (shapeName n)]
      [.basic (.var (.par .bool)), .basic (.var (.par .int))] :=
  ⟨checkArg_bool_name hx, checkArg_int_name hn, trivial⟩

theorem setInReif_check {env : StaticEnv} {v : Int} {S n : String}
    (hS : ∃ isVar, env (Ident.mk S) = some (.base .setOfInt, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeInt v), shapeE (shapeName S), shapeE (shapeName n)]
      [.basic (.var (.par .int)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .bool))] :=
  ⟨checkArg_shape_int_lit _, checkArg_set_name hS, checkArg_bool_name hn, trivial⟩

theorem intLeLitName_check {env : StaticEnv} {x : String} (k : Int)
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeInt k), shapeE (shapeName x)]
      [.basic (.var (.par .int)), .basic (.var (.par .int))] :=
  ⟨checkArg_shape_int_lit k, checkArg_int_name hx, trivial⟩

theorem intLeNameLit_check {env : StaticEnv} {x : String} (k : Int)
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar)) :
    Forall2 (Expr.checkArg env)
      [shapeE (shapeName x), shapeE (shapeInt k)]
      [.basic (.var (.par .int)), .basic (.var (.par .int))] :=
  ⟨checkArg_int_name hx, checkArg_shape_int_lit k, trivial⟩

theorem arrayVarBoolElement_check {env : StaticEnv} {i : BasicExpr}
    {bits : List String} {tv : String}
    (hi : Expr.checkArg env (.basic i) (.basic (.var (.par .int))))
    (hb : ∀ b ∈ bits, ∃ isVar, env (Ident.mk b) = some (.base .bool, isVar))
    (ht : ∃ isVar, env (Ident.mk tv) = some (.base .bool, isVar)) :
    Forall2 (Expr.checkArg env)
      [.basic i, .array (bits.map shapeName), .basic (shapeName tv)]
      [.basic (.var (.par .int)), .array .int (.var (.par .bool)),
        .basic (.var (.par .bool))] :=
  ⟨hi, checkArg_array_bool_names bits hb, checkArg_bool_name ht, trivial⟩


/-! ## Static checking: emitted rows -/

/-- A constraint whose arguments check against the global signature. -/
def ShapeState.ConstraintChecked (env : StaticEnv) (c : ConstraintItem) : Prop :=
  ∃ params, fullSig c.name = some params ∧
    Forall2 (Expr.checkArg env) c.args params

/-- An auxiliary whose defining constraint checks. -/
def ShapeAux.Checkable (env : StaticEnv) (a : ShapeAux) : Prop :=
  ShapeState.ConstraintChecked env a.definition

theorem checkable_member {env : StaticEnv} {S : String} {v : Int} {n : String}
    (hS : ∃ isVar, env (Ident.mk S) = some (.base .setOfInt, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .bool, isVar)) :
    ShapeAux.Checkable env ⟨n, .par .bool, .member S v⟩ :=
  ⟨_, fullSig_set_in_reif, setInReif_check hS hn⟩

theorem checkable_eq {env : StaticEnv} {x : String} {v : Int} {n : String}
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .bool, isVar)) :
    ShapeAux.Checkable env ⟨n, .par .bool, .eq x v⟩ :=
  ⟨_, fullSig_int_eq_reif, intEqReif_check hx hn⟩

theorem checkable_and {env : StaticEnv} {x y n : String}
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar))
    (hy : ∃ isVar, env (Ident.mk y) = some (.base .bool, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .bool, isVar)) :
    ShapeAux.Checkable env ⟨n, .par .bool, .and x y⟩ :=
  ⟨_, fullSig_bool_and, boolAnd_check hx hy hn⟩

theorem checkable_bit {env : StaticEnv} {x n : String}
    (hx : ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar))
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .int, isVar)) :
    ShapeAux.Checkable env ⟨n, .intRange 0 1, .bit x⟩ :=
  ⟨_, fullSig_bool2int, bool2int_check hx hn⟩

theorem checkable_const {env : StaticEnv} {v : Bool} {n : String}
    (hn : ∃ isVar, env (Ident.mk n) = some (.base .bool, isVar)) :
    ShapeAux.Checkable env ⟨n, .par .bool, .const v⟩ := by
  refine ⟨_, fullSig_bool_not, ?_⟩
  exact ⟨checkArg_bool_name hn, checkArg_shape_bool_lit _, trivial⟩

/-- Every row emitted by the range checks is checked, given that the index
    itself is a checked integer expression. -/
theorem shapeRangeChecks_checked {env : StaticEnv} {i : BasicExpr} {n : Nat}
    (hi : Expr.checkArg env (.basic i) (.basic (.var (.par .int)))) :
    ∀ c ∈ shapeRangeChecks i n, ShapeState.ConstraintChecked env c := by
  intro c hc
  cases i with
  | ident x =>
      have hx : ∃ isVar, env x = some (.base .int, isVar) :=
        staticEnv_int_of_checkArg hi
      have h1 : ShapeState.ConstraintChecked env
          (shapeConstraint "int_le" [shapeE (shapeInt 1), shapeE (.ident x)]) :=
        ⟨_, fullSig_int_le, by
          simpa [shapeConstraint, shapeE, shapeName] using
            intLeLitName_check (env := env) (x := x.name) 1 hx⟩
      have h2 : ShapeState.ConstraintChecked env
          (shapeConstraint "int_le"
            [shapeE (.ident x), shapeE (shapeInt (n : Int))]) :=
        ⟨_, fullSig_int_le, by
          simpa [shapeConstraint, shapeE, shapeName] using
            intLeNameLit_check (env := env) (x := x.name) (n : Int) hx⟩
      have hmem : c = shapeConstraint "int_le"
            [shapeE (shapeInt 1), shapeE (.ident x)] ∨
          c = shapeConstraint "int_le"
            [shapeE (.ident x), shapeE (shapeInt (n : Int))] := by
        simpa [shapeRangeChecks] using hc
      rcases hmem with rfl | rfl
      · exact h1
      · exact h2
  | lit l =>
      cases l with
      | int k =>
          by_cases hk : 1 ≤ k ∧ k ≤ (n : Int)
          · have hnil : shapeRangeChecks (.lit (.int k)) n = [] := by
              simp [shapeRangeChecks, hk]
            rw [hnil] at hc
            cases hc
          · have hsingle : shapeRangeChecks (.lit (.int k)) n = [falseConstraint] := by
              simp [shapeRangeChecks, hk]
            rw [hsingle] at hc
            rw [List.mem_singleton] at hc
            subst hc
            exact ⟨_, falseConstraint_sig, falseConstraint_check env⟩
      | bool b =>
          simp [Expr.checkArg, BasicExpr.checkBase, BasicPredParamType.accepts,
            BasicPredParamType.baseType, BasicPredParamType.isPar,
            BasicLiteral.type, BasicVarType.base, BasicParType.base] at hi
      | set sl =>
          simp [Expr.checkArg, BasicExpr.checkBase, BasicPredParamType.accepts,
            BasicPredParamType.baseType, BasicPredParamType.isPar,
            BasicLiteral.type, BasicVarType.base, BasicParType.base] at hi

/-- One emitted Boolean element row is checked. -/
theorem arrayElemRow_checked {env : StaticEnv} {i : BasicExpr}
    {bits : List String} {tv : String}
    (hi : Expr.checkArg env (.basic i) (.basic (.var (.par .int))))
    (hb : ∀ b ∈ bits, ∃ isVar, env (Ident.mk b) = some (.base .bool, isVar))
    (ht : ∃ isVar, env (Ident.mk tv) = some (.base .bool, isVar)) :
    ShapeState.ConstraintChecked env (arrayElemRow i bits tv) :=
  ⟨_, fullSig_array_var_bool_element, by
    simpa [arrayElemRow, shapeConstraint, shapeE] using
      arrayVarBoolElement_check (env := env) (i := i) (bits := bits) (tv := tv)
        hi hb ht⟩

/-- The environment entry of a Boolean auxiliary. -/
theorem env_bool_of_aux {env : StaticEnv} {st : ShapeState} {n : String} {k : ShapeKind}
    (henvAux : ∀ a ∈ st.aux, env (Ident.mk a.name) = some (.base a.ty.base, true))
    (h : (⟨n, .par .bool, k⟩ : ShapeAux) ∈ st.aux) :
    env (Ident.mk n) = some (.base .bool, true) := by
  have := henvAux _ h
  simpa [BasicVarType.base, BasicParType.base] using this

/-- The environment entry of a `0..1` integer auxiliary. -/
theorem env_int01_of_aux {env : StaticEnv} {st : ShapeState} {n : String} {k : ShapeKind}
    (henvAux : ∀ a ∈ st.aux, env (Ident.mk a.name) = some (.base a.ty.base, true))
    (h : (⟨n, .intRange 0 1, k⟩ : ShapeAux) ∈ st.aux) :
    env (Ident.mk n) = some (.base .int, true) := by
  have := henvAux _ h
  simpa [BasicVarType.base] using this

/-- The environment entry of a Boolean auxiliary, located by name and type. -/
theorem env_bool_of_aux_name {env : StaticEnv} {st : ShapeState} {n : String}
    (henvAux : ∀ a ∈ st.aux, env (Ident.mk a.name) = some (.base a.ty.base, true))
    (h : ∃ c ∈ st.aux, c.name = n ∧ c.ty = .par .bool) :
    env (Ident.mk n) = some (.base .bool, true) := by
  obtain ⟨c, hc, hcn, hct⟩ := h
  rcases c with ⟨cn, cty, ck⟩
  have h1 := henvAux _ hc
  simp only at hcn hct
  subst hcn
  subst hct
  simpa [BasicVarType.base, BasicParType.base] using h1

/-- The environment entry of a `0..1` integer auxiliary, located by name
    and type. -/
theorem env_int01_of_aux_name {env : StaticEnv} {st : ShapeState} {n : String}
    (henvAux : ∀ a ∈ st.aux, env (Ident.mk a.name) = some (.base a.ty.base, true))
    (h : ∃ c ∈ st.aux, c.name = n ∧ c.ty = .intRange 0 1) :
    env (Ident.mk n) = some (.base .int, true) := by
  obtain ⟨c, hc, hcn, hct⟩ := h
  rcases c with ⟨cn, cty, ck⟩
  have h1 := henvAux _ hc
  simp only at hcn hct
  subst hcn
  subst hct
  simpa [BasicVarType.base] using h1

/-! ## Source declarations in the static environment -/

/-- A declared set variable is set-typed in the source static
    environment. -/
theorem modelSetUniverse?_staticEnv {m : Model} (hwf : WellFormed fullSig m)
    {S : String} {us : List Int} (h : modelSetUniverse? m S = some us) :
    m.staticEnv (Ident.mk S) = some (.base .setOfInt, true) := by
  obtain ⟨ty, anns, init, hd, hun⟩ := modelSetUniverse?_some h
  have hs := staticEnv_var_of_mem hwf hd
  have hbase : ty.base = .setOfInt := setUniverse?_base hun
  simpa [VarDeclItem.name, VarDeclItem.type, hbase] using hs

/-- A declared finite integer variable is int-typed in the source static
    environment. -/
theorem modelIntValues?_staticEnv {m : Model} (hwf : WellFormed fullSig m)
    {x : String} {vals : List Int} (h : modelIntValues? m x = some vals) :
    m.staticEnv (Ident.mk x) = some (.base .int, true) := by
  obtain ⟨ty, anns, init, hd, hv⟩ := modelIntValues?_some h
  have hs := staticEnv_var_of_mem hwf hd
  have hbase : ty.base = .int := by
    cases ty with
    | par t => exact absurd hv (by simp [finiteIntValues?])
    | intRange lo hi => rfl
    | intSet xs => rfl
    | setOfIntRange lo hi => exact absurd hv (by simp [finiteIntValues?])
    | setOfIntSet xs => exact absurd hv (by simp [finiteIntValues?])
  simpa [VarDeclItem.name, VarDeclItem.type, hbase] using hs

/-- A declared set variable's name is taken. -/
theorem modelSetUniverse?_taken {m : Model} {S : String} {us : List Int}
    (h : modelSetUniverse? m S = some us) : S ∈ setTaken m := by
  obtain ⟨ty, anns, init, hd, _⟩ := modelSetUniverse?_some h
  exact List.mem_append_right _ (List.mem_map.mpr
    ⟨.basic ty (Ident.mk S) anns init, hd, by simp [VarDeclItem.name]⟩)

/-- A declared finite integer variable's name is taken. -/
theorem modelIntValues?_taken {m : Model} {x : String} {vals : List Int}
    (h : modelIntValues? m x = some vals) : x ∈ setTaken m := by
  obtain ⟨ty, anns, init, hd, _⟩ := modelIntValues?_some h
  exact List.mem_append_right _ (List.mem_map.mpr
    ⟨.basic ty (Ident.mk x) anns init, hd, by simp [VarDeclItem.name]⟩)

/-- The environment of a declared set name. -/
theorem env_set_of_source {env : StaticEnv} {m : Model} {taken : List String}
    (hwf : WellFormed fullSig m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (hsrcenv : ∀ x ∈ taken, env (Ident.mk x) = m.staticEnv (Ident.mk x))
    {S : String} {us : List Int} (h : modelSetUniverse? m S = some us) :
    env (Ident.mk S) = some (.base .setOfInt, true) := by
  rw [hsrcenv S (hsup S (modelSetUniverse?_taken h))]
  exact modelSetUniverse?_staticEnv hwf h

/-- The environment of a declared finite integer name. -/
theorem env_int_of_source {env : StaticEnv} {m : Model} {taken : List String}
    (hwf : WellFormed fullSig m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (hsrcenv : ∀ x ∈ taken, env (Ident.mk x) = m.staticEnv (Ident.mk x))
    {x : String} {vals : List Int} (h : modelIntValues? m x = some vals) :
    env (Ident.mk x) = some (.base .int, true) := by
  rw [hsrcenv x (hsup x (modelIntValues?_taken h))]
  exact modelIntValues?_staticEnv hwf h

/-! ## Checking is closed under the state operations -/

/-- Every constraint accumulated in a state is checked. -/
def ShapeState.CheckedIn (env : StaticEnv) (st : ShapeState) : Prop :=
  ∀ c ∈ st.cons, ShapeState.ConstraintChecked env c

/-- Every constraint of `st'` is an old constraint or checks in `env`. -/
def ShapeState.NewChecked (env : StaticEnv) (st st' : ShapeState) : Prop :=
  ∀ c ∈ st'.cons, c ∈ st.cons ∨ ShapeState.ConstraintChecked env c

theorem ShapeState.checkedIn_of_new {env : StaticEnv} {st st' : ShapeState}
    (h : st.CheckedIn env) (hn : st.NewChecked env st') : st'.CheckedIn env := by
  intro c hc
  rcases hn c hc with hc' | hc'
  · exact h c hc'
  · exact hc'

theorem ShapeState.newChecked_trans {env : StaticEnv} {st st' st'' : ShapeState}
    (h1 : st.NewChecked env st') (h2 : st'.NewChecked env st'') :
    st.NewChecked env st'' := by
  intro c hc
  rcases h2 c hc with hc' | hc'
  · exact h1 c hc'
  · exact Or.inr hc'

theorem ShapeState.newChecked_emit {env : StaticEnv} {st : ShapeState}
    {c : ConstraintItem} (hc : ShapeState.ConstraintChecked env c) :
    st.NewChecked env (st.emit c) := by
  intro c' hc'
  simp only [ShapeState.emit, List.mem_cons] at hc'
  rcases hc' with rfl | hc'
  · exact Or.inr hc
  · exact Or.inl hc'

theorem ShapeState.newChecked_emitList {env : StaticEnv} {st : ShapeState}
    {cs : List ConstraintItem}
    (hall : ∀ c ∈ cs, ShapeState.ConstraintChecked env c) :
    st.NewChecked env (st.emitList cs) := by
  intro c' hc'
  simp only [ShapeState.emitList, List.mem_append, List.mem_reverse] at hc'
  rcases hc' with hc' | hc'
  · exact Or.inr (hall c' hc')
  · exact Or.inl hc'

/-- A fresh auxiliary (or a cache hit) adds only its checked defining
    constraint. -/
theorem ShapeState.freshAux_newChecked {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState} {env : StaticEnv}
    (h : st.freshAux taken kind = (n, st'))
    (hc : st.CacheOk)
    (ha : ShapeAux.Checkable env ⟨n, kind.ty, kind⟩) :
    st.NewChecked env st' := by
  rcases hc' : st.cache.get? kind with _ | m
  · rw [ShapeState.freshAux_miss hc'] at h
    intro c hc''
    rw [ShapeState.allocAux_cons h] at hc''
    rcases List.mem_cons.mp hc'' with rfl | hc'''
    · exact Or.inr ha
    · exact Or.inl hc'''
  · rw [ShapeState.freshAux_hit hc'] at h
    obtain ⟨rfl, rfl⟩ := h
    intro c hc''
    exact Or.inl hc''

theorem ShapeState.freshBool_newChecked {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState} {env : StaticEnv}
    (h : st.freshBool taken kind = (n, st'))
    (hc : st.CacheOk)
    (ha : ShapeAux.Checkable env ⟨n, kind.ty, kind⟩) :
    st.NewChecked env st' :=
  ShapeState.freshAux_newChecked h hc ha

theorem ShapeState.freshInt01_newChecked {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState} {env : StaticEnv}
    (h : st.freshInt01 taken kind = (n, st'))
    (hc : st.CacheOk)
    (ha : ShapeAux.Checkable env ⟨n, kind.ty, kind⟩) :
    st.NewChecked env st' :=
  ShapeState.freshAux_newChecked h hc ha

/-- The empty cache of the initial shape state is consistent. -/
theorem ShapeState.initial_cacheOk (taken : List String) :
    (ShapeState.initial taken).CacheOk := by
  intro k n hk
  simp [ShapeState.initial] at hk

/-- Emitting one constraint does not change the cache. -/
theorem ShapeState.emit_cacheOk {st : ShapeState} {c : ConstraintItem}
    (hc : st.CacheOk) : (st.emit c).CacheOk := hc

/-- Emitting constraints does not change the cache. -/
theorem ShapeState.emitList_cacheOk {st : ShapeState} {cs : List ConstraintItem}
    (hc : st.CacheOk) : (st.emitList cs).CacheOk := hc

/-- Linking terms does not change the cache. -/
theorem ShapeState.linkOr_cacheOk {st : ShapeState} {terms : List String} {target : String}
    (hc : st.CacheOk) : (linkOr st terms target).CacheOk := by
  unfold linkOr
  split
  · exact hc
  · exact hc

/-! ### Cache-consistency of the allocating helpers -/

theorem memberTerm_cacheOk {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState}
    (h : memberTerm taken m st sa v = some (n, st')) (hc : st.CacheOk) :
    st'.CacheOk := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              by_cases hv : v ∈ us
              · simp only [memberTerm, hus, if_pos hv] at h
                exact ShapeState.freshAux_cacheOk (Option.some.inj h) hc
              · simp only [memberTerm, hus, if_neg hv] at h
                exact ShapeState.freshAux_cacheOk (Option.some.inj h) hc
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm] at h
              exact ShapeState.freshAux_cacheOk (Option.some.inj h) hc
  | array es => simp [memberTerm] at h

theorem varMemberTerms_cacheOk {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    (h : varMemberTerms taken m x s st vals = some (terms, st')) (hc : st.CacheOk) :
    st'.CacheOk := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      exact ih hr (ShapeState.freshAux_cacheOk ha
        (memberTerm_cacheOk hm (ShapeState.freshAux_cacheOk hfb hc)))

theorem resultTarget_cacheOk {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState}
    (h : resultTarget taken st r = some (n, st')) (hc : st.CacheOk) :
    st'.CacheOk := by
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact hc
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · exact ShapeState.freshAux_cacheOk
              (Option.some.inj (by simpa [resultTarget] using h)) hc
          · exact ShapeState.freshAux_cacheOk
              (Option.some.inj (by simpa [resultTarget] using h)) hc
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

theorem cardBits_cacheOk {taken : List String} {m : Model} {s : String}
    {st : ShapeState} {vals : List Int} {cs : List String} {st' : ShapeState}
    (h : cardBits taken m s st vals = some (cs, st')) (hc : st.CacheOk) :
    st'.CacheOk := by
  induction vals generalizing st cs st' with
  | nil =>
      simp only [cardBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  | cons v vs ih =>
      simp only [cardBits] at h
      cases hm : memberTerm taken m st (.basic (.ident (Ident.mk s))) v with
      | none => simp [hm] at h
      | some p =>
          obtain ⟨a, st1⟩ := p
          cases hb : st1.freshInt01 taken (.bit a) with
          | mk c st2 =>
              cases hr : cardBits taken m s st2 vs with
              | none => simp [hm, hb, hr] at h
              | some q =>
                  obtain ⟨cs, st3⟩ := q
                  simp only [hm, hb, hr, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ih hr (ShapeState.freshAux_cacheOk hb
                    (memberTerm_cacheOk hm hc))

theorem unionRows_cacheOk {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (h : unionRows taken m a b c st vals = some st') (hc : st.CacheOk) :
    st'.CacheOk := by
  induction vals generalizing st st' with
  | nil =>
      simp only [unionRows, Option.some.injEq] at h
      subst h
      exact hc
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        unionRows_cons_decomp h
      exact ih hr (ShapeState.emit_cacheOk (memberTerm_cacheOk hm3
        (memberTerm_cacheOk hm2 (memberTerm_cacheOk hm1 hc))))

theorem intersectRows_cacheOk {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (h : intersectRows taken m a b c st vals = some st') (hc : st.CacheOk) :
    st'.CacheOk := by
  induction vals generalizing st st' with
  | nil =>
      simp only [intersectRows, Option.some.injEq] at h
      subst h
      exact hc
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        intersectRows_cons_decomp h
      exact ih hr (ShapeState.emit_cacheOk (memberTerm_cacheOk hm3
        (memberTerm_cacheOk hm2 (memberTerm_cacheOk hm1 hc))))

theorem arrayElemBits_cacheOk {taken : List String} {m : Model} {v : Int} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      arrayElemBits taken m es st v = some (bits, st') →
      st.CacheOk → st'.CacheOk := by
  intro es
  induction es with
  | nil =>
      intro st bits st' h hc
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  | cons e rest ih =>
      intro st bits st' h hc
      simp only [arrayElemBits] at h
      cases hm : memberTerm taken m st (.basic e) v with
      | none => simp only [hm] at h; simp at h
      | some p =>
          obtain ⟨b, st1⟩ := p
          simp only [hm] at h
          cases hr : arrayElemBits taken m rest st1 v with
          | none => simp only [hr] at h; simp at h
          | some q =>
              obtain ⟨bs, st2⟩ := q
              simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ih st1 bs st2 hr (memberTerm_cacheOk hm hc)

theorem arrayElemRows_cacheOk {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState),
      arrayElemRows taken m i es T st vals = some (rows, st') →
      st.CacheOk → st'.CacheOk := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' h hc
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  | cons v vs ih =>
      intro st rows st' h hc
      simp only [arrayElemRows] at h
      cases hb : arrayElemBits taken m es st v with
      | none => simp only [hb] at h; simp at h
      | some p =>
          obtain ⟨bits, st1⟩ := p
          simp only [hb] at h
          cases hm : memberTerm taken m st1 (.basic (.ident (Ident.mk T))) v with
          | none => simp only [hm] at h; simp at h
          | some q =>
              obtain ⟨tv, st2⟩ := q
              simp only [hm] at h
              cases hr : arrayElemRows taken m i es T st2 vs with
              | none => simp only [hr] at h; simp at h
              | some r =>
                  obtain ⟨rows', st3⟩ := r
                  simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ih st2 rows' st3 hr (memberTerm_cacheOk hm
                    (arrayElemBits_cacheOk es st bits st1 hb hc))

theorem rewriteVarMember_cacheOk {taken : List String} {m : Model} {st : ShapeState}
    {x s : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteVarMember taken m st x s vals r = some (st', cs')) (hc : st.CacheOk) :
    st'.CacheOk := by
  obtain ⟨tms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  exact ShapeState.linkOr_cacheOk (resultTarget_cacheOk hres
    (varMemberTerms_cacheOk hterms hc))

theorem rewriteCard_cacheOk {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {k : BasicExpr} {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteCard taken m st S k = some (st', cs')) (hc : st.CacheOk) :
    st'.CacheOk := by
  unfold rewriteCard at h
  cases hm : modelSetUniverse? m S with
  | none =>
      simp only [hm, Option.getD_none, List.isEmpty_nil, ite_true] at h
      cases k with
      | ident kn =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hc
      | lit l =>
          cases l with
          | int j =>
              by_cases hj : j = 0
              · simp only [hj, ite_true] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact hc
              · simp only [if_neg hj] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact hc
          | bool b => simp at h
          | set sl => simp at h
  | some us' =>
      rw [hm] at h
      simp only [Option.getD_some] at h
      cases us' with
      | nil =>
          simp only [List.isEmpty_nil, ite_true] at h
          cases k with
          | ident kn =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact hc
          | lit l =>
              cases l with
              | int j =>
                  by_cases hj : j = 0
                  · simp only [hj, ite_true] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact hc
                  · simp only [if_neg hj] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact hc
              | bool b => simp at h
              | set sl => simp at h
      | cons u us =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
          cases hb : cardBits taken m S st (u :: us) with
          | none => simp [hb] at h
          | some p =>
              obtain ⟨cs, st1⟩ := p
              simp only [hb] at h
              cases k with
              | ident kn =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ShapeState.emit_cacheOk (cardBits_cacheOk hb hc)
              | lit l =>
                  cases l with
                  | int j =>
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact ShapeState.emit_cacheOk (cardBits_cacheOk hb hc)
                  | bool b => simp at h
                  | set sl => simp at h

theorem rewriteUnion_cacheOk {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs')) (hc : st.CacheOk) :
    st'.CacheOk := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteUnion_decomp h
  exact unionRows_cacheOk hr hc

theorem rewriteIntersect_cacheOk {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs'))
    (hc : st.CacheOk) : st'.CacheOk := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteIntersect_decomp h
  exact intersectRows_cacheOk hr hc

theorem rewriteArrayElem_cacheOk {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteArrayElem taken m st i es T = some (st', cs')) (hc : st.CacheOk) :
    st'.CacheOk := by
  obtain ⟨vals, rows, hvals, hrows, hcs⟩ := rewriteArrayElem_decomp h
  exact arrayElemRows_cacheOk vals st rows st' hrows hc

theorem shapeRewriteConstraint_cacheOk {taken : List String} {m : Model}
    {st : ShapeState} {c : ConstraintItem} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : shapeRewriteConstraint taken m st c = some (st', cs')) (hc : st.CacheOk) :
    st'.CacheOk := by
  rcases c with ⟨nm, args, anns⟩
  unfold shapeRewriteConstraint at h
  split at h
  case h_1 =>
    rename_i xarg sarg rarg hnm hargs
    have hnm' : nm = Ident.mk "set_in_reif" := ident_eq_of_name hnm
    have hargs' : args = [.basic xarg, .basic sarg, .basic rarg] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i S
      split at h
      case h_1 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hc
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_cacheOk h hc
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hc
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
    case h_3 => simp at h
  case h_2 =>
    rename_i xarg sarg hnm hargs
    have hnm' : nm = Ident.mk "set_in" := ident_eq_of_name hnm
    have hargs' : args = [.basic xarg, .basic sarg] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i S
      split at h
      case h_1 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hc
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_cacheOk h hc
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hc
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
    case h_3 => simp at h
  case h_3 =>
    rename_i sarg karg hnm hargs
    have hnm' : nm = Ident.mk "set_card" := ident_eq_of_name hnm
    have hargs' : args = [.basic sarg, .basic karg] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i S
      split at h
      case h_1 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hc
      case h_2 =>
        rename_i us hus
        exact rewriteCard_cacheOk h hc
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
    case h_3 => simp at h
  case h_4 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_union" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteUnion_cacheOk h hc
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  case h_5 =>
    rename_i iarg es targ hnm hargs
    have hnm' : nm = Ident.mk "array_var_set_element" := ident_eq_of_name hnm
    have hargs' : args = [.basic iarg, .array es, .basic targ] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i T
      split at h
      case h_1 =>
        rename_i i
        split at h
        case h_1 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hc
        case h_2 =>
          rename_i vals hvals
          exact rewriteArrayElem_cacheOk h hc
      case h_2 =>
        rename_i x
        split at h
        case h_1 =>
          rename_i vals hvals
          split at h
          case h_1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hc
          case h_2 =>
            rename_i us hus
            exact rewriteArrayElem_cacheOk h hc
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hc
      case h_3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hc
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  case h_6 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_intersect" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteIntersect_cacheOk h hc
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  case h_7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hc

/-! ## The per-shape checking lemmas -/
theorem checked_of_source {m : Model} {c : ConstraintItem}
    {taken : List String} {env : StaticEnv}
    (hcheckM : ∃ params, fullSig c.name = some params ∧
      Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hnames : ∀ x ∈ constraintNames c, x ∈ taken)
    (hsrcenv : ∀ x ∈ taken, env (Ident.mk x) = m.staticEnv (Ident.mk x)) :
    ShapeState.ConstraintChecked env c := by
  obtain ⟨params, hsig, hfor⟩ := hcheckM
  refine ⟨params, hsig, ?_⟩
  exact forall2_checkArg_staticEnv_eq hfor (fun e he x hx =>
    hsrcenv x (hnames x (by
      simp only [constraintNames, List.mem_flatMap]
      exact ⟨e, he, hx⟩)))

/-! ## The per-shape checking lemmas -/

theorem memberTerm_newChecked {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState} {env : StaticEnv}
    (h : memberTerm taken m st sa v = some (n, st'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (hsrcenv : ∀ x ∈ taken, env (Ident.mk x) = m.staticEnv (Ident.mk x))
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env st' := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              have hS : env (Ident.mk S.name) = some (.base .setOfInt, true) :=
                env_set_of_source hwf hsup hsrcenv hus
              by_cases hv : v ∈ us
              · simp only [memberTerm, hus, if_pos hv] at h
                have hf : st.freshBool taken (.member S.name v) = (n, st') :=
                  Option.some.inj h
                have haux : (⟨n, .par .bool, .member S.name v⟩ : ShapeAux) ∈ st'.aux := by
                  exact ShapeState.freshAux_aux_mem hf hc
                exact ShapeState.freshBool_newChecked hf hc
                  (checkable_member ⟨true, hS⟩ ⟨true, env_bool_of_aux henvAux haux⟩)
              · simp only [memberTerm, hus, if_neg hv] at h
                have hf : st.freshBool taken (.const false) = (n, st') :=
                  Option.some.inj h
                have haux : (⟨n, .par .bool, .const false⟩ : ShapeAux) ∈ st'.aux := by
                  exact ShapeState.freshAux_aux_mem hf hc
                exact ShapeState.freshBool_newChecked hf hc
                  (checkable_const ⟨true, env_bool_of_aux henvAux haux⟩)
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm] at h
              have hf : st.freshBool taken (.const (decide (sl.denote.Contains v))) =
                  (n, st') := Option.some.inj h
              have haux : (⟨n, .par .bool, .const (decide (sl.denote.Contains v))⟩ :
                  ShapeAux) ∈ st'.aux := by
                exact ShapeState.freshAux_aux_mem hf hc
              exact ShapeState.freshBool_newChecked hf hc
                (checkable_const ⟨true, env_bool_of_aux henvAux haux⟩)
  | array es => simp [memberTerm] at h

/-- Every term allocated by `varMemberTerms` is a Boolean auxiliary of
    the resulting state. -/
theorem varMemberTerms_terms_ty {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    (h : varMemberTerms taken m x s st vals = some (terms, st'))
    (hc : st.CacheOk) :
    ∀ t ∈ terms, ∃ c ∈ st'.aux, c.name = t ∧ c.ty = .par .bool := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro t ht
      cases ht
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      have hc1 : st1.CacheOk := ShapeState.freshAux_cacheOk hfb hc
      have hc2 : st2.CacheOk := memberTerm_cacheOk hm hc1
      have hc3 : st3.CacheOk := ShapeState.freshAux_cacheOk ha hc2
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · exact ⟨⟨u, .par .bool, .and e a⟩, by
          apply varMemberTerms_aux_subset hr
          exact ShapeState.freshAux_aux_mem ha hc2, rfl, rfl⟩
      · exact ih hr hc3 u hu

theorem varMemberTerms_newChecked {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    {env : StaticEnv}
    (h : varMemberTerms taken m x s st vals = some (terms, st'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (hxint : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar))
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env st' := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      exact Or.inl hc
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      have hc1 : st1.CacheOk := ShapeState.freshAux_cacheOk hfb hc
      have hc2 : st2.CacheOk := memberTerm_cacheOk hm hc1
      have hc3 : st3.CacheOk := ShapeState.freshAux_cacheOk ha hc2
      have hep : (⟨e, .par .bool, .eq x v⟩ : ShapeAux) ∈ st'.aux := by
        apply varMemberTerms_aux_subset hr
        apply ShapeState.freshBool_aux_subset ha
        apply memberTerm_aux_subset hm
        exact ShapeState.freshAux_aux_mem hfb hc
      have heint : env (Ident.mk e) = some (.base .bool, true) :=
        env_bool_of_aux henvAux hep
      have hap : ∃ c ∈ st'.aux, c.name = a ∧ c.ty = .par .bool := by
        obtain ⟨c, hc', hcn, hct⟩ := memberTerm_aux hm hc1
        exact ⟨c, varMemberTerms_aux_subset hr c
          (ShapeState.freshBool_aux_subset ha c hc'), hcn, hct⟩
      have haint : env (Ident.mk a) = some (.base .bool, true) :=
        env_bool_of_aux_name henvAux hap
      have htp : (⟨t, .par .bool, .and e a⟩ : ShapeAux) ∈ st'.aux := by
        apply varMemberTerms_aux_subset hr
        exact ShapeState.freshAux_aux_mem ha hc2
      have htint : env (Ident.mk t) = some (.base .bool, true) :=
        env_bool_of_aux henvAux htp
      have henv2 : ∀ b ∈ st2.aux, env (Ident.mk b.name) = some (.base b.ty.base, true) :=
        fun b hb => henvAux b (varMemberTerms_aux_subset hr b
          (ShapeState.freshBool_aux_subset ha b hb))
      exact ShapeState.newChecked_trans
        (ShapeState.freshBool_newChecked hfb hc (checkable_eq hxint ⟨true, heint⟩))
        (ShapeState.newChecked_trans
          (memberTerm_newChecked hm hc1 hwf hsup hsrcenv henv2)
          (ShapeState.newChecked_trans
            (ShapeState.freshBool_newChecked ha hc2
              (checkable_and ⟨true, heint⟩ ⟨true, haint⟩ ⟨true, htint⟩))
            (ih hr hc3 henvAux)))

theorem resultTarget_newChecked {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState} {env : StaticEnv}
    (h : resultTarget taken st r = some (n, st'))
    (hc : st.CacheOk)
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env st' := by
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      exact Or.inl hc
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget, Option.some.injEq] at h
            have hf : st.freshBool taken (.const false) = (n, st') := h
            have haux : (⟨n, .par .bool, .const false⟩ : ShapeAux) ∈ st'.aux := by
              exact ShapeState.freshAux_aux_mem hf hc
            exact ShapeState.freshBool_newChecked hf hc
              (checkable_const ⟨true, env_bool_of_aux henvAux haux⟩)
          · simp only [resultTarget, Option.some.injEq] at h
            have hf : st.freshBool taken (.const true) = (n, st') := h
            have haux : (⟨n, .par .bool, .const true⟩ : ShapeAux) ∈ st'.aux := by
              exact ShapeState.freshAux_aux_mem hf hc
            exact ShapeState.freshBool_newChecked hf hc
              (checkable_const ⟨true, env_bool_of_aux henvAux haux⟩)
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

theorem linkOr_newChecked {st : ShapeState} {terms : List String} {target : String}
    {env : StaticEnv}
    (h : ∀ x ∈ terms ++ [target],
      ∃ isVar, env (Ident.mk x) = some (.base .bool, isVar)) :
    st.NewChecked env (linkOr st terms target) := by
  cases terms with
  | nil =>
      refine ShapeState.newChecked_emit ?_
      refine ⟨_, fullSig_bool_not, ?_⟩
      exact ⟨checkArg_bool_name (h target (by simp)),
        checkArg_shape_bool_lit _, trivial⟩
  | cons t ts =>
      apply ShapeState.newChecked_emitList
      intro c hc
      simp only [List.mem_cons, List.mem_map] at hc
      rcases hc with rfl | ⟨u, hu, rfl⟩
      · exact ⟨_, fullSig_bool_clause, boolClause_check (fun x hx => h x hx)⟩
      · refine ⟨_, fullSig_bool_clause, ?_⟩
        show Forall2 (Expr.checkArg env)
          [.array [shapeName target], .array [shapeName u]]
          [.array .int (.var (.par .bool)), .array .int (.var (.par .bool))]
        refine boolClause_check (terms := [target]) (target := u) (fun x hx => ?_)
        rcases List.mem_append.mp hx with hx | hx
        · rw [List.mem_singleton] at hx
          rw [hx]
          exact h target (List.mem_append_right _ (List.mem_singleton_self _))
        · rw [List.mem_singleton] at hx
          rw [hx]
          rcases hu with rfl | hu
          · exact h u (List.mem_append_left _ (by simp))
          · exact h u (List.mem_append_left _ (List.mem_cons_of_mem _ hu))

theorem fullSig_set_card :
    fullSig (Ident.mk "set_card") =
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .int))] := by
  simp [fullSig, globalsSig, stdSig]

theorem fullSig_set_union :
    fullSig (Ident.mk "set_union") =
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .setOfInt)),
        .basic (.var (.par .setOfInt))] := by
  simp [fullSig, globalsSig, stdSig]

/-- **Static checking of the variable-membership rewrite**: all emitted
    constraints are checked in the fixed environment. -/
theorem rewriteVarMember_newChecked {taken : List String} {m : Model} {st : ShapeState}
    {x S : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem} {env : StaticEnv}
    (h : rewriteVarMember taken m st x S vals r = some (st', cs'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (hxint : ∃ isVar, env (Ident.mk x) = some (.base .int, isVar))
    (hbool : ∀ b : Ident, r = .ident b →
      ∃ isVar, env (Ident.mk b.name) = some (.base .bool, isVar))
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env (st'.emitList cs') := by
  obtain ⟨tms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  have hc1 : st1.CacheOk := varMemberTerms_cacheOk hterms hc
  have hc2 : st2.CacheOk := resultTarget_cacheOk hres hc1
  have henvAux2 : ∀ a ∈ st2.aux, env (Ident.mk a.name) = some (.base a.ty.base, true) :=
    fun a ha => henvAux a (by rw [linkOr_aux]; exact ha)
  have henvAux1 : ∀ a ∈ st1.aux, env (Ident.mk a.name) = some (.base a.ty.base, true) :=
    fun a ha => henvAux2 a (resultTarget_aux_subset hres a ha)
  have htms : ∀ t ∈ tms, ∃ isVar, env (Ident.mk t) = some (.base .bool, isVar) := by
    intro t ht
    obtain ⟨c, hc', hcn, hct⟩ := varMemberTerms_terms_ty hterms hc t ht
    exact ⟨true, env_bool_of_aux_name henvAux1 ⟨c, hc', hcn, hct⟩⟩
  have htarget : ∃ isVar, env (Ident.mk target) = some (.base .bool, isVar) := by
    cases r with
    | ident b =>
        simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at hres
        obtain ⟨rfl, rfl⟩ := hres
        exact hbool b rfl
    | lit l =>
        cases l with
        | bool bb =>
            cases bb
            · simp only [resultTarget, Option.some.injEq] at hres
              have haux : (⟨target, .par .bool, .const false⟩ : ShapeAux) ∈ st2.aux :=
                ShapeState.freshAux_aux_mem hres hc1
              exact ⟨true, env_bool_of_aux henvAux2 haux⟩
            · simp only [resultTarget, Option.some.injEq] at hres
              have haux : (⟨target, .par .bool, .const true⟩ : ShapeAux) ∈ st2.aux :=
                ShapeState.freshAux_aux_mem hres hc1
              exact ⟨true, env_bool_of_aux henvAux2 haux⟩
        | int i => simp [resultTarget] at hres
        | set sl => simp [resultTarget] at hres
  have hchain := ShapeState.newChecked_trans
    (varMemberTerms_newChecked hterms hc hwf hsup hsrcenv hxint henvAux1)
    (ShapeState.newChecked_trans
      (resultTarget_newChecked hres hc1 henvAux2)
      (linkOr_newChecked (st := st2) (terms := tms) (target := target)
        (fun y hy => by
          rcases List.mem_append.mp hy with hy | hy
          · exact htms y hy
          · rw [List.mem_singleton] at hy
            subst hy
            exact htarget)))
  simpa [ShapeState.emitList] using hchain

/-- Every `bool2int` bit allocated by `cardBits` is a `0..1`
    auxiliary of the resulting state. -/
theorem cardBits_bits_ty {taken : List String} {m : Model} {s : String}
    {st : ShapeState} {vals : List Int} {cs : List String} {st' : ShapeState}
    (h : cardBits taken m s st vals = some (cs, st'))
    (hc : st.CacheOk) :
    ∀ c ∈ cs, ∃ a ∈ st'.aux, a.name = c ∧ a.ty = .intRange 0 1 := by
  induction vals generalizing st cs st' with
  | nil =>
      simp only [cardBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      cases hc
  | cons v vs ih =>
      simp only [cardBits] at h
      cases hm : memberTerm taken m st (.basic (.ident (Ident.mk s))) v with
      | none => simp [hm] at h
      | some p =>
          obtain ⟨a, st1⟩ := p
          cases hb : st1.freshInt01 taken (.bit a) with
          | mk c0 st2 =>
              cases hr : cardBits taken m s st2 vs with
              | none => simp [hm, hb, hr] at h
              | some q =>
                  obtain ⟨cs0, st3⟩ := q
                  simp only [hm, hb, hr, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hc1 : st1.CacheOk := memberTerm_cacheOk hm hc
                  have hc2 : st2.CacheOk := ShapeState.freshAux_cacheOk hb hc1
                  intro c hmem
                  rcases List.mem_cons.mp hmem with hmem | hmem
                  · rw [hmem]
                    exact ⟨⟨c0, .intRange 0 1, .bit a⟩, by
                      apply cardBits_aux_subset hr
                      exact ShapeState.freshAux_aux_mem hb hc1, rfl, rfl⟩
                  · exact ih hr hc2 c hmem

/-- `cardBits` only adds checked auxiliary definitions. -/
theorem cardBits_newChecked {taken : List String} {m : Model} {s : String}
    {st : ShapeState} {vals : List Int} {cs : List String} {st' : ShapeState}
    {env : StaticEnv}
    (h : cardBits taken m s st vals = some (cs, st'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env st' := by
  induction vals generalizing st cs st' with
  | nil =>
      simp only [cardBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      exact Or.inl hc
  | cons v vs ih =>
      simp only [cardBits] at h
      cases hm : memberTerm taken m st (.basic (.ident (Ident.mk s))) v with
      | none => simp [hm] at h
      | some p =>
          obtain ⟨a, st1⟩ := p
          cases hb : st1.freshInt01 taken (.bit a) with
          | mk c0 st2 =>
              cases hr : cardBits taken m s st2 vs with
              | none => simp [hm, hb, hr] at h
              | some q =>
                  obtain ⟨cs0, st3⟩ := q
                  simp only [hm, hb, hr, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hc1 : st1.CacheOk := memberTerm_cacheOk hm hc
                  have hc2 : st2.CacheOk := ShapeState.freshAux_cacheOk hb hc1
                  have henvAux2 : ∀ a' ∈ st2.aux,
                      env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
                    fun a' ha' => henvAux a' (cardBits_aux_subset hr a' ha')
                  have henvAux1 : ∀ a' ∈ st1.aux,
                      env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
                    fun a' ha' =>
                      henvAux2 a' (ShapeState.freshInt01_aux_subset hb a' ha')
                  have haux : (⟨c0, .intRange 0 1, .bit a⟩ : ShapeAux) ∈ st2.aux :=
                    ShapeState.freshAux_aux_mem hb hc1
                  obtain ⟨ca, hca, hcan, hcat⟩ := memberTerm_aux hm hc
                  have hca2 : ca ∈ st2.aux := ShapeState.freshInt01_aux_subset hb ca hca
                  have haint : env (Ident.mk a) = some (.base .bool, true) :=
                    env_bool_of_aux_name henvAux2 ⟨ca, hca2, hcan, hcat⟩
                  exact ShapeState.newChecked_trans
                    (memberTerm_newChecked hm hc hwf hsup hsrcenv henvAux1)
                    (ShapeState.newChecked_trans
                      (ShapeState.freshInt01_newChecked hb hc1
                        (checkable_bit ⟨true, haint⟩
                          ⟨true, env_int01_of_aux henvAux2 haux⟩))
                      (ih hr hc2 henvAux))

/-- `rewriteCard` introduces only checked constraints. -/
theorem rewriteCard_newChecked {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {k : BasicExpr} {st' : ShapeState} {cs' : List ConstraintItem}
    {env : StaticEnv}
    (h : rewriteCard taken m st S k = some (st', cs'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (hkty : ∀ kn : Ident, k = .ident kn →
      ∃ isVar, env (Ident.mk kn.name) = some (.base .int, isVar))
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env (st'.emitList cs') := by
  unfold rewriteCard at h
  cases hus : (modelSetUniverse? m S).getD [] with
  | nil =>
      rw [hus] at h
      simp only [List.isEmpty_nil, ite_true] at h
      cases k with
      | ident kn =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hrow : ShapeState.ConstraintChecked env
              (shapeConstraint "int_eq"
                [shapeE (shapeName kn.name), shapeE (shapeInt 0)]) := by
            refine ⟨_, fullSig_int_eq, ?_⟩
            simpa [shapeConstraint] using
              intEq_check (env := env) (x := kn.name) (k := 0) (hkty kn rfl)
          simpa [ShapeState.emitList] using ShapeState.newChecked_emit hrow
      | lit l =>
          cases l with
          | int n =>
              by_cases hz : n = 0
              · simp only [hz, ite_true] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                intro c hc
                exact Or.inl (by simpa [ShapeState.emitList] using hc)
              · simp only [hz, ite_false] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hrow : ShapeState.ConstraintChecked env falseConstraint :=
                  ⟨_, falseConstraint_sig, falseConstraint_check env⟩
                simpa [ShapeState.emitList] using ShapeState.newChecked_emit hrow
          | bool b => simp at h
          | set sl => simp at h
  | cons u us =>
      rw [hus] at h
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
      cases hb : cardBits taken m S st (u :: us) with
      | none => simp [hb] at h
      | some p =>
          obtain ⟨cs, st1⟩ := p
          simp only [hb] at h
          cases k with
          | ident kn =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have henvAux1 : ∀ a ∈ st1.aux,
                  env (Ident.mk a.name) = some (.base a.ty.base, true) :=
                fun a ha => henvAux a (by simpa [ShapeState.emit] using ha)
              have hcs : ∀ x ∈ cs, ∃ isVar, env (Ident.mk x) = some (.base .int, isVar) := by
                intro x hx
                obtain ⟨a', ha', ha'n, ha't⟩ := cardBits_bits_ty hb hc x hx
                exact ⟨true, env_int01_of_aux_name henvAux1 ⟨a', ha', ha'n, ha't⟩⟩
              have hrow : ShapeState.ConstraintChecked env
                  (shapeLinEq (cs.map (fun _ => 1) ++ [-1]) (cs ++ [kn.name]) 0) := by
                refine ⟨_, fullSig_int_lin_eq, ?_⟩
                refine intLinEq_check (fun x hx => ?_)
                rcases List.mem_append.mp hx with hx | hx
                · exact hcs x hx
                · rw [List.mem_singleton] at hx
                  subst hx
                  exact hkty kn rfl
              exact ShapeState.newChecked_trans
                (cardBits_newChecked hb hc hwf hsup hsrcenv henvAux1)
                (by simpa [ShapeState.emitList] using ShapeState.newChecked_emit hrow)
          | lit l =>
              cases l with
              | int j =>
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have henvAux1 : ∀ a ∈ st1.aux,
                      env (Ident.mk a.name) = some (.base a.ty.base, true) :=
                    fun a ha => henvAux a (by simpa [ShapeState.emit] using ha)
                  have hcs : ∀ x ∈ cs, ∃ isVar, env (Ident.mk x) = some (.base .int, isVar) := by
                    intro x hx
                    obtain ⟨a', ha', ha'n, ha't⟩ := cardBits_bits_ty hb hc x hx
                    exact ⟨true, env_int01_of_aux_name henvAux1 ⟨a', ha', ha'n, ha't⟩⟩
                  have hrow : ShapeState.ConstraintChecked env
                      (shapeLinEq (cs.map (fun _ => 1)) cs j) := by
                    refine ⟨_, fullSig_int_lin_eq, ?_⟩
                    exact intLinEq_check (fun x hx => hcs x hx)
                  exact ShapeState.newChecked_trans
                    (cardBits_newChecked hb hc hwf hsup hsrcenv henvAux1)
                    (by simpa [ShapeState.emitList] using ShapeState.newChecked_emit hrow)
              | bool b => simp at h
              | set sl => simp at h

/-- `unionRows` only adds checked auxiliary definitions and `bool_or`
    rows. -/
theorem unionRows_newChecked {taken : List String} {m : Model} {a b c : Expr}
    {st st' : ShapeState} {vals : List Int} {env : StaticEnv}
    (h : unionRows taken m a b c st vals = some st')
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (henvAux : ∀ a' ∈ st'.aux, env (Ident.mk a'.name) = some (.base a'.ty.base, true)) :
    st.NewChecked env st' := by
  induction vals generalizing st st' with
  | nil =>
      simp only [unionRows, Option.some.injEq] at h
      subst h
      intro c' hc'
      exact Or.inl hc'
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        unionRows_cons_decomp h
      have hc1 : st1.CacheOk := memberTerm_cacheOk hm1 hc
      have hc2 : st2.CacheOk := memberTerm_cacheOk hm2 hc1
      have hc3 : st3.CacheOk := memberTerm_cacheOk hm3 hc2
      have henvAux3 : ∀ a' ∈ st3.aux,
          env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
        fun a' ha' => henvAux a' (unionRows_aux_subset hr a' ha')
      have henvAux2 : ∀ a' ∈ st2.aux,
          env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
        fun a' ha' => henvAux3 a' (memberTerm_aux_subset hm3 a' ha')
      have henvAux1 : ∀ a' ∈ st1.aux,
          env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
        fun a' ha' => henvAux2 a' (memberTerm_aux_subset hm2 a' ha')
      have hav : ∃ isVar, env (Ident.mk av) = some (.base .bool, isVar) := by
        obtain ⟨ca, hca, hcan, hcat⟩ := memberTerm_aux hm1 hc
        have hca3 : ca ∈ st3.aux :=
          memberTerm_aux_subset hm3 ca (memberTerm_aux_subset hm2 ca hca)
        exact ⟨true, env_bool_of_aux_name henvAux3 ⟨ca, hca3, hcan, hcat⟩⟩
      have hbv : ∃ isVar, env (Ident.mk bv) = some (.base .bool, isVar) := by
        obtain ⟨cb, hcb, hcbn, hcbt⟩ := memberTerm_aux hm2 hc1
        have hcb3 : cb ∈ st3.aux := memberTerm_aux_subset hm3 cb hcb
        exact ⟨true, env_bool_of_aux_name henvAux3 ⟨cb, hcb3, hcbn, hcbt⟩⟩
      have hcv : ∃ isVar, env (Ident.mk cv) = some (.base .bool, isVar) := by
        obtain ⟨cc, hcc, hccn, hcct⟩ := memberTerm_aux hm3 hc2
        exact ⟨true, env_bool_of_aux_name henvAux3 ⟨cc, hcc, hccn, hcct⟩⟩
      have hrow : ShapeState.ConstraintChecked env (unionRow av bv cv) := by
        refine ⟨_, fullSig_bool_or, ?_⟩
        simpa [unionRow, shapeConstraint] using boolOr_check hav hbv hcv
      exact ShapeState.newChecked_trans
        (memberTerm_newChecked hm1 hc hwf hsup hsrcenv henvAux1)
        (ShapeState.newChecked_trans
          (memberTerm_newChecked hm2 hc1 hwf hsup hsrcenv henvAux2)
          (ShapeState.newChecked_trans
            (memberTerm_newChecked hm3 hc2 hwf hsup hsrcenv henvAux3)
            (ShapeState.newChecked_trans
              (ShapeState.newChecked_emit hrow)
              (ih hr hc3 henvAux))))

/-- `rewriteUnion` introduces only checked constraints. -/
theorem rewriteUnion_newChecked {taken : List String} {m : Model}
    {st : ShapeState} {a b c : Expr} {ua ub uc : List Int}
    {st' : ShapeState} {cs' : List ConstraintItem} {env : StaticEnv}
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (henvAux : ∀ a' ∈ st'.aux, env (Ident.mk a'.name) = some (.base a'.ty.base, true)) :
    st.NewChecked env (st'.emitList cs') := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteUnion_decomp h
  simpa [ShapeState.emitList] using
    unionRows_newChecked hr hc hwf hsup hsrcenv henvAux

/-- `intersectRows` only adds checked auxiliary definitions and `bool_and`
    rows. -/
theorem intersectRows_newChecked {taken : List String} {m : Model} {a b c : Expr}
    {st st' : ShapeState} {vals : List Int} {env : StaticEnv}
    (h : intersectRows taken m a b c st vals = some st')
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (henvAux : ∀ a' ∈ st'.aux, env (Ident.mk a'.name) = some (.base a'.ty.base, true)) :
    st.NewChecked env st' := by
  induction vals generalizing st st' with
  | nil =>
      simp only [intersectRows, Option.some.injEq] at h
      subst h
      intro c' hc'
      exact Or.inl hc'
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        intersectRows_cons_decomp h
      have hc1 : st1.CacheOk := memberTerm_cacheOk hm1 hc
      have hc2 : st2.CacheOk := memberTerm_cacheOk hm2 hc1
      have hc3 : st3.CacheOk := memberTerm_cacheOk hm3 hc2
      have henvAux3 : ∀ a' ∈ st3.aux,
          env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
        fun a' ha' => henvAux a' (intersectRows_aux_subset hr a' ha')
      have henvAux2 : ∀ a' ∈ st2.aux,
          env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
        fun a' ha' => henvAux3 a' (memberTerm_aux_subset hm3 a' ha')
      have henvAux1 : ∀ a' ∈ st1.aux,
          env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
        fun a' ha' => henvAux2 a' (memberTerm_aux_subset hm2 a' ha')
      have hav : ∃ isVar, env (Ident.mk av) = some (.base .bool, isVar) := by
        obtain ⟨ca, hca, hcan, hcat⟩ := memberTerm_aux hm1 hc
        have hca3 : ca ∈ st3.aux :=
          memberTerm_aux_subset hm3 ca (memberTerm_aux_subset hm2 ca hca)
        exact ⟨true, env_bool_of_aux_name henvAux3 ⟨ca, hca3, hcan, hcat⟩⟩
      have hbv : ∃ isVar, env (Ident.mk bv) = some (.base .bool, isVar) := by
        obtain ⟨cb, hcb, hcbn, hcbt⟩ := memberTerm_aux hm2 hc1
        have hcb3 : cb ∈ st3.aux := memberTerm_aux_subset hm3 cb hcb
        exact ⟨true, env_bool_of_aux_name henvAux3 ⟨cb, hcb3, hcbn, hcbt⟩⟩
      have hcv : ∃ isVar, env (Ident.mk cv) = some (.base .bool, isVar) := by
        obtain ⟨cc, hcc, hccn, hcct⟩ := memberTerm_aux hm3 hc2
        exact ⟨true, env_bool_of_aux_name henvAux3 ⟨cc, hcc, hccn, hcct⟩⟩
      have hrow : ShapeState.ConstraintChecked env (intersectRow av bv cv) := by
        refine ⟨_, fullSig_bool_and, ?_⟩
        simpa [intersectRow, shapeConstraint] using boolAnd_check hav hbv hcv
      exact ShapeState.newChecked_trans
        (memberTerm_newChecked hm1 hc hwf hsup hsrcenv henvAux1)
        (ShapeState.newChecked_trans
          (memberTerm_newChecked hm2 hc1 hwf hsup hsrcenv henvAux2)
          (ShapeState.newChecked_trans
            (memberTerm_newChecked hm3 hc2 hwf hsup hsrcenv henvAux3)
            (ShapeState.newChecked_trans
              (ShapeState.newChecked_emit hrow)
              (ih hr hc3 henvAux))))

/-- `rewriteIntersect` introduces only checked constraints. -/
theorem rewriteIntersect_newChecked {taken : List String} {m : Model}
    {st : ShapeState} {a b c : Expr} {ua ub uc : List Int}
    {st' : ShapeState} {cs' : List ConstraintItem} {env : StaticEnv}
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (henvAux : ∀ a' ∈ st'.aux, env (Ident.mk a'.name) = some (.base a'.ty.base, true)) :
    st.NewChecked env (st'.emitList cs') := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteIntersect_decomp h
  simpa [ShapeState.emitList] using
    intersectRows_newChecked hr hc hwf hsup hsrcenv henvAux

/-- Every membership bit allocated by `arrayElemBits` is a Boolean
    auxiliary of the resulting state. -/
theorem arrayElemBits_terms_ty {taken : List String} {m : Model} {v : Int} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      arrayElemBits taken m es st v = some (bits, st') →
      st.CacheOk →
      ∀ b ∈ bits, ∃ c ∈ st'.aux, c.name = b ∧ c.ty = .par .bool := by
  intro es
  induction es with
  | nil =>
      intro st bits st' h hc
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro b hb
      cases hb
  | cons e rest ih =>
      intro st bits st' h hc
      simp only [arrayElemBits] at h
      cases hm : memberTerm taken m st (.basic e) v with
      | none => simp only [hm] at h; simp at h
      | some p =>
          obtain ⟨b, st1⟩ := p
          simp only [hm] at h
          cases hr : arrayElemBits taken m rest st1 v with
          | none => simp only [hr] at h; simp at h
          | some q =>
              obtain ⟨bs, st2⟩ := q
              simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hc1 : st1.CacheOk := memberTerm_cacheOk hm hc
              intro c hmem
              rcases List.mem_cons.mp hmem with hmem | hmem
              · rw [hmem]
                obtain ⟨a, ha, han, hat⟩ := memberTerm_aux hm hc
                exact ⟨a, arrayElemBits_aux_subset rest st1 bs st2 hr a ha, han, hat⟩
              · exact ih st1 bs st2 hr hc1 c hmem

/-- `arrayElemBits` only adds checked auxiliary definitions. -/
theorem arrayElemBits_newChecked {taken : List String} {m : Model} {v : Int}
    {env : StaticEnv} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      arrayElemBits taken m es st v = some (bits, st') →
      st.CacheOk →
      WellFormed fullSig m →
      (∀ y ∈ setTaken m, y ∈ taken) →
      (∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y)) →
      (∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) →
      st.NewChecked env st' := by
  intro es
  induction es with
  | nil =>
      intro st bits st' h hc hwf hsup hsrcenv henvAux
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      exact Or.inl hc
  | cons e rest ih =>
      intro st bits st' h hc hwf hsup hsrcenv henvAux
      simp only [arrayElemBits] at h
      cases hm : memberTerm taken m st (.basic e) v with
      | none => simp only [hm] at h; simp at h
      | some p =>
          obtain ⟨b, st1⟩ := p
          simp only [hm] at h
          cases hr : arrayElemBits taken m rest st1 v with
          | none => simp only [hr] at h; simp at h
          | some q =>
              obtain ⟨bs, st2⟩ := q
              simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hc1 : st1.CacheOk := memberTerm_cacheOk hm hc
              have henvAux1 : ∀ a' ∈ st1.aux,
                  env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
                fun a' ha' =>
                  henvAux a' (arrayElemBits_aux_subset rest st1 bs st2 hr a' ha')
              exact ShapeState.newChecked_trans
                (memberTerm_newChecked hm hc hwf hsup hsrcenv henvAux1)
                (ih st1 bs st2 hr hc1 hwf hsup hsrcenv henvAux)

/-- Every membership bit and target bit stored in a row of `arrayElemRows`
    is a Boolean auxiliary of the resulting state. -/
theorem arrayElemRows_terms_ty {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState),
      arrayElemRows taken m i es T st vals = some (rows, st') →
      st.CacheOk →
      ∀ r ∈ rows,
        (∀ b ∈ r.2.1, ∃ c ∈ st'.aux, c.name = b ∧ c.ty = .par .bool) ∧
        ∃ c ∈ st'.aux, c.name = r.2.2 ∧ c.ty = .par .bool := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' h hc
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro r hr
      cases hr
  | cons v vs ih =>
      intro st rows st' h hc
      simp only [arrayElemRows] at h
      cases hb : arrayElemBits taken m es st v with
      | none => simp only [hb] at h; simp at h
      | some p =>
          obtain ⟨bits, st1⟩ := p
          simp only [hb] at h
          cases hm : memberTerm taken m st1 (.basic (.ident (Ident.mk T))) v with
          | none => simp only [hm] at h; simp at h
          | some q =>
              obtain ⟨tv, st2⟩ := q
              simp only [hm] at h
              cases hrec : arrayElemRows taken m i es T st2 vs with
              | none => simp only [hrec] at h; simp at h
              | some r' =>
                  obtain ⟨rows', st3⟩ := r'
                  simp only [hrec, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hcb : st1.CacheOk := arrayElemBits_cacheOk es st bits st1 hb hc
                  have hcm : st2.CacheOk := memberTerm_cacheOk hm hcb
                  intro r hr
                  rcases List.mem_cons.mp hr with rfl | hr'
                  · refine ⟨?_, ?_⟩
                    · intro b hbm
                      obtain ⟨c, hc', hcn, hct⟩ :=
                        arrayElemBits_terms_ty es st bits st1 hb hc b hbm
                      exact ⟨c, arrayElemRows_aux_subset vs st2 rows' st3 hrec c
                        (memberTerm_aux_subset hm c hc'), hcn, hct⟩
                    · obtain ⟨c, hc', hcn, hct⟩ := memberTerm_aux hm hcb
                      exact ⟨c, arrayElemRows_aux_subset vs st2 rows' st3 hrec c hc',
                        hcn, hct⟩
                  · exact ih st2 rows' st3 hrec hcm r hr'

/-- `arrayElemRows` only adds checked auxiliary definitions. -/
theorem arrayElemRows_newChecked {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} {env : StaticEnv} :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState),
      arrayElemRows taken m i es T st vals = some (rows, st') →
      st.CacheOk →
      WellFormed fullSig m →
      (∀ y ∈ setTaken m, y ∈ taken) →
      (∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y)) →
      (∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) →
      st.NewChecked env st' := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' h hc hwf hsup hsrcenv henvAux
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      exact Or.inl hc
  | cons v vs ih =>
      intro st rows st' h hc hwf hsup hsrcenv henvAux
      simp only [arrayElemRows] at h
      cases hb : arrayElemBits taken m es st v with
      | none => simp only [hb] at h; simp at h
      | some p =>
          obtain ⟨bits, st1⟩ := p
          simp only [hb] at h
          cases hm : memberTerm taken m st1 (.basic (.ident (Ident.mk T))) v with
          | none => simp only [hm] at h; simp at h
          | some q =>
              obtain ⟨tv, st2⟩ := q
              simp only [hm] at h
              cases hr : arrayElemRows taken m i es T st2 vs with
              | none => simp only [hr] at h; simp at h
              | some r' =>
                  obtain ⟨rows', st3⟩ := r'
                  simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hcb : st1.CacheOk := arrayElemBits_cacheOk es st bits st1 hb hc
                  have hcm : st2.CacheOk := memberTerm_cacheOk hm hcb
                  have henvAux2 : ∀ a' ∈ st2.aux,
                      env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
                    fun a' ha' =>
                      henvAux a' (arrayElemRows_aux_subset vs st2 rows' st3 hr a' ha')
                  have henvAux1 : ∀ a' ∈ st1.aux,
                      env (Ident.mk a'.name) = some (.base a'.ty.base, true) :=
                    fun a' ha' => henvAux2 a' (memberTerm_aux_subset hm a' ha')
                  exact ShapeState.newChecked_trans
                    (arrayElemBits_newChecked es st bits st1 hb hc hwf hsup hsrcenv henvAux1)
                    (ShapeState.newChecked_trans
                      (memberTerm_newChecked hm hcb hwf hsup hsrcenv henvAux2)
                      (ih st2 rows' st3 hr hcm hwf hsup hsrcenv henvAux))

/-- Every row in an `arrayElemRowList` is checked. -/
theorem arrayElemRowList_checked {env : StaticEnv} {st : ShapeState} {i : BasicExpr}
    {rows : List (Int × List String × String)}
    (hi : Expr.checkArg env (.basic i) (.basic (.var (.par .int))))
    (henvAux : ∀ a ∈ st.aux, env (Ident.mk a.name) = some (.base a.ty.base, true))
    (hrows : ∀ r ∈ rows,
      (∀ b ∈ r.2.1, ∃ c ∈ st.aux, c.name = b ∧ c.ty = .par .bool) ∧
      ∃ c ∈ st.aux, c.name = r.2.2 ∧ c.ty = .par .bool) :
    ∀ c ∈ arrayElemRowList i rows, ShapeState.ConstraintChecked env c := by
  intro c hc
  obtain ⟨r, hr, rfl⟩ := mem_arrayElemRowList_elim hc
  exact arrayElemRow_checked hi
    (fun b hb => ⟨true, env_bool_of_aux_name (n := b) henvAux ((hrows r hr).1 b hb)⟩)
    ⟨true, env_bool_of_aux_name (n := r.2.2) henvAux (hrows r hr).2⟩

/-- `rewriteArrayElem` introduces only checked constraints. -/
theorem rewriteArrayElem_newChecked {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem} {env : StaticEnv}
    (h : rewriteArrayElem taken m st i es T = some (st', cs'))
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (hi : Expr.checkArg env (.basic i) (.basic (.var (.par .int))))
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env (st'.emitList cs') := by
  obtain ⟨vals, rows, hvals, hrows, rfl⟩ := rewriteArrayElem_decomp h
  exact ShapeState.newChecked_trans
    (arrayElemRows_newChecked vals st rows st' hrows hc hwf hsup hsrcenv henvAux)
    (ShapeState.newChecked_emitList (fun c hc' => by
      rcases List.mem_append.mp hc' with hc' | hc'
      · exact arrayElemRowList_checked hi henvAux
          (arrayElemRows_terms_ty vals st rows st' hrows hc) c hc'
      · exact shapeRangeChecks_checked hi c hc'))

/-- **Static checking of the per-constraint rewrite**: using the source
    constraint's signature check, every emitted constraint is checked in
    the fixed environment. -/
theorem shapeRewriteConstraint_newChecked {taken : List String} {m : Model}
    {st : ShapeState} {c : ConstraintItem} {st' : ShapeState}
    {cs' : List ConstraintItem} {env : StaticEnv}
    (h : shapeRewriteConstraint taken m st c = some (st', cs'))
    (hcheck : ShapeState.ConstraintChecked env c)
    (hc : st.CacheOk)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (henvAux : ∀ a ∈ st'.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env (st'.emitList cs') := by
  rcases c with ⟨nm, args, anns⟩
  unfold shapeRewriteConstraint at h
  split at h
  case h_1 =>
    rename_i xarg sarg rarg hnm hargs
    have hnm' : nm = Ident.mk "set_in_reif" := ident_eq_of_name hnm
    have hargs' : args = [.basic xarg, .basic sarg, .basic rarg] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i S
      split at h
      case h_1 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ShapeState.newChecked_emitList (fun d hd => by
          rw [List.mem_singleton] at hd
          subst hd
          exact hcheck)
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            obtain ⟨params, hsig, hfor⟩ := hcheck
            have hparams : params =
                [.basic (.var (.par .int)), .basic (.var (.par .setOfInt)),
                  .basic (.var (.par .bool))] :=
              Option.some.inj (hsig.symm.trans fullSig_set_in_reif)
            subst hparams
            simp only [Forall2] at hfor
            obtain ⟨hxchk, hschk, hrchk, -⟩ := hfor
            exact rewriteVarMember_newChecked h hc hwf hsup hsrcenv
              (staticEnv_int_of_checkArg hxchk)
              (fun b hb => by
                cases hb
                simpa using staticEnv_bool_of_checkArg hrchk)
              henvAux
          case h_2 => simp at h
        case h_2 =>
          rename_i i
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.newChecked_emitList (fun d hd => by
            rw [List.mem_singleton] at hd
            subst hd
            exact hcheck)
        case h_3 => simp at h
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newChecked_emitList (fun d hd => by
        rw [List.mem_singleton] at hd
        subst hd
        exact hcheck)
    case h_3 => simp at h
  case h_2 =>
    rename_i xarg sarg hnm hargs
    have hnm' : nm = Ident.mk "set_in" := ident_eq_of_name hnm
    have hargs' : args = [.basic xarg, .basic sarg] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i S
      split at h
      case h_1 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ShapeState.newChecked_emitList (fun d hd => by
          rw [List.mem_singleton] at hd
          subst hd
          exact hcheck)
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            obtain ⟨params, hsig, hfor⟩ := hcheck
            have hparams : params =
                [.basic (.var (.par .int)), .basic (.var (.par .setOfInt))] :=
              Option.some.inj (hsig.symm.trans fullSig_set_in)
            subst hparams
            simp only [Forall2] at hfor
            obtain ⟨hxchk, hschk, -⟩ := hfor
            exact rewriteVarMember_newChecked h hc hwf hsup hsrcenv
              (staticEnv_int_of_checkArg hxchk)
              (fun b hb => by cases hb)
              henvAux
          case h_2 => simp at h
        case h_2 =>
          rename_i i
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.newChecked_emitList (fun d hd => by
            rw [List.mem_singleton] at hd
            subst hd
            exact hcheck)
        case h_3 => simp at h
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newChecked_emitList (fun d hd => by
        rw [List.mem_singleton] at hd
        subst hd
        exact hcheck)
    case h_3 => simp at h
  case h_3 =>
    rename_i sarg karg hnm hargs
    have hnm' : nm = Ident.mk "set_card" := ident_eq_of_name hnm
    have hargs' : args = [.basic sarg, .basic karg] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i S
      split at h
      case h_1 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ShapeState.newChecked_emitList (fun d hd => by
          rw [List.mem_singleton] at hd
          subst hd
          exact hcheck)
      case h_2 =>
        rename_i us hus
        obtain ⟨params, hsig, hfor⟩ := hcheck
        have hparams : params =
            [.basic (.var (.par .setOfInt)), .basic (.var (.par .int))] :=
          Option.some.inj (hsig.symm.trans fullSig_set_card)
        subst hparams
        simp only [Forall2] at hfor
        obtain ⟨-, hkchk, -⟩ := hfor
        refine rewriteCard_newChecked h hc hwf hsup hsrcenv (fun kn hk => ?_) henvAux
        cases hk
        simpa using staticEnv_int_of_checkArg hkchk
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newChecked_emitList (fun d hd => by
        rw [List.mem_singleton] at hd
        subst hd
        exact hcheck)
    case h_3 => simp at h
  case h_4 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_union" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteUnion_newChecked h hc hwf hsup hsrcenv henvAux
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newChecked_emitList (fun d hd => by
        rw [List.mem_singleton] at hd
        subst hd
        exact hcheck)
  case h_5 =>
    rename_i iarg es targ hnm hargs
    have hnm' : nm = Ident.mk "array_var_set_element" := ident_eq_of_name hnm
    have hargs' : args = [.basic iarg, .array es, .basic targ] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i T
      split at h
      case h_1 =>
        rename_i i
        split at h
        case h_1 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.newChecked_emitList (fun d hd => by
            rw [List.mem_singleton] at hd
            subst hd
            exact hcheck)
        case h_2 =>
          rename_i vals hvals
          obtain ⟨params, hsig, hfor⟩ := hcheck
          have hparams : params =
              [.basic (.var (.par .int)), .array .int (.var (.par .setOfInt)),
                .basic (.var (.par .setOfInt))] :=
            Option.some.inj (hsig.symm.trans fullSig_array_var_set_element)
          subst hparams
          simp only [Forall2] at hfor
          obtain ⟨hichk, -, -, -⟩ := hfor
          exact rewriteArrayElem_newChecked h hc hwf hsup hsrcenv hichk henvAux
      case h_2 =>
        rename_i x
        split at h
        case h_1 =>
          rename_i vals hvals
          split at h
          case h_1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ShapeState.newChecked_emitList (fun d hd => by
              rw [List.mem_singleton] at hd
              subst hd
              exact hcheck)
          case h_2 =>
            rename_i us hus
            obtain ⟨params, hsig, hfor⟩ := hcheck
            have hparams : params =
                [.basic (.var (.par .int)), .array .int (.var (.par .setOfInt)),
                  .basic (.var (.par .setOfInt))] :=
              Option.some.inj (hsig.symm.trans fullSig_array_var_set_element)
            subst hparams
            simp only [Forall2] at hfor
            obtain ⟨hichk, -, -, -⟩ := hfor
            exact rewriteArrayElem_newChecked h hc hwf hsup hsrcenv hichk henvAux
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.newChecked_emitList (fun d hd => by
            rw [List.mem_singleton] at hd
            subst hd
            exact hcheck)
      case h_3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ShapeState.newChecked_emitList (fun d hd => by
          rw [List.mem_singleton] at hd
          subst hd
          exact hcheck)
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newChecked_emitList (fun d hd => by
        rw [List.mem_singleton] at hd
        subst hd
        exact hcheck)
  case h_6 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_intersect" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteIntersect_newChecked h hc hwf hsup hsrcenv henvAux
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newChecked_emitList (fun d hd => by
        rw [List.mem_singleton] at hd
        subst hd
        exact hcheck)
  case h_7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ShapeState.newChecked_emitList (fun d hd => by
      rw [List.mem_singleton] at hd
      subst hd
      exact hcheck)

/-- **The shape traversal preserves static checking** when every source
    constraint is checked in the fixed environment. -/
theorem shapeExpandConstraints_newChecked {taken : List String} {m : Model}
    {cs : List ConstraintItem} {st stF : ShapeState} {env : StaticEnv}
    (h : shapeExpandConstraints taken m cs st = some stF)
    (hchecked : st.CheckedIn env)
    (hc : st.CacheOk)
    (hsource : ∀ c ∈ cs, ShapeState.ConstraintChecked env c)
    (hwf : WellFormed fullSig m)
    (hsup : ∀ y ∈ setTaken m, y ∈ taken)
    (hsrcenv : ∀ y ∈ taken, env (Ident.mk y) = m.staticEnv (Ident.mk y))
    (henvAux : ∀ a ∈ stF.aux, env (Ident.mk a.name) = some (.base a.ty.base, true)) :
    st.NewChecked env stF := by
  induction cs generalizing st with
  | nil =>
      simp only [shapeExpandConstraints, Option.some.injEq] at h
      subst h
      intro c hc
      exact Or.inl hc
  | cons c cs ih =>
      simp only [shapeExpandConstraints] at h
      cases hr : shapeRewriteConstraint taken m st c with
      | none => simp [hr] at h
      | some p =>
          obtain ⟨st1, cs'⟩ := p
          simp only [hr] at h
          have hsub : ∀ a ∈ st1.aux, a ∈ stF.aux := by
            intro a ha
            exact shapeExpandConstraints_aux_subset (st := st1.emitList cs') h a ha
          have henvAux1 : ∀ a ∈ st1.aux,
              env (Ident.mk a.name) = some (.base a.ty.base, true) :=
            fun a ha => henvAux a (hsub a ha)
          have hc1 : st1.CacheOk := shapeRewriteConstraint_cacheOk hr hc
          have hcE : (st1.emitList cs').CacheOk :=
            ShapeState.emitList_cacheOk hc1
          have hnew := shapeRewriteConstraint_newChecked hr (hsource c (by simp))
            hc hwf hsup hsrcenv henvAux1
          have hchecked' : (st1.emitList cs').CheckedIn env :=
            ShapeState.checkedIn_of_new hchecked hnew
          exact ShapeState.newChecked_trans hnew
            (ih h hchecked' hcE (fun c' hc' => hsource c' (List.mem_cons_of_mem _ hc')))

/-- The final shape model's static environment is the state's environment. -/
theorem ShapeExpansion.staticEnv_apply {m : Model} {sh : ShapeExpansion}
    {stF : ShapeState}
    (hpar : sh.model.parameters = m.parameters)
    (hvars : sh.model.variables = stF.decls.reverse ++ m.variables)
    (x : Ident) :
    sh.model.staticEnv x = stF.env m x := by
  unfold ShapeState.env Model.staticEnv
  rw [hpar, hvars]

/-- The final shape model's static environment is the state's environment. -/
theorem ShapeExpansion.staticEnv_eq {m : Model} {sh : ShapeExpansion}
    {stF : ShapeState}
    (hpar : sh.model.parameters = m.parameters)
    (hvars : sh.model.variables = stF.decls.reverse ++ m.variables) :
    sh.model.staticEnv = stF.env m :=
  funext (ShapeExpansion.staticEnv_apply hpar hvars)

/-- Auxiliary declaration names are absent from the source namespace. -/
theorem ShapeState.auxDecl_not_mem {taken : List String} {m : Model}
    {st : ShapeState} (hwf : st.WF taken m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken) :
    ∀ x ∈ st.decls.reverse.map (fun d => d.name), x.name ∉ setTaken m := by
  intro x hx
  rw [List.map_reverse, List.mem_reverse] at hx
  obtain ⟨d, hd, hdn⟩ := List.mem_map.mp hx
  rw [hwf.auxDecls] at hd
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hd
  have hx' : x = Ident.mk a.name := by
    dsimp [VarDeclItem.name] at hdn
    exact hdn.symm
  have hxn : x.name = a.name := congrArg Ident.name hx'
  intro hxset
  exact hwf.namesAvoid a ha (hsup a.name (hxn ▸ hxset))

/-- **Static well-formedness is preserved by the shape pass.** -/
theorem wf_shapeExpand {taken : List String} {m : Model} {sh : ShapeExpansion}
    (hwf : WellFormed fullSig m) (hpred : m.predicates = [])
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : shapeExpandModelWith taken m = some sh) :
    WellFormed fullSig sh.model := by
  obtain ⟨hpar, hpred', hsol, stF, hexp, hvars, hcons, haux⟩ :=
    shapeExpandModelWith_inv h
  have hstwf : stF.WF taken m :=
    shapeExpandConstraints_wf (ShapeState.initial_wf taken m) hwf hsup hexp
  have henv : sh.model.staticEnv = stF.env m :=
    ShapeExpansion.staticEnv_eq hpar hvars
  have hpredsh : sh.model.predicates = [] := by
    rw [hpred']
    exact hpred
  have hsig : sh.model.sigEnv fullSig = fullSig :=
    Model.sigEnv_eq_of_predicates_nil hpredsh
  have hdeclNodup : (stF.decls.reverse.map (fun d => d.name)).Nodup := by
    rw [List.map_reverse]
    exact nodup_reverse_iff.mpr (ShapeState.decls_names_nodup hstwf)
  have hauxNot : ∀ x ∈ stF.decls.reverse.map (fun d => d.name),
      x.name ∉ setTaken m :=
    ShapeState.auxDecl_not_mem hstwf hsup
  have hsetVar : ∀ x ∈ m.variables.map (fun d => d.name),
      x.name ∈ setTaken m := by
    intro x hx
    exact List.mem_append_right _ (by
      obtain ⟨d, hd, hdn⟩ := List.mem_map.mp hx
      exact List.mem_map.mpr ⟨d, hd, congrArg Ident.name hdn⟩)
  refine
    { predNamesUnique := ?_
      valueNamesUnique := ?_
      predParamsUnique := ?_
      parameterTypes := ?_
      variableArrayLengths := ?_
      variableInitializers := ?_
      objectiveType := ?_
      constraintsChecked := ?_ }
  · rw [hpred']
    exact hwf.predNamesUnique
  · rw [hpar, hvars, List.map_append, List.nodup_append]
    refine ⟨(List.nodup_append.mp hwf.valueNamesUnique).1, ?_, ?_⟩
    · rw [List.nodup_append]
      exact ⟨hdeclNodup, (List.nodup_append.mp hwf.valueNamesUnique).2.1,
        fun a ha b hb hab => hauxNot a ha ((congrArg Ident.name hab) ▸ hsetVar b hb)⟩
    · intro a ha b hb hab
      rcases List.mem_append.mp hb with hb' | hb'
      · exact hauxNot b hb' ((congrArg Ident.name hab) ▸
          List.mem_append_left _ (by
            obtain ⟨d, hd, hdn⟩ := List.mem_map.mp ha
            exact List.mem_map.mpr ⟨d, hd, congrArg Ident.name hdn⟩))
      · exact (List.nodup_append.mp hwf.valueNamesUnique).2.2 a ha b hb' hab
  · rw [hpred']
    exact hwf.predParamsUnique
  · rw [hpar]
    exact hwf.parameterTypes
  · intro d hd
    rw [hvars] at hd
    rcases List.mem_append.mp hd with hda | hdv
    · rw [hstwf.auxDecls] at hda
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hda)
      simp
    · exact hwf.variableArrayLengths d hdv
  · intro d hd
    rw [hvars] at hd
    rcases List.mem_append.mp hd with hda | hdv
    · rw [hstwf.auxDecls] at hda
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp (List.mem_reverse.mp hda)
      simp
    · cases d with
      | basic ty n anns init =>
          cases init with
          | none => trivial
          | some e =>
              apply hasBaseType_staticEnv_eq (hwf.variableInitializers _ hdv)
              intro x hx
              rw [henv]
              exact ShapeState.env_source hstwf (hsup x (wf_init_names_taken hwf
                (.basic ty n anns (some e)) hdv x (by simpa [varDeclNames] using hx)))
      | array ty n anns es =>
          intro v hv
          apply hasBaseType_staticEnv_eq (hwf.variableInitializers _ hdv v hv)
          intro x hx
          rw [henv]
          exact ShapeState.env_source hstwf (hsup x (wf_init_names_taken hwf
            (.array ty n anns es) hdv x (by
              simp only [varDeclNames, List.mem_flatMap]
              exact ⟨v, hv, hx⟩)))
  · rw [hsol]
    cases hsw : m.solve with
    | satisfy anns => exact trivial
    | minimize anns e =>
        have hobj : e.hasBaseType m.staticEnv .int := by
          simpa [hsw] using hwf.objectiveType
        apply hasBaseType_staticEnv_eq hobj
        intro x hx
        rw [henv]
        have hxT : x ∈ setTaken m := by
          obtain ⟨info, hinv⟩ := hasBaseType_names hobj x hx
          exact staticEnv_mem_setTaken hinv
        exact ShapeState.env_source hstwf (hsup x hxT)
    | maximize anns e =>
        have hobj : e.hasBaseType m.staticEnv .int := by
          simpa [hsw] using hwf.objectiveType
        apply hasBaseType_staticEnv_eq hobj
        intro x hx
        rw [henv]
        have hxT : x ∈ setTaken m := by
          obtain ⟨info, hinv⟩ := hasBaseType_names hobj x hx
          exact staticEnv_mem_setTaken hinv
        exact ShapeState.env_source hstwf (hsup x hxT)
  · intro c' hc'
    rw [hcons] at hc'
    have hc'F : c' ∈ stF.cons := List.mem_reverse.mp hc'
    have hchecked0 : (ShapeState.initial taken).CheckedIn (stF.env m) := by
      intro c hc
      simp [ShapeState.initial] at hc
    have hsrcsig : m.sigEnv fullSig = fullSig :=
      Model.sigEnv_eq_of_predicates_nil hpred
    have hsource : ∀ c ∈ m.constraints,
        ShapeState.ConstraintChecked (stF.env m) c := by
      intro c hc
      obtain ⟨params, hp, hfor⟩ := hwf.constraintsChecked c hc
      have hp' : fullSig c.name = some params := by
        rw [← hsrcsig]
        exact hp
      exact checked_of_source ⟨params, hp', hfor⟩
        (fun x hx => hsup x (wf_constraint_names_taken hwf c hc x hx))
        (fun x hx => ShapeState.env_source hstwf hx)
    have henvAux : ∀ a ∈ stF.aux,
        (stF.env m) (Ident.mk a.name) = some (.base a.ty.base, true) :=
      fun a ha => ShapeState.env_aux hstwf hwf hsup ha
    have hnew := shapeExpandConstraints_newChecked hexp hchecked0
      (ShapeState.initial_cacheOk taken) hsource hwf hsup
      (fun x hx => ShapeState.env_source hstwf hx) henvAux
    rcases hnew c' hc'F with hmem | hcc
    · simp [ShapeState.initial] at hmem
    · obtain ⟨params, hfull, hfor⟩ := hcc
      refine ⟨params, ?_, ?_⟩
      · rw [hsig]
        exact hfull
      · rw [henv]
        exact hfor

end LeanFzn.Compiler
