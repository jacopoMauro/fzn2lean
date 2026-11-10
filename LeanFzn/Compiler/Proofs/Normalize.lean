/-
File: LeanFzn/Compiler/Proofs/Normalize.lean

Purpose:
  Correctness of the array front end (`Compiler/Normalize.lean`):
  `compileModelFull m = .ok problem` is exact for the ORIGINAL model
  `m` -- an accepted assignment's store (which also gives every array
  name its element-wise value) satisfies every dynamic condition of
  `Satisfies fullSig fullInterp m` and is parameter-honest
  (`compileFull_exact`), and every parameter-honest store satisfying
  the dynamic conditions of `m` is covered by an accepted assignment
  (`compileFull_covers`).  Both reduce to the unchanged
  `compile_exact` / `compile_covers` of the normalized model via the
  inlining equivalence `holds_inline`.

Dependencies:
  - LeanFzn.Compiler.Normalize, LeanFzn.Compiler.Proofs.Exact,
    LeanFzn.Compiler.Proofs.Fragment, LeanFzn.Compiler.Proofs.LiteralFold,
    LeanFzn.Compiler.Proofs.SetIn.
-/

import LeanFzn.Compiler.Normalize
import LeanFzn.Compiler.Proofs.Bounds
import LeanFzn.Compiler.Proofs.Exact
import LeanFzn.Compiler.Proofs.Fragment
import LeanFzn.Compiler.Proofs.LiteralFold
import LeanFzn.Compiler.Proofs.SetExpand
import LeanFzn.Compiler.Proofs.SetShapeWF
import LeanFzn.Compiler.Proofs.SetIn
open LeanFzn.Compiler.Domains

namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Core

/-! ## Generic list lemmas -/

theorem mapM_some_prop {α β : Type} {f : α → Option β} {P : β → Prop} :
    ∀ {l : List α} {vs : List β}, l.mapM f = some vs →
    (∀ a ∈ l, ∀ v, f a = some v → P v) → ∀ v ∈ vs, P v := by
  intro l
  induction l with
  | nil =>
      intro vs h _ v hv
      simp [List.mapM_nil] at h
      subst h
      cases hv
  | cons a rest ih =>
      intro vs h hP v hv
      rw [List.mapM_cons] at h
      cases hfa : f a with
      | none => rw [hfa] at h; simp at h
      | some w =>
          rw [hfa] at h
          cases hr : rest.mapM f with
          | none => rw [hr] at h; simp at h
          | some ws =>
              rw [hr] at h
              simp at h
              subst h
              rcases List.mem_cons.mp hv with rfl | hv'
              · exact hP a List.mem_cons_self _ hfa
              · exact ih hr (fun b hb => hP b (List.mem_cons_of_mem _ hb)) v hv'

theorem mapM_some_exists {α β : Type} {f : α → Option β} {P : β → Prop} :
    ∀ {l : List α}, (∀ a ∈ l, ∃ v, f a = some v ∧ P v) →
    ∃ vs, l.mapM f = some vs ∧ ∀ v ∈ vs, P v := by
  intro l
  induction l with
  | nil => intro _; exact ⟨[], by simp [List.mapM_nil], by simp⟩
  | cons a rest ih =>
      intro h
      obtain ⟨v, hv, hPv⟩ := h a List.mem_cons_self
      obtain ⟨vs, hvs, hPvs⟩ := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      refine ⟨v :: vs, ?_, ?_⟩
      · rw [List.mapM_cons, hv, hvs]; rfl
      · intro w hw
        rcases List.mem_cons.mp hw with rfl | hw'
        · exact hPv
        · exact hPvs w hw'

theorem mapM_congr {α β : Type} {f g : α → Option β} :
    ∀ {l : List α}, (∀ a ∈ l, f a = g a) → l.mapM f = l.mapM g := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      rw [List.mapM_cons, List.mapM_cons, h a List.mem_cons_self,
        ih (fun b hb => h b (List.mem_cons_of_mem _ hb))]

theorem mapM_length {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM f = some vs → vs.length = l.length := by
  intro l
  induction l with
  | nil => intro vs h; simp [List.mapM_nil] at h; subst h; rfl
  | cons a rest ih =>
      intro vs h
      rw [List.mapM_cons] at h
      cases hfa : f a with
      | none => rw [hfa] at h; simp at h
      | some w =>
          rw [hfa] at h
          cases hr : rest.mapM f with
          | none => rw [hr] at h; simp at h
          | some ws =>
              rw [hr] at h
              simp at h
              subst h
              simp [ih hr]

/-! ## `lookupIdent` facts -/

theorem lookupIdent_isSome_of_mem {β : Type} {x : Ident} :
    ∀ {l : List (Ident × β)} {y : Ident} {v : β},
    (y, v) ∈ l → y.name = x.name → ∃ w, lookupIdent x l = some w := by
  intro l
  induction l with
  | nil => intro y v h; cases h
  | cons ab rest ih =>
      intro y v hmem hname
      obtain ⟨y', v'⟩ := ab
      by_cases h : x.name = y'.name
      · exact ⟨v', by simp [lookupIdent, h]⟩
      · rcases List.mem_cons.mp hmem with heq | htl
        · exfalso
          have : y = y' := (Prod.mk.injEq .. ▸ heq).1
          subst this
          exact h hname.symm
        · rw [lookupIdent_cons_ne h]
          exact ih htl hname


theorem inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y := by
  intro l
  induction l with
  | nil => intro _ x hx; cases hx
  | cons a rest ih =>
      intro hnu x hx y hy hxy
      rw [List.map_cons, List.nodup_cons] at hnu
      rcases List.mem_cons.mp hx with rfl | hx'
      · rcases List.mem_cons.mp hy with rfl | hy'
        · rfl
        · exfalso; exact hnu.1 (List.mem_map.mpr ⟨y, hy', hxy.symm⟩)
      · rcases List.mem_cons.mp hy with rfl | hy'
        · exfalso; exact hnu.1 (List.mem_map.mpr ⟨x, hx', hxy⟩)
        · exact ih hnu.2 x hx' y hy' hxy

/-! ## The array definitions -/

/-- The value-name uniqueness of a well-formed model, as a list fact. -/
abbrev NamesNodup (m : Model) : Prop :=
  (m.parameters.map (fun d => d.name) ++ m.variables.map (fun d => d.name)).Nodup

theorem names_inj_par {m : Model} (hnu : NamesNodup m) {d d' : ParDeclItem}
    (hd : d ∈ m.parameters) (hd' : d' ∈ m.parameters)
    (h : d.name = d'.name) : d = d' := by
  have h1 := (List.nodup_append.mp hnu).1
  exact inj_of_nodup_map _ h1 d hd d' hd' h

theorem names_inj_var {m : Model} (hnu : NamesNodup m) {d d' : VarDeclItem}
    (hd : d ∈ m.variables) (hd' : d' ∈ m.variables)
    (h : d.name = d'.name) : d = d' := by
  have h1 := (List.nodup_append.mp hnu).2.1
  exact inj_of_nodup_map _ h1 d hd d' hd' h

theorem names_disj {m : Model} (hnu : NamesNodup m) {d : ParDeclItem}
    {d' : VarDeclItem} (hd : d ∈ m.parameters) (hd' : d' ∈ m.variables) :
    d.name ≠ d'.name :=
  (List.nodup_append.mp hnu).2.2 _ (List.mem_map.mpr ⟨d, hd, rfl⟩) _
    (List.mem_map.mpr ⟨d', hd', rfl⟩)

theorem mem_arrayDefs {m : Model} {y : Ident} {es : List BasicExpr}
    (h : (y, es) ∈ arrayDefs m) :
    (∃ d ∈ m.parameters, ∃ idx t lits,
        d = .array idx t y lits ∧ es = lits.map BasicExpr.lit) ∨
    (∃ d ∈ m.variables, ∃ ty anns, d = .array ty y anns es) := by
  unfold arrayDefs at h
  rcases List.mem_append.mp h with h1 | h2
  · left
    obtain ⟨d, hd, hdef⟩ := List.mem_filterMap.mp h1
    cases d with
    | basic t n v => simp [parArrayDef] at hdef
    | array idx t n lits =>
        simp only [parArrayDef, Option.some.injEq, Prod.mk.injEq] at hdef
        obtain ⟨rfl, rfl⟩ := hdef
        exact ⟨_, hd, idx, t, lits, rfl, rfl⟩
  · right
    obtain ⟨d, hd, hdef⟩ := List.mem_filterMap.mp h2
    cases d with
    | basic t n anns v => simp [varArrayDef] at hdef
    | array ty n anns es' =>
        simp only [varArrayDef, Option.some.injEq, Prod.mk.injEq] at hdef
        obtain ⟨rfl, rfl⟩ := hdef
        exact ⟨_, hd, ty, anns, rfl⟩

theorem arrayDefs_par {m : Model} {idx t n lits}
    (hd : (ParDeclItem.array idx t n lits) ∈ m.parameters) :
    (n, lits.map BasicExpr.lit) ∈ arrayDefs m := by
  unfold arrayDefs
  apply List.mem_append.mpr; left
  exact List.mem_filterMap.mpr ⟨_, hd, rfl⟩

theorem arrayDefs_var {m : Model} {ty n anns es}
    (hd : (VarDeclItem.array ty n anns es) ∈ m.variables) :
    (n, es) ∈ arrayDefs m := by
  unfold arrayDefs
  apply List.mem_append.mpr; right
  exact List.mem_filterMap.mpr ⟨_, hd, rfl⟩

/-- A scalar parameter name or initializer-free... any non-array
    declaration's name is not an array name. -/
theorem lookup_arrayDefs_none {m : Model} (hnu : NamesNodup m) {x : Ident}
    (hx : (∃ d ∈ m.parameters, isArrayPar d = false ∧ d.name.name = x.name) ∨
          (∃ d ∈ m.variables, isBasicVar d = true ∧ d.name.name = x.name)) :
    lookupIdent x (arrayDefs m) = none := by
  cases hl : lookupIdent x (arrayDefs m) with
  | none => rfl
  | some es =>
      exfalso
      obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x (arrayDefs m) es hl
      rcases mem_arrayDefs hy with ⟨d', hd', idx, t, lits, rfl, _⟩ | ⟨d', hd', ty, anns, rfl⟩
      · rcases hx with ⟨d, hd, hnarr, hdn⟩ | ⟨d, hd, hb, hdn⟩
        · have heq : d.name = (ParDeclItem.array idx t y lits).name :=
            ident_eq_of_name (hdn.trans hyn.symm)
          have := names_inj_par hnu hd hd' heq
          subst this
          simp [isArrayPar] at hnarr
        · exact names_disj hnu hd' hd
            (ident_eq_of_name (hyn.trans hdn.symm))
      · rcases hx with ⟨d, hd, hnarr, hdn⟩ | ⟨d, hd, hb, hdn⟩
        · exact names_disj hnu hd hd'
            (ident_eq_of_name (hdn.trans hyn.symm))
        · have heq : d.name = (VarDeclItem.array ty y anns es).name :=
            ident_eq_of_name (hdn.trans hyn.symm)
          have := names_inj_var hnu hd hd' heq
          subst this
          simp [isBasicVar] at hb

/-- A parameter array's name resolves to its own literals. -/
theorem lookup_par_array {m : Model} (hnu : NamesNodup m) {idx t n lits}
    (hd : (ParDeclItem.array idx t n lits) ∈ m.parameters) :
    lookupIdent n (arrayDefs m) = some (lits.map BasicExpr.lit) := by
  have hmem := arrayDefs_par hd
  obtain ⟨w, hw⟩ := lookupIdent_isSome_of_mem (x := n) hmem rfl
  obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem n (arrayDefs m) w hw
  rw [hw]
  congr 1
  rcases mem_arrayDefs hy with ⟨d', hd', idx', t', lits', rfl, rfl⟩ | ⟨d', hd', ty, anns, rfl⟩
  · have := names_inj_par hnu hd hd' (ident_eq_of_name hyn.symm)
    cases this
    rfl
  · exact absurd (ident_eq_of_name hyn.symm) (names_disj hnu hd hd')

/-- A variable array's name resolves to its own initializer. -/
theorem lookup_var_array {m : Model} (hnu : NamesNodup m) {ty n anns es}
    (hd : (VarDeclItem.array ty n anns es) ∈ m.variables) :
    lookupIdent n (arrayDefs m) = some es := by
  have hmem := arrayDefs_var hd
  obtain ⟨w, hw⟩ := lookupIdent_isSome_of_mem (x := n) hmem rfl
  obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem n (arrayDefs m) w hw
  rw [hw]
  congr 1
  rcases mem_arrayDefs hy with ⟨d', hd', idx', t', lits', rfl, rfl⟩ | ⟨d', hd', ty', anns', rfl⟩
  · exact absurd (ident_eq_of_name hyn.symm).symm (names_disj hnu hd' hd)
  · have := names_inj_var hnu hd hd' (ident_eq_of_name hyn.symm)
    cases this
    rfl


/-! ## The inlining equivalence -/

/-- A store is faithful to the array definitions when every array name
    reads the array of its elements' values. -/
def Faithful (defs : List (Ident × List BasicExpr)) (s : Store) : Prop :=
  ∀ x es, lookupIdent x defs = some es →
    ∃ vs, s x = some (.array vs) ∧ es.mapM (BasicExpr.eval s) = some vs

/-- Semantic faithfulness: an array name reads an array that is pointwise
    semantically equal to its elements' values.  Set-valued array
    variables need this weaker notion because a stored set value need
    not be syntactically the literal that denotes it. -/
def SemFaithful (defs : List (Ident × List BasicExpr)) (s : Store) : Prop :=
  ∀ x es, lookupIdent x defs = some es →
    ∃ vs ws, s x = some (.array ws) ∧ es.mapM (BasicExpr.eval s) = some vs ∧
      Forall2 Value.SemEq vs ws

/-- A variable array with set elements contributes its name to
    `setArrayNames`. -/
theorem mem_setArrayNames_of_elem {m : Model} {ty : ArrayVarType} {n : Ident}
    {anns : List Annotation} {es : List BasicExpr}
    (hd : (.array ty n anns es : VarDeclItem) ∈ m.variables)
    (h : ty.elem = .par .setOfInt) : n.name ∈ setArrayNames m := by
  unfold setArrayNames
  rw [List.mem_filterMap]
  exact ⟨.array ty n anns es, hd, by simp [h]⟩

theorem elem_ne_set_of_not_mem {m : Model} {ty : ArrayVarType} {n : Ident}
    {anns : List Annotation} {es : List BasicExpr}
    (hd : (.array ty n anns es : VarDeclItem) ∈ m.variables)
    (hx : n.name ∉ setArrayNames m) : ty.elem ≠ .par .setOfInt := by
  intro h
  exact hx (mem_setArrayNames_of_elem hd h)

theorem inlineExpr_eval {defs : List (Ident × List BasicExpr)} {s : Store}
    (hf : Faithful defs s) (e : Expr) :
    (inlineExpr defs e).eval s = e.eval s := by
  cases e with
  | array es => rfl
  | basic b =>
      cases b with
      | lit l => rfl
      | ident x =>
          cases hl : lookupIdent x defs with
          | none => simp [inlineExpr, hl]
          | some es =>
              obtain ⟨vs, hx, hes⟩ := hf x es hl
              simp only [inlineExpr, hl]
              show (es.mapM (BasicExpr.eval s)).map Value.array = s x
              rw [hes, hx]; rfl

theorem holds_inline {defs : List (Ident × List BasicExpr)} {s : Store}
    (hf : Faithful defs s) (pred : PredicateInterpretation)
    (c : ConstraintItem) :
    (inlineConstraint defs c).Holds pred s ↔ c.Holds pred s := by
  have hmap : (c.args.map (inlineExpr defs)).mapM (Expr.eval s) =
      c.args.mapM (Expr.eval s) := by
    rw [List.mapM_map]
    apply mapM_congr
    intro e _
    exact inlineExpr_eval hf e
  unfold ConstraintItem.Holds
  show (∃ args, (c.args.map (inlineExpr defs)).mapM (Expr.eval s) = some args ∧
      pred c.name args) ↔ _
  rw [hmap]

/-- An expression whose identifiers are not array names. -/
def IdentFree (defs : List (Ident × List BasicExpr)) : Expr → Prop
  | .basic (.ident x) => lookupIdent x defs = none
  | .basic (.lit _) => True
  | .array es => ∀ b ∈ es, ∀ x, b = BasicExpr.ident x → lookupIdent x defs = none

theorem fullStore_of_none {defs : List (Ident × List BasicExpr)} {s : Store}
    {x : Ident} (h : lookupIdent x defs = none) : fullStore defs s x = s x := by
  simp [fullStore, arrayValue, h]

theorem eval_full_of_free {defs : List (Ident × List BasicExpr)} {s : Store}
    {e : Expr} (h : IdentFree defs e) :
    e.eval (fullStore defs s) = e.eval s := by
  cases e with
  | basic b =>
      cases b with
      | lit l => rfl
      | ident x =>
          show fullStore defs s x = s x
          exact fullStore_of_none h
  | array es =>
      show (es.mapM (BasicExpr.eval (fullStore defs s))).map Value.array =
        (es.mapM (BasicExpr.eval s)).map Value.array
      rw [mapM_congr (g := BasicExpr.eval s)]
      intro b hb
      cases b with
      | lit l => rfl
      | ident x =>
          show fullStore defs s x = s x
          exact fullStore_of_none (h _ hb x rfl)

theorem holds_full_iff {defs : List (Ident × List BasicExpr)} {s : Store}
    {pred : PredicateInterpretation} {c : ConstraintItem}
    (h : ∀ e ∈ c.args, IdentFree defs e) :
    c.Holds pred (fullStore defs s) ↔ c.Holds pred s := by
  have hmap : c.args.mapM (Expr.eval (fullStore defs s)) =
      c.args.mapM (Expr.eval s) :=
    mapM_congr (fun e he => eval_full_of_free (h e he))
  unfold ConstraintItem.Holds
  rw [hmap]


/-! ## Fast array-gate lookup

The executable gate uses per-type hash sets; these lemmas connect them to
the scanning definitions used by the correctness proofs. -/

theorem basicNamesFold_contains (ds : List VarDeclItem)
    (s : Std.HashSet String) (p : BasicVarType → Bool) (x : String) :
    (basicNamesFold ds s p).contains x =
    (s.contains x || ds.any (fun d => match d with
      | .basic ty n _ none => p ty && n.name == x
      | _ => false)) := by
  induction ds generalizing s with
  | nil => simp [basicNamesFold]
  | cons d ds ih =>
      simp only [basicNamesFold, List.foldl_cons] at ih ⊢
      rw [ih]
      cases d with
      | array ty n anns es => simp [basicNameStep]
      | basic ty n anns v =>
          cases v with
          | some e => simp [basicNameStep]
          | none =>
              by_cases hp : p ty = true
              · simp [basicNameStep, hp, Std.HashSet.contains_insert,
                  Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]
              · have hp' : p ty = false := by simpa using hp
                simp [basicNameStep, hp']

theorem basicNamesOf_contains (m : Model) (p : BasicVarType → Bool)
    (x : String) :
    (basicNamesOf m p).contains x =
    m.variables.any (fun d => match d with
      | .basic ty n _ none => p ty && n.name == x
      | _ => false) := by
  simpa [basicNamesOf] using
    basicNamesFold_contains m.variables ∅ p x

theorem elemOkBFast_eq (m : Model) (defs : List (Ident × List BasicExpr))
    (b : BaseType) (e : BasicExpr) :
    elemOkBFast (arrayGate m) defs b e = elemOkB m defs b e := by
  cases e with
  | lit l =>
      cases l <;> cases b <;> rfl
  | ident x =>
      cases b <;>
        simp only [elemOkBFast, elemOkB, arrayGate, basicNamesOf_contains,
          Bool.and_comm, Bool.and_left_comm, Bool.and_assoc] <;> rfl

theorem setElemOkBFast_eq (m : Model) (defs : List (Ident × List BasicExpr))
    (e : BasicExpr) :
    setElemOkBFast (arrayGate m) defs e = setElemOkB m defs e := by
  cases e with
  | lit l => cases l <;> rfl
  | ident x =>
      simp only [setElemOkBFast, setElemOkB, arrayGate,
        basicNamesOf_contains, Bool.and_comm, Bool.and_left_comm,
        Bool.and_assoc]
      rfl

theorem varArrayOkBFast_eq (m : Model) (defs : List (Ident × List BasicExpr))
    (d : VarDeclItem) :
    varArrayOkBFast (arrayGate m) defs d = varArrayOkB m defs d := by
  cases d with
  | basic ty n anns v => rfl
  | array ty n anns es =>
      cases h : ty.elem with
      | par t =>
          cases t with
          | bool =>
              simp only [varArrayOkBFast, varArrayOkB, h]
              exact List.all_congr rfl (fun e => elemOkBFast_eq m defs .bool e)
          | int =>
              simp only [varArrayOkBFast, varArrayOkB, h]
              exact List.all_congr rfl (fun e => elemOkBFast_eq m defs .int e)
          | setOfInt =>
              simp only [varArrayOkBFast, varArrayOkB, h]
              exact List.all_congr rfl (fun e => setElemOkBFast_eq m defs e)
      | intRange lo hi => simp only [varArrayOkBFast, varArrayOkB, h]
      | intSet xs => simp only [varArrayOkBFast, varArrayOkB, h]
      | setOfIntRange lo hi => simp only [varArrayOkBFast, varArrayOkB, h]
      | setOfIntSet xs => simp only [varArrayOkBFast, varArrayOkB, h]

/-- The precomputed finite-name gate equals the scanning drop test. -/
theorem setInRestrictsOf_eq (m : Model) (c : ConstraintItem) :
    setInRestrictsOf (basicNamesOf m (fun ty => isFiniteIntType ty)) c =
      setInRestricts m c := by
  unfold setInRestrictsOf setInRestricts
  cases hs : setInSubject c with
  | none => rfl
  | some x =>
      show ((basicNamesOf m (fun ty => isFiniteIntType ty)).contains x &&
          (setInCondOf x c).isSome) =
        (plainFiniteIntVar m x && (setInCondOf x c).isSome)
      rw [basicNamesOf_contains]
      unfold plainFiniteIntVar
      have hany : m.variables.any (fun d => match d with
          | .basic ty n _ none => isFiniteIntType ty && n.name == x
          | _ => false) =
          m.variables.any (fun d => match d with
          | .basic ty n _ none => n.name == x && isFiniteIntType ty
          | _ => false) := by
        apply List.any_congr rfl
        intro d
        cases d with
        | array ty n anns es => rfl
        | basic ty n anns init =>
            cases init with
            | some e => rfl
            | none => simp [Bool.and_comm]
      rw [hany]
      rfl

/-- The precomputed constant-set restriction equals the scanning one. -/
theorem restrictSetInModelFast_eq (m : Model) :
    restrictSetInModelFast m = restrictSetInModel m := by
  have hmap : m.variables.map
      (restrictVarDeclOf (setInRestrictionList m)
        (setInSubjectNames (setInRestrictionList m))) =
      m.variables.map (restrictVarDecl m) := by
    apply List.map_congr_left
    intro d _
    exact restrictVarDeclOf_restrictionList m d
  have hfilter : m.constraints.filter (fun c =>
      !setInRestrictsOf (basicNamesOf m (fun ty => isFiniteIntType ty)) c) =
      m.constraints.filter (fun c => !setInRestricts m c) := by
    apply List.filter_congr
    intro c _
    rw [setInRestrictsOf_eq]
  dsimp only [restrictSetInModelFast, restrictSetInModel]
  rw [hmap, hfilter]

/-! ## Consequences of the array gate -/

/-- A value of the (int or bool) base type `b`. -/
def ValOf : BaseType → Value → Prop
  | .int, .int _ => True
  | .bool, .bool _ => True
  | _, _ => False

theorem valOf_of_contains {ty : BasicVarType} {b : BaseType} {v : Value}
    (hb : ty.base = b) (hib : b = .int ∨ b = .bool)
    (h : ty.contains v) : ValOf b v := by
  subst hb
  revert h hib
  cases ty <;> cases v <;>
    simp [BasicVarType.contains, BasicVarType.base, BasicParType.base, ValOf]
  all_goals (split <;> simp_all)

theorem contains_par_of_valOf {b : BaseType} {v : Value}
    (h : ValOf b v) :
    (b = .int → (BasicVarType.par .int).contains v) ∧
    (b = .bool → (BasicVarType.par .bool).contains v) := by
  cases b <;> cases v <;> simp_all [ValOf, BasicVarType.contains]

theorem elemOk_ident {m : Model} {defs : List (Ident × List BasicExpr)}
    {b : BaseType} {x : Ident}
    (h : elemOkB m defs b (.ident x) = true) :
    lookupIdent x defs = none ∧ ∃ ty n anns,
      (VarDeclItem.basic ty n anns none) ∈ m.variables ∧
      n.name = x.name ∧ ty.base = b := by
  simp only [elemOkB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨h1, ?_⟩
  obtain ⟨d, hd, hdd⟩ := List.any_eq_true.mp h2
  cases d with
  | array ty n anns es => simp at hdd
  | basic ty n anns v =>
      cases v with
      | some e => simp at hdd
      | none =>
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hdd
          exact ⟨ty, n, anns, hd, hdd.1, hdd.2⟩

/-- A set-array element that is a name is a non-array name. -/
theorem setElemOk_ident {m : Model} {defs : List (Ident × List BasicExpr)}
    {x : Ident} (h : setElemOkB m defs (.ident x) = true) :
    lookupIdent x defs = none := by
  simp only [setElemOkB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  exact h.1

/-- Inversion of the set-array gate on a name element. -/
theorem setElemOk_ident_full {m : Model} {defs : List (Ident × List BasicExpr)}
    {x : Ident} (h : setElemOkB m defs (.ident x) = true) :
    lookupIdent x defs = none ∧ ∃ ty n anns us,
      (VarDeclItem.basic ty n anns none) ∈ m.variables ∧
      n.name = x.name ∧ setUniverse? ty = some us := by
  simp only [setElemOkB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
  obtain ⟨hln, hany⟩ := h
  obtain ⟨d, hd, hdd⟩ := List.any_eq_true.mp hany
  cases d with
  | array ty n anns es => simp at hdd
  | basic ty n anns v =>
      cases v with
      | some e => simp at hdd
      | none =>
          simp only [Bool.and_eq_true, beq_iff_eq,
            Option.isSome_iff_exists] at hdd
          obtain ⟨us, huniv⟩ := hdd.2
          exact ⟨hln, ty, n, anns, us, hd, hdd.1, huniv⟩

/-- Inversion of the set-array element gate, with the declaration. -/
theorem setElemOk_inv {m : Model} {defs : List (Ident × List BasicExpr)}
    {e : BasicExpr} (h : setElemOkB m defs e = true) :
    (∃ l, e = .lit (.set l)) ∨
    (∃ x ty n anns us, e = .ident x ∧ lookupIdent x defs = none ∧
      (VarDeclItem.basic ty n anns none) ∈ m.variables ∧ n.name = x.name ∧
      setUniverse? ty = some us) := by
  cases e with
  | lit l =>
      cases l with
      | int i => simp [setElemOkB] at h
      | bool b => simp [setElemOkB] at h
      | set sl => exact Or.inl ⟨sl, rfl⟩
  | ident x =>
      right
      simp only [setElemOkB, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
      obtain ⟨hln, hany⟩ := h
      obtain ⟨d, hd, hdd⟩ := List.any_eq_true.mp hany
      cases d with
      | array ty n anns es => simp at hdd
      | basic ty n anns v =>
          cases v with
          | some e => simp at hdd
          | none =>
              simp only [Bool.and_eq_true, beq_iff_eq,
                Option.isSome_iff_exists] at hdd
              obtain ⟨us, huniv⟩ := hdd.2
              exact ⟨x, ty, n, anns, us, rfl, hln, hd, hdd.1, huniv⟩

theorem varArrayOk_inv {m : Model} {defs : List (Ident × List BasicExpr)}
    {ty : ArrayVarType} {n : Ident} {anns : List Annotation}
    {es : List BasicExpr}
    (h : varArrayOkB m defs (.array ty n anns es) = true) :
    (ty.elem = .par .int ∧ ∀ e ∈ es, elemOkB m defs .int e = true) ∨
    (ty.elem = .par .bool ∧ ∀ e ∈ es, elemOkB m defs .bool e = true) ∨
    (ty.elem = .par .setOfInt ∧ ∀ e ∈ es, setElemOkB m defs e = true) := by
  simp only [varArrayOkB] at h
  revert h
  cases hel : ty.elem with
  | par t =>
      cases t
      · exact fun h => Or.inr (Or.inl ⟨rfl, List.all_eq_true.mp h⟩)
      · exact fun h => Or.inl ⟨rfl, List.all_eq_true.mp h⟩
      · exact fun h => Or.inr (Or.inr ⟨rfl, List.all_eq_true.mp h⟩)
  | intRange lo hi => simp
  | intSet xs => simp
  | setOfIntRange lo hi => simp
  | setOfIntSet xs => simp

theorem gate_vars {m : Model} (h : arraysOkB m = true) :
    ∀ d ∈ m.variables, varArrayOkB m (arrayDefs m) d = true := by
  unfold arraysOkB at h
  have h' := (Bool.and_eq_true _ _).mp h
  have h'' := (Bool.and_eq_true _ _).mp h'.1
  exact fun d hd => by
    rw [← varArrayOkBFast_eq m (arrayDefs m) d]
    exact List.all_eq_true.mp h''.1 d hd

theorem gate_cons {m : Model} (h : arraysOkB m = true) :
    ∀ c ∈ m.constraints, ∀ e ∈ c.args, explicitOkB (arrayDefs m) e = true := by
  unfold arraysOkB at h
  have h' := (Bool.and_eq_true _ _).mp h
  have hc := List.all_eq_true.mp h'.2
  exact fun c hcm e he =>
    List.all_eq_true.mp ((Bool.and_eq_true _ _).mp (hc c hcm)).1 e he

/-- The set-array-use gate of a constraint. -/
theorem gate_setUse {m : Model} (h : arraysOkB m = true) :
    ∀ c ∈ m.constraints, setArrayUseOkB (setArrayNames m) c = true := by
  unfold arraysOkB at h
  have h' := (Bool.and_eq_true _ _).mp h
  have hc := List.all_eq_true.mp h'.2
  exact fun c hcm => ((Bool.and_eq_true _ _).mp (hc c hcm)).2

/-- The elements of any array definition (of a gated model) are
    literals or non-array identifiers. -/
theorem defs_elems_free {m : Model} (h : arraysOkB m = true)
    {x : Ident} {es : List BasicExpr}
    (hl : lookupIdent x (arrayDefs m) = some es) :
    ∀ b ∈ es, ∀ z, b = BasicExpr.ident z → lookupIdent z (arrayDefs m) = none := by
  obtain ⟨y, hy, _⟩ := lookupIdent_inv_mem x (arrayDefs m) es hl
  intro b hb z hbz
  rcases mem_arrayDefs hy with ⟨d, hd, idx, t, lits, rfl, rfl⟩ | ⟨d, hd, ty, anns, rfl⟩
  · obtain ⟨l, _, hl'⟩ := List.mem_map.mp hb
    subst hbz
    cases hl'
  · have hok := gate_vars h _ hd
    subst hbz
    rcases varArrayOk_inv hok with ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
    · exact (elemOk_ident (h2 _ hb)).1
    · exact (elemOk_ident (h2 _ hb)).1
    · exact setElemOk_ident (h2 _ hb)

/-- Under the gate, inlining produces array-name-free arguments. -/
theorem inline_identFree {m : Model} (h : arraysOkB m = true)
    {c : ConstraintItem} (hc : c ∈ m.constraints) :
    ∀ e ∈ (inlineConstraint (arrayDefs m) c).args,
      IdentFree (arrayDefs m) e := by
  intro e he
  obtain ⟨e0, he0, rfl⟩ := List.mem_map.mp he
  have hex := gate_cons h c hc e0 he0
  cases e0 with
  | array es =>
      show IdentFree (arrayDefs m) (.array es)
      intro b hb z hbz
      subst hbz
      have := List.all_eq_true.mp hex _ hb
      simpa [Option.isNone_iff_eq_none] using this
  | basic b =>
      cases b with
      | lit l => exact trivial
      | ident x =>
          cases hl : lookupIdent x (arrayDefs m) with
          | none => simp [inlineExpr, hl, IdentFree]
          | some es =>
              simp only [inlineExpr, hl]
              exact defs_elems_free h hl


/-! ## Element evaluation -/

/-- Every initializer-free basic variable reads a value in its domain. -/
def BasicRead (m : Model) (s : Store) : Prop :=
  ∀ ty n anns, (VarDeclItem.basic ty n anns none) ∈ m.variables →
    ∃ v, s n = some v ∧ ty.contains v

/-- A scalar (int or bool) value. -/
def IsScalar (v : Value) : Prop := (∃ i, v = .int i) ∨ (∃ b, v = .bool b)

theorem isScalar_of_valOf {b : BaseType} {v : Value} (h : ValOf b v) :
    IsScalar v := by
  cases b <;> cases v <;> simp_all [ValOf, IsScalar]

theorem elem_eval {m : Model} {defs : List (Ident × List BasicExpr)}
    {s : Store} {b : BaseType} {e : BasicExpr}
    (hb : b = .int ∨ b = .bool) (hs : BasicRead m s)
    (he : elemOkB m defs b e = true) :
    ∃ v, e.eval s = some v ∧ ValOf b v := by
  cases e with
  | lit l =>
      cases l with
      | int i =>
          simp only [elemOkB, decide_eq_true_eq] at he
          subst he
          exact ⟨.int i, rfl, trivial⟩
      | bool bb =>
          simp only [elemOkB, decide_eq_true_eq] at he
          subst he
          exact ⟨.bool bb, rfl, trivial⟩
      | set _ => simp [elemOkB] at he
  | ident x =>
      obtain ⟨_, ty, n, anns, hd, hn, hty⟩ := elemOk_ident he
      obtain ⟨v, hv, hcont⟩ := hs ty n anns hd
      have hx : x = n := (ident_eq_of_name hn).symm
      subst hx
      exact ⟨v, hv, valOf_of_contains hty hb hcont⟩

theorem mapM_lit_eval (s : Store) (lits : List BasicLiteral) :
    (lits.map BasicExpr.lit).mapM (BasicExpr.eval s) =
      some (lits.map BasicLiteral.denote) := by
  induction lits with
  | nil => rfl
  | cons l rest ih =>
      rw [List.map_cons, List.mapM_cons]
      simp only [BasicExpr.eval]
      rw [ih]; rfl

/-- A set-typed declaration admitted by the set-array gate stores a set
    value. -/
theorem setOfInt_of_contains_of_setUniverse {ty : BasicVarType} {us : List Int}
    {v : Value} (hu : setUniverse? ty = some us) (h : ty.contains v) :
    ∃ sv, v = .setOfInt sv := by
  cases ty <;> cases v <;> simp_all [setUniverse?, BasicVarType.contains]

theorem setElem_eval {m : Model} {defs : List (Ident × List BasicExpr)}
    {s : Store} (hs : BasicRead m s) {e : BasicExpr}
    (he : setElemOkB m defs e = true) :
    ∃ sv, e.eval s = some (.setOfInt sv) := by
  rcases setElemOk_inv he with ⟨l, rfl⟩ | ⟨x, ty, n, anns, us, rfl, hln, hd, hn, huniv⟩
  · exact ⟨l.denote, rfl⟩
  · obtain ⟨v, hv, hcont⟩ := hs ty n anns hd
    have hx : x = n := (ident_eq_of_name hn).symm
    subst hx
    obtain ⟨sv, rfl⟩ := setOfInt_of_contains_of_setUniverse huniv hcont
    exact ⟨sv, hv⟩

/-- A gated variable array's initializer evaluates, to values inside
    the declared element type. -/
theorem var_elems {m : Model} (h : arraysOkB m = true) {s : Store}
    (hs : BasicRead m s) {ty : ArrayVarType} {n : Ident}
    {anns : List Annotation} {es : List BasicExpr}
    (hd : (VarDeclItem.array ty n anns es) ∈ m.variables) :
    ∃ vs, es.mapM (BasicExpr.eval s) = some vs ∧
      ∀ v ∈ vs, ty.elem.contains v := by
  have hok := gate_vars h _ hd
  rcases varArrayOk_inv hok with ⟨hel, h2⟩ | ⟨hel, h2⟩ | ⟨hel, h2⟩
  · obtain ⟨vs, hvs, hP⟩ := mapM_some_exists (f := BasicExpr.eval s)
      (P := fun v => ValOf .int v) (l := es)
      (fun e he => elem_eval (Or.inl rfl) hs (h2 e he))
    refine ⟨vs, hvs, fun v hv => ?_⟩
    rw [hel]
    exact (contains_par_of_valOf (hP v hv)).1 rfl
  · obtain ⟨vs, hvs, hP⟩ := mapM_some_exists (f := BasicExpr.eval s)
      (P := fun v => ValOf .bool v) (l := es)
      (fun e he => elem_eval (Or.inr rfl) hs (h2 e he))
    refine ⟨vs, hvs, fun v hv => ?_⟩
    rw [hel]
    exact (contains_par_of_valOf (hP v hv)).2 rfl
  · obtain ⟨vs, hvs, hP⟩ := mapM_some_exists (f := BasicExpr.eval s)
      (P := fun v => ∃ sv, v = .setOfInt sv) (l := es)
      (fun e he => by
        obtain ⟨sv, hsv⟩ := setElem_eval hs (h2 e he)
        exact ⟨.setOfInt sv, hsv, ⟨sv, rfl⟩⟩)
    refine ⟨vs, hvs, fun v hv => ?_⟩
    rw [hel]
    obtain ⟨sv, rfl⟩ := hP v hv
    exact trivial

/-- Every array definition of a gated model evaluates. -/
theorem defs_eval {m : Model} (h : arraysOkB m = true) {s : Store}
    (hs : BasicRead m s) {x : Ident} {es : List BasicExpr}
    (hl : lookupIdent x (arrayDefs m) = some es) :
    ∃ vs, es.mapM (BasicExpr.eval s) = some vs := by
  obtain ⟨y, hy, _⟩ := lookupIdent_inv_mem x (arrayDefs m) es hl
  rcases mem_arrayDefs hy with ⟨d, hd, idx, t, lits, rfl, rfl⟩ | ⟨d, hd, ty, anns, rfl⟩
  · exact ⟨_, mapM_lit_eval s lits⟩
  · obtain ⟨vs, hvs, _⟩ := var_elems h hs hd
    exact ⟨vs, hvs⟩

/-- The array-extended store is faithful to the definitions. -/
theorem faithful_full {m : Model} (h : arraysOkB m = true) {s : Store}
    (hs : BasicRead m s) :
    Faithful (arrayDefs m) (fullStore (arrayDefs m) s) := by
  intro x es hl
  obtain ⟨vs, hvs⟩ := defs_eval h hs hl
  refine ⟨vs, ?_, ?_⟩
  · simp [fullStore, arrayValue, hl, hvs]
  · rw [mapM_congr (g := BasicExpr.eval s) ?_]
    · exact hvs
    · intro b hb
      cases b with
      | lit l => rfl
      | ident z =>
          show fullStore (arrayDefs m) s z = s z
          exact fullStore_of_none (defs_elems_free h hl _ hb z rfl)


/-! ## Static environments -/

theorem lookupIdent_filter_map {α β : Type} (f : α → Ident × β) (p : α → Bool)
    (x : Ident) :
    ∀ {l : List α}, (∀ a ∈ l, (f a).1.name = x.name → p a = true) →
    lookupIdent x ((l.filter p).map f) = lookupIdent x (l.map f) := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro h
      have hrest := ih (fun b hb => h b (List.mem_cons_of_mem _ hb))
      rcases hfa : f a with ⟨y, v⟩
      by_cases hname : x.name = y.name
      · have hp : p a = true := h a List.mem_cons_self (by rw [hfa]; exact hname.symm)
        simp only [List.filter_cons, hp, if_true, List.map_cons, hfa]
        simp [lookupIdent, hname]
      · cases hp : p a with
        | true =>
            simp only [List.filter_cons, hp, if_true, List.map_cons, hfa]
            rw [lookupIdent_cons_ne hname, lookupIdent_cons_ne hname, hrest]
        | false =>
            simp only [List.filter_cons, hp, Bool.false_eq_true, if_false,
              List.map_cons, hfa]
            rw [lookupIdent_cons_ne hname, hrest]

/-- The normalized model's static environment agrees with the
    original's on every non-array name. -/
theorem staticEnv_norm_eq {m : Model} {x : Ident}
    (hx : lookupIdent x (arrayDefs m) = none) :
    (normalizeModel m).staticEnv x = m.staticEnv x := by
  unfold Model.staticEnv
  have hpar : lookupIdent x (((normalizeModel m).parameters).map
      (fun d => (d.name, (d.type, false)))) =
      lookupIdent x (m.parameters.map (fun d => (d.name, (d.type, false)))) := by
    show lookupIdent x ((m.parameters.filter (fun d => !isArrayPar d)).map _) = _
    apply lookupIdent_filter_map
    intro d hd hdn
    cases d with
    | basic t n v => rfl
    | array idx t n lits =>
        exfalso
        obtain ⟨w, hw⟩ := lookupIdent_isSome_of_mem (x := x)
          (arrayDefs_par hd) hdn
        rw [hx] at hw; cases hw
  have hvar : lookupIdent x (((normalizeModel m).variables).map
      (fun d => (d.name, (d.type, true)))) =
      lookupIdent x (m.variables.map (fun d => (d.name, (d.type, true)))) := by
    show lookupIdent x ((m.variables.filter isBasicVar).map _) = _
    apply lookupIdent_filter_map
    intro d hd hdn
    cases d with
    | basic t n a v => rfl
    | array ty n a es =>
        exfalso
        obtain ⟨w, hw⟩ := lookupIdent_isSome_of_mem (x := x)
          (arrayDefs_var hd) hdn
        rw [hx] at hw; cases hw
  rw [hpar, hvar]

theorem staticEnv_par {m : Model} (hnu : NamesNodup m) {d : ParDeclItem}
    (hd : d ∈ m.parameters) :
    m.staticEnv d.name = some (d.type, false) := by
  unfold Model.staticEnv
  have hk : ((m.parameters.map (fun d => (d.name, (d.type, false)))).map
      Prod.fst).Nodup := by
    rw [List.map_map]
    exact (List.nodup_append.mp hnu).1
  rw [lookupIdent_of_mem hk (List.mem_map.mpr ⟨d, hd, rfl⟩)]

theorem staticEnv_var {m : Model} (hnu : NamesNodup m) {d : VarDeclItem}
    (hd : d ∈ m.variables) :
    m.staticEnv d.name = some (d.type, true) := by
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
    exact names_disj hnu hd' hd (ident_eq_of_name hpn)
  rw [hnone]
  exact lookupIdent_of_mem hk (List.mem_map.mpr ⟨d, hd, rfl⟩)

/-- An array-typed static entry belongs to an array definition. -/
theorem staticEnv_array_defs {m : Model} {x : Ident} {n : Nat}
    {t : BaseType} {v : Bool}
    (h : m.staticEnv x = some (.array n t, v)) :
    ∃ es, lookupIdent x (arrayDefs m) = some es := by
  unfold Model.staticEnv at h
  cases hp : lookupIdent x (m.parameters.map
      (fun d => (d.name, (d.type, false)))) with
  | some info =>
      rw [hp] at h
      obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ info hp
      obtain ⟨d, hd, hdy⟩ := List.mem_map.mp hy
      cases d with
      | basic ty nm val =>
          simp [ParDeclItem.type] at hdy
          have : info = (FznType.base ty.base, false) := hdy.2.symm
          simp [this] at h
      | array idx ty nm lits =>
          obtain ⟨w, hw⟩ := lookupIdent_isSome_of_mem (x := x)
            (arrayDefs_par hd) (by
              have : y = nm := (Prod.mk.inj hdy).1.symm
              rw [← this]; exact hyn)
          exact ⟨w, hw⟩
  | none =>
      rw [hp] at h
      obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ _ h
      obtain ⟨d, hd, hdy⟩ := List.mem_map.mp hy
      cases d with
      | basic ty nm a val =>
          simp [VarDeclItem.type] at hdy
      | array ty nm a es =>
          obtain ⟨w, hw⟩ := lookupIdent_isSome_of_mem (x := x)
            (arrayDefs_var hd) (by
              have : y = nm := (Prod.mk.inj hdy).1.symm
              rw [← this]; exact hyn)
          exact ⟨w, hw⟩

/-- A name with an array definition has an array-typed static entry. -/
theorem staticEnv_array_of_lookup {m : Model} (hnu : NamesNodup m) {x : Ident}
    {es : List BasicExpr} (hl : lookupIdent x (arrayDefs m) = some es) :
    ∃ n t v, m.staticEnv x = some (.array n t, v) := by
  obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x (arrayDefs m) es hl
  have hyx : y = x := ident_eq_of_name hyn
  subst hyx
  rcases mem_arrayDefs hy with ⟨d, hd, idx, t, lits, rfl, rfl⟩ |
    ⟨d, hd, ty, anns, rfl⟩
  · exact ⟨_, _, _, staticEnv_par hnu hd⟩
  · exact ⟨_, _, _, staticEnv_var hnu hd⟩

/-- A name whose static entry is scalar is not an array name. -/
theorem lookup_arrayDefs_none_of_base {m : Model} (hnu : NamesNodup m) {x : Ident}
    {t : BaseType} {b : Bool} (h : m.staticEnv x = some (.base t, b)) :
    lookupIdent x (arrayDefs m) = none := by
  cases hl : lookupIdent x (arrayDefs m) with
  | none => rfl
  | some es =>
      obtain ⟨n, t', v, harr⟩ := staticEnv_array_of_lookup hnu hl
      rw [h] at harr
      exact absurd harr (by simp)

theorem accepts_mono {bt : BasicPredParamType} {t : BaseType}
    (h : bt.accepts t true) : bt.accepts t false := by
  unfold BasicPredParamType.accepts at *
  exact ⟨h.1, fun _ => rfl⟩

/-- Scalar array elements of a gated array check against the array
    parameter type when the declared element base does. -/
theorem checkBase_of_elemOk {m : Model} (hnu : NamesNodup m)
    {bt : BasicPredParamType}
    {b0 : BaseType} (hacc : bt.accepts b0 true)
    {es : List BasicExpr}
    (h2 : ∀ e ∈ es, elemOkB m (arrayDefs m) b0 e = true) :
    ∀ b ∈ es, BasicExpr.checkBase (normalizeModel m).staticEnv b bt := by
  intro b hb
  cases b with
  | lit l =>
      have := h2 _ hb
      cases l with
      | int i =>
          simp only [elemOkB, decide_eq_true_eq] at this
          subst this
          exact accepts_mono hacc
      | bool bb =>
          simp only [elemOkB, decide_eq_true_eq] at this
          subst this
          exact accepts_mono hacc
      | set _ => simp [elemOkB] at this
  | ident z =>
      obtain ⟨hzn, ty', n', anns', hd', hnn, hty'⟩ := elemOk_ident (h2 _ hb)
      have h3 := staticEnv_var hnu hd'
      have hz : z = n' := (ident_eq_of_name hnn).symm
      subst hz
      simp only [BasicExpr.checkBase]
      rw [staticEnv_norm_eq hzn]
      simp only [VarDeclItem.name, VarDeclItem.type] at h3
      rw [h3]
      simp only [BasicVarType.base] at hty' ⊢
      rw [hty']
      exact hacc

/-- Set array elements of a gated array check against a set array
    parameter type whose declared element base it accepts. -/
theorem checkBase_of_setElemOk {m : Model} (hnu : NamesNodup m)
    {bt : BasicPredParamType}
    (hacc : bt.accepts .setOfInt true)
    {es : List BasicExpr}
    (h2 : ∀ e ∈ es, setElemOkB m (arrayDefs m) e = true) :
    ∀ b ∈ es, BasicExpr.checkBase (normalizeModel m).staticEnv b bt := by
  intro b hb
  cases b with
  | lit l =>
      have h := h2 _ hb
      cases l with
      | int i => simp [setElemOkB] at h
      | bool bb => simp [setElemOkB] at h
      | set sl =>
          simp only [BasicExpr.checkBase, BasicLiteral.type]
          exact accepts_mono hacc
  | ident z =>
      obtain ⟨hzn, ty', n', anns', us, hd', hnn, huniv⟩ :=
        setElemOk_ident_full (h2 _ hb)
      have h3 := staticEnv_var hnu hd'
      have hz : z = n' := (ident_eq_of_name hnn).symm
      subst hz
      simp only [BasicExpr.checkBase]
      rw [staticEnv_norm_eq hzn]
      simp only [VarDeclItem.name, VarDeclItem.type] at h3
      rw [h3]
      rw [setUniverse?_base huniv]
      exact hacc


/-! ## Well-formedness of the normalized model -/

theorem checkArg_inline {m : Model} (hwf : WellFormed fullSig m)
    (hgate : arraysOkB m = true) {e : Expr} {pt : PredParamType}
    (hca : Expr.checkArg m.staticEnv e pt)
    (hex : explicitOkB (arrayDefs m) e = true) :
    Expr.checkArg (normalizeModel m).staticEnv (inlineExpr (arrayDefs m) e) pt := by
  have hnu : NamesNodup m := hwf.valueNamesUnique
  cases pt with
  | basic bt =>
      cases e with
      | array es => exact hca.elim
      | basic b =>
          cases b with
          | lit l => simpa [inlineExpr, Expr.checkArg, BasicExpr.checkBase] using hca
          | ident x =>
              have hnone : lookupIdent x (arrayDefs m) = none := by
                cases hl : lookupIdent x (arrayDefs m) with
                | none => rfl
                | some es =>
                    exfalso
                    obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ es hl
                    have hx : x = y := (ident_eq_of_name hyn).symm
                    subst hx
                    rcases mem_arrayDefs hy with ⟨d, hd, idx, t, lits, rfl, _⟩ | ⟨d, hd, ty, anns, rfl⟩
                    · have := staticEnv_par hnu hd
                      simp [Expr.checkArg, BasicExpr.checkBase, ParDeclItem.name,
                        ParDeclItem.type] at this hca
                      rw [this] at hca
                      exact hca
                    · have := staticEnv_var hnu hd
                      simp [Expr.checkArg, BasicExpr.checkBase, VarDeclItem.name,
                        VarDeclItem.type] at this hca
                      rw [this] at hca
                      exact hca
              simp only [inlineExpr, hnone, Expr.checkArg, BasicExpr.checkBase]
              rw [staticEnv_norm_eq hnone]
              exact hca
  | array idx bt =>
      cases e with
      | basic b =>
          cases b with
          | lit l => exact hca.elim
          | ident x =>
              simp only [Expr.checkArg] at hca
              cases hse : m.staticEnv x with
              | none => rw [hse] at hca; exact hca.elim
              | some info =>
                  obtain ⟨ft, isVar⟩ := info
                  rw [hse] at hca
                  cases ft with
                  | base t => exact hca.elim
                  | array nlen t =>
                      obtain ⟨hlen, hacc⟩ := hca
                      obtain ⟨es, hl⟩ := staticEnv_array_defs hse
                      simp only [inlineExpr, hl, Expr.checkArg]
                      obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x _ es hl
                      have hx : x = y := (ident_eq_of_name hyn).symm
                      subst hx
                      rcases mem_arrayDefs hy with ⟨d, hd, idx', t', lits, rfl, rfl⟩ | ⟨d, hd, ty, anns, rfl⟩
                      · have h1 := staticEnv_par hnu hd
                        simp only [ParDeclItem.name, ParDeclItem.type] at h1
                        rw [hse] at h1
                        simp only [Option.some.injEq, Prod.mk.injEq,
                          FznType.array.injEq] at h1
                        obtain ⟨⟨hn1, ht1⟩, hv1⟩ := h1
                        have hpt := hwf.parameterTypes _ hd
                        simp only at hpt
                        obtain ⟨hplen, hptype⟩ := hpt
                        refine ⟨?_, ?_⟩
                        · rw [List.length_map, hplen]
                          rw [hn1] at hlen
                          exact hlen
                        · intro b hb
                          obtain ⟨l, hl', rfl⟩ := List.mem_map.mp hb
                          simp only [BasicExpr.checkBase]
                          rw [hptype l hl']
                          rw [ht1, hv1] at hacc
                          exact hacc
                      · have h1 := staticEnv_var hnu hd
                        simp only [VarDeclItem.name, VarDeclItem.type] at h1
                        rw [hse] at h1
                        simp only [Option.some.injEq, Prod.mk.injEq,
                          FznType.array.injEq] at h1
                        obtain ⟨⟨hn1, ht1⟩, hv1⟩ := h1
                        have hlens := hwf.variableArrayLengths _ hd
                        simp only at hlens
                        refine ⟨?_, ?_⟩
                        · rw [hlens]
                          rw [hn1] at hlen
                          exact hlen
                        · intro b hb
                          have hok := gate_vars hgate _ hd
                          rcases varArrayOk_inv hok with ⟨hel, h2⟩ | ⟨hel, h2⟩ |
                            ⟨hel, h2⟩
                          · have hbase : ty.elem.base = .int := by rw [hel]; rfl
                            rw [ht1, hbase, hv1] at hacc
                            exact checkBase_of_elemOk hnu hacc h2 b hb
                          · have hbase : ty.elem.base = .bool := by rw [hel]; rfl
                            rw [ht1, hbase, hv1] at hacc
                            exact checkBase_of_elemOk hnu hacc h2 b hb
                          · have hbase : ty.elem.base = .setOfInt := by rw [hel]; rfl
                            rw [ht1, hbase, hv1] at hacc
                            exact checkBase_of_setElemOk hnu hacc h2 b hb
      | array es0 =>
          simp only [Expr.checkArg] at hca
          obtain ⟨hlen, hall⟩ := hca
          refine ⟨hlen, ?_⟩
          intro b hb
          have h1 := hall b hb
          cases b with
          | lit l => exact h1
          | ident z =>
              have hzn : lookupIdent z (arrayDefs m) = none := by
                have := List.all_eq_true.mp hex _ hb
                simpa [Option.isNone_iff_eq_none] using this
              simp only [BasicExpr.checkBase] at h1 ⊢
              rw [staticEnv_norm_eq hzn]
              exact h1


theorem forall2_map_left {α α' β : Type} (R : α → β → Prop) (R' : α' → β → Prop)
    (f : α → α') :
    ∀ (l1 : List α) (l2 : List β), Forall2 R l1 l2 →
    (∀ a ∈ l1, ∀ b, R a b → R' (f a) b) → Forall2 R' (l1.map f) l2 := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 h _
      cases l2 with
      | nil => exact trivial
      | cons b bs => exact h.elim
  | cons a rest ih =>
      intro l2 h hall
      cases l2 with
      | nil => exact h.elim
      | cons b bs =>
          exact ⟨hall a List.mem_cons_self b h.1,
            ih bs h.2 (fun a' ha' b' hb' => hall a' (List.mem_cons_of_mem _ ha') b' hb')⟩

theorem hasBaseType_norm {m : Model} (hnu : NamesNodup m) {v : BasicExpr}
    {t : BaseType} (h : v.hasBaseType m.staticEnv t) :
    v.hasBaseType (normalizeModel m).staticEnv t := by
  cases v with
  | lit l => exact h
  | ident x =>
      cases hs : m.staticEnv x with
      | none =>
          exfalso
          simpa [BasicExpr.hasBaseType, hs] using h
      | some info =>
          obtain ⟨ty, b⟩ := info
          cases ty with
          | base t' =>
              have hnone := lookup_arrayDefs_none_of_base hnu hs
              have heq := staticEnv_norm_eq hnone
              simpa [BasicExpr.hasBaseType, hs, heq] using h
          | array n t' =>
              exfalso
              simpa [BasicExpr.hasBaseType, hs] using h

theorem lookup_arrayDefs_none_of_hasBaseType {m : Model} (hnu : NamesNodup m)
    {b : BasicExpr} {t : BaseType} (h : b.hasBaseType m.staticEnv t)
    {x : Ident} (hb : b = .ident x) : lookupIdent x (arrayDefs m) = none := by
  subst hb
  cases hs : m.staticEnv x with
  | none =>
      exfalso
      simpa [BasicExpr.hasBaseType, hs] using h
  | some info =>
      obtain ⟨ty, bb⟩ := info
      cases ty with
      | base t' => exact lookup_arrayDefs_none_of_base hnu hs
      | array n t' =>
          exfalso
          simpa [BasicExpr.hasBaseType, hs] using h

theorem basicExpr_eval_fullStore {m : Model} (hnu : NamesNodup m)
    {b : BasicExpr} {t : BaseType} (h : b.hasBaseType m.staticEnv t) (s : Store) :
    b.eval (fullStore (arrayDefs m) s) = b.eval s := by
  cases b with
  | lit l => rfl
  | ident x =>
      show fullStore (arrayDefs m) s x = s x
      exact fullStore_of_none
        (lookup_arrayDefs_none_of_hasBaseType hnu h rfl)

theorem basic_initializerHolds_fullStore {m : Model} (hnu : NamesNodup m)
    {ty : BasicVarType} {n : Ident} {anns : List Annotation} {v : BasicExpr}
    (hv : v.hasBaseType m.staticEnv ty.base) {s : Store}
    (h : (VarDeclItem.basic ty n anns (some v)).initializerHolds s)
    (hn : lookupIdent n (arrayDefs m) = none) :
    (VarDeclItem.basic ty n anns (some v)).initializerHolds
      (fullStore (arrayDefs m) s) := by
  obtain ⟨val, val', hval, hn', hsem⟩ := h
  exact ⟨val, val', by rw [basicExpr_eval_fullStore hnu hv]; exact hval,
    by rw [fullStore_of_none hn]; exact hn', hsem⟩

theorem wf_normalize {m : Model} (hwf : WellFormed fullSig m)
    (hgate : arraysOkB m = true)
    (hsolve : ∃ anns, m.solve = .satisfy anns) :
    WellFormed fullSig (normalizeModel m) := by
  have hnu : NamesNodup m := hwf.valueNamesUnique
  obtain ⟨anns, hs⟩ := hsolve
  refine
    { predNamesUnique := hwf.predNamesUnique
      valueNamesUnique := ?_
      predParamsUnique := hwf.predParamsUnique
      parameterTypes := ?_
      variableArrayLengths := ?_
      variableInitializers := ?_
      objectiveType := ?_
      constraintsChecked := ?_ }
  · have h := hwf.valueNamesUnique
    refine List.Nodup.sublist ?_ h
    exact List.Sublist.append
      (List.Sublist.map _ List.filter_sublist)
      (List.Sublist.map _ List.filter_sublist)
  · intro d hd
    exact hwf.parameterTypes d (List.mem_filter.mp hd).1
  · intro d hd
    exact hwf.variableArrayLengths d (List.mem_filter.mp hd).1
  · intro d hd
    have hd' : d ∈ m.variables.filter isBasicVar := by
      simpa [normalizeModel] using hd
    obtain ⟨hdm, hb⟩ := List.mem_filter.mp hd'
    cases d with
    | array ty n anns es => simp [isBasicVar] at hb
    | basic ty n anns init =>
        cases init with
        | none => trivial
        | some v =>
            exact hasBaseType_norm hnu (hwf.variableInitializers _ hdm)
  · show match m.solve with
      | .satisfy _ => True
      | .minimize _ e | .maximize _ e => e.hasBaseType (normalizeModel m).staticEnv .int
    rw [hs]
    exact trivial
  · intro c' hc'
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hc'
    obtain ⟨params, hsig, hF⟩ := hwf.constraintsChecked c hc
    refine ⟨params, hsig, ?_⟩
    apply forall2_map_left _ _ _ c.args params hF
    intro e he pt hca
    exact checkArg_inline hwf hgate hca
      (gate_cons hgate c hc e he)


/-! ## Parameter reads of the compiled store -/

theorem parEnv_nodup {m : Model} (hnu : NamesNodup m) :
    ((m.parameters.filterMap
      (fun d2 => parDeclValue d2 |>.map (fun v2 => (ParDeclItem.name d2, v2)))).map
      Prod.fst).Nodup := by
  have hparnames : (m.parameters.map ParDeclItem.name).Nodup :=
    nodup_of_append_left hnu
  have hmain : ∀ (l : List ParDeclItem),
      (l.map ParDeclItem.name).Nodup →
      ((l.filterMap
        (fun d2 => parDeclValue d2 |>.map (fun v2 =>
          (ParDeclItem.name d2, v2)))).map Prod.fst).Nodup := by
    intro l
    induction l with
    | nil => intro _; simp
    | cons d2 rest ih =>
        intro hnod
        have h2 := List.nodup_cons.mp hnod
        cases hpv : parDeclValue d2 with
        | none =>
            rw [List.filterMap_cons, hpv]
            exact ih h2.2
        | some v2 =>
            rw [List.filterMap_cons, hpv]
            simp only [List.map_cons, Option.map_some, List.nodup_cons]
            refine ⟨?_, ih h2.2⟩
            intro hmem
            have hsub : ∀ x ∈ (rest.filterMap
                (fun d2 => parDeclValue d2 |>.map (fun v2 =>
                  (ParDeclItem.name d2, v2)))).map Prod.fst,
                x ∈ rest.map ParDeclItem.name := by
              intro x hx
              obtain ⟨p, hpmem, hpname⟩ := List.mem_map.mp hx
              obtain ⟨d4, hd4mem, hd4val⟩ :=
                mem_filterMap_src
                  (fun d2 => parDeclValue d2 |>.map (fun v2 =>
                    (ParDeclItem.name d2, v2))) rest p hpmem
              have hpfst : ParDeclItem.name d4 = p.1 := by
                cases hpd : parDeclValue d4 with
                | none => rw [hpd] at hd4val; exact absurd hd4val (by simp)
                | some w =>
                    rw [hpd] at hd4val
                    have hsome : some (ParDeclItem.name d4, w) = some p := hd4val
                    have hp : (ParDeclItem.name d4, w) = p := (Option.some.inj hsome)
                    exact congrArg Prod.fst hp
              exact List.mem_map.mpr ⟨d4, hd4mem, hpname ▸ hpfst⟩
            apply h2.1
            exact hsub _ hmem
  exact hmain m.parameters hparnames

/-- A scalar parameter of a compiled model reads its declared value in
    the compiled store. -/
theorem toStore_scalar_param {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem) (hwf : WellFormed fullSig m)
    {a : List Value} {d : ParDeclItem} (hd : d ∈ m.parameters) {v : Value}
    (hv : parDeclValue d = some v) :
    problem.toStore a (ParDeclItem.name d) = some v := by
  obtain ⟨_, slots, dcs, ⟨slots0, hslots0, hslots⟩, hcomp, hasm⟩ :=
    compileModel_ok_inv hc
  have hnu : NamesNodup m := hwf.valueNamesUnique
  have hnone : nameIndex (slots.map Prod.fst) (ParDeclItem.name d).name = none := by
    cases hni : nameIndex (slots.map Prod.fst) (ParDeclItem.name d).name with
    | none => rfl
    | some i =>
        exfalso
        rw [hslots, List.map_append] at hni
        rcases nameIndex_append_inv hni with hmodel | ⟨j, hj, _⟩
        · obtain ⟨_, hget⟩ := nameIndex_some _ _ i hmodel
          rw [List.getElem?_map] at hget
          cases hsl : slots0[i]? with
          | none => rw [hsl] at hget; simp at hget
          | some p =>
              rw [hsl] at hget
              have hp1 : p.1 = (ParDeclItem.name d).name := by
                simpa using hget
              have hpmem : p ∈ slots0 := List.mem_of_getElem? hsl
              obtain ⟨d', hd', hdslot⟩ := declSlots_mem m.variables slots0
                (declSlots_of_slotsChecked hslots0) p hpmem
              have := slot_name_eq_var d' p hdslot
              exact names_disj hnu hd hd'
                (ident_eq_of_name (hp1.symm.trans this))
        · obtain ⟨_, hget⟩ := nameIndex_some _ _ j hj
          rw [List.getElem?_map] at hget
          cases hsl : (modelAuxSlots m)[j]? with
          | none => rw [hsl] at hget; simp at hget
          | some p =>
              rw [hsl] at hget
              have hp1 : p.1 = (ParDeclItem.name d).name := by
                simpa using hget
              have hspec := (modelAuxSlots_spec hslots0).1 j p hsl
              have htaken : (ParDeclItem.name d).name ∈ auxTaken m slots0 :=
                List.mem_append.mpr (Or.inr
                  (List.mem_map.mpr ⟨d, hd, rfl⟩))
              rw [← hp1, hspec] at htaken
              exact auxName_not_mem htaken
  rw [hasm]
  exact toStore_param (m := m) hnone (parEnv_of_decl hd hv (parEnv_nodup hnu))


/-! ## The array front end is exact -/

/-- The bounds pass preserves the "no initializer" shape, because it only
    rewrites basic variable types. -/
theorem bounds_vars_none {m mb : Model}
    (hbm : boundsModel m = some mb)
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel mb = .ok problem) :
    ∀ d ∈ m.variables,
      ∃ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
        d = .basic ty n anns none := by
  intro d hd
  rcases boundsModel_inv hbm with rfl | ⟨env, rfl⟩
  · exact compileModel_vars_basic hc d hd
  · have hd' : tightenDecl env d ∈ (tightenModel m env).variables :=
      List.mem_map_of_mem hd
    obtain ⟨ty, n, anns, heq⟩ :=
      compileModel_vars_basic hc (tightenDecl env d) hd'
    cases d with
    | array ty0 n0 anns0 es =>
        simp [tightenDecl] at heq
    | basic ty0 n0 anns0 init =>
        obtain ⟨ty', hdecl, _⟩ :=
          tightenDecl_base (env := env) (ty := ty0) (n := n0)
            (anns := anns0) (v := init)
        rw [hdecl] at heq
        cases init with
        | none => exact ⟨ty0, n0, anns0, rfl⟩
        | some e => cases heq

/-- Every fragment declaration is an initializer-free basic declaration,
    as witnessed by the compiled model beyond the set expansion. -/
theorem vars_basic_of_fragment {m mb : Model}
    {problem : CompiledProblem DomConstraint} {sh : ShapeExpansion}
    {se : SetExpansion}
    (hsh : shapeExpandModel (normalizeFull m) = some sh)
    (hbm : boundsModel se.model = some mb)
    (hinv : se.Inv (setTaken sh.model) sh.model)
    (hc : compileModel mb = .ok problem) :
    ∀ d ∈ (fragmentModel (normalizeModel m)).variables,
      ∃ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
        d = .basic ty n anns none := by
  obtain ⟨_, _, _, stF, hexp, hvars0, hcons0, haux0⟩ := shapeExpandModelWith_inv hsh
  have hsrc_mem : ∀ d ∈ (normalizeFull m).variables, d ∈ sh.model.variables := by
    intro d hd
    rw [hvars0]
    exact List.mem_append_right _ hd
  have hvars := bounds_vars_none hbm hc
  intro d hd
  have hd' : restrictVarDecl
      (foldLiteralsModel (fragmentModel (normalizeModel m))) d ∈
      (normalizeFull m).variables := by
    simp only [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
      foldGroundModel, foldReifModel]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  rcases hinv.source _ (hsrc_mem _ hd') with hkept |
    ⟨i, hi, ty0, anns0, heq0, hty, huniv⟩
  · obtain ⟨ty, n, anns, hrest⟩ := hvars _ hkept
    cases d with
    | array ty0 n0 anns0 es =>
        simp only [restrictVarDecl] at hrest
        simp at hrest
    | basic ty0 n0 anns0 init =>
        cases init with
        | none => exact ⟨ty0, n0, anns0, rfl⟩
        | some e =>
            simp only [restrictVarDecl] at hrest
            simp at hrest
  · cases d with
    | array ty0 n0 anns0 es =>
        simp only [restrictVarDecl] at heq0
        cases heq0
    | basic ty0 n0 anns0 init =>
        cases init with
        | none => exact ⟨ty0, n0, anns0, rfl⟩
        | some e =>
            simp only [restrictVarDecl] at heq0
            cases heq0

/-- Every surviving normalized declaration is initializer-free: it is
    either kept by the set expansion (and then the compiled model has no
    initializer) or a removed set declaration (which has none). -/
theorem normalizeFull_init_trivial {m mb : Model}
    {problem : CompiledProblem DomConstraint} {sh : ShapeExpansion}
    {se : SetExpansion}
    (hsh : shapeExpandModel (normalizeFull m) = some sh)
    (hbm : boundsModel se.model = some mb)
    (hinv : se.Inv (setTaken sh.model) sh.model)
    (hc : compileModel mb = .ok problem)
    {store : Store} :
    ∀ d ∈ (normalizeFull m).variables, d.initializerHolds store := by
  obtain ⟨_, _, _, stF, hexp, hvars0, hcons0, haux0⟩ := shapeExpandModelWith_inv hsh
  have hsrc_mem : ∀ d ∈ (normalizeFull m).variables, d ∈ sh.model.variables := by
    intro d hd
    rw [hvars0]
    exact List.mem_append_right _ hd
  intro d hd
  rcases hinv.source _ (hsrc_mem _ hd) with hkept |
    ⟨i, hi, ty0, anns0, heq0, hty, huniv⟩
  · obtain ⟨ty, n, anns, heq⟩ := bounds_vars_none hbm hc d hkept
    subst heq
    exact trivial
  · subst heq0
    exact trivial

theorem compileFull_inv {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem) :
    arraysOkB m = true ∧ ∃ sh se mb p0,
      shapeExpandModel (normalizeFull m) = some sh ∧
      setExpandModel sh.model = some se ∧
      boundsModel se.model = some mb ∧
      compileModel mb = .ok p0 ∧ problem = relabel m se p0 := by
  unfold compileModelFull at hc
  split at hc
  · rename_i h
    split at hc
    · cases hc
    · rename_i sh hsh
      split at hc
      · cases hc
      · rename_i se hse
        split at hc
        · cases hc
        · rename_i mb hbm
          cases hcm : compileModel mb with
          | error e => rw [hcm] at hc; cases hc
          | ok p =>
              rw [hcm] at hc
              exact ⟨h, sh, se, mb, p, hsh, hse, hbm, hcm, (Except.ok.inj hc).symm⟩
  · cases hc

/-- Inversion of a successful `compileModelFull` together with the set
    expansion invariant and the well-formedness of the intermediate
    models. -/
theorem compileFull_inv_wf {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem)
    (hwf : WellFormed fullSig m) :
    ∃ sh se mb p0,
      shapeExpandModel (normalizeFull m) = some sh ∧
      setExpandModel sh.model = some se ∧
      boundsModel se.model = some mb ∧
      compileModel mb = .ok p0 ∧ problem = relabel m se p0 ∧
      WellFormed fullSig sh.model ∧
      SetExpansion.Inv (setTaken sh.model) sh.model se ∧
      WellFormed fullSig se.model ∧ WellFormed fullSig mb := by
  obtain ⟨hgate, sh, se, mb, p0, hsh, hse, hbm, hcn, rfl⟩ := compileFull_inv hc
  have hshfields := shapeExpandModel_fields hsh
  have hsefields := setExpandModel_fields hse
  have hsolve0 : ∃ anns, (normalizeModel m).solve = .satisfy anns := by
    have h1 := compileModel_solve_satisfy hcn
    rw [boundsModel_solve hbm] at h1
    rw [hsefields.2.2] at h1
    rw [hshfields.2.2] at h1
    simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
      foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
      substParamsModel] using h1
  have hprednf : (normalizeFull m).predicates = [] := by
    have h1 := compileModel_predicates_nil hcn
    rw [boundsModel_predicates hbm] at h1
    rw [hsefields.2.1] at h1
    rw [hshfields.2.1] at h1
    exact h1
  have hpred : (normalizeModel m).predicates = [] := by
    simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
      foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
      substParamsModel] using hprednf
  have hpredf : (fragmentModel (normalizeModel m)).predicates = [] := by
    simpa [fragmentModel, expandInitModel, substParamsModel] using hpred
  have hpredsh : sh.model.predicates = [] := by
    rw [hshfields.2.1]
    exact hprednf
  have hwfn := wf_normalize hwf hgate hsolve0
  have hwfF := wf_fragment hwfn hpred
  have hwff := wf_fold hwfF hpredf
  have hwfr := wf_restrict hwff hsolve0
  have hwfrFast : WellFormed fullSig
      (restrictSetInModelFast
        (foldLiteralsModel (fragmentModel (normalizeModel m)))) := by
    rw [restrictSetInModelFast_eq]
    exact hwfr
  have hwfsh := wf_shapeExpand hwfrFast hprednf (fun _ h => h) hsh
  have hinv := SetExpansion.Inv.of_wellFormed hwfsh (fun _ h => h) hse
  have hwse := wf_setExpand hwfsh hpredsh (fun _ h => h) hse
  have hwmb := wf_boundsModel hbm hwse
  exact ⟨sh, se, mb, p0, hsh, hse, hbm, hcn, rfl, hwfsh, hinv, hwse, hwmb⟩

theorem forall2_semEq_scalar :
    ∀ {vs ws : List Value}, Forall2 Value.SemEq vs ws →
    (∀ v ∈ vs, IsScalar v) → ws = vs := by
  intro vs
  induction vs with
  | nil =>
      intro ws h _
      cases ws with
      | nil => rfl
      | cons w ws => exact h.elim
  | cons v rest ih =>
      intro ws h hs
      cases ws with
      | nil => exact h.elim
      | cons w ws =>
          have hv := hs v List.mem_cons_self
          have hw : w = v := by
            obtain ⟨h1, h2⟩ := h
            rcases hv with ⟨i, rfl⟩ | ⟨b, rfl⟩
            · cases w <;> simp_all [Value.SemEq]
            · cases w <;> simp_all [Value.SemEq]
          rw [hw, ih h.2 (fun x hx => hs x (List.mem_cons_of_mem _ hx))]

theorem forall2_semEq_refl :
    ∀ (vs : List Value), (∀ v ∈ vs, IsScalar v) → Forall2 Value.SemEq vs vs := by
  intro vs
  induction vs with
  | nil => intro _; exact trivial
  | cons v rest ih =>
      intro hs
      refine ⟨?_, ih (fun x hx => hs x (List.mem_cons_of_mem _ hx))⟩
      rcases hs v List.mem_cons_self with ⟨i, rfl⟩ | ⟨b, rfl⟩ <;> simp [Value.SemEq]

theorem forall2_semEq_refl_of_forall :
    ∀ (vs : List Value), (∀ v ∈ vs, Value.SemEq v v) →
      Forall2 Value.SemEq vs vs := by
  intro vs
  induction vs with
  | nil => intro _; exact trivial
  | cons v rest ih =>
      intro h
      exact ⟨h v List.mem_cons_self,
        ih (fun x hx => h x (List.mem_cons_of_mem _ hx))⟩

theorem semEq_sym {v w : Value} (h : Value.SemEq v w) : Value.SemEq w v := by
  cases v with
  | bool a => cases w <;> simp_all [Value.SemEq]
  | int a => cases w <;> simp_all [Value.SemEq]
  | setOfInt sa =>
      cases w with
      | bool _ => simp [Value.SemEq] at h
      | int _ => simp [Value.SemEq] at h
      | setOfInt sb => intro x; exact (h x).symm
      | array _ => simp [Value.SemEq] at h
  | array _ => cases w <;> simp_all [Value.SemEq]

theorem forall2_semEq_sym {vs ws : List Value}
    (h : Forall2 Value.SemEq vs ws) : Forall2 Value.SemEq ws vs := by
  induction vs generalizing ws with
  | nil =>
      cases ws with
      | nil => exact trivial
      | cons w ws => exact h.elim
  | cons v rest ih =>
      cases ws with
      | nil => exact h.elim
      | cons w ws =>
          obtain ⟨hvw, hrest⟩ := h
          exact ⟨semEq_sym hvw, ih hrest⟩

theorem forall2_length {α β : Type} {R : α → β → Prop} :
    ∀ {l1 : List α} {l2 : List β}, Forall2 R l1 l2 →
      l1.length = l2.length := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 h
      cases l2 with
      | nil => rfl
      | cons _ _ => exact h.elim
  | cons a as ih =>
      intro l2 h
      cases l2 with
      | nil => exact h.elim
      | cons b bs =>
          obtain ⟨_, hrest⟩ := h
          simp only [List.length_cons]
          rw [ih hrest]

theorem forall2_getElem?_some {vs ws : List Value}
    (h : Forall2 Value.SemEq vs ws) :
    ∀ (k : Nat) {v w : Value}, vs[k]? = some v → ws[k]? = some w →
      Value.SemEq v w := by
  induction vs generalizing ws with
  | nil =>
      intro k v w hv _
      simp at hv
  | cons a rest ih =>
      intro k v w hv hw
      cases ws with
      | nil => exact h.elim
      | cons b bs =>
          obtain ⟨hab, hrest⟩ := h
          cases k with
      | zero =>
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hv hw
          rw [← hv, ← hw]
          exact hab
      | succ k =>
          simp only [List.getElem?_cons_succ] at hv hw
          exact ih hrest k hv hw

/-- A successful 1-based read is related under pointwise semantic
    equality. -/
theorem forall2_valuesGet1 {vs ws : List Value}
    (h : Forall2 Value.SemEq vs ws) {i : Int} {w : Value}
    (hg : valuesGet1 ws i = some w) :
    ∃ v, valuesGet1 vs i = some v ∧ Value.SemEq v w := by
  unfold valuesGet1 at hg ⊢
  by_cases hpos : 0 < i
  · simp only [hpos, if_true] at hg ⊢
    have hlen := forall2_length h
    have hlt : i.toNat - 1 < ws.length := (List.getElem?_eq_some_iff.mp hg).1
    have hlt' : i.toNat - 1 < vs.length := by rw [hlen]; exact hlt
    refine ⟨vs[i.toNat - 1], List.getElem?_eq_getElem hlt', ?_⟩
    exact forall2_getElem?_some h _ (List.getElem?_eq_getElem hlt') hg
  · simp only [hpos, if_false] at hg
    cases hg

/-- A set-typed declaration's type is unchanged by the membership
    domain restriction. -/
theorem restrictVarType_set {m : Model} {name : String} {ty : BasicVarType}
    (h : ty.base = .setOfInt) : restrictVarType m name ty = ty := by
  cases ty <;> simp_all [BasicVarType.base, BasicParType.base, restrictVarType]

/-- A source basic declaration survives `normalizeFull` with only its
    type possibly restricted. -/
theorem normalizeFull_basic_decl {m : Model} {ty : BasicVarType} {n : Ident}
    {anns : List Annotation}
    (hd : (.basic ty n anns none : VarDeclItem) ∈ m.variables) :
    (.basic (restrictVarType
        (foldLiteralsModel (fragmentModel (normalizeModel m))) n.name ty)
      n anns none : VarDeclItem) ∈ (normalizeFull m).variables := by
  simp only [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
    foldGroundModel, foldReifModel]
  have hnf : (.basic ty n anns none : VarDeclItem) ∈
      (normalizeModel m).variables :=
    List.mem_filter.mpr ⟨hd, rfl⟩
  have hfr : (.basic ty n anns none : VarDeclItem) ∈
      (fragmentModel (normalizeModel m)).variables := by
    rw [fragment_variables_eq]
    exact List.mem_map.mpr ⟨.basic ty n anns none, hnf,
      by simp [substParamVarDecl, expandInitDecl]⟩
  exact List.mem_map.mpr ⟨.basic ty n anns none, hfr, by simp [restrictVarDecl]⟩

/-- A source set declaration survives `normalizeFull` unchanged. -/
theorem normalizeFull_set_decl {m : Model} {ty : BasicVarType} {n : Ident}
    {anns : List Annotation}
    (hd : (.basic ty n anns none : VarDeclItem) ∈ m.variables)
    (hbase : ty.base = .setOfInt) :
    (.basic ty n anns none : VarDeclItem) ∈ (normalizeFull m).variables := by
  have h := normalizeFull_basic_decl (m := m) hd
  rwa [restrictVarType_set
    (m := foldLiteralsModel (fragmentModel (normalizeModel m)))
    (name := n.name) (ty := ty) hbase] at h

/-- A non-set declaration is kept by the set expansion pass. -/
theorem SetExpansion.Inv.kept_basic_of_base_ne {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m)
    {ty : BasicVarType} {n : Ident} {anns : List Annotation}
    (hd : (.basic ty n anns none : VarDeclItem) ∈ m.variables)
    (hbase : ty.base ≠ .setOfInt) :
    ∃ (ty' : BasicVarType) (anns' : List Annotation),
      (.basic ty' n anns' none : VarDeclItem) ∈ se.model.variables := by
  rcases inv.source _ hd with hkept | ⟨i, hi, ty0, anns0, heq0, hty0, huniv⟩
  · exact ⟨_, _, hkept⟩
  · exfalso
    injection heq0 with htyeq _ _ _
    rw [htyeq] at hbase
    exact hbase (setUniverse?_base huniv)

/-- A value admitted by a declared scalar type is semantically equal to
    itself. -/
theorem semEq_refl_of_contains {ty : BasicVarType} {v : Value}
    (h : ty.contains v) : Value.SemEq v v := by
  cases ty <;> cases v <;> simp_all [BasicVarType.contains, Value.SemEq]
  all_goals (split at h <;> simp_all)

/-- A value admitted by a non-set declaration is scalar. -/
theorem isScalar_of_contains_of_base_ne {ty : BasicVarType} {v : Value}
    (hbase : ty.base ≠ .setOfInt) (h : ty.contains v) : IsScalar v := by
  cases ty with
  | par t =>
      cases t with
      | bool => cases v <;> simp_all [IsScalar, BasicVarType.contains]
      | int => cases v <;> simp_all [IsScalar, BasicVarType.contains]
      | setOfInt => simp [BasicVarType.base, BasicParType.base] at hbase
  | intRange lo hi => cases v <;> simp_all [IsScalar, BasicVarType.contains]
  | intSet xs => cases v <;> simp_all [IsScalar, BasicVarType.contains]
  | setOfIntRange lo hi => simp [BasicVarType.base] at hbase
  | setOfIntSet xs => simp [BasicVarType.base] at hbase

/-- Semantic equality with a scalar is syntactic equality. -/
theorem eq_of_semEq_of_isScalar_right {v w : Value}
    (h : Value.SemEq v w) (hw : IsScalar w) : v = w := by
  rcases hw with ⟨i, rfl⟩ | ⟨b, rfl⟩
  · cases v <;> simp_all [Value.SemEq]
  · cases v <;> simp_all [Value.SemEq]

/-- A literal denotes a value semantically equal to itself. -/
theorem basicLiteral_semEq_denote (l : BasicLiteral) :
    Value.SemEq l.denote l.denote := by
  cases l with
  | bool b => rfl
  | int i => rfl
  | set sl => intro x; exact Iff.rfl

/-- A dynamically satisfying store is semantically faithful to the array
    definitions: parameter arrays are exact, variable arrays are
    elementwise semantically equal by their initializer condition. -/
theorem semFaithful_of_satisfies {m : Model} {s : Store}
    (hsat : SatisfiesDyn fullInterp m s)
    (hpar : LeanFzn.Semantics.ParamHonest m s) :
    SemFaithful (arrayDefs m) s := by
  intro x es hl
  obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x (arrayDefs m) es hl
  have hxy : x = y := ident_eq_of_name hyn.symm
  rw [hxy]
  rcases mem_arrayDefs hy with ⟨d, hd, idx, t, lits, rfl, rfl⟩ |
    ⟨d, hd, ty, anns, rfl⟩
  · refine ⟨lits.map BasicLiteral.denote, lits.map BasicLiteral.denote, ?_,
      mapM_lit_eval s lits, ?_⟩
    · have hp := hpar _ hd
      simpa [ParDeclItem.name, ParDeclItem.value] using hp
    · exact forall2_semEq_refl_of_forall _
        (fun v hv => by
          obtain ⟨l, _, rfl⟩ := List.mem_map.mp hv
          exact basicLiteral_semEq_denote l)
  · obtain ⟨vs, ws, hvs, hws, hF⟩ := hsat.2.2 _ hd
    exact ⟨vs, ws, hws, hvs, hF⟩

/-- A gated array name outside `setArrayNames` reads exactly the array of
    its evaluated elements.  Parameter arrays are fixed by parameter
    honesty; variable int/bool arrays have scalar element values, for
    which semantic equality is syntactic equality. -/
theorem semFaithful_exact_at {m : Model} (hgate : arraysOkB m = true)
    {s : Store} (hbr : BasicRead m s) (hpar : LeanFzn.Semantics.ParamHonest m s)
    (hsem : SemFaithful (arrayDefs m) s) {x : Ident} {es : List BasicExpr}
    (hl : lookupIdent x (arrayDefs m) = some es)
    (hx : x.name ∉ setArrayNames m) :
    ∃ vs, es.mapM (BasicExpr.eval s) = some vs ∧ s x = some (.array vs) := by
  obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x (arrayDefs m) es hl
  have hyx : y = x := ident_eq_of_name hyn
  rw [hyx] at hy
  rcases mem_arrayDefs hy with ⟨d, hd, idx, t, lits, rfl, rfl⟩ |
    ⟨d, hd, ty, anns, rfl⟩
  · refine ⟨lits.map BasicLiteral.denote, mapM_lit_eval s lits, ?_⟩
    have hp := hpar _ hd
    simpa [ParDeclItem.name, ParDeclItem.value] using hp
  · have hnot := elem_ne_set_of_not_mem hd hx
    obtain ⟨vs, ws, hws, hvs, hF⟩ := hsem x es hl
    rcases varArrayOk_inv (gate_vars hgate _ hd) with ⟨hel, h2⟩ | ⟨hel, h2⟩ |
      ⟨hel, h2⟩
    · obtain ⟨vs', hvs', hcont⟩ := var_elems hgate hbr hd
      have hvv : vs = vs' := by
        have := hvs.symm.trans hvs'
        exact Option.some.inj this
      have hbase : ty.elem.base ≠ .setOfInt := by
        rw [hel]; simp [BasicVarType.base, BasicParType.base]
      have hws_eq : ws = vs' := by
        rw [← hvv]
        exact forall2_semEq_scalar hF
          (fun v hv => isScalar_of_contains_of_base_ne hbase (hcont v (hvv ▸ hv)))
      rw [hws_eq] at hws
      exact ⟨vs', hvs', hws⟩
    · obtain ⟨vs', hvs', hcont⟩ := var_elems hgate hbr hd
      have hvv : vs = vs' := by
        have := hvs.symm.trans hvs'
        exact Option.some.inj this
      have hbase : ty.elem.base ≠ .setOfInt := by
        rw [hel]; simp [BasicVarType.base, BasicParType.base]
      have hws_eq : ws = vs' := by
        rw [← hvv]
        exact forall2_semEq_scalar hF
          (fun v hv => isScalar_of_contains_of_base_ne hbase (hcont v (hvv ▸ hv)))
      rw [hws_eq] at hws
      exact ⟨vs', hvs', hws⟩
    · exact absurd hel hnot

/-- Inlining preserves evaluation on expressions that mention no
    set-valued variable array. -/
theorem inlineExpr_eval_eq_of_not_set {m : Model} (hgate : arraysOkB m = true)
    {s : Store} (hbr : BasicRead m s) (hpar : LeanFzn.Semantics.ParamHonest m s)
    (hsem : SemFaithful (arrayDefs m) s) {e : Expr}
    (hns : exprMentionsName (setArrayNames m) e = false) :
    (inlineExpr (arrayDefs m) e).eval s = e.eval s := by
  cases e with
  | array es => rfl
  | basic b =>
      cases b with
      | lit l => rfl
      | ident x =>
          simp only [exprMentionsName, mentionsName] at hns
          have hx : x.name ∉ setArrayNames m := by
            simpa using hns
          cases hl : lookupIdent x (arrayDefs m) with
          | none => simp [inlineExpr, hl]
          | some es =>
              obtain ⟨vs, hvs, hxs⟩ :=
                semFaithful_exact_at hgate hbr hpar hsem hl hx
              simp [inlineExpr, hl, Expr.eval, BasicExpr.eval, hvs, hxs]

/-- Under the gate, an argument that mentions no set-array name inlines
    to a constraint that holds iff the original does. -/
theorem holds_inline_of_no_set_use {m : Model} (hgate : arraysOkB m = true)
    {s : Store} (hbr : BasicRead m s) (hpar : LeanFzn.Semantics.ParamHonest m s)
    (hsem : SemFaithful (arrayDefs m) s) {c : ConstraintItem}
    (hns : ∀ e ∈ c.args, exprMentionsName (setArrayNames m) e = false) :
    (inlineConstraint (arrayDefs m) c).Holds fullInterp s ↔ c.Holds fullInterp s := by
  have hmap : (c.args.map (inlineExpr (arrayDefs m))).mapM (Expr.eval s) =
      c.args.mapM (Expr.eval s) := by
    rw [List.mapM_map]
    apply mapM_congr
    intro e he
    exact inlineExpr_eval_eq_of_not_set hgate hbr hpar hsem (hns e he)
  unfold ConstraintItem.Holds
  show (∃ args, (c.args.map (inlineExpr (arrayDefs m))).mapM (Expr.eval s) = some args ∧
      fullInterp c.name args) ↔ _
  rw [hmap]

/-! ### Semantic congruence for the three set-element predicates -/

theorem stdInterp_array_set_element_apply (args : List Value) :
    stdInterp (Ident.mk "array_set_element") args =
      match args with
      | [.int i, .array xs, .setOfInt e] =>
          (match valuesGet1 xs i with
            | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
            | _ => False)
      | _ => False := rfl

theorem stdInterp_array_var_set_element_apply (args : List Value) :
    stdInterp (Ident.mk "array_var_set_element") args =
      match args with
      | [.int i, .array xs, .setOfInt e] =>
          (match valuesGet1 xs i with
            | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
            | _ => False)
      | _ => False := rfl

theorem stdInterp_array_var_set_element_nonshifted_apply (args : List Value) :
    stdInterp (Ident.mk "array_var_set_element_nonshifted") args =
      match args with
      | [.int i, .array xs, .setOfInt e] =>
          (match valuesGet1 xs i with
            | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
            | _ => False)
      | _ => False := rfl

/-- The membership comparison of a selected set is invariant under
    pointwise semantic equality of the arrays. -/
theorem setElement_pred_congr {vs ws : List Value}
    (h : Forall2 Value.SemEq vs ws) {i : Int} {e : IntSetValue} :
    (match valuesGet1 vs i with
      | some (.setOfInt v) => ∀ j, v.Contains j ↔ e.Contains j
      | _ => False) ↔
    (match valuesGet1 ws i with
      | some (.setOfInt w) => ∀ j, w.Contains j ↔ e.Contains j
      | _ => False) := by
  cases hg : valuesGet1 ws i with
  | none =>
      have hnone : valuesGet1 vs i = none := by
        cases hv : valuesGet1 vs i with
        | none => rfl
        | some v =>
            obtain ⟨w, hw, _⟩ :=
              forall2_valuesGet1 (forall2_semEq_sym h) hv
            rw [hg] at hw
            cases hw
      simp [hnone, hg]
  | some w =>
      obtain ⟨v, hv, hvw⟩ := forall2_valuesGet1 h hg
      simp only [hv, hg]
      cases v with
      | bool _ => cases w <;> simp_all [Value.SemEq]
      | int _ => cases w <;> simp_all [Value.SemEq]
      | array _ => cases w <;> simp_all [Value.SemEq]
      | setOfInt sv =>
          cases w with
          | bool _ => simp_all [Value.SemEq]
          | int _ => simp_all [Value.SemEq]
          | array _ => simp_all [Value.SemEq]
          | setOfInt sw =>
              simp only
              constructor
              · intro hh j
                exact (hvw j).symm.trans (hh j)
              · intro hh j
                exact (hvw j).trans (hh j)

theorem stdInterp_setElement_body {vs ws : List Value}
    (h : Forall2 Value.SemEq vs ws) {i e : Value} :
    (match [i, .array vs, e] with
      | [.int ii, .array xs, .setOfInt ee] =>
          (match valuesGet1 xs ii with
            | some (.setOfInt v) => ∀ j, v.Contains j ↔ ee.Contains j
            | _ => False)
      | _ => False) ↔
    (match [i, .array ws, e] with
      | [.int ii, .array xs, .setOfInt ee] =>
          (match valuesGet1 xs ii with
            | some (.setOfInt v) => ∀ j, v.Contains j ↔ ee.Contains j
            | _ => False)
      | _ => False) := by
  cases i with
  | int ii =>
      cases e with
      | int _ => simp
      | bool _ => simp
      | array _ => simp
      | setOfInt ee =>
          simp only
          exact setElement_pred_congr h
  | bool _ => simp
  | setOfInt _ => simp
  | array _ => simp

/-- The three set-element predicates agree on arrays that are pointwise
    semantically equal. -/
theorem arraySetElement_congr {name : String} {i e : Value}
    {vs ws : List Value} (h : Forall2 Value.SemEq vs ws)
    (hname : name = "array_var_set_element" ∨ name = "array_set_element" ∨
      name = "array_var_set_element_nonshifted") :
    fullInterp (Ident.mk name) [i, .array vs, e] ↔
      fullInterp (Ident.mk name) [i, .array ws, e] := by
  rcases hname with rfl | rfl | rfl
  · simpa only [fullInterp_eq_std_of_not_global (n := "array_var_set_element")
        (by decide), stdInterp_array_var_set_element_apply]
      using stdInterp_setElement_body h
  · simpa only [fullInterp_eq_std_of_not_global (n := "array_set_element")
        (by decide), stdInterp_array_set_element_apply]
      using stdInterp_setElement_body h
  · simpa only [
        fullInterp_eq_std_of_not_global (n := "array_var_set_element_nonshifted")
        (by decide), stdInterp_array_var_set_element_nonshifted_apply]
      using stdInterp_setElement_body h

/-- A whitelisted three-argument set-element constraint holds after
    inlining iff it held before. -/
theorem inline_three_holds {m : Model} (hgate : arraysOkB m = true) {s : Store}
    (hbr : BasicRead m s) (hpar : LeanFzn.Semantics.ParamHonest m s)
    (hsem : SemFaithful (arrayDefs m) s)
    {c : ConstraintItem} (hc : c ∈ m.constraints)
    {a0 a1 a2 : Expr} (hargs : c.args = [a0, a1, a2])
    (hname : c.name.name = "array_var_set_element" ∨
      c.name.name = "array_set_element" ∨
      c.name.name = "array_var_set_element_nonshifted") :
    (inlineConstraint (arrayDefs m) c).Holds fullInterp s ↔ c.Holds fullInterp s := by
  have hname' := hname
  have huse := gate_setUse hgate c hc
  unfold setArrayUseOkB at huse
  rw [hargs] at huse
  rcases hname with hn | hn | hn <;> rw [hn] at huse
  all_goals
    simp only [Bool.and_eq_true] at huse
    have h0 : exprMentionsName (setArrayNames m) a0 = false := by
      simpa using huse.1.1
    have h2 : exprMentionsName (setArrayNames m) a2 = false := by
      simpa using huse.2
    have he0 : (inlineExpr (arrayDefs m) a0).eval s = a0.eval s :=
      inlineExpr_eval_eq_of_not_set hgate hbr hpar hsem h0
    have he2 : (inlineExpr (arrayDefs m) a2).eval s = a2.eval s :=
      inlineExpr_eval_eq_of_not_set hgate hbr hpar hsem h2
    have hmiddle_of_old : ∀ {w : Value}, a1.eval s = some w →
        ∃ v, (inlineExpr (arrayDefs m) a1).eval s = some v ∧
          (v = w ∨ ∃ vs ws, v = .array vs ∧ w = .array ws ∧
            Forall2 Value.SemEq vs ws) := by
      intro w hw
      cases a1 with
      | array es => exact ⟨w, by simpa [inlineExpr] using hw, Or.inl rfl⟩
      | basic b =>
          cases b with
          | lit l => exact ⟨w, by simpa [inlineExpr] using hw, Or.inl rfl⟩
          | ident x =>
              cases hl : lookupIdent x (arrayDefs m) with
              | none => exact ⟨w, by simpa [inlineExpr, hl] using hw, Or.inl rfl⟩
              | some es =>
                  obtain ⟨vs, ws, hws, hvs, hF⟩ := hsem x es hl
                  have hw' : w = .array ws := by
                    have h' : s x = some w := hw
                    exact Option.some.inj (h'.symm.trans hws)
                  subst hw'
                  refine ⟨.array vs, ?_, Or.inr ⟨vs, ws, rfl, rfl, hF⟩⟩
                  simp [inlineExpr, hl, Expr.eval, hvs]
    have hmiddle_of_new : ∀ {v : Value},
        (inlineExpr (arrayDefs m) a1).eval s = some v →
        ∃ w, a1.eval s = some w ∧
          (v = w ∨ ∃ vs ws, v = .array vs ∧ w = .array ws ∧
            Forall2 Value.SemEq vs ws) := by
      intro v hv
      cases a1 with
      | array es => exact ⟨v, by simpa [inlineExpr] using hv, Or.inl rfl⟩
      | basic b =>
          cases b with
          | lit l => exact ⟨v, by simpa [inlineExpr] using hv, Or.inl rfl⟩
          | ident x =>
              cases hl : lookupIdent x (arrayDefs m) with
              | none => exact ⟨v, by simpa [inlineExpr, hl] using hv, Or.inl rfl⟩
              | some es =>
                  obtain ⟨vs, ws, hws, hvs, hF⟩ := hsem x es hl
                  have hv' : v = .array vs := by
                    have h' : (es.mapM (BasicExpr.eval s)).map Value.array =
                        some v := by
                      simpa [inlineExpr, hl, Expr.eval] using hv
                    rw [hvs] at h'
                    exact (Option.some.inj h').symm
                  subst hv'
                  exact ⟨.array ws, by simpa only [Expr.eval, BasicExpr.eval] using hws,
                    Or.inr ⟨vs, ws, rfl, rfl, hF⟩⟩
    constructor
    · rintro ⟨argsN, hmapN, hpredN⟩
      have hmapN' : ([inlineExpr (arrayDefs m) a0,
          inlineExpr (arrayDefs m) a1,
          inlineExpr (arrayDefs m) a2].mapM (Expr.eval s)) = some argsN := by
        simpa [inlineConstraint, hargs] using hmapN
      rw [mapM_three_iff] at hmapN'
      obtain ⟨v0, v1, v2, h0N, h1N, h2N, rfl⟩ := hmapN'
      obtain ⟨w1, hw1, hrel⟩ := hmiddle_of_new h1N
      have h0O : a0.eval s = some v0 := by rw [← he0]; exact h0N
      have h2O : a2.eval s = some v2 := by rw [← he2]; exact h2N
      refine ⟨[v0, w1, v2], ?_, ?_⟩
      · rw [hargs, mapM_three_iff]
        exact ⟨v0, w1, v2, h0O, hw1, h2O, rfl⟩
      · rcases hrel with rfl | ⟨vs, ws, rfl, rfl, hF⟩
        · exact hpredN
        · have hcongr := (arraySetElement_congr (name := c.name.name)
              (i := v0) (e := v2) (vs := vs) (ws := ws) hF
              (by rcases hname' with h | h | h
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h)
                  · exact Or.inr (Or.inr h))).mp hpredN
          simpa [inlineConstraint] using hcongr
    · rintro ⟨argsO, hmapO, hpredO⟩
      have hmapO' : ([a0, a1, a2].mapM (Expr.eval s)) = some argsO := by
        simpa [hargs] using hmapO
      rw [mapM_three_iff] at hmapO'
      obtain ⟨w0, w1, w2, h0O, h1O, h2O, rfl⟩ := hmapO'
      obtain ⟨v1, hv1, hrel⟩ := hmiddle_of_old h1O
      have h0N : (inlineExpr (arrayDefs m) a0).eval s = some w0 := by
        rw [he0]; exact h0O
      have h2N : (inlineExpr (arrayDefs m) a2).eval s = some w2 := by
        rw [he2]; exact h2O
      refine ⟨[w0, v1, w2], ?_, ?_⟩
      · have hmap : ([inlineExpr (arrayDefs m) a0,
            inlineExpr (arrayDefs m) a1,
            inlineExpr (arrayDefs m) a2].mapM (Expr.eval s)) =
            some [w0, v1, w2] := by
          rw [mapM_three_iff]
          exact ⟨w0, v1, w2, h0N, hv1, h2N, rfl⟩
        simpa [inlineConstraint, hargs] using hmap
      · rcases hrel with rfl | ⟨vs, ws, rfl, rfl, hF⟩
        · exact hpredO
        · have hcongr := (arraySetElement_congr (name := c.name.name)
              (i := w0) (e := w2) (vs := ws) (ws := vs)
              (forall2_semEq_sym hF)
              (by rcases hname' with h | h | h
                  · exact Or.inl h
                  · exact Or.inr (Or.inl h)
                  · exact Or.inr (Or.inr h))).mp hpredO
          simpa [inlineConstraint] using hcongr

/-- Constraint-level inlining preserves satisfaction under semantic
    faithfulness: the only set-array occurrences the gate admits are the
    array argument of the three set-element predicates. -/
theorem holds_inline_sem {m : Model} (hgate : arraysOkB m = true) {s : Store}
    (hbr : BasicRead m s) (hpar : LeanFzn.Semantics.ParamHonest m s)
    (hsem : SemFaithful (arrayDefs m) s)
    {c : ConstraintItem} (hc : c ∈ m.constraints) :
    (inlineConstraint (arrayDefs m) c).Holds fullInterp s ↔ c.Holds fullInterp s := by
  have huse := gate_setUse hgate c hc
  unfold setArrayUseOkB at huse
  split at huse
  · rename_i a0 a1 a2 hn ha
    exact inline_three_holds hgate hbr hpar hsem hc ha (Or.inl hn)
  · rename_i a0 a1 a2 hn ha
    exact inline_three_holds hgate hbr hpar hsem hc ha (Or.inr (Or.inl hn))
  · rename_i a0 a1 a2 hn ha
    exact inline_three_holds hgate hbr hpar hsem hc ha (Or.inr (Or.inr hn))
  · apply holds_inline_of_no_set_use hgate hbr hpar hsem
    intro e he
    have := List.all_eq_true.mp huse e he
    simpa using this

/-- A parameter name is not a removed set name. -/
theorem SetExpansion.Inv.parName_not_set {m : Model} {se : SetExpansion}
    {taken : List String} (inv : se.Inv taken m) (hwf : WellFormed fullSig m)
    {d : ParDeclItem} (hd : d ∈ m.parameters) : d.name.name ∉ se.setNames := by
  intro hmem
  obtain ⟨i, hi, hiname⟩ := List.mem_map.mp hmem
  obtain ⟨n', D⟩ := inv.decls
  obtain ⟨ty, x, anns, hxmem, hxnam, hty, huniv⟩ := D.info_source i hi
  exact names_disj hwf.valueNamesUnique hd hxmem (ident_eq_of_name (by
    rw [← hiname]
    exact hxnam))

/-- **COVERAGE for the array + set front end**: a store that satisfies the
    dynamic conditions of the original model (with its parameter and
    array declarations honoured) is covered by an accepted assignment
    of the compiled problem, up to semantic set equality. -/
theorem compileFull_covers_agree {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem)
    (hwf : WellFormed fullSig m)
    {store : Store}
    (hsat : SatisfiesDyn fullInterp m store)
    (hparam : LeanFzn.Semantics.ParamHonest m store) :
    ∃ a, a ∈ allAssigns problem.domains ∧ accepts problem a = true ∧
      ∀ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
        (.basic ty n anns none : VarDeclItem) ∈ m.variables →
        ∃ v w, problem.toStore a n = some v ∧ store n = some w ∧
          Value.SemEq v w := by
  obtain ⟨hgate, sh, se, mb, p0, hsh, hse, hbm, hcn, rfl⟩ := compileFull_inv hc
  have hnu : NamesNodup m := hwf.valueNamesUnique
  have hshfields := shapeExpandModel_fields hsh
  have hsefields := setExpandModel_fields hse
  have hsolve0 : ∃ anns, (normalizeModel m).solve = .satisfy anns := by
    have h1 := compileModel_solve_satisfy hcn
    rw [boundsModel_solve hbm] at h1
    rw [hsefields.2.2] at h1
    rw [hshfields.2.2] at h1
    simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
      foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
      substParamsModel] using h1
  have hwfn := wf_normalize hwf hgate hsolve0
  have hprednf : (normalizeFull m).predicates = [] := by
    have h1 := compileModel_predicates_nil hcn
    rw [boundsModel_predicates hbm] at h1
    rw [hsefields.2.1] at h1
    rw [hshfields.2.1] at h1
    exact h1
  have hpred : (normalizeModel m).predicates = [] := by
    simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
      foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
      substParamsModel] using hprednf
  have hpredf : (fragmentModel (normalizeModel m)).predicates = [] := by
    simpa [fragmentModel, expandInitModel, substParamsModel] using hpred
  have hpredsh : sh.model.predicates = [] := by
    rw [hshfields.2.1]
    exact hprednf
  have hwfF := wf_fragment hwfn hpred
  have hwff := wf_fold hwfF hpredf
  have hwfr := wf_restrict hwff hsolve0
  have hwfrFast : WellFormed fullSig
      (restrictSetInModelFast
        (foldLiteralsModel (fragmentModel (normalizeModel m)))) := by
    rw [restrictSetInModelFast_eq]
    exact hwfr
  have hwfsh := wf_shapeExpand hwfrFast hprednf (fun _ h => h) hsh
  have hinv := SetExpansion.Inv.of_wellFormed hwfsh (fun _ h => h) hse
  have hwse := wf_setExpand hwfsh hpredsh (fun _ h => h) hse
  have hwmb := wf_boundsModel hbm hwse
  obtain ⟨_, _, _, stF, hexp, hvars, hcons, haux⟩ := shapeExpandModelWith_inv hsh
  have hstwf : stF.WF (setTaken (normalizeFull m)) (normalizeFull m) :=
    shapeExpandConstraints_wf (ShapeState.initial_wf _ _) hwfrFast
      (fun _ h => h) hexp
  have henc : sh.encStore store = stF.encStore store :=
    ShapeExpansion.encStore_eq_of haux
  have hsrc_mem : ∀ d ∈ (normalizeFull m).variables, d ∈ sh.model.variables := by
    intro d hd
    rw [hvars]
    exact List.mem_append_right _ hd
  have henc_taken : ∀ x : Ident,
      x.name ∈ setTaken (normalizeFull m) → sh.encStore store x = store x := by
    intro x hx
    rw [henc]
    exact ShapeExpansion.encStore_at_taken hstwf hx store
  -- the source store satisfies the normalized model
  have hsem : SemFaithful (arrayDefs m) store :=
    semFaithful_of_satisfies hsat hparam
  obtain ⟨hcons0, hvar0, hinit0⟩ := hsat
  have hs : BasicRead m store := fun ty n anns hd => by
    simpa using hvar0 _ hd
  have hcons_n : ∀ c ∈ (normalizeModel m).constraints,
      c.Holds fullInterp store := by
    intro c' hc'
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc'
    exact (holds_inline_sem hgate hs hparam hsem hcm).mpr (hcons0 c hcm)
  have hvars_n : ∀ d ∈ (normalizeModel m).variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v := by
    intro d hd
    exact hvar0 d (List.mem_filter.mp hd).1
  have hinit_n : ∀ d ∈ (normalizeModel m).variables,
      d.initializerHolds store :=
    fun d hd => hinit0 d (List.mem_filter.mp hd).1
  have hsat_n : SatisfiesDyn fullInterp (normalizeModel m) store :=
    ⟨hcons_n, hvars_n, hinit_n⟩
  have hparam_n : LeanFzn.Semantics.ParamHonest (normalizeModel m) store := by
    intro d hd
    exact hparam d (List.mem_filter.mp hd).1
  have henv_n : ∀ x v, parEnv (normalizeModel m) x = some v → store x = some v :=
    parEnv_sound hparam_n
  have hfrag := fragment_covers henv_n hsat_n
  have hcons_f : ∀ c ∈ (foldLiteralsModel (fragmentModel (normalizeModel m))).constraints,
      c.Holds fullInterp store :=
    foldLiterals_covers hfrag.1
  obtain ⟨hcons_r, hvars_r⟩ := restrictSetIn_covers hcons_f hfrag.2.1
  have hnf : normalizeFull m = restrictSetInModel
      (foldLiteralsModel (fragmentModel (normalizeModel m))) := by
    simp [normalizeFull, restrictSetInModelFast_eq]
  have hinit_r : ∀ d ∈ (restrictSetInModel
      (foldLiteralsModel (fragmentModel (normalizeModel m)))).variables,
      d.initializerHolds store := by
    simpa [hnf] using normalizeFull_init_trivial hsh hbm hinv hcn
  have hsat_r : SatisfiesDyn fullInterp (normalizeFull m) store := by
    rw [hnf]
    exact ⟨hcons_r, hvars_r, hinit_r⟩
  -- the completeness store of the shape pass satisfies the shape model
  have hsat_sh : SatisfiesDyn fullInterp sh.model (sh.encStore store) :=
    shapeExpand_complete hwfrFast (fun _ h => h) hsh hsat_r
  -- the completeness store satisfies the set-expanded model
  have hsat_se := (setExpand_complete hwfsh (fun _ h => h) hse hsat_sh).1
  have hsat_b := boundsModel_sound hbm hsat_se
  have hvars_b' : ∀ d ∈ mb.variables, match d with
      | .basic ty n _ _ =>
          ∃ v, (encodeStore se (sh.encStore store)) n = some v ∧ ty.contains v
      | .array _ _ _ _ => False := by
    intro d hd
    obtain ⟨ty, n, anns, heq⟩ := compileModel_vars_basic hcn d hd
    subst heq
    simpa using hsat_b.2.1 _ hd
  have hcov := compile_covers_agree (m := mb) hcn hwmb
      (store := encodeStore se (sh.encStore store)) hsat_b.1 hvars_b'
    (by
      intro d hd v hv
      rw [boundsModel_parameters hbm] at hd
      rw [hinv.parameters] at hd
      have hd' : d ∈ (normalizeFull m).parameters := by
        rw [hshfields.1] at hd
        exact hd
      have hdm : d ∈ m.parameters := by
        have h : d ∈ m.parameters.filter (fun d => !isArrayPar d) := hd'
        exact (List.mem_filter.mp h).1
      have henc1 : encodeStore se (sh.encStore store) d.name =
          sh.encStore store d.name :=
        SetExpansion.encodeStore_of_mem_taken hinv (x := d.name)
          (List.mem_append_left _ (List.mem_map.mpr ⟨d, hd, rfl⟩))
      have henc2 : sh.encStore store d.name = store d.name :=
        henc_taken d.name (List.mem_append_left _
          (List.mem_map.mpr ⟨d, hd', rfl⟩))
      show encodeStore se (sh.encStore store) d.name = some v
      rw [henc1, henc2, ← parDeclValue_value hv]
      exact hparam d hdm)
  obtain ⟨a, h1, h2, h3⟩ := hcov
  refine ⟨a, h1, h2, ?_⟩
  intro ty n anns hd
  have hnone := lookup_arrayDefs_none hnu (x := n) (Or.inr ⟨_, hd, rfl, rfl⟩)
  have hdom := hvar0 (.basic ty n anns none) hd
  have hstore : (relabel m se p0).toStore a n =
      setStore se (p0.toStore a) n := by
    show fullStore (arrayDefs m) (setStore se (p0.toStore a)) n = _
    rw [fullStore_of_none hnone]
  have hdn := normalizeFull_basic_decl (m := m) hd
  have htake : n.name ∈ setTaken (normalizeFull m) :=
    List.mem_append_right _ (List.mem_map.mpr
      ⟨(.basic _ n anns none : VarDeclItem), hdn, rfl⟩)
  rw [hstore]
  rcases hinv.source _ (hsrc_mem _ hdn) with hkept |
    ⟨i, hi, ty0, anns0, heq0, hty, huniv⟩
  · -- kept (non-set) declaration: the reconstruction is the identity
    have hnotname : n.name ∉ se.setNames := by
      have h := hinv.kept_name_not_set hkept
      simpa [VarDeclItem.name] using h
    have hnotbool : n.name ∉ se.boolNames := by
      have h := hinv.varName_not_bool (hsrc_mem _ hdn)
      simpa [VarDeclItem.name] using h
    obtain ⟨d', hd', hname⟩ := boundsModel_variables_mem hbm hkept
    obtain ⟨ty', n', anns', heq'⟩ := compileModel_vars_basic hcn d' hd'
    subst heq'
    have hn' : n' = n := by simpa [VarDeclItem.name] using hname
    have hread : p0.toStore a n = encodeStore se (sh.encStore store) n := by
      rw [← hn']
      exact h3 ty' n' anns' hd'
    rw [SetExpansion.setStore_of_not_mem hnotname, hread,
      SetExpansion.encodeStore_of_not_bool hnotbool, henc_taken n htake]
    obtain ⟨w, hw, hcont⟩ := hdom
    exact ⟨w, w, hw, hw, semEq_refl_of_contains hcont⟩
  · -- removed set variable: the rebuilt set is semantically equal
    injection heq0 with htyeq hnname hannseq hiniteq
    have hb0 : ty.base = ty0.base := by
      rw [← restrictVarType_base
        (m := foldLiteralsModel (fragmentModel (normalizeModel m)))
        (name := n.name) (ty := ty), htyeq]
    have hbase : ty.base = .setOfInt := by
      rw [hb0]
      exact setUniverse?_base huniv
    have hty0 : ty0 = ty := by
      rw [← htyeq, restrictVarType_set hbase]
    subst hty0
    subst hnname
    subst hannseq
    obtain ⟨w, hw, hcont⟩ := hdom
    obtain ⟨sv, rfl⟩ := setOfInt_of_contains_set hbase hcont
    have hiset : i.name ∈ setTaken (normalizeFull m) := htake
    have hsrc : i.sourceSet? (sh.encStore store) = some sv := by
      unfold SetInfo.sourceSet?
      rw [henc_taken (Ident.mk i.name) hiset, hw]
    have htyc : i.ty.contains (.setOfInt sv) := by
      rw [hty]
      exact hcont
    have hpoint : ∀ x, (i.rebuilt (encodeStore se (sh.encStore store))).Contains x ↔
        sv.Contains x :=
      SetInfo.rebuilt_encodeStore_contains_iff hinv.boolNames_nodup
        (hinv.bools_nodup i hi) (hinv.values_nodup i hi) hi hsrc
        (by rw [hty]; exact huniv) htyc
    have hreadi : ∀ p ∈ i.bools, p0.toStore a (Ident.mk p.1) =
        encodeStore se (sh.encStore store) (Ident.mk p.1) := by
      intro p hp
      have hfresh := hinv.fresh_vars i hi p hp
      obtain ⟨d2, hd2, hname2⟩ := boundsModel_variables_mem hbm hfresh
      obtain ⟨ty2, n2, anns2, heq2⟩ := compileModel_vars_basic hcn d2 hd2
      subst heq2
      have hn2 : n2 = Ident.mk p.1 := by
        simpa [VarDeclItem.name] using hname2
      rw [← hn2]
      exact h3 ty2 n2 anns2 hd2
    have hcongr : ∀ x : Int,
        (i.rebuilt (p0.toStore a)).Contains x ↔
          (i.rebuilt (encodeStore se (sh.encStore store))).Contains x := fun x =>
      SetInfo.rebuilt_congr_contains (i := i)
        (s := p0.toStore a) (t := encodeStore se (sh.encStore store)) hreadi (v := x)
    refine ⟨.setOfInt (i.rebuilt (p0.toStore a)), .setOfInt sv, ?_, hw, ?_⟩
    · exact SetExpansion.setStore_at
        (SetExpansion.infoOf_eq_some_of_mem hinv.setNames_nodup hi)
    · intro x
      exact (hcongr (x := x)).trans (hpoint x)

theorem compileFull_covers {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem)
    (hwf : WellFormed fullSig m)
    {store : Store}
    (hsat : SatisfiesDyn fullInterp m store)
    (hparam : LeanFzn.Semantics.ParamHonest m store) :
    ∃ a, a ∈ allAssigns problem.domains ∧ accepts problem a = true := by
  obtain ⟨a, h1, h2, _⟩ := compileFull_covers_agree hc hwf hsat hparam
  exact ⟨a, h1, h2⟩

/-- **COVERAGE (set-free corollary)**: for models with no set-typed basic
    declarations the reconstructed store is syntactically equal to the
    source store on every source variable. -/
theorem compileFull_covers_agree_setFree {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem)
    (hwf : WellFormed fullSig m)
    (hfree : ∀ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
      (.basic ty n anns none : VarDeclItem) ∈ m.variables →
      ty.base ≠ .setOfInt)
    {store : Store}
    (hsat : SatisfiesDyn fullInterp m store)
    (hparam : LeanFzn.Semantics.ParamHonest m store) :
    ∃ a, a ∈ allAssigns problem.domains ∧ accepts problem a = true ∧
      ∀ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
        (.basic ty n anns none : VarDeclItem) ∈ m.variables →
        problem.toStore a n = store n := by
  obtain ⟨a, h1, h2, h3⟩ := compileFull_covers_agree hc hwf hsat hparam
  refine ⟨a, h1, h2, ?_⟩
  intro ty n anns hd
  obtain ⟨v, w, hv, hw, heq⟩ := h3 ty n anns hd
  obtain ⟨w', hw', hcont⟩ := hsat.2.1 (.basic ty n anns none) hd
  have hww : w' = w := Option.some.inj (hw'.symm.trans hw)
  have hcont' : ty.contains w := hww ▸ hcont
  have hscalar := isScalar_of_contains_of_base_ne (hfree ty n anns hd) hcont'
  have hvw : v = w := eq_of_semEq_of_isScalar_right heq hscalar
  rw [hvw] at hv
  rw [hv, hw]

/-- **EXACTNESS for the array front end**: an accepted assignment's
    store (the compiled store extended with the array values) satisfies
    every dynamic condition of the ORIGINAL model and is
    parameter-honest, parameter arrays and variable-array aliases
    included. -/
theorem compileFull_exact {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem)
    (hwf : WellFormed fullSig m)
    {a : List Value}
    (hmem : a ∈ allAssigns problem.domains)
    (hacc : accepts problem a = true) :
    SatisfiesDyn fullInterp m (problem.toStore a) ∧
      LeanFzn.Semantics.ParamHonest m (problem.toStore a) := by
  obtain ⟨hgate, sh, se, mb, p0, hsh, hse, hbm, hcn, rfl⟩ := compileFull_inv hc
  have hnu : NamesNodup m := hwf.valueNamesUnique
  have hshfields := shapeExpandModel_fields hsh
  have hsefields := setExpandModel_fields hse
  have hsolve0 : ∃ anns, (normalizeModel m).solve = .satisfy anns := by
    have h1 := compileModel_solve_satisfy hcn
    rw [boundsModel_solve hbm] at h1
    rw [hsefields.2.2] at h1
    rw [hshfields.2.2] at h1
    simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
      foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
      substParamsModel] using h1
  have hwfn := wf_normalize hwf hgate hsolve0
  have hprednf : (normalizeFull m).predicates = [] := by
    have h1 := compileModel_predicates_nil hcn
    rw [boundsModel_predicates hbm] at h1
    rw [hsefields.2.1] at h1
    rw [hshfields.2.1] at h1
    exact h1
  have hpred : (normalizeModel m).predicates = [] := by
    simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
      foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
      substParamsModel] using hprednf
  have hpredf : (fragmentModel (normalizeModel m)).predicates = [] := by
    simpa [fragmentModel, expandInitModel, substParamsModel] using hpred
  have hpredsh : sh.model.predicates = [] := by
    rw [hshfields.2.1]
    exact hprednf
  have hwfF := wf_fragment hwfn hpred
  have hwff := wf_fold hwfF hpredf
  have hwfr := wf_restrict hwff hsolve0
  have hwfrFast : WellFormed fullSig
      (restrictSetInModelFast
        (foldLiteralsModel (fragmentModel (normalizeModel m)))) := by
    rw [restrictSetInModelFast_eq]
    exact hwfr
  have hwfsh := wf_shapeExpand hwfrFast hprednf (fun _ h => h) hsh
  have hinv := SetExpansion.Inv.of_wellFormed hwfsh (fun _ h => h) hse
  have hwse := wf_setExpand hwfsh hpredsh (fun _ h => h) hse
  have hwmb := wf_boundsModel hbm hwse
  obtain ⟨hex1_b, hex2_b⟩ := compile_exact (m := mb) hcn hwmb hmem hacc
  have hex2_b' : ∀ d ∈ mb.variables, match d with
      | .basic ty n _ _ => ∃ v, (p0.toStore a) n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, (p0.toStore a) n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v := by
    intro d hd
    obtain ⟨ty, n, anns, heq⟩ := compileModel_vars_basic hcn d hd
    subst heq
    simpa using hex2_b _ hd
  have hinit_b : ∀ d ∈ mb.variables, d.initializerHolds (p0.toStore a) := by
    intro d hd
    obtain ⟨ty, n, anns, heq⟩ := compileModel_vars_basic hcn d hd
    subst heq
    exact trivial
  have hsat_b : SatisfiesDyn fullInterp mb (p0.toStore a) :=
    ⟨hex1_b, hex2_b', hinit_b⟩
  have hsat_se : SatisfiesDyn fullInterp se.model (p0.toStore a) :=
    boundsModel_exact hbm hsat_b
  have hsat_sh : SatisfiesDyn fullInterp sh.model
      (setStore se (p0.toStore a)) :=
    setExpand_sound hwfsh (fun _ h => h) hse hsat_se
  have hsat_r : SatisfiesDyn fullInterp (normalizeFull m)
      (setStore se (p0.toStore a)) :=
    shapeExpand_sound hwfrFast (fun _ h => h) hsh hsat_sh
  have hnf : normalizeFull m = restrictSetInModel
      (foldLiteralsModel (fragmentModel (normalizeModel m))) := by
    simp [normalizeFull, restrictSetInModelFast_eq]
  rw [hnf] at hsat_r
  obtain ⟨hex1n, hex2n⟩ := restrictSetIn_exact hsat_r.1 hsat_r.2.1
  have hex1f : ∀ c ∈ (fragmentModel (normalizeModel m)).constraints,
      c.Holds fullInterp (setStore se (p0.toStore a)) :=
    foldLiterals_exact hex1n
  have hvars_basic := vars_basic_of_fragment hsh hbm hinv hcn
  have hinitf : ∀ d ∈ (fragmentModel (normalizeModel m)).variables,
      d.initializerHolds (setStore se (p0.toStore a)) := by
    intro d hd
    obtain ⟨ty, n, anns, rfl⟩ := hvars_basic d hd
    exact trivial
  have hsatf : SatisfiesDyn fullInterp (fragmentModel (normalizeModel m))
      (setStore se (p0.toStore a)) := by
    refine ⟨hex1f, ?_, hinitf⟩
    intro d hd
    cases d with
    | basic ty n anns v => exact hex2n (.basic ty n anns v) hd
    | array ty n anns es => exact hex2n (.array ty n anns es) hd
  have hstore_par : ∀ d ∈ (normalizeModel m).parameters, ∀ v,
      parDeclValue d = some v →
      setStore se (p0.toStore a) (ParDeclItem.name d) = some v := by
    intro d hd v hv
    have hdnf : d ∈ (normalizeFull m).parameters := by
      simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
        foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
        substParamsModel] using hd
    have hnot : d.name.name ∉ se.setNames :=
      hinv.parName_not_set hwfsh (hshfields.1.symm ▸ hdnf)
    have hdb : d ∈ mb.parameters := by
      rw [boundsModel_parameters hbm]
      rw [hinv.parameters]
      exact hshfields.1.symm ▸ hdnf
    rw [SetExpansion.setStore_of_not_mem (by simpa [ParDeclItem.name] using hnot)]
    exact toStore_scalar_param hcn hwmb (a := a) hdb hv
  have henv : ∀ x v, parEnv (normalizeModel m) x = some v →
      setStore se (p0.toStore a) x = some v := by
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
          have h1 := hstore_par d hd w hpd
          have hyx : y = x := ident_eq_of_name hyname
          rw [hdn, hyx, hw, hwlv] at h1
          exact h1
    · simp at hv
  have hsat_n := fragment_exact henv hsatf
  have hex1m : ∀ c ∈ (normalizeModel m).constraints,
      c.Holds fullInterp (setStore se (p0.toStore a)) := hsat_n.1
  have hex2m : ∀ d ∈ (normalizeModel m).variables, match d with
      | .basic ty n _ _ =>
          ∃ v, (setStore se (p0.toStore a)) n = some v ∧ ty.contains v
      | .array ty n _ _ =>
          ∃ vs, (setStore se (p0.toStore a)) n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v := by
    intro d hd
    cases d with
    | basic ty n anns v => exact hsat_n.2.1 (.basic ty n anns v) hd
    | array ty n anns es => exact hsat_n.2.1 (.array ty n anns es) hd
  have hex3m : ∀ d ∈ (normalizeModel m).variables,
      d.initializerHolds (setStore se (p0.toStore a)) := hsat_n.2.2
  have hs : BasicRead m (setStore se (p0.toStore a)) := by
    intro ty n anns hd
    have hdn : (VarDeclItem.basic ty n anns none) ∈ (normalizeModel m).variables :=
      List.mem_filter.mpr ⟨hd, rfl⟩
    simpa using hex2m _ hdn
  have hfull := faithful_full hgate hs
  show SatisfiesDyn fullInterp m
      (fullStore (arrayDefs m) (setStore se (p0.toStore a))) ∧
    LeanFzn.Semantics.ParamHonest m
      (fullStore (arrayDefs m) (setStore se (p0.toStore a)))
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- constraints
    intro c hcm
    have hc' : inlineConstraint (arrayDefs m) c ∈ (normalizeModel m).constraints :=
      List.mem_map.mpr ⟨c, hcm, rfl⟩
    have h1 := hex1m _ hc'
    have h2 := (holds_full_iff (defs := arrayDefs m)
      (inline_identFree hgate hcm)).mpr h1
    exact (holds_inline hfull _ c).mp h2
  · -- variable domains
    intro d hd
    cases d with
    | basic ty n anns v =>
        have hdn : (VarDeclItem.basic ty n anns v) ∈ (normalizeModel m).variables :=
          List.mem_filter.mpr ⟨hd, rfl⟩
        have hnone := lookup_arrayDefs_none hnu
          (x := n) (Or.inr ⟨_, hd, rfl, rfl⟩)
        have := hex2m _ hdn
        simp only at this ⊢
        rw [fullStore_of_none hnone]
        exact this
    | array ty n anns es =>
        obtain ⟨vs, hvs, hP⟩ := var_elems hgate hs hd
        refine ⟨vs, ?_, ?_, fun v hv => hP v hv⟩
        · simp [fullStore, arrayValue, lookup_var_array hnu hd, hvs]
        · rw [mapM_length hvs]
          exact hwf.variableArrayLengths _ hd
  · -- initializers
    intro d hd
    cases d with
    | basic ty n anns v =>
        have hdn : (VarDeclItem.basic ty n anns v) ∈ (normalizeModel m).variables :=
          List.mem_filter.mpr ⟨hd, rfl⟩
        have hinit := hex3m _ hdn
        cases v with
        | none => exact trivial
        | some e =>
            exact basic_initializerHolds_fullStore hnu
              (hwf.variableInitializers _ hd) hinit
              (lookup_arrayDefs_none hnu (x := n) (Or.inr ⟨_, hd, rfl, rfl⟩))
    | array ty n anns es =>
        obtain ⟨vs, hvs, hP⟩ := var_elems hgate hs hd
        have hl := lookup_var_array hnu hd
        refine ⟨vs, vs, ?_, ?_, forall2_semEq_refl_of_forall vs
          (fun v hv => semEq_refl_of_contains (ty := ty.elem) (hP v hv))⟩
        · rw [mapM_congr (g := BasicExpr.eval (setStore se (p0.toStore a))) ?_]
          · exact hvs
          · intro b hb
            cases b with
            | lit l => rfl
            | ident z =>
                show fullStore (arrayDefs m) (setStore se (p0.toStore a)) z = _
                exact fullStore_of_none (defs_elems_free hgate hl _ hb z rfl)
        · simp [fullStore, arrayValue, hl, hvs]
  · -- parameter honesty
    intro d hd
    cases d with
    | basic t n l =>
        have hdn : (ParDeclItem.basic t n l) ∈ (normalizeModel m).parameters :=
          List.mem_filter.mpr ⟨hd, rfl⟩
        have hdnf : (ParDeclItem.basic t n l) ∈ (normalizeFull m).parameters := by
          simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
            foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
            substParamsModel] using hdn
        have hscal : (normalizeModel m).parameters.filter
            (fun d => parDeclValue d = none) = [] := by
          have h1 := compileModel_params_scalar hcn
          rw [boundsModel_parameters hbm] at h1
          rw [hinv.parameters] at h1
          rw [hshfields.1] at h1
          simpa [normalizeFull, restrictSetInModelFast_eq, restrictSetInModel, foldLiteralsModel, foldSetCardModel,
            foldGroundModel, foldReifModel, fragmentModel, expandInitModel,
            substParamsModel] using h1
        obtain ⟨v, hv⟩ : ∃ v, parDeclValue (ParDeclItem.basic t n l) = some v := by
          cases hpv : parDeclValue (ParDeclItem.basic t n l) with
          | some v => exact ⟨v, rfl⟩
          | none =>
              exfalso
              have : (ParDeclItem.basic t n l) ∈
                  (normalizeModel m).parameters.filter (fun d => parDeclValue d = none) :=
                List.mem_filter.mpr ⟨hdn, by simpa using hpv⟩
              rw [hscal] at this
              cases this
        have hnone := lookup_arrayDefs_none hnu
          (x := n) (Or.inl ⟨_, hd, rfl, rfl⟩)
        have hdnb : (ParDeclItem.basic t n l) ∈ mb.parameters := by
          rw [boundsModel_parameters hbm]
          rw [hinv.parameters]
          exact hshfields.1.symm ▸ hdnf
        have hnot : n.name ∉ se.setNames := by
          have h' := hinv.parName_not_set hwfsh (hshfields.1.symm ▸ hdnf)
          simpa [ParDeclItem.name] using h'
        have h1 := toStore_scalar_param hcn hwmb (a := a) hdnb hv
        simp only [ParDeclItem.name] at h1
        show fullStore (arrayDefs m) (setStore se (p0.toStore a)) n =
          some (ParDeclItem.value _)
        rw [fullStore_of_none hnone,
          SetExpansion.setStore_of_not_mem hnot, h1, parDeclValue_value hv]
    | array idx t n lits =>
        show fullStore (arrayDefs m) (setStore se (p0.toStore a)) n = _
        have hm := mapM_lit_eval (setStore se (p0.toStore a)) lits
        simp only [fullStore, arrayValue, lookup_par_array hnu hd,
          Option.bind_some, hm, Option.map_some, ParDeclItem.value]

end LeanFzn.Compiler
