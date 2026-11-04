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
  - LeanFzn.Compiler.Normalize, LeanFzn.Compiler.Proofs.Exact.
-/

import LeanFzn.Compiler.Normalize
import LeanFzn.Compiler.Proofs.Exact
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

theorem varArrayOk_inv {m : Model} {defs : List (Ident × List BasicExpr)}
    {ty : ArrayVarType} {n : Ident} {anns : List Annotation}
    {es : List BasicExpr}
    (h : varArrayOkB m defs (.array ty n anns es) = true) :
    (ty.elem = .par .int ∧ ∀ e ∈ es, elemOkB m defs .int e = true) ∨
    (ty.elem = .par .bool ∧ ∀ e ∈ es, elemOkB m defs .bool e = true) := by
  simp only [varArrayOkB] at h
  revert h
  cases hel : ty.elem with
  | par t =>
      cases t <;> simp [List.all_eq_true]
  | intRange lo hi => simp
  | intSet xs => simp
  | setOfIntRange lo hi => simp
  | setOfIntSet xs => simp

theorem gate_vars {m : Model} (h : arraysOkB m = true) :
    ∀ d ∈ m.variables, varArrayOkB m (arrayDefs m) d = true := by
  unfold arraysOkB at h
  have := (Bool.and_eq_true _ _).mp h
  exact fun d hd => List.all_eq_true.mp this.1 d hd

theorem gate_cons {m : Model} (h : arraysOkB m = true) :
    ∀ c ∈ m.constraints, ∀ e ∈ c.args, explicitOkB (arrayDefs m) e = true := by
  unfold arraysOkB at h
  have := (Bool.and_eq_true _ _).mp h
  exact fun c hc e he => List.all_eq_true.mp (List.all_eq_true.mp this.2 c hc) e he

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
    rcases varArrayOk_inv hok with ⟨_, h2⟩ | ⟨_, h2⟩
    · exact (elemOk_ident (h2 _ hb)).1
    · exact (elemOk_ident (h2 _ hb)).1

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

/-- A gated variable array's initializer evaluates, to scalars inside
    the declared element type. -/
theorem var_elems {m : Model} (h : arraysOkB m = true) {s : Store}
    (hs : BasicRead m s) {ty : ArrayVarType} {n : Ident}
    {anns : List Annotation} {es : List BasicExpr}
    (hd : (VarDeclItem.array ty n anns es) ∈ m.variables) :
    ∃ vs, es.mapM (BasicExpr.eval s) = some vs ∧
      ∀ v ∈ vs, ty.elem.contains v ∧ IsScalar v := by
  have hok := gate_vars h _ hd
  rcases varArrayOk_inv hok with ⟨hel, h2⟩ | ⟨hel, h2⟩
  · obtain ⟨vs, hvs, hP⟩ := mapM_some_exists (f := BasicExpr.eval s)
      (P := fun v => ValOf .int v) (l := es)
      (fun e he => elem_eval (Or.inl rfl) hs (h2 e he))
    refine ⟨vs, hvs, fun v hv => ⟨?_, isScalar_of_valOf (hP v hv)⟩⟩
    rw [hel]
    exact (contains_par_of_valOf (hP v hv)).1 rfl
  · obtain ⟨vs, hvs, hP⟩ := mapM_some_exists (f := BasicExpr.eval s)
      (P := fun v => ValOf .bool v) (l := es)
      (fun e he => elem_eval (Or.inr rfl) hs (h2 e he))
    refine ⟨vs, hvs, fun v hv => ⟨?_, isScalar_of_valOf (hP v hv)⟩⟩
    rw [hel]
    exact (contains_par_of_valOf (hP v hv)).2 rfl

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

theorem accepts_mono {bt : BasicPredParamType} {t : BaseType}
    (h : bt.accepts t true) : bt.accepts t false := by
  unfold BasicPredParamType.accepts at *
  exact ⟨h.1, fun _ => rfl⟩


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
                          obtain ⟨b0, hbase, h2⟩ :
                              ∃ b0 : BaseType, ty.elem.base = b0 ∧
                                ∀ e ∈ es, elemOkB m (arrayDefs m) b0 e = true := by
                            rcases varArrayOk_inv hok with ⟨hel, h2⟩ | ⟨hel, h2⟩
                            · exact ⟨.int, by rw [hel]; rfl, h2⟩
                            · exact ⟨.bool, by rw [hel]; rfl, h2⟩
                          rw [ht1, hbase, hv1] at hacc
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
                              obtain ⟨hzn, ty', n', anns', hd', hnn, hty'⟩ :=
                                elemOk_ident (h2 _ hb)
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

theorem wf_normalize {m : Model} (hwf : WellFormed fullSig m)
    (hgate : arraysOkB m = true)
    (hvars : ∀ d ∈ (normalizeModel m).variables,
      ∃ ty n anns, d = VarDeclItem.basic ty n anns none)
    (hsolve : ∃ anns, m.solve = .satisfy anns) :
    WellFormed fullSig (normalizeModel m) := by
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
    obtain ⟨ty, n, a, rfl⟩ := hvars d hd
    exact trivial
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

theorem parDeclValue_value {d : ParDeclItem} {v : Value}
    (h : parDeclValue d = some v) : d.value = v := by
  cases d with
  | basic t n l =>
      cases t <;> cases l <;> simp_all [parDeclValue, ParDeclItem.value,
        BasicLiteral.denote]
  | array idx t n lits => simp [parDeclValue] at h


/-! ## The array front end is exact -/

theorem vars_basic_of_normalizeFull {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel (normalizeFull m) = .ok problem) :
    ∀ d ∈ (normalizeModel m).variables,
      ∃ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
        d = .basic ty n anns none := by
  have hvars := compileModel_vars_basic hc
  intro d hd
  have hd' : restrictVarDecl (normalizeModel m) d ∈
      (normalizeFull m).variables := by
    simp only [normalizeFull, restrictSetInModel]
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  obtain ⟨ty, n, anns, hrest⟩ := hvars _ hd'
  cases d with
  | array ty0 n0 anns0 es =>
      have hb : isBasicVar (.array ty0 n0 anns0 es) = true :=
        (List.mem_filter.mp hd).2
      simp [isBasicVar] at hb
  | basic ty0 n0 anns0 init =>
      cases init with
      | none => exact ⟨ty0, n0, anns0, rfl⟩
      | some e =>
          simp only [restrictVarDecl] at hrest
          simp at hrest

theorem compileFull_inv {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok problem) :
    arraysOkB m = true ∧ ∃ p0, compileModel (normalizeFull m) = .ok p0 ∧
      problem = relabel m p0 := by
  unfold compileModelFull at hc
  split at hc
  · rename_i h
    cases hcm : compileModel (normalizeFull m) with
    | error e => rw [hcm] at hc; cases hc
    | ok p =>
        rw [hcm] at hc
        exact ⟨h, p, rfl, (Except.ok.inj hc).symm⟩
  · cases hc

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

/-- **COVERAGE for the array front end**: a store that satisfies the
    dynamic conditions of the original model (with its parameter and
    array declarations honoured) is covered by an accepted assignment
    of the compiled problem. -/
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
        problem.toStore a n = store n := by
  obtain ⟨hgate, p0, hcn, rfl⟩ := compileFull_inv hc
  have hnu : NamesNodup m := hwf.valueNamesUnique
  have hvars0 := vars_basic_of_normalizeFull hcn
  have hsolve0 : ∃ anns, (normalizeModel m).solve = .satisfy anns := by
    simpa [normalizeFull, restrictSetInModel] using
      compileModel_solve_satisfy hcn
  have hwfn := wf_normalize hwf hgate hvars0 hsolve0
  have hwfr := wf_restrict hwfn hsolve0
  obtain ⟨hcons0, hvar0, hinit0⟩ := hsat
  have hs : BasicRead m store := fun ty n anns hd => by
    simpa using hvar0 _ hd
  have hfaith : Faithful (arrayDefs m) store := by
    intro x es hl
    obtain ⟨y, hy, hyn⟩ := lookupIdent_inv_mem x (arrayDefs m) es hl
    have hxy : x = y := (ident_eq_of_name hyn).symm
    subst hxy
    rcases mem_arrayDefs hy with ⟨d, hd, idx, t, lits, rfl, rfl⟩ | ⟨d, hd, ty, anns, rfl⟩
    · refine ⟨_, ?_, mapM_lit_eval store lits⟩
      have := hparam _ hd
      simpa [ParDeclItem.name, ParDeclItem.value] using this
    · obtain ⟨vs, hvs, hP⟩ := var_elems hgate hs hd
      obtain ⟨vs', ws, hvs', hws, hF⟩ := hinit0 _ hd
      have hvv : vs' = vs := by
        have := hvs'.symm.trans hvs
        exact Option.some.inj this
      subst hvv
      have hwv := forall2_semEq_scalar hF (fun v hv => (hP v hv).2)
      subst hwv
      exact ⟨_, hws, hvs⟩
  have hcons_n : ∀ c ∈ (normalizeModel m).constraints,
      c.Holds fullInterp store := by
    intro c' hc'
    obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hc'
    exact (holds_inline hfaith _ c).mpr (hcons0 c hcm)
  have hvars_n : ∀ d ∈ (normalizeModel m).variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v := by
    intro d hd
    obtain ⟨ty, n, anns, rfl⟩ := hvars0 d hd
    have hdm : (VarDeclItem.basic ty n anns none) ∈ m.variables :=
      (List.mem_filter.mp hd).1
    simpa using hvar0 _ hdm
  obtain ⟨hcons_r, hvars_r⟩ := restrictSetIn_covers hcons_n hvars_n
  have hvars_r' : ∀ d ∈ (normalizeFull m).variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array _ _ _ _ => False := by
    intro d hd
    obtain ⟨ty, n, anns, heq⟩ := compileModel_vars_basic hcn d hd
    subst heq
    simpa using hvars_r _ hd
  have hcov := compile_covers_agree (m := normalizeFull m) hcn hwfr
      (store := store) hcons_r hvars_r'
    (by
      intro d hd v hv
      have hd' : d ∈ (normalizeModel m).parameters := by
        simpa [normalizeFull, restrictSetInModel] using hd
      have hdm : d ∈ m.parameters := (List.mem_filter.mp hd').1
      have := hparam d hdm
      rw [parDeclValue_value hv] at this
      exact this)
  obtain ⟨a, h1, h2, h3⟩ := hcov
  refine ⟨a, h1, h2, ?_⟩
  intro ty n anns hd
  have hnone := lookup_arrayDefs_none hnu (x := n) (Or.inr ⟨_, hd, rfl, rfl⟩)
  have hdn : (VarDeclItem.basic
      (restrictVarType (normalizeModel m) n.name ty) n anns none) ∈
      (normalizeFull m).variables := by
    simp only [normalizeFull, restrictSetInModel]
    exact List.mem_map.mpr ⟨.basic ty n anns none,
      List.mem_filter.mpr ⟨hd, rfl⟩, by simp [restrictVarDecl]⟩
  show fullStore (arrayDefs m) (p0.toStore a) n = store n
  rw [fullStore_of_none hnone]
  exact h3 (restrictVarType (normalizeModel m) n.name ty) n anns hdn

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
  obtain ⟨hgate, p0, hcn, rfl⟩ := compileFull_inv hc
  have hnu : NamesNodup m := hwf.valueNamesUnique
  have hvars0 := vars_basic_of_normalizeFull hcn
  have hsolve0 : ∃ anns, (normalizeModel m).solve = .satisfy anns := by
    simpa [normalizeFull, restrictSetInModel] using
      compileModel_solve_satisfy hcn
  have hwfn := wf_normalize hwf hgate hvars0 hsolve0
  have hwfr := wf_restrict hwfn hsolve0
  obtain ⟨hex1, hex2⟩ := compile_exact (m := normalizeFull m) hcn hwfr hmem hacc
  have hex2v : ∀ d ∈ (normalizeFull m).variables, match d with
      | .basic ty n _ _ => ∃ v, (p0.toStore a) n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, (p0.toStore a) n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v := by
    intro d hd
    obtain ⟨ty, n, anns, heq⟩ := compileModel_vars_basic hcn d hd
    subst heq
    simpa using hex2 _ hd
  obtain ⟨hex1n, hex2n⟩ := restrictSetIn_exact hex1 hex2v
  have hs : BasicRead m (p0.toStore a) := by
    intro ty n anns hd
    have hdn : (VarDeclItem.basic ty n anns none) ∈ (normalizeModel m).variables :=
      List.mem_filter.mpr ⟨hd, rfl⟩
    simpa using hex2n _ hdn
  have hfull := faithful_full hgate hs
  show SatisfiesDyn fullInterp m (fullStore (arrayDefs m) (p0.toStore a)) ∧
    LeanFzn.Semantics.ParamHonest m (fullStore (arrayDefs m) (p0.toStore a))
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · -- constraints
    intro c hcm
    have hc' : inlineConstraint (arrayDefs m) c ∈ (normalizeModel m).constraints :=
      List.mem_map.mpr ⟨c, hcm, rfl⟩
    have h1 := hex1n _ hc'
    have h2 := (holds_full_iff (defs := arrayDefs m)
      (inline_identFree hgate hcm)).mpr h1
    exact (holds_inline hfull _ c).mp h2
  · -- variable domains
    intro d hd
    cases d with
    | basic ty n anns v =>
        have hdn : (VarDeclItem.basic ty n anns v) ∈ (normalizeModel m).variables :=
          List.mem_filter.mpr ⟨hd, rfl⟩
        obtain ⟨ty', n', anns', heq⟩ := hvars0 _ hdn
        cases heq
        have hnone := lookup_arrayDefs_none hnu
          (x := n) (Or.inr ⟨_, hd, rfl, rfl⟩)
        have := hex2n _ hdn
        simp only at this ⊢
        rw [fullStore_of_none hnone]
        exact this
    | array ty n anns es =>
        obtain ⟨vs, hvs, hP⟩ := var_elems hgate hs hd
        refine ⟨vs, ?_, ?_, fun v hv => (hP v hv).1⟩
        · simp [fullStore, arrayValue, lookup_var_array hnu hd, hvs]
        · rw [mapM_length hvs]
          exact hwf.variableArrayLengths _ hd
  · -- initializers
    intro d hd
    cases d with
    | basic ty n anns v =>
        have hdn : (VarDeclItem.basic ty n anns v) ∈ (normalizeModel m).variables :=
          List.mem_filter.mpr ⟨hd, rfl⟩
        obtain ⟨ty', n', anns', heq⟩ := hvars0 _ hdn
        cases heq
        exact trivial
    | array ty n anns es =>
        obtain ⟨vs, hvs, hP⟩ := var_elems hgate hs hd
        have hl := lookup_var_array hnu hd
        refine ⟨vs, vs, ?_, ?_, forall2_semEq_refl vs (fun v hv => (hP v hv).2)⟩
        · rw [mapM_congr (g := BasicExpr.eval (p0.toStore a)) ?_]
          · exact hvs
          · intro b hb
            cases b with
            | lit l => rfl
            | ident z =>
                show fullStore (arrayDefs m) (p0.toStore a) z = _
                exact fullStore_of_none (defs_elems_free hgate hl _ hb z rfl)
        · simp [fullStore, arrayValue, hl, hvs]
  · -- parameter honesty
    intro d hd
    cases d with
    | basic t n l =>
        have hdn : (ParDeclItem.basic t n l) ∈ (normalizeModel m).parameters :=
          List.mem_filter.mpr ⟨hd, rfl⟩
        have hscal : (normalizeModel m).parameters.filter
            (fun d => parDeclValue d = none) = [] := by
          simpa [normalizeFull, restrictSetInModel] using
            compileModel_params_scalar hcn
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
        have h1 := toStore_scalar_param hcn hwfr (a := a) hdn hv
        simp only [ParDeclItem.name] at h1
        show fullStore (arrayDefs m) (p0.toStore a) n = some (ParDeclItem.value _)
        rw [fullStore_of_none hnone, h1, parDeclValue_value hv]
    | array idx t n lits =>
        show fullStore (arrayDefs m) (p0.toStore a) n = _
        have hm := mapM_lit_eval (p0.toStore a) lits
        simp only [fullStore, arrayValue, lookup_par_array hnu hd,
          Option.bind_some, hm, Option.map_some, ParDeclItem.value]

end LeanFzn.Compiler
