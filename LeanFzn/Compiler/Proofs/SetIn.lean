/-
File: LeanFzn/Compiler/Proofs/SetIn.lean

Purpose:
  Correctness of the constant-set membership domain restriction
  (`Compiler/SetIn.lean`): restricting a plain finite scalar variable's
  declared domain by its `set_in` / literal-reified `set_in_reif`
  constraints and dropping those constraints preserves both directions
  of the source semantics.  `restrictSetIn_covers` turns a store
  satisfying the original constraints and variable domains into one
  satisfying the restricted model; `restrictSetIn_exact` turns a store
  satisfying the restricted model back into one satisfying the original
  model (the dropped membership constraints follow from the restricted
  domain).  `wf_restrict` carries static well-formedness across the
  rewrite, so `Proofs/Normalize` composes this pass with the unchanged
  `compile_exact` / `compile_covers_agree` on the rewritten model.

Dependencies:
  - LeanFzn.Compiler.SetIn, LeanFzn.Compiler.Compile.
-/

import LeanFzn.Compiler.SetIn

namespace LeanFzn.Compiler
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Semantics.Globals

/-! ## The restriction predicate -/

/-- The proposition one constant-set restriction demands of an integer
    value. -/
def CondHolds (sv : IntSetValue) (pos : Bool) (v : Int) : Prop :=
  if pos then sv.Contains v else ¬ sv.Contains v

theorem setInCondAccepts_eq {sv : IntSetValue} {pos : Bool} {v : Int} :
    setInCondAccepts sv pos v = true ↔ CondHolds sv pos v := by
  unfold setInCondAccepts CondHolds
  by_cases h : pos <;> simp [h]

theorem setInAccepts_eq {conds : List SetInRestriction} {v : Int} :
    setInAccepts conds v = true ↔ ∀ q ∈ conds, CondHolds q.1 q.2 v := by
  induction conds with
  | nil => simp [setInAccepts, CondHolds]
  | cons q rest ih =>
      have ih' : (rest.all (fun q => setInCondAccepts q.1 q.2 v) = true) ↔
          ∀ r ∈ rest, CondHolds r.1 r.2 v := by
        simpa [setInAccepts] using ih
      rw [setInAccepts, List.all_cons, Bool.and_eq_true, ih',
        setInCondAccepts_eq]
      simp only [List.mem_cons]
      constructor
      · rintro ⟨hq, hrest⟩ r (rfl | hr)
        · exact hq
        · exact hrest r hr
      · intro h
        exact ⟨h q (Or.inl rfl), fun r hr => h r (Or.inr hr)⟩

/-! ## Shape inversion -/

/-- Inversion of the droppable shape. -/
theorem setInShape_inv {c : ConstraintItem} {y : Ident} {s : BasicExpr}
    {b : Bool} (h : setInShape c = some (y, s, b)) :
    (c.name.name = "set_in" ∧
      c.args = [.basic (.ident y), .basic s] ∧ b = true) ∨
    (c.name.name = "set_in_reif" ∧
      c.args = [.basic (.ident y), .basic s, .basic (.lit (.bool b))]) := by
  obtain ⟨nm, args, anns⟩ := c
  unfold setInShape at h
  split at h
  · rename_i hn hs
    injection h with h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact Or.inl ⟨hn, hs, rfl⟩
  · rename_i hn hs
    injection h with h1
    obtain ⟨rfl, rfl, rfl⟩ := h1
    exact Or.inr ⟨hn, hs⟩
  · cases h


/-! ## Inversion of one condition -/

/-- The shape, subject and set behind a constant-set restriction. -/
theorem setInCondOf_some_inv {x : String} {c : ConstraintItem}
    {sv : IntSetValue} {b : Bool}
    (h : setInCondOf x c = some (sv, b)) :
    ∃ y s, setInShape c = some (y, s, b) ∧ y.name = x ∧
      setArgDenote s = some sv := by
  unfold setInCondOf at h
  cases hsh : setInShape c with
  | none => rw [hsh] at h; cases h
  | some q =>
      obtain ⟨y, s, b0⟩ := q
      rw [hsh] at h
      dsimp only at h
      by_cases hyn : y.name = x
      · rw [if_pos hyn] at h
        cases hs : setArgDenote s with
        | none => rw [hs] at h; cases h
        | some sv0 =>
            rw [hs] at h
            have hq : (sv0, b0) = (sv, b) := Option.some.inj h
            simp only [Prod.mk.injEq] at hq
            obtain ⟨rfl, rfl⟩ := hq
            exact ⟨y, s, rfl, hyn, hs⟩
      · rw [if_neg hyn] at h; cases h

/-- A constant set argument evaluates to its denoted set. -/
theorem eval_of_setArgDenote {s : BasicExpr} {sv : IntSetValue}
    (h : setArgDenote s = some sv) (store : Store) :
    BasicExpr.eval store s = some (.setOfInt sv) := by
  cases s with
  | lit l =>
      cases l with
      | bool b => simp [setArgDenote] at h
      | int i => simp [setArgDenote] at h
      | set sl =>
          simp only [setArgDenote, Option.some.injEq] at h
          subst h
          rfl
  | ident x => simp [setArgDenote] at h

/-- Evaluation of the two-argument `set_in` shape. -/
theorem mapM_cond_args_two {store : Store} {y : Ident} {s : BasicExpr}
    {sv : IntSetValue} {p : Int}
    (hy : store y = some (.int p))
    (hs : BasicExpr.eval store s = some (.setOfInt sv)) :
    ([Expr.basic (.ident y), Expr.basic s] : List Expr).mapM
        (Expr.eval store) = some [.int p, .setOfInt sv] := by
  have hx : Expr.eval store (.basic (.ident y)) = some (.int p) := hy
  have hS : Expr.eval store (.basic s) = some (.setOfInt sv) := hs
  rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, hx, hS]
  rfl

/-- Evaluation of the three-argument `set_in_reif` shape. -/
theorem mapM_cond_args_three {store : Store} {y : Ident} {s : BasicExpr}
    {sv : IntSetValue} {p : Int} {b : Bool}
    (hy : store y = some (.int p))
    (hs : BasicExpr.eval store s = some (.setOfInt sv)) :
    ([Expr.basic (.ident y), Expr.basic s,
        Expr.basic (.lit (.bool b))] : List Expr).mapM (Expr.eval store) =
      some [.int p, .setOfInt sv, .bool b] := by
  have hx : Expr.eval store (.basic (.ident y)) = some (.int p) := hy
  have hS : Expr.eval store (.basic s) = some (.setOfInt sv) := hs
  have hb : Expr.eval store (.basic (.lit (.bool b))) = some (.bool b) := rfl
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_nil,
    hx, hS, hb]
  rfl

/-- A restriction condition reconstructs the source constraint. -/
theorem holds_of_cond {c : ConstraintItem} {x : String} {store : Store}
    {sv : IntSetValue} {b : Bool} {p : Int}
    (hcond : setInCondOf x c = some (sv, b))
    (hread : store (Ident.mk x) = some (.int p))
    (h : CondHolds sv b p) :
    c.Holds fullInterp store := by
  obtain ⟨y, s, hshape, hyn, hs⟩ := setInCondOf_some_inv hcond
  have hy : y = Ident.mk x := Ident.eq_of_name_eq hyn
  rcases setInShape_inv hshape with ⟨hn, hargs, hb⟩ | ⟨hn, hargs⟩
  · subst hb
    subst hy
    refine ⟨[.int p, .setOfInt sv], ?_, ?_⟩
    · rw [hargs, mapM_cond_args_two hread (eval_of_setArgDenote hs store)]
    · have hname : c.name = Ident.mk "set_in" := Ident.eq_of_name_eq hn
      rw [hname, fullInterp_of_extracted_setIn "set_in" (Or.inl rfl)]
      simp only [stdInterp]
      simpa [CondHolds] using h
  · subst hy
    refine ⟨[.int p, .setOfInt sv, .bool b], ?_, ?_⟩
    · rw [hargs, mapM_cond_args_three hread (eval_of_setArgDenote hs store)]
    · have hname : c.name = Ident.mk "set_in_reif" :=
        Ident.eq_of_name_eq hn
      rw [hname, fullInterp_of_extracted_setIn "set_in_reif" (Or.inr rfl)]
      simp only [stdInterp]
      unfold CondHolds at h
      cases b <;> simp_all

/-- The source constraint determines the restriction condition. -/
theorem cond_of_holds {c : ConstraintItem} {x : String} {store : Store}
    {sv : IntSetValue} {b : Bool} {p : Int}
    (hcond : setInCondOf x c = some (sv, b))
    (hread : store (Ident.mk x) = some (.int p))
    (hh : c.Holds fullInterp store) :
    CondHolds sv b p := by
  obtain ⟨y, s, hshape, hyn, hs⟩ := setInCondOf_some_inv hcond
  have hy : y = Ident.mk x := Ident.eq_of_name_eq hyn
  obtain ⟨args, hmap, hinterp⟩ := hh
  rcases setInShape_inv hshape with ⟨hn, hargs, hb⟩ | ⟨hn, hargs⟩
  · subst hb
    subst hy
    rw [hargs, mapM_cond_args_two hread (eval_of_setArgDenote hs store)] at hmap
    have hargs' : args = [.int p, .setOfInt sv] := by
      simpa using hmap.symm
    have hname : c.name = Ident.mk "set_in" := Ident.eq_of_name_eq hn
    rw [hname, fullInterp_of_extracted_setIn "set_in" (Or.inl rfl)] at hinterp
    rw [hargs'] at hinterp
    simp only [stdInterp] at hinterp
    simpa [CondHolds] using hinterp
  · subst hy
    rw [hargs, mapM_cond_args_three hread (eval_of_setArgDenote hs store)] at hmap
    have hargs' : args = [.int p, .setOfInt sv, .bool b] := by
      simpa using hmap.symm
    have hname : c.name = Ident.mk "set_in_reif" := Ident.eq_of_name_eq hn
    rw [hname, fullInterp_of_extracted_setIn "set_in_reif" (Or.inr rfl)] at hinterp
    rw [hargs'] at hinterp
    simp only [stdInterp] at hinterp
    unfold CondHolds
    cases b <;> simp_all


/-! ## Domain restriction -/

theorem intRange_contains_int {lo hi x : Int} :
    (BasicVarType.intRange lo hi).contains (.int x) ↔ lo ≤ x ∧ x ≤ hi := by
  simp [BasicVarType.contains]

theorem intSet_contains_int {xs : List Int} {x : Int} :
    (BasicVarType.intSet xs).contains (.int x) ↔ x ∈ xs := by
  simp [BasicVarType.contains]

theorem mem_setElems_interval {lo hi x : Int} :
    x ∈ setElems (.interval lo hi) ↔ lo ≤ x ∧ x ≤ hi := by
  rw [← setElems_mem_iff]
  rfl

/-- A nonempty condition list has a head and a tail. -/
theorem exists_setInConds_cons {m : Model} {name : String}
    (h : setInConds m name ≠ []) :
    ∃ q conds, setInConds m name = q :: conds := by
  cases hc : setInConds m name with
  | nil => exact absurd hc h
  | cons q conds => exact ⟨q, conds, rfl⟩

/-- With no constant-set conditions the declared range is preserved. -/
theorem restrictVarType_range_nil {m : Model} {name : String} {lo hi : Int}
    (h : setInConds m name = []) :
    restrictVarType m name (.intRange lo hi) = .intRange lo hi := by
  simp [restrictVarType, h]

/-- With constant-set conditions the declared range becomes the filtered
    explicit set. -/
theorem restrictVarType_range_cons {m : Model} {name : String} {lo hi : Int}
    {q : SetInRestriction} {conds : List SetInRestriction}
    (h : setInConds m name = q :: conds) :
    restrictVarType m name (.intRange lo hi) =
      .intSet ((setElems (.interval lo hi)).filter (setInAccepts (q :: conds))) := by
  simp [restrictVarType, h]

/-- With no constant-set conditions the declared enumeration is preserved. -/
theorem restrictVarType_set_nil {m : Model} {name : String} {xs : List Int}
    (h : setInConds m name = []) :
    restrictVarType m name (.intSet xs) = .intSet xs := by
  simp [restrictVarType, h]

/-- With constant-set conditions the declared enumeration becomes the
    filtered explicit set. -/
theorem restrictVarType_set_cons {m : Model} {name : String} {xs : List Int}
    {q : SetInRestriction} {conds : List SetInRestriction}
    (h : setInConds m name = q :: conds) :
    restrictVarType m name (.intSet xs) =
      .intSet (xs.filter (setInAccepts (q :: conds))) := by
  simp [restrictVarType, h]

/-- The restricted range domain contains exactly the range values that
    satisfy every constant-set condition. -/
theorem restrictVarType_range_int {m : Model} {name : String}
    {lo hi x : Int} :
    (restrictVarType m name (.intRange lo hi)).contains (.int x) ↔
      (BasicVarType.intRange lo hi).contains (.int x) ∧
        ∀ q ∈ setInConds m name, CondHolds q.1 q.2 x := by
  cases hc : setInConds m name with
  | nil =>
      rw [restrictVarType_range_nil hc]
      simp [intRange_contains_int]
  | cons q conds =>
      rw [restrictVarType_range_cons hc]
      simp only [intSet_contains_int, List.mem_filter, mem_setElems_interval,
        setInAccepts_eq, intRange_contains_int]

/-- The restricted enumerated domain contains exactly the enumeration
    values that satisfy every constant-set condition. -/
theorem restrictVarType_set_int {m : Model} {name : String}
    {xs : List Int} {x : Int} :
    (restrictVarType m name (.intSet xs)).contains (.int x) ↔
      (BasicVarType.intSet xs).contains (.int x) ∧
        ∀ q ∈ setInConds m name, CondHolds q.1 q.2 x := by
  cases hc : setInConds m name with
  | nil =>
      rw [restrictVarType_set_nil hc]
      simp [intSet_contains_int]
  | cons q conds =>
      rw [restrictVarType_set_cons hc]
      simp only [intSet_contains_int, List.mem_filter, setInAccepts_eq]

/-- Restriction only removes values. -/
theorem restrictVarType_contains_imp {m : Model} {name : String}
    {ty : BasicVarType} {v : Value}
    (h : (restrictVarType m name ty).contains v) : ty.contains v := by
  cases ty with
  | intRange lo hi =>
      by_cases hc : setInConds m name = []
      · rw [restrictVarType_range_nil hc] at h
        exact h
      · obtain ⟨q, conds, hq⟩ := exists_setInConds_cons hc
        rw [restrictVarType_range_cons hq] at h
        cases v with
        | int x =>
            simp only [intSet_contains_int, List.mem_filter] at h
            exact intRange_contains_int.mpr (mem_setElems_interval.mp h.1)
        | bool b => simp [BasicVarType.contains] at h
        | setOfInt s => simp [BasicVarType.contains] at h
        | array vs => simp [BasicVarType.contains] at h
  | intSet xs =>
      by_cases hc : setInConds m name = []
      · rw [restrictVarType_set_nil hc] at h
        exact h
      · obtain ⟨q, conds, hq⟩ := exists_setInConds_cons hc
        rw [restrictVarType_set_cons hq] at h
        cases v with
        | int x =>
            simp only [intSet_contains_int, List.mem_filter] at h
            exact h.1
        | bool b => simp [BasicVarType.contains] at h
        | setOfInt s => simp [BasicVarType.contains] at h
        | array vs => simp [BasicVarType.contains] at h
  | par t => simpa [restrictVarType] using h
  | setOfIntRange lo hi => simpa [restrictVarType] using h
  | setOfIntSet xs => simpa [restrictVarType] using h

/-- A finite integer domain's values are integers. -/
theorem exists_int_of_finite_contains {ty : BasicVarType} {v : Value}
    (hfin : isFiniteIntType ty = true) (h : ty.contains v) :
    ∃ x, v = .int x := by
  rcases isFiniteIntType_iff.mp hfin with ⟨lo, hi, rfl⟩ | ⟨xs, rfl⟩
  · cases v with
    | int x => exact ⟨x, rfl⟩
    | bool b => simp [BasicVarType.contains] at h
    | setOfInt s => simp [BasicVarType.contains] at h
    | array vs => simp [BasicVarType.contains] at h
  · cases v with
    | int x => exact ⟨x, rfl⟩
    | bool b => simp [BasicVarType.contains] at h
    | setOfInt s => simp [BasicVarType.contains] at h
    | array vs => simp [BasicVarType.contains] at h

/-- A restricted finite integer domain's values are integers. -/
theorem exists_int_of_restrictVarType_contains {m : Model} {name : String}
    {ty : BasicVarType} {v : Value}
    (hfin : isFiniteIntType ty = true)
    (h : (restrictVarType m name ty).contains v) :
    ∃ x, v = .int x := by
  rcases isFiniteIntType_iff.mp hfin with ⟨lo, hi, rfl⟩ | ⟨xs, rfl⟩
  · by_cases hc : setInConds m name = []
    · rw [restrictVarType_range_nil hc] at h
      cases v with
      | int x => exact ⟨x, rfl⟩
      | bool b => simp [BasicVarType.contains] at h
      | setOfInt s => simp [BasicVarType.contains] at h
      | array vs => simp [BasicVarType.contains] at h
    · obtain ⟨q, conds, hq⟩ := exists_setInConds_cons hc
      rw [restrictVarType_range_cons hq] at h
      cases v with
      | int x => exact ⟨x, rfl⟩
      | bool b => simp [BasicVarType.contains] at h
      | setOfInt s => simp [BasicVarType.contains] at h
      | array vs => simp [BasicVarType.contains] at h
  · by_cases hc : setInConds m name = []
    · rw [restrictVarType_set_nil hc] at h
      cases v with
      | int x => exact ⟨x, rfl⟩
      | bool b => simp [BasicVarType.contains] at h
      | setOfInt s => simp [BasicVarType.contains] at h
      | array vs => simp [BasicVarType.contains] at h
    · obtain ⟨q, conds, hq⟩ := exists_setInConds_cons hc
      rw [restrictVarType_set_cons hq] at h
      cases v with
      | int x => exact ⟨x, rfl⟩
      | bool b => simp [BasicVarType.contains] at h
      | setOfInt s => simp [BasicVarType.contains] at h
      | array vs => simp [BasicVarType.contains] at h

/-- Inversion of the plain-finite-variable test. -/
theorem plainFiniteIntVar_inv {m : Model} {x : String}
    (h : plainFiniteIntVar m x = true) :
    ∃ ty n anns, (.basic ty n anns none : VarDeclItem) ∈ m.variables ∧
      n.name = x ∧ isFiniteIntType ty = true := by
  unfold plainFiniteIntVar at h
  obtain ⟨d, hd, hdok⟩ := List.any_eq_true.mp h
  cases d with
  | array ty n anns es => simp at hdok
  | basic ty n anns init =>
      cases init with
      | some e => simp at hdok
      | none =>
          simp only [Bool.and_eq_true, beq_iff_eq] at hdok
          exact ⟨ty, n, anns, hd, hdok.1, hdok.2⟩

/-- Inversion of the drop test. -/
theorem setInRestricts_inv {m : Model} {c : ConstraintItem}
    (h : setInRestricts m c = true) :
    ∃ x sv b, setInSubject c = some x ∧ plainFiniteIntVar m x = true ∧
      setInCondOf x c = some (sv, b) := by
  unfold setInRestricts at h
  cases hs : setInSubject c with
  | none => rw [hs] at h; cases h
  | some x =>
      rw [hs] at h
      simp only [Bool.and_eq_true] at h
      cases hc : setInCondOf x c with
      | none => rw [hc] at h; simp at h
      | some q =>
          obtain ⟨sv, b⟩ := q
          exact ⟨x, sv, b, rfl, h.1, hc⟩

/-- Restriction leaves non-finite-integer types unchanged. -/
theorem restrictVarType_eq_of_not_finite {m : Model} {name : String}
    {ty : BasicVarType} (h : isFiniteIntType ty = false) :
    restrictVarType m name ty = ty := by
  cases ty with
  | intRange lo hi => simp [isFiniteIntType] at h
  | intSet xs => simp [isFiniteIntType] at h
  | par t => rfl
  | setOfIntRange lo hi => rfl
  | setOfIntSet xs => rfl

/-! ## Semantic preservation -/

/-- **Coverage of the constant-set restriction**: a store satisfying
    the original constraints and variable domains satisfies the
    restricted model (the kept constraints are a sublist, and the
    dropped memberships follow from the original constraints and the
    original domain). -/
theorem restrictSetIn_covers {m : Model} {store : Store}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    (hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v) :
    (∀ c ∈ (restrictSetInModel m).constraints, c.Holds fullInterp store) ∧
    (∀ d ∈ (restrictSetInModel m).variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v) := by
  constructor
  · intro c hc
    exact hcons c (List.mem_filter.mp hc).1
  · intro d' hd'
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hd'
    cases d with
    | array ty n anns es =>
        simpa [restrictVarDecl] using hvars (.array ty n anns es) hd
    | basic ty n anns init =>
        cases init with
        | some e =>
            simpa [restrictVarDecl] using
              hvars (.basic ty n anns (some e)) hd
        | none =>
            obtain ⟨v, hread, hcont⟩ :=
              hvars (.basic ty n anns none) hd
            simp only [restrictVarDecl]
            by_cases hfin : isFiniteIntType ty = true
            · rcases isFiniteIntType_iff.mp hfin with
                ⟨lo, hi, rfl⟩ | ⟨xs, rfl⟩
              · obtain ⟨p, rfl⟩ := exists_int_of_finite_contains hfin hcont
                refine ⟨.int p, hread, ?_⟩
                rw [restrictVarType_range_int]
                refine ⟨intRange_contains_int.mpr hcont, ?_⟩
                intro q hq
                obtain ⟨c, hc, hcond⟩ := List.mem_filterMap.mp hq
                exact cond_of_holds hcond (by simpa using hread)
                  (hcons c hc)
              · obtain ⟨p, rfl⟩ := exists_int_of_finite_contains hfin hcont
                refine ⟨.int p, hread, ?_⟩
                rw [restrictVarType_set_int]
                refine ⟨intSet_contains_int.mpr hcont, ?_⟩
                intro q hq
                obtain ⟨c, hc, hcond⟩ := List.mem_filterMap.mp hq
                exact cond_of_holds hcond (by simpa using hread)
                  (hcons c hc)
            · have hf : isFiniteIntType ty = false := by
                cases hh : isFiniteIntType ty <;> simp_all
              rw [restrictVarType_eq_of_not_finite hf]
              exact ⟨v, hread, hcont⟩

/-- **Exactness of the constant-set restriction**: a store satisfying
    the restricted model satisfies the original model.  Kept
    constraints are unchanged; a dropped membership is implied by the
    restricted domain. -/
theorem restrictSetIn_exact {m : Model} {store : Store}
    (hcons : ∀ c ∈ (restrictSetInModel m).constraints,
      c.Holds fullInterp store)
    (hvars : ∀ d ∈ (restrictSetInModel m).variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v) :
    (∀ c ∈ m.constraints, c.Holds fullInterp store) ∧
    (∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
          vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v) := by
  constructor
  · intro c hc
    by_cases hdrop : setInRestricts m c = true
    · obtain ⟨x, sv, b, hsubj, hplain, hcond⟩ :=
        setInRestricts_inv hdrop
      obtain ⟨ty, n, anns, hdmem, hname, hfin⟩ :=
        plainFiniteIntVar_inv hplain
      have hd' : (restrictVarDecl m (.basic ty n anns none)) ∈
          (restrictSetInModel m).variables := by
        show _ ∈ m.variables.map (restrictVarDecl m)
        exact List.mem_map.mpr ⟨_, hdmem, rfl⟩
      obtain ⟨v, hread, hcont⟩ := hvars _ hd'
      obtain ⟨p, rfl⟩ := exists_int_of_restrictVarType_contains hfin hcont
      have hcondn : setInCondOf n.name c = some (sv, b) := by
        rw [hname]
        exact hcond
      have hreadx : store (Ident.mk x) = some (.int p) := by
        rw [← hname]
        simpa using hread
      have hconds : CondHolds sv b p := by
        have hqmem : (sv, b) ∈ setInConds m n.name :=
          List.mem_filterMap.mpr ⟨c, hc, hcondn⟩
        rcases isFiniteIntType_iff.mp hfin with
          ⟨lo, hi, rfl⟩ | ⟨xs, rfl⟩
        · rw [restrictVarType_range_int] at hcont
          exact hcont.2 (sv, b) hqmem
        · rw [restrictVarType_set_int] at hcont
          exact hcont.2 (sv, b) hqmem
      exact holds_of_cond hcond hreadx hconds
    · have hkeep : c ∈ (restrictSetInModel m).constraints :=
        List.mem_filter.mpr ⟨hc, by simp [hdrop]⟩
      exact hcons c hkeep
  · intro d hd
    have hd' : restrictVarDecl m d ∈ (restrictSetInModel m).variables := by
      show _ ∈ m.variables.map (restrictVarDecl m)
      exact List.mem_map.mpr ⟨_, hd, rfl⟩
    have hv := hvars _ hd'
    cases d with
    | array ty n anns es =>
        simpa [restrictVarDecl] using hv
    | basic ty n anns init =>
        cases init with
        | some e =>
            simpa [restrictVarDecl] using hv
        | none =>
            have hv' : ∃ v, store n = some v ∧
                (restrictVarType m n.name ty).contains v := by
              simpa [restrictVarDecl] using hv
            obtain ⟨v, hread, hcont⟩ := hv'
            exact ⟨v, hread, restrictVarType_contains_imp hcont⟩

/-! ## The precomputed fast twin

`SetIn.setInRestrictionList` collects the tagged restrictions in one
pass, `setInCondsOf` filters that list, and the subject/finite-name hash
sets gate the scans.  The lemmas below connect them to the scanning
definitions, so `restrictSetInModelFast` is extensionally identical. -/

/-- The per-variable scan equals filtering the precomputed tagged list. -/
theorem setInConds_eq_filterMap (m : Model) (x : String) :
    setInConds m x =
      (setInRestrictionList m).filterMap
        (fun p => if p.1 = x then some p.2 else none) := by
  unfold setInConds setInRestrictionList
  rw [List.filterMap_filterMap]
  congr 1
  funext c
  cases hs : setInShape c with
  | none => simp [setInCondOf, hs]
  | some p =>
      obtain ⟨y, s, b⟩ := p
      cases hd : setArgDenote s with
      | none => simp [setInCondOf, hs, hd]
      | some sv =>
          by_cases hy : y.name = x <;> simp [setInCondOf, hs, hd, hy]

/-- `setInCondsOf` is the filterMap of the tagged list. -/
theorem setInCondsOf_eq_filterMap (rs : List (String × SetInRestriction))
    (x : String) :
    setInCondsOf rs x =
      rs.filterMap (fun p => if p.1 = x then some p.2 else none) := rfl

/-- The restricted type is the model-independent match on its condition
    list. -/
theorem restrictVarType_eq_restrictVarTypeOf (m : Model) (name : String)
    (ty : BasicVarType) :
    restrictVarType m name ty = restrictVarTypeOf (setInConds m name) ty := by
  cases ty with
  | intRange lo hi =>
      cases h : setInConds m name <;> simp [restrictVarType, restrictVarTypeOf, h]
  | intSet xs =>
      cases h : setInConds m name <;> simp [restrictVarType, restrictVarTypeOf, h]
  | par t =>
      cases h : setInConds m name <;> simp [restrictVarType, restrictVarTypeOf, h]
  | setOfIntRange lo hi =>
      cases h : setInConds m name <;> simp [restrictVarType, restrictVarTypeOf, h]
  | setOfIntSet xs =>
      cases h : setInConds m name <;> simp [restrictVarType, restrictVarTypeOf, h]

/-- With no conditions the model-independent restriction is the identity. -/
theorem restrictVarTypeOf_nil (ty : BasicVarType) :
    restrictVarTypeOf [] ty = ty := by
  cases ty <;> rfl

/-- Membership in the precomputed subject-name set. -/
theorem insertSubjectNames_contains
    (rs : List (String × SetInRestriction)) (s : Std.HashSet String)
    (x : String) :
    (insertSubjectNames rs s).contains x =
      (s.contains x || rs.any (fun p => p.1 == x)) := by
  induction rs generalizing s with
  | nil => simp [insertSubjectNames]
  | cons p ps ih =>
      simp only [insertSubjectNames, List.foldl_cons] at ih ⊢
      rw [ih, Std.HashSet.contains_insert]
      simp [Bool.or_assoc, Bool.or_comm, Bool.or_left_comm]

/-- Membership in the subject-name set is exactly being a subject. -/
theorem setInSubjectNames_contains
    (rs : List (String × SetInRestriction)) (x : String) :
    (setInSubjectNames rs).contains x =
      rs.any (fun p => p.1 == x) := by
  simp [setInSubjectNames, insertSubjectNames_contains]

/-- A condition list is empty exactly when no tagged restriction has the
    name. -/
theorem setInCondsOf_eq_nil_iff
    (rs : List (String × SetInRestriction)) (x : String) :
    setInCondsOf rs x = [] ↔ rs.any (fun p => p.1 == x) = false := by
  induction rs with
  | nil => simp [setInCondsOf]
  | cons p ps ih =>
      simp only [setInCondsOf, List.filterMap_cons, List.any_cons] at ih ⊢
      by_cases hp : p.1 = x
      · simp [hp]
      · simp [hp, ih]

/-- Outside the subject-name set there are no conditions. -/
theorem setInCondsOf_eq_nil_of_subjects_false
    {rs : List (String × SetInRestriction)} {x : String}
    (h : (setInSubjectNames rs).contains x = false) :
    setInCondsOf rs x = [] := by
  rw [setInCondsOf_eq_nil_iff]
  rw [setInSubjectNames_contains] at h
  exact h

/-- The gated declaration rewrite equals the scanning one. -/
theorem restrictVarDeclOf_eq (m : Model)
    (rs : List (String × SetInRestriction))
    (hconds : ∀ x, setInCondsOf rs x = setInConds m x)
    (d : VarDeclItem) :
    restrictVarDeclOf rs (setInSubjectNames rs) d = restrictVarDecl m d := by
  cases d with
  | array ty n anns es => rfl
  | basic ty n anns init =>
      cases init with
      | some e => rfl
      | none =>
          unfold restrictVarDeclOf restrictVarDecl
          by_cases hs : (setInSubjectNames rs).contains n.name
          · simp only [hs, if_true]
            rw [hconds n.name, ← restrictVarType_eq_restrictVarTypeOf]
          · have hsf : (setInSubjectNames rs).contains n.name = false := by
              simpa using hs
            have hnil : setInCondsOf rs n.name = [] :=
              setInCondsOf_eq_nil_of_subjects_false hsf
            have hnil' : setInConds m n.name = [] := by
              rw [← hconds n.name, hnil]
            have ht : restrictVarType m n.name ty = ty := by
              rw [restrictVarType_eq_restrictVarTypeOf, hnil',
                restrictVarTypeOf_nil]
            simp [hsf, ht]

/-- Specialization of `restrictVarDeclOf_eq` to the collected list. -/
theorem restrictVarDeclOf_restrictionList (m : Model) (d : VarDeclItem) :
    restrictVarDeclOf (setInRestrictionList m)
        (setInSubjectNames (setInRestrictionList m)) d =
      restrictVarDecl m d := by
  apply restrictVarDeclOf_eq
  intro x
  rw [setInCondsOf_eq_filterMap]
  exact (setInConds_eq_filterMap m x).symm

/-! ## Static well-formedness -/

theorem restrictVarDecl_name (m : Model) (d : VarDeclItem) :
    (restrictVarDecl m d).name = d.name := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => rfl
      | some e => rfl
  | array ty n anns es => rfl

theorem restrictVarType_base {m : Model} {name : String}
    {ty : BasicVarType} :
    (restrictVarType m name ty).base = ty.base := by
  cases ty with
  | intRange lo hi =>
      by_cases hc : setInConds m name = []
      · rw [restrictVarType_range_nil hc]
      · obtain ⟨q, conds, hq⟩ := exists_setInConds_cons hc
        rw [restrictVarType_range_cons hq]
        rfl
  | intSet xs =>
      by_cases hc : setInConds m name = []
      · rw [restrictVarType_set_nil hc]
      · obtain ⟨q, conds, hq⟩ := exists_setInConds_cons hc
        rw [restrictVarType_set_cons hq]
        rfl
  | par t => rfl
  | setOfIntRange lo hi => rfl
  | setOfIntSet xs => rfl

theorem restrictVarDecl_type (m : Model) (d : VarDeclItem) :
    (restrictVarDecl m d).type = d.type := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none =>
          show FznType.base (restrictVarType m n.name ty).base =
            FznType.base ty.base
          rw [restrictVarType_base]
      | some e => rfl
  | array ty n anns es => rfl

/-- The rewrite preserves the global static environment. -/
theorem staticEnv_restrict (m : Model) :
    (restrictSetInModel m).staticEnv = m.staticEnv := by
  funext x
  show (match lookupIdent x ((restrictSetInModel m).parameters.map
          (fun (d : ParDeclItem) => (d.name, (d.type, false)))) with
        | some info => some info
        | none => lookupIdent x ((restrictSetInModel m).variables.map
            (fun (d : VarDeclItem) => (d.name, (d.type, true))))) =
       (match lookupIdent x (m.parameters.map
          (fun (d : ParDeclItem) => (d.name, (d.type, false)))) with
        | some info => some info
        | none => lookupIdent x (m.variables.map
            (fun (d : VarDeclItem) => (d.name, (d.type, true)))))
  have hp : (restrictSetInModel m).parameters = m.parameters := rfl
  have hv : ((restrictSetInModel m).variables.map
        (fun d => (d.name, (d.type, true)))) =
      m.variables.map (fun d => (d.name, (d.type, true))) := by
    rw [show (restrictSetInModel m).variables =
      m.variables.map (restrictVarDecl m) from rfl]
    rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    simp only [Function.comp_apply, restrictVarDecl_name, restrictVarDecl_type]
  rw [hp, hv]

/-- Static well-formedness is preserved by the constant-set
    restriction (the rewrite keeps names, base types, array lengths and
    initializers, and only removes constraints). -/
theorem wf_restrict {m : Model} (hwf : WellFormed fullSig m)
    (hsolve : ∃ anns, m.solve = .satisfy anns) :
    WellFormed fullSig (restrictSetInModel m) := by
  obtain ⟨anns, hs⟩ := hsolve
  have hp : (restrictSetInModel m).parameters = m.parameters := rfl
  have hv : ((restrictSetInModel m).variables.map VarDeclItem.name) =
      m.variables.map VarDeclItem.name := by
    rw [show (restrictSetInModel m).variables =
      m.variables.map (restrictVarDecl m) from rfl]
    rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    exact restrictVarDecl_name m d
  refine
    { predNamesUnique := hwf.predNamesUnique
      valueNamesUnique := ?_
      predParamsUnique := hwf.predParamsUnique
      parameterTypes := ?_
      variableArrayLengths := ?_
      variableInitializers := ?_
      objectiveType := ?_
      constraintsChecked := ?_ }
  · rw [hp, hv]
    exact hwf.valueNamesUnique
  · intro d hd
    rw [hp] at hd
    exact hwf.parameterTypes d hd
  · intro d hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    cases d0 with
    | array ty n anns es =>
        simpa [restrictVarDecl] using hwf.variableArrayLengths _ hd0
    | basic ty n anns init =>
        cases init <;> simp [restrictVarDecl]
  · intro d hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    cases d0 with
    | array ty n anns es =>
        rw [staticEnv_restrict]
        simpa [restrictVarDecl] using hwf.variableInitializers _ hd0
    | basic ty n anns init =>
        cases init with
        | none => trivial
        | some e =>
            rw [staticEnv_restrict]
            simpa [restrictVarDecl] using
              hwf.variableInitializers _ hd0
  · show match m.solve with
      | .satisfy _ => True
      | .minimize _ e | .maximize _ e =>
          e.hasBaseType (restrictSetInModel m).staticEnv .int
    rw [hs]
    exact trivial
  · intro c hc
    have hc0 : c ∈ m.constraints := (List.mem_filter.mp hc).1
    obtain ⟨params, hsig, hca⟩ := hwf.constraintsChecked c hc0
    refine ⟨params, hsig, ?_⟩
    simpa [staticEnv_restrict] using hca

end LeanFzn.Compiler
