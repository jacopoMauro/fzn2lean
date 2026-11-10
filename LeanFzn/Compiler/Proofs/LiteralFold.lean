/-
File: LeanFzn/Compiler/Proofs/LiteralFold.lean

Purpose:
  Correctness of literal folding (`Compiler/LiteralFold.lean`, PLAN.md
  tasks L1, L2 and L3).

  L1 (`foldGroundModel`): a constraint whose arguments are all literals is
  decided by the executable full semantics.  The per-constraint core is
  `groundFold_holds`: the source constraint holds exactly when every
  produced constraint holds.  A false ground fact becomes the always-false
  accepted row `int_lin_le([], [], -1)`, never the empty list.

  L2 (`foldReifModel`): a reified predicate with a Boolean-literal result
  is rewritten to its plain form (`true`) or checked negation (`false`),
  with the semantic table of `tmp/design/l1-l2-literal-fold.md`.

  L3 (`foldSetCardModel`): `set_card(R, x)` with a literal set `R` is
  rewritten to `int_eq(x, |R|)`, using `IntSetValue.card`.

  Model-level `foldSetCard_covers` / `foldSetCard_exact`,
  `foldGround_covers` / `foldGround_exact` and
  `foldReif_covers` / `foldReif_exact` compose into
  `foldLiterals_covers` / `foldLiterals_exact`; `wf_fold` carries static
  well-formedness across all passes.  `Proofs/Normalize` inserts these
  between the array-inlining equivalence and the constant-set
  restriction.

  No public `solveModel_*` statement changes.

Dependencies:
  - LeanFzn.Compiler.LiteralFold (the definitions).
-/

import LeanFzn.Compiler.LiteralFold

namespace LeanFzn.Compiler
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Semantics.Globals

/-! ## Ground arguments -/

theorem groundBasic_eval {b : BasicExpr} {v : Value}
    (h : groundBasic b = some v) (s : Store) : BasicExpr.eval s b = some v := by
  cases b with
  | lit l => simpa [groundBasic, BasicExpr.eval] using h
  | ident x => simp [groundBasic] at h

theorem mapM_groundBasic_eval {es : List BasicExpr} {vs : List Value}
    (h : es.mapM groundBasic = some vs) (s : Store) :
    es.mapM (BasicExpr.eval s) = some vs := by
  induction es generalizing vs with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      rfl
  | cons b rest ih =>
      rw [List.mapM_cons] at h
      cases hb : groundBasic b with
      | none => rw [hb] at h; simp at h
      | some v =>
          rw [hb] at h
          cases hr : rest.mapM groundBasic with
          | none => rw [hr] at h; simp at h
          | some ws =>
              rw [hr] at h
              simp at h
              subst h
              rw [List.mapM_cons, groundBasic_eval hb s, ih hr]
              rfl

theorem groundExpr_eval {e : Expr} {v : Value}
    (h : groundExpr e = some v) (s : Store) : Expr.eval s e = some v := by
  cases e with
  | basic b => exact groundBasic_eval h s
  | array es =>
      simp only [groundExpr, Option.map_eq_some_iff] at h
      obtain ⟨vs, hvs, rfl⟩ := h
      show (es.mapM (BasicExpr.eval s)).map Value.array = some (.array vs)
      rw [mapM_groundBasic_eval hvs s]
      rfl

theorem mapM_groundExpr_eval {es : List Expr} {vs : List Value}
    (h : es.mapM groundExpr = some vs) (s : Store) :
    es.mapM (Expr.eval s) = some vs := by
  induction es generalizing vs with
  | nil =>
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      rfl
  | cons e rest ih =>
      rw [List.mapM_cons] at h
      cases he : groundExpr e with
      | none => rw [he] at h; simp at h
      | some v =>
          rw [he] at h
          cases hr : rest.mapM groundExpr with
          | none => rw [hr] at h; simp at h
          | some ws =>
              rw [hr] at h
              simp at h
              subst h
              rw [List.mapM_cons, groundExpr_eval he s, ih hr]
              rfl

theorem groundArgs_eval {args : List Expr} {vals : List Value}
    (h : groundArgs args = some vals) (s : Store) :
    args.mapM (Expr.eval s) = some vals :=
  mapM_groundExpr_eval h s

/-! ## The always-false row -/

theorem int_lin_le_not_globals : "int_lin_le" ∉ globalsNames := by decide
theorem int_lin_ne_not_globals : "int_lin_ne" ∉ globalsNames := by decide

theorem fullInterp_std_of_not_mem {n : String} (h : n ∉ globalsNames)
    (args : List Value) :
    fullInterp (Ident.mk n) args = stdInterp (Ident.mk n) args := by
  simp [fullInterp, h]

/-! ### Specialised linear semantics

`stdInterp` is a very large name match; unfolding it once per shape here
keeps the value-level case analyses below cheap. -/

theorem stdInterp_int_lin_eq_apply (args : List Value) :
    stdInterp (Ident.mk "int_lin_eq") args =
      match args with
      | [.array as_, .array xs, .int b] => dotProduct as_ xs = some b
      | _ => False := rfl

theorem stdInterp_int_lin_le_apply (args : List Value) :
    stdInterp (Ident.mk "int_lin_le") args =
      match args with
      | [.array as_, .array xs, .int b] => dotLe as_ xs b = true
      | _ => False := rfl

theorem stdInterp_int_lin_ne_apply (args : List Value) :
    stdInterp (Ident.mk "int_lin_ne") args =
      match args with
      | [.array as_, .array xs, .int b] => dotNe as_ xs b = true
      | _ => False := rfl

theorem stdInterp_int_lin_eq_reif_apply (args : List Value) :
    stdInterp (Ident.mk "int_lin_eq_reif") args =
      match args with
      | [.array as_, .array xs, .int b, .bool r] =>
          (r = true ∧ dotProduct as_ xs = some b) ∨
            (r = false ∧ dotProduct as_ xs ≠ some b)
      | _ => False := rfl

theorem stdInterp_int_lin_le_reif_apply (args : List Value) :
    stdInterp (Ident.mk "int_lin_le_reif") args =
      match args with
      | [.array as_, .array xs, .int b, .bool r] =>
          (r = true ∧ dotLe as_ xs b = true) ∨
            (r = false ∧ dotLe as_ xs b = false)
      | _ => False := rfl

theorem stdInterp_int_lin_ne_reif_apply (args : List Value) :
    stdInterp (Ident.mk "int_lin_ne_reif") args =
      match args with
      | [.array as_, .array xs, .int b, .bool r] =>
          (r = true ∧ dotNe as_ xs b = true) ∨
            (r = false ∧ dotNe as_ xs b = false)
      | _ => False := rfl

theorem falseConstraint_args_eval (s : Store) :
    falseConstraint.args.mapM (Expr.eval s) =
      some [.array [], .array [], .int (-1)] := rfl

/-- The false row does not hold in any store. -/
theorem falseConstraint_holds_false (s : Store) :
    ¬ falseConstraint.Holds fullInterp s := by
  rintro ⟨args, hmap, hinterp⟩
  have hargs : args = [.array [], .array [], .int (-1)] := by
    rw [falseConstraint_args_eval s] at hmap
    exact (Option.some.inj hmap).symm
  subst hargs
  have hno : ¬ fullInterp (Ident.mk "int_lin_le")
      [Value.array [], Value.array [], Value.int (-1)] := by
    simp [fullInterp, int_lin_le_not_globals, stdInterp, dotLe, dotProduct]
  exact hno hinterp

theorem falseConstraint_sig :
    fullSig (Ident.mk "int_lin_le") =
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))] := by
  simp [fullSig, globalsSig, stdSig]

theorem falseConstraint_check (env : StaticEnv) :
    Forall2 (Expr.checkArg env) falseConstraint.args
      [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))] := by
  simp [falseConstraint, Forall2, Expr.checkArg, BasicExpr.checkBase,
    BasicPredParamType.accepts, PredIndexSet.acceptsLength,
    BasicPredParamType.baseType, BasicLiteral.type, BasicParType.base,
    BasicVarType.base]

/-! ## Per-constraint ground folding -/

/-- A true ground constraint can be dropped and a false one is
    equivalent to the always-false row. -/
theorem groundFold_holds {c : ConstraintItem} {s : Store} :
    c.Holds fullInterp s ↔
      ∀ d ∈ groundFold c, d.Holds fullInterp s := by
  unfold groundFold
  cases hg : groundArgs c.args with
  | none =>
      dsimp only
      simp
  | some vals =>
      dsimp only
      by_cases hmem : c.name.name ∈ fullCheckableNames
      · rw [dif_pos hmem]
        cases hb : fullInterpB c.name vals with
        | false =>
            rw [if_neg (by simp [hb])]
            constructor
            · intro hc
              exfalso
              obtain ⟨args, hmap, hp⟩ := hc
              have hargs : args = vals := by
                rw [groundArgs_eval hg s] at hmap
                exact (Option.some.inj hmap).symm
              have hp' : fullInterp c.name vals := by
                rwa [hargs] at hp
              have htrue : fullInterpB c.name vals = true :=
                (fullInterpB_iff hmem).mpr hp'
              rw [hb] at htrue
              cases htrue
            · intro h
              exact False.elim (falseConstraint_holds_false s
                (h falseConstraint (by simp)))
        | true =>
            rw [if_pos (by simp [hb])]
            constructor
            · intro _; simp
            · intro _
              exact ⟨vals, groundArgs_eval hg s, (fullInterpB_iff hmem).mp hb⟩
      · rw [dif_neg hmem]
        simp

theorem foldGround_covers {m : Model} {s : Store}
    (h : ∀ c ∈ m.constraints, c.Holds fullInterp s) :
    ∀ c ∈ (foldGroundModel m).constraints, c.Holds fullInterp s := by
  intro c hc
  obtain ⟨c0, hc0, hfold⟩ := List.mem_flatMap.mp hc
  exact (groundFold_holds (c := c0)).mp (h c0 hc0) c hfold

theorem foldGround_exact {m : Model} {s : Store}
    (h : ∀ c ∈ (foldGroundModel m).constraints, c.Holds fullInterp s) :
    ∀ c ∈ m.constraints, c.Holds fullInterp s := by
  intro c hc
  exact (groundFold_holds (c := c)).mpr
    (fun d hd => h d (List.mem_flatMap.mpr ⟨c, hc, hd⟩))

theorem wf_groundFold {m : Model} (hwf : WellFormed fullSig m)
    (hpred : m.predicates = []) :
    WellFormed fullSig (foldGroundModel m) := by
  refine
    { predNamesUnique := ?_
      valueNamesUnique := hwf.valueNamesUnique
      predParamsUnique := hwf.predParamsUnique
      parameterTypes := hwf.parameterTypes
      variableArrayLengths := hwf.variableArrayLengths
      variableInitializers := hwf.variableInitializers
      objectiveType := hwf.objectiveType
      constraintsChecked := ?_ }
  · simpa [foldGroundModel, hpred] using hwf.predNamesUnique
  · intro c' hc'
    obtain ⟨c, hc, hfold⟩ := List.mem_flatMap.mp hc'
    unfold groundFold at hfold
    split at hfold
    · rename_i vals hg
      split at hfold
      · rename_i hmem
        split at hfold
        · simp at hfold
        · simp only [List.mem_singleton] at hfold
          subst hfold
          refine ⟨_, ?_, falseConstraint_check _⟩
          have hsig : (foldGroundModel m).sigEnv fullSig
              falseConstraint.name = fullSig falseConstraint.name := by
            simp [Model.sigEnv, Model.declaredSigs, foldGroundModel, hpred,
              lookupIdent]
          rw [hsig]
          exact falseConstraint_sig
      · rename_i hmem
        simp only [List.mem_singleton] at hfold
        subst hfold
        exact hwf.constraintsChecked _ hc
    · rename_i hg
      simp only [List.mem_singleton] at hfold
      subst hfold
      exact hwf.constraintsChecked _ hc


/-! ## Evaluating fixed argument shapes -/

theorem mapM_three {s : Store} {a b k : Expr} {va vb vk : Value}
    (ha : Expr.eval s a = some va) (hb : Expr.eval s b = some vb)
    (hk : Expr.eval s k = some vk) :
    ([a, b, k] : List Expr).mapM (Expr.eval s) = some [va, vb, vk] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_nil, ha, hb, hk]
  rfl

theorem mapM_three_inv {s : Store} {a b k : Expr} {args : List Value}
    (h : ([a, b, k] : List Expr).mapM (Expr.eval s) = some args) :
    ∃ va vb vk, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
      Expr.eval s k = some vk ∧ args = [va, vb, vk] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_nil] at h
  cases ha : Expr.eval s a with
  | none => rw [ha] at h; simp at h
  | some va =>
      rw [ha] at h
      cases hb : Expr.eval s b with
      | none => rw [hb] at h; simp at h
      | some vb =>
          rw [hb] at h
          cases hk : Expr.eval s k with
          | none => rw [hk] at h; simp at h
          | some vk =>
              rw [hk] at h
              simp at h
              exact ⟨va, vb, vk, rfl, rfl, rfl, h.symm⟩

theorem mapM_four_lit {s : Store} {a b k : Expr} {r : Bool}
    {va vb vk : Value}
    (ha : Expr.eval s a = some va) (hb : Expr.eval s b = some vb)
    (hk : Expr.eval s k = some vk) :
    ([a, b, k, .basic (.lit (.bool r))] : List Expr).mapM (Expr.eval s) =
      some [va, vb, vk, .bool r] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_cons,
    List.mapM_nil, ha, hb, hk]
  rfl

theorem mapM_four_lit_inv {s : Store} {a b k : Expr} {r : Bool}
    {args : List Value}
    (h : ([a, b, k, .basic (.lit (.bool r))] : List Expr).mapM
      (Expr.eval s) = some args) :
    ∃ va vb vk, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
      Expr.eval s k = some vk ∧ args = [va, vb, vk, .bool r] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_cons,
    List.mapM_nil] at h
  cases ha : Expr.eval s a with
  | none => rw [ha] at h; simp at h
  | some va =>
      rw [ha] at h
      cases hb : Expr.eval s b with
      | none => rw [hb] at h; simp at h
      | some vb =>
          rw [hb] at h
          cases hk : Expr.eval s k with
          | none => rw [hk] at h; simp at h
          | some vk =>
              rw [hk] at h
              rw [show Expr.eval s (.basic (.lit (.bool r))) = some (.bool r)
                from rfl] at h
              simp at h
              exact ⟨va, vb, vk, rfl, rfl, rfl, h.symm⟩


theorem mapM_pair {s : Store} {a b : Expr} {va vb : Value}
    (ha : Expr.eval s a = some va) (hb : Expr.eval s b = some vb) :
    ([a, b] : List Expr).mapM (Expr.eval s) = some [va, vb] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_nil, ha, hb]
  rfl

theorem mapM_pair_inv {s : Store} {a b : Expr} {args : List Value}
    (h : ([a, b] : List Expr).mapM (Expr.eval s) = some args) :
    ∃ va vb, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
      args = [va, vb] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_nil] at h
  cases ha : Expr.eval s a with
  | none => rw [ha] at h; simp at h
  | some va =>
      rw [ha] at h
      cases hb : Expr.eval s b with
      | none => rw [hb] at h; simp at h
      | some vb =>
          rw [hb] at h
          simp at h
          exact ⟨va, vb, rfl, rfl, h.symm⟩

theorem mapM_three_lit {s : Store} {a b : Expr} {r : Bool} {va vb : Value}
    (ha : Expr.eval s a = some va) (hb : Expr.eval s b = some vb) :
    ([a, b, .basic (.lit (.bool r))] : List Expr).mapM (Expr.eval s) =
      some [va, vb, .bool r] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_nil, ha, hb]
  rfl

theorem mapM_three_lit_inv {s : Store} {a b : Expr} {r : Bool}
    {args : List Value}
    (h : ([a, b, .basic (.lit (.bool r))] : List Expr).mapM (Expr.eval s) =
      some args) :
    ∃ va vb, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
      args = [va, vb, .bool r] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_cons, List.mapM_nil] at h
  cases ha : Expr.eval s a with
  | none => rw [ha] at h; simp at h
  | some va =>
      rw [ha] at h
      cases hb : Expr.eval s b with
      | none => rw [hb] at h; simp at h
      | some vb =>
          rw [hb] at h
          rw [show Expr.eval s (.basic (.lit (.bool r))) = some (.bool r)
            from rfl] at h
          simp at h
          exact ⟨va, vb, rfl, rfl, h.symm⟩

/-! ## `Holds` at fixed arities -/

theorem holds_two_iff {p : Ident} {s : Store} {a b : Expr}
    {anns : List Annotation} :
    (ConstraintItem.mk p [a, b] anns).Holds fullInterp s ↔
      ∃ va vb, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
        fullInterp p [va, vb] := by
  constructor
  · rintro ⟨args, hmap, hp⟩
    obtain ⟨va, vb, ha, hb, rfl⟩ := mapM_pair_inv hmap
    exact ⟨va, vb, ha, hb, hp⟩
  · rintro ⟨va, vb, ha, hb, hp⟩
    exact ⟨[va, vb], mapM_pair ha hb, hp⟩

theorem holds_three_lit_iff {p : Ident} {s : Store} {a b : Expr} {r : Bool}
    {anns : List Annotation} :
    (ConstraintItem.mk p [a, b, .basic (.lit (.bool r))] anns).Holds
      fullInterp s ↔
      ∃ va vb, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
        fullInterp p [va, vb, .bool r] := by
  constructor
  · rintro ⟨args, hmap, hp⟩
    obtain ⟨va, vb, ha, hb, rfl⟩ := mapM_three_lit_inv hmap
    exact ⟨va, vb, ha, hb, hp⟩
  · rintro ⟨va, vb, ha, hb, hp⟩
    exact ⟨[va, vb, .bool r], mapM_three_lit ha hb, hp⟩

theorem holds_three_iff {p : Ident} {s : Store} {a b k : Expr}
    {anns : List Annotation} :
    (ConstraintItem.mk p [a, b, k] anns).Holds fullInterp s ↔
      ∃ va vb vk, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
        Expr.eval s k = some vk ∧ fullInterp p [va, vb, vk] := by
  constructor
  · rintro ⟨args, hmap, hp⟩
    obtain ⟨va, vb, vk, ha, hb, hk, rfl⟩ := mapM_three_inv hmap
    exact ⟨va, vb, vk, ha, hb, hk, hp⟩
  · rintro ⟨va, vb, vk, ha, hb, hk, hp⟩
    exact ⟨[va, vb, vk], mapM_three ha hb hk, hp⟩

theorem holds_four_lit_true_iff {p : Ident} {s : Store} {a b k : Expr}
    {anns : List Annotation} :
    (ConstraintItem.mk p [a, b, k, .basic (.lit (.bool true))] anns).Holds
      fullInterp s ↔
      ∃ va vb vk, Expr.eval s a = some va ∧ Expr.eval s b = some vb ∧
        Expr.eval s k = some vk ∧
        fullInterp p [va, vb, vk, .bool true] := by
  constructor
  · rintro ⟨args, hmap, hp⟩
    obtain ⟨va, vb, vk, ha, hb, hk, rfl⟩ := mapM_four_lit_inv hmap
    exact ⟨va, vb, vk, ha, hb, hk, hp⟩
  · rintro ⟨va, vb, vk, ha, hb, hk, hp⟩
    exact ⟨[va, vb, vk, .bool true], mapM_four_lit ha hb hk, hp⟩

/-! ## Combined argument-shape rewrites -/

theorem holds_two_three_rewrite {p q : Ident} {s : Store} {a b : Expr}
    {r : Bool} {anns1 anns2 : List Annotation}
    (hval : ∀ va vb, fullInterp p [va, vb, .bool r] ↔
      fullInterp q [va, vb]) :
    (ConstraintItem.mk p [a, b, .basic (.lit (.bool r))] anns1).Holds
        fullInterp s ↔
      (ConstraintItem.mk q [a, b] anns2).Holds fullInterp s := by
  rw [holds_three_lit_iff, holds_two_iff]
  constructor
  · rintro ⟨va, vb, ha, hb, hp⟩
    exact ⟨va, vb, ha, hb, (hval va vb).mp hp⟩
  · rintro ⟨va, vb, ha, hb, hp⟩
    exact ⟨va, vb, ha, hb, (hval va vb).mpr hp⟩

theorem holds_two_three_swap_rewrite {p q : Ident} {s : Store} {a b : Expr}
    {r : Bool} {anns1 anns2 : List Annotation}
    (hval : ∀ va vb, fullInterp p [va, vb, .bool r] ↔
      fullInterp q [vb, va]) :
    (ConstraintItem.mk p [a, b, .basic (.lit (.bool r))] anns1).Holds
        fullInterp s ↔
      (ConstraintItem.mk q [b, a] anns2).Holds fullInterp s := by
  rw [holds_three_lit_iff, holds_two_iff]
  constructor
  · rintro ⟨va, vb, ha, hb, hp⟩
    exact ⟨vb, va, hb, ha, (hval va vb).mp hp⟩
  · rintro ⟨vb, va, hb, ha, hp⟩
    exact ⟨va, vb, ha, hb, (hval va vb).mpr hp⟩

theorem holds_three_four_rewrite {p q : Ident} {s : Store} {a b k : Expr}
    {anns1 anns2 : List Annotation}
    (hval : ∀ va vb vk, fullInterp p [va, vb, vk, .bool true] ↔
      fullInterp q [va, vb, vk]) :
    (ConstraintItem.mk p [a, b, k, .basic (.lit (.bool true))] anns1).Holds
        fullInterp s ↔
      (ConstraintItem.mk q [a, b, k] anns2).Holds fullInterp s := by
  rw [holds_four_lit_true_iff, holds_three_iff]
  constructor
  · rintro ⟨va, vb, vk, ha, hb, hk, hp⟩
    exact ⟨va, vb, vk, ha, hb, hk, (hval va vb vk).mp hp⟩
  · rintro ⟨va, vb, vk, ha, hb, hk, hp⟩
    exact ⟨va, vb, vk, ha, hb, hk, (hval va vb vk).mpr hp⟩

/-! ## Value-level semantics of the rewrites -/

theorem int_eq_not_globals : "int_eq" ∉ globalsNames := by decide
theorem int_ne_not_globals : "int_ne" ∉ globalsNames := by decide
theorem int_le_not_globals : "int_le" ∉ globalsNames := by decide
theorem int_lt_not_globals : "int_lt" ∉ globalsNames := by decide
theorem int_eq_reif_not_globals : "int_eq_reif" ∉ globalsNames := by decide
theorem int_ne_reif_not_globals : "int_ne_reif" ∉ globalsNames := by decide
theorem int_le_reif_not_globals : "int_le_reif" ∉ globalsNames := by decide
theorem int_lt_reif_not_globals : "int_lt_reif" ∉ globalsNames := by decide
theorem int_ge_reif_not_globals : "int_ge_reif" ∉ globalsNames := by decide
theorem int_gt_reif_not_globals : "int_gt_reif" ∉ globalsNames := by decide
theorem int_lin_eq_not_globals : "int_lin_eq" ∉ globalsNames := by decide
theorem int_lin_eq_reif_not_globals : "int_lin_eq_reif" ∉ globalsNames := by decide
theorem int_lin_le_reif_not_globals : "int_lin_le_reif" ∉ globalsNames := by decide
theorem int_lin_ne_reif_not_globals : "int_lin_ne_reif" ∉ globalsNames := by decide

theorem int_eq_reif_true_val (va vb : Value) :
    fullInterp (Ident.mk "int_eq_reif") [va, vb, .bool true] ↔
      fullInterp (Ident.mk "int_eq") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_eq_reif_not_globals,
    fullInterp_std_of_not_mem int_eq_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_eq_reif_false_val (va vb : Value) :
    fullInterp (Ident.mk "int_eq_reif") [va, vb, .bool false] ↔
      fullInterp (Ident.mk "int_ne") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_eq_reif_not_globals,
    fullInterp_std_of_not_mem int_ne_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_ne_reif_true_val (va vb : Value) :
    fullInterp (Ident.mk "int_ne_reif") [va, vb, .bool true] ↔
      fullInterp (Ident.mk "int_ne") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_ne_reif_not_globals,
    fullInterp_std_of_not_mem int_ne_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_ne_reif_false_val (va vb : Value) :
    fullInterp (Ident.mk "int_ne_reif") [va, vb, .bool false] ↔
      fullInterp (Ident.mk "int_eq") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_ne_reif_not_globals,
    fullInterp_std_of_not_mem int_eq_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_le_reif_true_val (va vb : Value) :
    fullInterp (Ident.mk "int_le_reif") [va, vb, .bool true] ↔
      fullInterp (Ident.mk "int_le") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_le_reif_not_globals,
    fullInterp_std_of_not_mem int_le_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_le_reif_false_val (va vb : Value) :
    fullInterp (Ident.mk "int_le_reif") [va, vb, .bool false] ↔
      fullInterp (Ident.mk "int_lt") [vb, va] := by
  rw [fullInterp_std_of_not_mem int_le_reif_not_globals,
    fullInterp_std_of_not_mem int_lt_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_lt_reif_true_val (va vb : Value) :
    fullInterp (Ident.mk "int_lt_reif") [va, vb, .bool true] ↔
      fullInterp (Ident.mk "int_lt") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_lt_reif_not_globals,
    fullInterp_std_of_not_mem int_lt_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_lt_reif_false_val (va vb : Value) :
    fullInterp (Ident.mk "int_lt_reif") [va, vb, .bool false] ↔
      fullInterp (Ident.mk "int_le") [vb, va] := by
  rw [fullInterp_std_of_not_mem int_lt_reif_not_globals,
    fullInterp_std_of_not_mem int_le_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_ge_reif_true_val (va vb : Value) :
    fullInterp (Ident.mk "int_ge_reif") [va, vb, .bool true] ↔
      fullInterp (Ident.mk "int_le") [vb, va] := by
  rw [fullInterp_std_of_not_mem int_ge_reif_not_globals,
    fullInterp_std_of_not_mem int_le_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_ge_reif_false_val (va vb : Value) :
    fullInterp (Ident.mk "int_ge_reif") [va, vb, .bool false] ↔
      fullInterp (Ident.mk "int_lt") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_ge_reif_not_globals,
    fullInterp_std_of_not_mem int_lt_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_gt_reif_true_val (va vb : Value) :
    fullInterp (Ident.mk "int_gt_reif") [va, vb, .bool true] ↔
      fullInterp (Ident.mk "int_lt") [vb, va] := by
  rw [fullInterp_std_of_not_mem int_gt_reif_not_globals,
    fullInterp_std_of_not_mem int_lt_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_gt_reif_false_val (va vb : Value) :
    fullInterp (Ident.mk "int_gt_reif") [va, vb, .bool false] ↔
      fullInterp (Ident.mk "int_le") [va, vb] := by
  rw [fullInterp_std_of_not_mem int_gt_reif_not_globals,
    fullInterp_std_of_not_mem int_le_not_globals]
  cases va <;> cases vb <;> simp [stdInterp]

theorem int_lin_eq_reif_true_val (va vb vk : Value) :
    fullInterp (Ident.mk "int_lin_eq_reif") [va, vb, vk, .bool true] ↔
      fullInterp (Ident.mk "int_lin_eq") [va, vb, vk] := by
  rw [fullInterp_std_of_not_mem int_lin_eq_reif_not_globals,
    fullInterp_std_of_not_mem int_lin_eq_not_globals,
    stdInterp_int_lin_eq_reif_apply, stdInterp_int_lin_eq_apply]
  cases va <;> cases vb <;> cases vk <;> simp

theorem int_lin_le_reif_true_val (va vb vk : Value) :
    fullInterp (Ident.mk "int_lin_le_reif") [va, vb, vk, .bool true] ↔
      fullInterp (Ident.mk "int_lin_le") [va, vb, vk] := by
  rw [fullInterp_std_of_not_mem int_lin_le_reif_not_globals,
    fullInterp_std_of_not_mem int_lin_le_not_globals,
    stdInterp_int_lin_le_reif_apply, stdInterp_int_lin_le_apply]
  cases va <;> cases vb <;> cases vk <;> simp

theorem int_lin_ne_reif_true_val (va vb vk : Value) :
    fullInterp (Ident.mk "int_lin_ne_reif") [va, vb, vk, .bool true] ↔
      fullInterp (Ident.mk "int_lin_ne") [va, vb, vk] := by
  rw [fullInterp_std_of_not_mem int_lin_ne_reif_not_globals,
    fullInterp_std_of_not_mem int_lin_ne_not_globals,
    stdInterp_int_lin_ne_reif_apply, stdInterp_int_lin_ne_apply]
  cases va <;> cases vb <;> cases vk <;> simp

/-! ## Constant-set cardinality -/

theorem set_card_not_globals : "set_card" ∉ globalsNames := by decide

theorem set_card_int_eq_val (sv : IntSetValue) (v : Value) :
    fullInterp (Ident.mk "set_card") [.setOfInt sv, v] ↔
      fullInterp (Ident.mk "int_eq") [v, .int (sv.card : Int)] := by
  rw [fullInterp_std_of_not_mem set_card_not_globals,
    fullInterp_std_of_not_mem int_eq_not_globals]
  cases v <;> simp [stdInterp]

/-- The `set_card` rewrite at fixed argument shapes. -/
theorem holds_set_card_rewrite {s : Store} {sl : SetLiteral} {x : BasicExpr}
    {anns1 anns2 : List Annotation} :
    (ConstraintItem.mk (Ident.mk "set_card")
      [.basic (.lit (.set sl)), .basic x] anns1).Holds fullInterp s ↔
    (ConstraintItem.mk (Ident.mk "int_eq")
      [.basic x, .basic (.lit (.int (sl.denote.card)))] anns2).Holds
        fullInterp s := by
  rw [holds_two_iff, holds_two_iff]
  constructor
  · rintro ⟨v1, v2, h1, h2, hp⟩
    have hv1 : v1 = .setOfInt sl.denote := by
      simpa [Expr.eval, BasicExpr.eval, BasicLiteral.denote] using h1.symm
    subst hv1
    exact ⟨v2, .int (sl.denote.card : Int), h2, rfl,
      (set_card_int_eq_val sl.denote v2).mp hp⟩
  · rintro ⟨v1, v2, h1, h2, hp⟩
    have hv2 : v2 = .int (sl.denote.card : Int) := by
      simpa [Expr.eval, BasicExpr.eval, BasicLiteral.denote] using h2.symm
    subst hv2
    exact ⟨.setOfInt sl.denote, v1, rfl, h1,
      (set_card_int_eq_val sl.denote v1).mpr hp⟩

/-- One `set_card` constraint before the ground decision. -/
theorem setCard_holds {c d : ConstraintItem} {s : Store}
    (h : setCardFold c = [d]) :
    c.Holds fullInterp s ↔ d.Holds fullInterp s := by
  obtain ⟨cn, cargs, canns⟩ := c
  unfold setCardFold at h
  split at h
  · rename_i sl x heqn heqa
    rw [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hcn : cn = Ident.mk "set_card" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    exact holds_set_card_rewrite
  · rename_i hnone
    rw [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Iff.rfl

theorem setCard_singleton (c : ConstraintItem) :
    ∃ d, setCardFold c = [d] := by
  unfold setCardFold
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem setCard_eq_of_mem {c d : ConstraintItem} (h : d ∈ setCardFold c) :
    setCardFold c = [d] := by
  obtain ⟨e, he⟩ := setCard_singleton c
  rw [he] at h ⊢
  rw [List.mem_singleton] at h
  rw [← h]

theorem foldSetCard_covers {m : Model} {s : Store}
    (h : ∀ c ∈ m.constraints, c.Holds fullInterp s) :
    ∀ c ∈ (foldSetCardModel m).constraints, c.Holds fullInterp s := by
  intro c hc
  obtain ⟨c0, hc0, hfold⟩ := List.mem_flatMap.mp hc
  exact (setCard_holds (c := c0) (d := c) (s := s)
    (setCard_eq_of_mem hfold)).mp (h c0 hc0)

theorem foldSetCard_exact {m : Model} {s : Store}
    (h : ∀ c ∈ (foldSetCardModel m).constraints, c.Holds fullInterp s) :
    ∀ c ∈ m.constraints, c.Holds fullInterp s := by
  intro c hc
  obtain ⟨d, hd⟩ := setCard_singleton c
  exact (setCard_holds (c := c) (d := d) (s := s) hd).mpr
    (h d (List.mem_flatMap.mpr ⟨c, hc, by simp [hd]⟩))

/-! ## One reified constraint -/

theorem reifScalar_holds {c d : ConstraintItem} {s : Store}
    (h : reifScalar c = some d) :
    c.Holds fullInterp s ↔ d.Holds fullInterp s := by
  obtain ⟨cn, cargs, canns⟩ := c
  unfold reifScalar at h
  split at h
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_eq" else "int_ne")
                    args := [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_eq_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_eq_reif") (q := Ident.mk "int_ne")
        (anns1 := canns) (anns2 := []) int_eq_reif_false_val
    · simp only [if_true]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_eq_reif") (q := Ident.mk "int_eq")
        (anns1 := canns) (anns2 := []) int_eq_reif_true_val
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_ne" else "int_eq")
                    args := [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_ne_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_ne_reif") (q := Ident.mk "int_eq")
        (anns1 := canns) (anns2 := []) int_ne_reif_false_val
    · simp only [if_true]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_ne_reif") (q := Ident.mk "int_ne")
        (anns1 := canns) (anns2 := []) int_ne_reif_true_val
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_le" else "int_lt")
                    args := if r then [a, b] else [b, a], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_le_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact holds_two_three_swap_rewrite
        (p := Ident.mk "int_le_reif") (q := Ident.mk "int_lt")
        (anns1 := canns) (anns2 := []) int_le_reif_false_val
    · simp only [if_true]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_le_reif") (q := Ident.mk "int_le")
        (anns1 := canns) (anns2 := []) int_le_reif_true_val
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_lt" else "int_le")
                    args := if r then [a, b] else [b, a], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lt_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact holds_two_three_swap_rewrite
        (p := Ident.mk "int_lt_reif") (q := Ident.mk "int_le")
        (anns1 := canns) (anns2 := []) int_lt_reif_false_val
    · simp only [if_true]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_lt_reif") (q := Ident.mk "int_lt")
        (anns1 := canns) (anns2 := []) int_lt_reif_true_val
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_le" else "int_lt")
                    args := if r then [b, a] else [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_ge_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_ge_reif") (q := Ident.mk "int_lt")
        (anns1 := canns) (anns2 := []) int_ge_reif_false_val
    · simp only [if_true]
      exact holds_two_three_swap_rewrite
        (p := Ident.mk "int_ge_reif") (q := Ident.mk "int_le")
        (anns1 := canns) (anns2 := []) int_ge_reif_true_val
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_lt" else "int_le")
                    args := if r then [b, a] else [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_gt_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact holds_two_three_rewrite
        (p := Ident.mk "int_gt_reif") (q := Ident.mk "int_le")
        (anns1 := canns) (anns2 := []) int_gt_reif_false_val
    · simp only [if_true]
      exact holds_two_three_swap_rewrite
        (p := Ident.mk "int_gt_reif") (q := Ident.mk "int_lt")
        (anns1 := canns) (anns2 := []) int_gt_reif_true_val
  · rename_i a b k heqn heqa
    have hd : d = { name := Ident.mk "int_lin_eq"
                    args := [a, b, k], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lin_eq_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    exact holds_three_four_rewrite
      (p := Ident.mk "int_lin_eq_reif") (q := Ident.mk "int_lin_eq")
      (anns1 := canns) (anns2 := []) int_lin_eq_reif_true_val
  · rename_i a b k heqn heqa
    have hd : d = { name := Ident.mk "int_lin_le"
                    args := [a, b, k], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lin_le_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    exact holds_three_four_rewrite
      (p := Ident.mk "int_lin_le_reif") (q := Ident.mk "int_lin_le")
      (anns1 := canns) (anns2 := []) int_lin_le_reif_true_val
  · rename_i a b k heqn heqa
    have hd : d = { name := Ident.mk "int_lin_ne"
                    args := [a, b, k], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lin_ne_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    exact holds_three_four_rewrite
      (p := Ident.mk "int_lin_ne_reif") (q := Ident.mk "int_lin_ne")
      (anns1 := canns) (anns2 := []) int_lin_ne_reif_true_val
  · cases h

theorem reifFold_holds {c d : ConstraintItem} {s : Store}
    (h : reifFold c = [d]) :
    c.Holds fullInterp s ↔ d.Holds fullInterp s := by
  unfold reifFold at h
  split at h
  · rename_i d0 hsome
    rw [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact reifScalar_holds hsome
  · rename_i hnone
    rw [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    exact Iff.rfl

theorem reifFold_singleton (c : ConstraintItem) :
    ∃ d, reifFold c = [d] := by
  unfold reifFold
  split
  · exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem reifFold_eq_of_mem {c d : ConstraintItem} (h : d ∈ reifFold c) :
    reifFold c = [d] := by
  obtain ⟨e, he⟩ := reifFold_singleton c
  rw [he] at h ⊢
  rw [List.mem_singleton] at h
  rw [← h]

theorem foldReif_covers {m : Model} {s : Store}
    (h : ∀ c ∈ m.constraints, c.Holds fullInterp s) :
    ∀ c ∈ (foldReifModel m).constraints, c.Holds fullInterp s := by
  intro c hc
  obtain ⟨c0, hc0, hfold⟩ := List.mem_flatMap.mp hc
  exact (reifFold_holds (c := c0) (d := c) (s := s)
    (reifFold_eq_of_mem hfold)).mp (h c0 hc0)

theorem foldReif_exact {m : Model} {s : Store}
    (h : ∀ c ∈ (foldReifModel m).constraints, c.Holds fullInterp s) :
    ∀ c ∈ m.constraints, c.Holds fullInterp s := by
  intro c hc
  obtain ⟨d, hd⟩ := reifFold_singleton c
  exact (reifFold_holds (c := c) (d := d) (s := s) hd).mpr
    (h d (List.mem_flatMap.mpr ⟨c, hc, by simp [hd]⟩))

/-! ## Well-formedness of the literal-result rewrite -/

/-- Par-to-var coercion at the basic-expression level. -/
theorem checkBase_par_var {env : StaticEnv} {b : BasicExpr} {t : BasicParType}
    (h : b.checkBase env (.par t)) : b.checkBase env (.var (.par t)) := by
  cases b with
  | lit l =>
      simpa [BasicExpr.checkBase, BasicParType.base, BasicVarType.base,
        BasicPredParamType.accepts, BasicPredParamType.baseType,
        BasicPredParamType.isPar] using h
  | ident x =>
      cases hx : env x with
      | none => simpa [BasicExpr.checkBase, hx] using h
      | some info =>
          obtain ⟨ty, isVar⟩ := info
          cases ty with
          | base t' =>
              simp [BasicExpr.checkBase, hx, BasicParType.base,
                BasicVarType.base, BasicPredParamType.accepts,
                BasicPredParamType.baseType, BasicPredParamType.isPar] at h ⊢
              exact h.1
          | array n t' => simpa [BasicExpr.checkBase, hx] using h

/-- Par-to-var coercion at the expression level. -/
theorem checkArg_par_var {env : StaticEnv} {e : Expr} {t : BasicParType}
    (h : Expr.checkArg env e (.basic (.par t))) :
    Expr.checkArg env e (.basic (.var (.par t))) := by
  cases e with
  | basic b => exact checkBase_par_var h
  | array es => simpa [Expr.checkArg] using h

/-- Signature of the plain scalar integer predicates. -/
theorem sigEnv_two_int {m : Model} (hpred : m.predicates = [])
    {n : String}
    (hn : n = "int_eq" ∨ n = "int_ne" ∨ n = "int_le" ∨ n = "int_lt" ∨
      n = "int_ge" ∨ n = "int_gt") :
    m.sigEnv fullSig (Ident.mk n) =
      some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Model.sigEnv, Model.declaredSigs, hpred, lookupIdent, fullSig,
      globalsSig, stdSig]

/-- Signature of the plain linear integer predicates. -/
theorem sigEnv_three_linear {m : Model} (hpred : m.predicates = [])
    {n : String}
    (hn : n = "int_lin_eq" ∨ n = "int_lin_le" ∨ n = "int_lin_ne") :
    m.sigEnv fullSig (Ident.mk n) =
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.var (.par .int))] := by
  rcases hn with rfl | rfl | rfl <;>
    simp [Model.sigEnv, Model.declaredSigs, hpred, lookupIdent, fullSig,
      globalsSig, stdSig]

/-- Signature of the scalar reified integer predicates. -/
theorem sigEnv_two_int_reif {m : Model} (hpred : m.predicates = [])
    {n : String}
    (hn : n = "int_eq_reif" ∨ n = "int_ne_reif" ∨ n = "int_le_reif" ∨
      n = "int_lt_reif" ∨ n = "int_ge_reif" ∨ n = "int_gt_reif") :
    m.sigEnv fullSig (Ident.mk n) =
      some [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Model.sigEnv, Model.declaredSigs, hpred, lookupIdent, fullSig,
      globalsSig, stdSig]

/-- Signature of the linear reified integer predicates. -/
theorem sigEnv_three_linear_reif {m : Model} (hpred : m.predicates = [])
    {n : String}
    (hn : n = "int_lin_eq_reif" ∨ n = "int_lin_le_reif" ∨
      n = "int_lin_ne_reif") :
    m.sigEnv fullSig (Ident.mk n) =
      some [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int), .basic (.var (.par .bool))] := by
  rcases hn with rfl | rfl | rfl <;>
    simp [Model.sigEnv, Model.declaredSigs, hpred, lookupIdent, fullSig,
      globalsSig, stdSig]

/-- Signature of `set_card`. -/
theorem sigEnv_set_card {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "set_card") =
      some [.basic (.var (.par .setOfInt)), .basic (.var (.par .int))] := by
  simp [Model.sigEnv, Model.declaredSigs, hpred, lookupIdent, fullSig,
    globalsSig, stdSig]

theorem checkArg_int_lit {env : StaticEnv} (k : Int) :
    Expr.checkArg env (.basic (.lit (.int k))) (.basic (.var (.par .int))) := by
  simp [Expr.checkArg, BasicExpr.checkBase, BasicPredParamType.accepts,
    BasicPredParamType.baseType, BasicPredParamType.isPar, BasicParType.base,
    BasicVarType.base, BasicLiteral.type]

/-- The `set_card` rewrite preserves static checking. -/
theorem setCard_wf {m : Model} (hpred : m.predicates = [])
    {c d : ConstraintItem} (h : setCardFold c = [d])
    (hwf : WellFormed fullSig m) (hc : c ∈ m.constraints) :
    ∃ params, m.sigEnv fullSig d.name = some params ∧
      Forall2 (Expr.checkArg m.staticEnv) d.args params := by
  obtain ⟨cn, cargs, canns⟩ := c
  obtain ⟨ps, hsig, hca⟩ := hwf.constraintsChecked ⟨cn, cargs, canns⟩ hc
  unfold setCardFold at h
  split at h
  · rename_i sl x heqn heqa
    rw [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    have hcn : cn = Ident.mk "set_card" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.basic (.var (.par .setOfInt)),
        .basic (.var (.par .int))] := by
      have hstd := sigEnv_set_card hpred
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
      sigEnv_two_int hpred (Or.inl rfl), hca.2, checkArg_int_lit _, trivial⟩
  · rename_i hnone
    rw [List.cons.injEq] at h
    obtain ⟨rfl, -⟩ := h
    obtain ⟨params, hpsig, hpca⟩ := hwf.constraintsChecked ⟨cn, cargs, canns⟩ hc
    exact ⟨params, hpsig, hpca⟩

/-- The literal-result rewrite preserves static checking: the rewritten
    constraint is well-formed whenever the source one is. -/
theorem reifScalar_wf {m : Model} (hpred : m.predicates = [])
    {c d : ConstraintItem} (h : reifScalar c = some d)
    (hwf : WellFormed fullSig m) (hc : c ∈ m.constraints) :
    ∃ params, m.sigEnv fullSig d.name = some params ∧
      Forall2 (Expr.checkArg m.staticEnv) d.args params := by
  obtain ⟨cn, cargs, canns⟩ := c
  obtain ⟨ps, hsig, hca⟩ := hwf.constraintsChecked ⟨cn, cargs, canns⟩ hc
  unfold reifScalar at h
  split at h
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_eq" else "int_ne")
                    args := [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_eq_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
      have hstd := sigEnv_two_int_reif hpred (n := "int_eq_reif") (Or.inl rfl)
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inl rfl)), hca.1, hca.2.1, trivial⟩
    · simp only [if_true]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inl rfl), hca.1, hca.2.1, trivial⟩
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_ne" else "int_eq")
                    args := [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_ne_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
      have hstd := sigEnv_two_int_reif hpred (n := "int_ne_reif")
        (Or.inr (Or.inl rfl))
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inl rfl), hca.1, hca.2.1, trivial⟩
    · simp only [if_true]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inl rfl)), hca.1, hca.2.1, trivial⟩
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_le" else "int_lt")
                    args := if r then [a, b] else [b, a], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_le_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
      have hstd := sigEnv_two_int_reif hpred (n := "int_le_reif")
        (Or.inr (Or.inr (Or.inl rfl)))
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        hca.2.1, hca.1, trivial⟩
    · simp only [if_true]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inl rfl))),
        hca.1, hca.2.1, trivial⟩
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_lt" else "int_le")
                    args := if r then [a, b] else [b, a], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lt_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
      have hstd := sigEnv_two_int_reif hpred (n := "int_lt_reif")
        (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inl rfl))),
        hca.2.1, hca.1, trivial⟩
    · simp only [if_true]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        hca.1, hca.2.1, trivial⟩
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_le" else "int_lt")
                    args := if r then [b, a] else [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_ge_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
      have hstd := sigEnv_two_int_reif hpred (n := "int_ge_reif")
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        hca.1, hca.2.1, trivial⟩
    · simp only [if_true]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inl rfl))),
        hca.2.1, hca.1, trivial⟩
  · rename_i a b r heqn heqa
    have hd : d = { name := Ident.mk (if r then "int_lt" else "int_le")
                    args := if r then [b, a] else [a, b], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_gt_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.basic (.var (.par .int)), .basic (.var (.par .int)),
        .basic (.var (.par .bool))] := by
      have hstd := sigEnv_two_int_reif hpred (n := "int_gt_reif")
        (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl)))))
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    cases r
    · simp only [Bool.false_eq_true, if_false]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inl rfl))),
        hca.1, hca.2.1, trivial⟩
    · simp only [if_true]
      exact ⟨[.basic (.var (.par .int)), .basic (.var (.par .int))],
        sigEnv_two_int hpred (Or.inr (Or.inr (Or.inr (Or.inl rfl)))),
        hca.2.1, hca.1, trivial⟩
  · rename_i a b k heqn heqa
    have hd : d = { name := Ident.mk "int_lin_eq"
                    args := [a, b, k], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lin_eq_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int), .basic (.var (.par .bool))] := by
      have hstd := sigEnv_three_linear_reif hpred (n := "int_lin_eq_reif")
        (Or.inl rfl)
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    exact ⟨[.array .int (.par .int), .array .int (.var (.par .int)),
      .basic (.var (.par .int))],
      sigEnv_three_linear hpred (Or.inl rfl),
      hca.1, hca.2.1, checkArg_par_var hca.2.2.1, trivial⟩
  · rename_i a b k heqn heqa
    have hd : d = { name := Ident.mk "int_lin_le"
                    args := [a, b, k], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lin_le_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int), .basic (.var (.par .bool))] := by
      have hstd := sigEnv_three_linear_reif hpred (n := "int_lin_le_reif")
        (Or.inr (Or.inl rfl))
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    exact ⟨[.array .int (.par .int), .array .int (.var (.par .int)),
      .basic (.var (.par .int))],
      sigEnv_three_linear hpred (Or.inr (Or.inl rfl)),
      hca.1, hca.2.1, checkArg_par_var hca.2.2.1, trivial⟩
  · rename_i a b k heqn heqa
    have hd : d = { name := Ident.mk "int_lin_ne"
                    args := [a, b, k], anns := [] } :=
      (Option.some.inj h).symm
    subst hd
    have hcn : cn = Ident.mk "int_lin_ne_reif" := Ident.eq_of_name_eq heqn
    subst hcn
    subst heqa
    have hps : ps = [.array .int (.par .int), .array .int (.var (.par .int)),
        .basic (.par .int), .basic (.var (.par .bool))] := by
      have hstd := sigEnv_three_linear_reif hpred (n := "int_lin_ne_reif")
        (Or.inr (Or.inr rfl))
      rw [hstd] at hsig
      exact (Option.some.inj hsig).symm
    subst hps
    simp [Forall2] at hca
    exact ⟨[.array .int (.par .int), .array .int (.var (.par .int)),
      .basic (.var (.par .int))],
      sigEnv_three_linear hpred (Or.inr (Or.inr rfl)),
      hca.1, hca.2.1, checkArg_par_var hca.2.2.1, trivial⟩
  · cases h

theorem wf_reifFold {m : Model} (hwf : WellFormed fullSig m)
    (hpred : m.predicates = []) :
    WellFormed fullSig (foldReifModel m) := by
  have hsig : (foldReifModel m).sigEnv fullSig = m.sigEnv fullSig := rfl
  have hstat : (foldReifModel m).staticEnv = m.staticEnv := rfl
  refine
    { predNamesUnique := ?_
      valueNamesUnique := ?_
      predParamsUnique := hwf.predParamsUnique
      parameterTypes := hwf.parameterTypes
      variableArrayLengths := hwf.variableArrayLengths
      variableInitializers := hwf.variableInitializers
      objectiveType := hwf.objectiveType
      constraintsChecked := ?_ }
  · simpa [foldReifModel, hpred] using hwf.predNamesUnique
  · simpa [foldReifModel] using hwf.valueNamesUnique
  · intro c' hc'
    obtain ⟨c, hc, hfold⟩ := List.mem_flatMap.mp hc'
    unfold reifFold at hfold
    split at hfold
    · rename_i d hsome
      rw [List.mem_singleton] at hfold
      rw [hfold]
      obtain ⟨params, hpsig, hpca⟩ := reifScalar_wf hpred hsome hwf hc
      refine ⟨params, ?_, ?_⟩
      · rw [hsig]; exact hpsig
      · rw [hstat]; exact hpca
    · rename_i hnone
      rw [List.mem_singleton] at hfold
      rw [hfold]
      obtain ⟨params, hpsig, hpca⟩ := hwf.constraintsChecked c hc
      refine ⟨params, ?_, ?_⟩
      · rw [hsig]; exact hpsig
      · rw [hstat]; exact hpca

theorem wf_setCard {m : Model} (hwf : WellFormed fullSig m)
    (hpred : m.predicates = []) :
    WellFormed fullSig (foldSetCardModel m) := by
  refine
    { predNamesUnique := ?_
      valueNamesUnique := hwf.valueNamesUnique
      predParamsUnique := hwf.predParamsUnique
      parameterTypes := hwf.parameterTypes
      variableArrayLengths := hwf.variableArrayLengths
      variableInitializers := hwf.variableInitializers
      objectiveType := hwf.objectiveType
      constraintsChecked := ?_ }
  · simpa [foldSetCardModel, hpred] using hwf.predNamesUnique
  · intro c' hc'
    obtain ⟨c, hc, hfold⟩ := List.mem_flatMap.mp hc'
    have hsingle : setCardFold c = [c'] := setCard_eq_of_mem hfold
    obtain ⟨params, hpsig, hpca⟩ := setCard_wf hpred hsingle hwf hc
    exact ⟨params, hpsig, hpca⟩

theorem wf_fold {m : Model} (hwf : WellFormed fullSig m)
    (hpred : m.predicates = []) :
    WellFormed fullSig (foldLiteralsModel m) := by
  apply wf_reifFold
  · apply wf_groundFold
    · exact wf_setCard hwf hpred
    · simpa [foldSetCardModel] using hpred
  · simpa [foldGroundModel, foldSetCardModel] using hpred

/-! ## Composition -/

theorem foldLiterals_covers {m : Model} {s : Store}
    (h : ∀ c ∈ m.constraints, c.Holds fullInterp s) :
    ∀ c ∈ (foldLiteralsModel m).constraints, c.Holds fullInterp s :=
  foldReif_covers (foldGround_covers (foldSetCard_covers h))

theorem foldLiterals_exact {m : Model} {s : Store}
    (h : ∀ c ∈ (foldLiteralsModel m).constraints, c.Holds fullInterp s) :
    ∀ c ∈ m.constraints, c.Holds fullInterp s :=
  foldSetCard_exact (foldGround_exact (foldReif_exact h))

end LeanFzn.Compiler
