/-
File: LeanFzn/Compiler/Proofs/Bounds.lean

Purpose:
  Correctness of the U1 bound-derivation front end
  (`Compiler/Bounds.lean`, PLAN.md task U1).

  The recognizer `deriveCerts` is untrusted.  The checker `checkCerts`
  replays the proposed certificates from the model's declared bounds;
  `checkCerts_sound` shows that every checked entry really holds of
  every store that satisfies the source model.  Consequently
  `tightenModel` only narrows `var int` declarations to intervals that
  contain the variable in every solution:

  * `boundsModel_sound` (coverage): a store satisfying the source model
    satisfies the tightened model;
  * `boundsModel_exact` (exactness): a store satisfying the tightened
    model satisfies the source model (the constraints are unchanged and
    the original domains are wider);
  * `wf_bounds` (well-formedness): tightening keeps static correctness.

  `Proofs/Normalize` inserts `boundsModel` between the source
  normalization and `compileModel`, threading these theorems through
  `compileFull_covers` and `compileFull_exact`.

Dependencies:
  - LeanFzn.Compiler.Bounds (the executable pass).
  - LeanFzn.Compiler.Proofs.LiteralFold (`Holds` inversions and the
    standard-predicate unfolding used below).
-/

import LeanFzn.Compiler.Bounds
import LeanFzn.Compiler.Proofs.LiteralFold

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Globals

/-! ## Semantic reading of the checked environment -/

/-- A checked entry is sound for a store when the store's value lies in
    the entry's interval.  Booleans are read as 0/1. -/
def BoundEntry.Sound (store : Store) (e : BoundEntry) : Prop :=
  match e.sort with
  | .int =>
      ∃ i : Int, store e.var = some (.int i) ∧ e.lo ≤ i ∧ i ≤ e.hi
  | .bool =>
      ∃ b : Bool, store e.var = some (.bool b) ∧
        e.lo ≤ (if b then (1 : Int) else 0) ∧
        (if b then (1 : Int) else 0) ≤ e.hi

/-- Every entry of an environment is sound. -/
def EnvSound (store : Store) (env : List BoundEntry) : Prop :=
  ∀ e ∈ env, e.Sound store

theorem envSound_append {store : Store} {env₁ env₂ : List BoundEntry}
    (h₁ : EnvSound store env₁) (h₂ : EnvSound store env₂) :
    EnvSound store (env₁ ++ env₂) := by
  intro e he
  rw [List.mem_append] at he
  rcases he with he | he
  · exact h₁ e he
  · exact h₂ e he

theorem envSound_singleton {store : Store} {e : BoundEntry}
    (h : e.Sound store) : EnvSound store [e] := by
  intro e' he'
  rw [List.mem_singleton] at he'
  subst he'
  exact h

theorem lookupEntry_mem {x : Ident} {env : List BoundEntry} {e : BoundEntry}
    (h : lookupEntry x env = some e) : e ∈ env := by
  induction env with
  | nil => simp [lookupEntry] at h
  | cons e' es ih =>
      simp only [lookupEntry] at h
      split at h
      · rename_i hname
        rw [Option.some.inj h]
        exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (ih h)

theorem lookupEntry_name {x : Ident} {env : List BoundEntry} {e : BoundEntry}
    (h : lookupEntry x env = some e) : e.var.name = x.name := by
  induction env with
  | nil => simp [lookupEntry] at h
  | cons e' es ih =>
      simp only [lookupEntry] at h
      split at h
      · rename_i hname
        rw [← Option.some.inj h]
        exact hname
      · exact ih h

theorem envSound_lookup {store : Store} {env : List BoundEntry}
    (henv : EnvSound store env) {x : Ident} {e : BoundEntry}
    (h : lookupEntry x env = some e) : e.Sound store :=
  henv e (lookupEntry_mem h)

/-- Saving the interval of an integer lookup. -/
theorem int_sound_of_lookup {store : Store} {env : List BoundEntry}
    (henv : EnvSound store env) {x : Ident} {e : BoundEntry}
    (h : lookupEntry x env = some e) (hs : e.sort = .int) :
    ∃ i : Int, store x = some (.int i) ∧ e.lo ≤ i ∧ i ≤ e.hi := by
  have hsnd := envSound_lookup henv h
  unfold BoundEntry.Sound at hsnd
  simp only [hs] at hsnd
  have hvar : e.var = x := Ident.eq_of_name_eq (lookupEntry_name h)
  rw [hvar] at hsnd
  exact hsnd

/-- Saving the value of a Boolean lookup. -/
theorem bool_sound_of_lookup {store : Store} {env : List BoundEntry}
    (henv : EnvSound store env) {x : Ident} {e : BoundEntry}
    (h : lookupEntry x env = some e) (hs : e.sort = .bool) :
    ∃ b : Bool, store x = some (.bool b) ∧
      e.lo ≤ (if b then (1 : Int) else 0) ∧
      (if b then (1 : Int) else 0) ≤ e.hi := by
  have hsnd := envSound_lookup henv h
  unfold BoundEntry.Sound at hsnd
  simp only [hs] at hsnd
  have hvar : e.var = x := Ident.eq_of_name_eq (lookupEntry_name h)
  rw [hvar] at hsnd
  exact hsnd

/-! ## Declared bounds -/

/-- The variable-domain part of `SatisfiesDyn`. -/
def VarDomains (store : Store) (m : Model) : Prop :=
  ∀ d ∈ m.variables, match d with
    | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
    | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
        vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v

/-- The domain condition of one variable declaration. -/
def DeclDomain (store : Store) : VarDeclItem → Prop
  | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
  | .array ty n _ _ => ∃ vs, store n = some (.array vs) ∧
      vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v

theorem varDomains_iff {store : Store} {m : Model} :
    VarDomains store m ↔ ∀ d ∈ m.variables, DeclDomain store d :=
  Iff.rfl

theorem nativeEnv_sound {store : Store} {m : Model}
    (hvar : VarDomains store m) : EnvSound store (nativeEnv m) := by
  intro e he
  unfold nativeEnv at he
  obtain ⟨d, hd, hmap⟩ := List.mem_filterMap.mp he
  have hvd := hvar d hd
  cases d with
  | basic ty n anns v =>
      cases ty with
      | par t =>
          cases t with
          | bool =>
              simp only [nativeEntry, Option.some.injEq] at hmap
              subst hmap
              obtain ⟨val, hval, hcont⟩ := hvd
              cases val with
              | bool b => exact ⟨b, hval, by cases b <;> simp, by cases b <;> simp⟩
              | int i => simp [BasicVarType.contains] at hcont
              | setOfInt s => simp [BasicVarType.contains] at hcont
              | array vs => simp [BasicVarType.contains] at hcont
          | int => simp [nativeEntry] at hmap
          | setOfInt => simp [nativeEntry] at hmap
      | intRange lo hi =>
          simp only [nativeEntry, Option.some.injEq] at hmap
          subst hmap
          obtain ⟨val, hval, hcont⟩ := hvd
          cases val with
          | bool b => simp [BasicVarType.contains] at hcont
          | int i =>
              simp only [BasicVarType.contains] at hcont
              exact ⟨i, hval, hcont.1, hcont.2⟩
          | setOfInt s => simp [BasicVarType.contains] at hcont
          | array vs => simp [BasicVarType.contains] at hcont
      | intSet xs => simp [nativeEntry] at hmap
      | setOfIntRange lo hi => simp [nativeEntry] at hmap
      | setOfIntSet xs => simp [nativeEntry] at hmap
  | array ty n anns es => simp [nativeEntry] at hmap

/-! ## Value and array-evaluation helpers -/

theorem bool_clause_not_globals : "bool_clause" ∉ globalsNames := by decide

theorem stdInterp_bool_clause_apply (args : List Value) :
    stdInterp (Ident.mk "bool_clause") args =
      match args with
      | [.array xs, .array ys] =>
          ((xs.any (fun x => x.eqB (.bool true))) ||
            (ys.any (fun y => y.eqB (.bool false)))) = true
      | _ => False := rfl

theorem stdInterp_int_eq_reif_apply (args : List Value) :
    stdInterp (Ident.mk "int_eq_reif") args =
      match args with
      | [.int a, .int b, .bool r] =>
          (r = true ∧ a = b) ∨ (r = false ∧ a ≠ b)
      | _ => False := rfl

theorem eqB_bool_true_iff (v : Value) :
    v.eqB (.bool true) = true ↔ v = .bool true := by
  cases v <;> simp [Value.eqB]

theorem eqB_bool_false_iff (v : Value) :
    v.eqB (.bool false) = true ↔ v = .bool false := by
  cases v <;> simp [Value.eqB]

theorem eval_array_many {s : Store} {es : ArrayLiteral} {arg : Value}
    (h : Expr.eval s (.array es) = some arg) :
    ∃ vs, es.mapM (BasicExpr.eval s) = some vs ∧ arg = .array vs := by
  unfold Expr.eval at h
  obtain ⟨vs, hvs, harg⟩ := Option.map_eq_some_iff.mp h
  exact ⟨vs, hvs, harg.symm⟩

theorem mapM_basic_singleton {s : Store} {e : BasicExpr} {vs : List Value}
    (h : [e].mapM (BasicExpr.eval s) = some vs) :
    ∃ v, e.eval s = some v ∧ vs = [v] := by
  rw [List.mapM_cons, List.mapM_nil] at h
  cases he : BasicExpr.eval s e with
  | none => rw [he] at h; cases h
  | some v =>
      rw [he] at h
      simp at h
      exact ⟨v, rfl, h.symm⟩

theorem mapM_basic_pair {s : Store} {a b : BasicExpr} {vs : List Value}
    (h : [a, b].mapM (BasicExpr.eval s) = some vs) :
    ∃ va vb, a.eval s = some va ∧ b.eval s = some vb ∧ vs = [va, vb] := by
  rw [List.mapM_cons, List.mapM_cons, List.mapM_nil] at h
  cases ha : BasicExpr.eval s a with
  | none => rw [ha] at h; cases h
  | some va =>
      rw [ha] at h
      cases hb : BasicExpr.eval s b with
      | none => rw [hb] at h; cases h
      | some vb =>
          rw [hb] at h
          simp at h
          exact ⟨va, vb, rfl, rfl, h.symm⟩

theorem eval_array_singleton {s : Store} {e : BasicExpr} {arg : Value}
    (h : Expr.eval s (.array [e]) = some arg) :
    ∃ v, e.eval s = some v ∧ arg = .array [v] := by
  obtain ⟨vs, hvs, rfl⟩ := eval_array_many h
  obtain ⟨v, hv, rfl⟩ := mapM_basic_singleton hvs
  exact ⟨v, hv, rfl⟩

theorem eval_array_pair {s : Store} {a b : BasicExpr} {arg : Value}
    (h : Expr.eval s (.array [a, b]) = some arg) :
    ∃ va vb, a.eval s = some va ∧ b.eval s = some vb ∧
      arg = .array [va, vb] := by
  obtain ⟨vs, hvs, rfl⟩ := eval_array_many h
  obtain ⟨va, vb, ha, hb, rfl⟩ := mapM_basic_pair hvs
  exact ⟨va, vb, ha, hb, rfl⟩

/-! ## Inverting the concrete constraint shapes -/

theorem clause1_disj {vr vc : Value}
    (h : (vr.eqB (.bool true) || vc.eqB (.bool false)) = true) :
    vr = .bool true ∨ vc = .bool false := by
  rw [Bool.or_eq_true] at h
  exact h.imp (eqB_bool_true_iff vr).mp (eqB_bool_false_iff vc).mp

theorem clause2_disj {vc vr : Value}
    (h : (vc.eqB (.bool true) || vr.eqB (.bool true)) = true) :
    vc = .bool true ∨ vr = .bool true := by
  rw [Bool.or_eq_true] at h
  exact h.imp (eqB_bool_true_iff vc).mp (eqB_bool_true_iff vr).mp

theorem clause1Neg_disj {vc vr : Value}
    (h : (vc.eqB (.bool false) || vr.eqB (.bool false)) = true) :
    vc = .bool false ∨ vr = .bool false := by
  rw [Bool.or_eq_true] at h
  exact h.imp (eqB_bool_false_iff vc).mp (eqB_bool_false_iff vr).mp

theorem clause2Neg_disj {vc vr : Value}
    (h : (vc.eqB (.bool true) || vr.eqB (.bool false)) = true) :
    vc = .bool true ∨ vr = .bool false := by
  rw [Bool.or_eq_true] at h
  exact h.imp (eqB_bool_true_iff vc).mp (eqB_bool_false_iff vr).mp

/-- `bool_clause([r],[c])`: `r` is true or `c` is false. -/
theorem holds_clause1 {s : Store} {con : ConstraintItem} {r cc : Ident}
    (hname : con.name.name = "bool_clause")
    (hargs : con.args = [.array [.ident r], .array [.ident cc]])
    (h : con.Holds fullInterp s) :
    ∃ vr vc, s r = some vr ∧ s cc = some vc ∧
      (vr = .bool true ∨ vc = .bool false) := by
  obtain ⟨vs, ws, hvs, hws, hany⟩ := holds_bool_clause hname hargs h
  obtain ⟨vr, hvr, rfl⟩ := mapM_basic_singleton hvs
  obtain ⟨vc, hvc, rfl⟩ := mapM_basic_singleton hws
  simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
  exact ⟨vr, vc, hvr, hvc, clause1_disj hany⟩

/-- `bool_clause([c,r],[])`: `c` is true or `r` is true. -/
theorem holds_clause2 {s : Store} {con : ConstraintItem} {cc r : Ident}
    (hname : con.name.name = "bool_clause")
    (hargs : con.args = [.array [.ident cc, .ident r], .array []])
    (h : con.Holds fullInterp s) :
    ∃ vc vr, s cc = some vc ∧ s r = some vr ∧
      (vc = .bool true ∨ vr = .bool true) := by
  obtain ⟨vs, ws, hvs, hws, hany⟩ := holds_bool_clause hname hargs h
  obtain ⟨vc, vr, hvc, hvr, rfl⟩ := mapM_basic_pair hvs
  have hws' : ws = [] := by simpa using hws.symm
  subst hws'
  simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
  exact ⟨vc, vr, hvc, hvr, clause2_disj hany⟩

/-- `bool_clause([],[c,r])`: `c` is false or `r` is false. -/
theorem holds_clause1Neg {s : Store} {con : ConstraintItem} {cc r : Ident}
    (hname : con.name.name = "bool_clause")
    (hargs : con.args = [.array [], .array [.ident cc, .ident r]])
    (h : con.Holds fullInterp s) :
    ∃ vc vr, s cc = some vc ∧ s r = some vr ∧
      (vc = .bool false ∨ vr = .bool false) := by
  obtain ⟨vs, ws, hvs, hws, hany⟩ := holds_bool_clause hname hargs h
  have hvs' : vs = [] := by simpa using hvs.symm
  subst hvs'
  obtain ⟨vc, vr, hvc, hvr, rfl⟩ := mapM_basic_pair hws
  simp only [List.any_cons, List.any_nil, Bool.false_or, Bool.or_false] at hany
  exact ⟨vc, vr, hvc, hvr, clause1Neg_disj hany⟩

/-- `bool_clause([c],[r])`: `c` is true or `r` is false. -/
theorem holds_clause2Neg {s : Store} {con : ConstraintItem} {cc r : Ident}
    (hname : con.name.name = "bool_clause")
    (hargs : con.args = [.array [.ident cc], .array [.ident r]])
    (h : con.Holds fullInterp s) :
    ∃ vc vr, s cc = some vc ∧ s r = some vr ∧
      (vc = .bool true ∨ vr = .bool false) := by
  obtain ⟨vs, ws, hvs, hws, hany⟩ := holds_bool_clause hname hargs h
  obtain ⟨vc, hvc, rfl⟩ := mapM_basic_singleton hvs
  obtain ⟨vr, hvr, rfl⟩ := mapM_basic_singleton hws
  simp only [List.any_cons, List.any_nil, Bool.or_false] at hany
  exact ⟨vc, vr, hvc, hvr, clause2Neg_disj hany⟩

/-- `int_eq_reif(y, a, r)`, with the semantic table. -/
theorem holds_int_eq_reif_val {s : Store} {con : ConstraintItem} {y : Ident}
    {a : BasicExpr} {r : Ident}
    (hname : con.name.name = "int_eq_reif")
    (hargs : con.args = [.basic (.ident y), .basic a, .basic (.ident r)])
    (h : con.Holds fullInterp s) :
    ∃ i j : Int, s y = some (.int i) ∧ a.eval s = some (.int j) ∧
      ∃ b : Bool, s r = some (.bool b) ∧
        ((b = true ∧ i = j) ∨ (b = false ∧ i ≠ j)) := by
  have hc : con = ConstraintItem.mk (Ident.mk "int_eq_reif")
      [.basic (.ident y), .basic a, .basic (.ident r)] con.anns := by
    cases con with
    | mk name args anns =>
      simp only at hname hargs
      rw [Ident.eq_of_name_eq hname, hargs]
  rw [hc] at h
  rw [holds_three_iff] at h
  obtain ⟨vy, va, vr, hy, ha, hr, hp⟩ := h
  rw [fullInterp_std_of_not_mem int_eq_reif_not_globals,
    stdInterp_int_eq_reif_apply] at hp
  cases vy with
  | int i =>
      cases va with
      | int j =>
          cases vr with
          | bool b =>
              simp only at hp
              exact ⟨i, j, hy, ha, b, hr, hp⟩
          | int k => simp at hp
          | setOfInt sv => simp at hp
          | array vs => simp at hp
      | bool b => simp at hp
      | setOfInt sv => simp at hp
      | array vs => simp at hp
  | bool b => simp at hp
  | setOfInt sv => simp at hp
  | array vs => simp at hp

/-- The `true` case of `int_eq_reif`: both sides are the same integer. -/
theorem holds_int_eq_reif_true {s : Store} {con : ConstraintItem} {y : Ident}
    {a : BasicExpr} {r : Ident}
    (hname : con.name.name = "int_eq_reif")
    (hargs : con.args = [.basic (.ident y), .basic a, .basic (.ident r)])
    (h : con.Holds fullInterp s)
    (hr : s r = some (.bool true)) :
    ∃ i : Int, s y = some (.int i) ∧ a.eval s = some (.int i) := by
  obtain ⟨i, j, hy, ha, b, hb, hdisj⟩ :=
    holds_int_eq_reif_val hname hargs h
  rw [hr] at hb
  have hbtrue : b = true := (Value.bool.inj (Option.some.inj hb)).symm
  rcases hdisj with ⟨-, hij⟩ | ⟨hbf, -⟩
  · subst hij
    exact ⟨i, hy, ha⟩
  · rw [hbtrue] at hbf
    cases hbf

/-! ## Pair sums and their checked bounds -/

/-- The value of a parsed linear row under a store. -/
def pairSum (s : Store) : List (Int × Ident) → Option Int
  | [] => some 0
  | (c, x) :: rest =>
      match s x with
      | some (.int i) =>
          match pairSum s rest with
          | some t => some (c * i + t)
          | none => none
      | _ => none

theorem pairSum_cons_inv {s : Store} {c : Int} {x : Ident}
    {rest : List (Int × Ident)} {t : Int}
    (h : pairSum s ((c, x) :: rest) = some t) :
    ∃ i u, s x = some (.int i) ∧ pairSum s rest = some u ∧
      t = c * i + u := by
  unfold pairSum at h
  split at h
  · rename_i i hi
    split at h
    · rename_i u hu
      exact ⟨i, u, hi, hu, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem pairSum_append {s : Store} :
    ∀ (l₁ l₂ : List (Int × Ident)) {a b : Int},
      pairSum s l₁ = some a → pairSum s l₂ = some b →
      pairSum s (l₁ ++ l₂) = some (a + b) := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ a b ha hb
      have ha0 : a = 0 := (Option.some.inj ha).symm
      subst ha0
      simpa using hb
  | cons p rest ih =>
      intro l₂ a b ha hb
      obtain ⟨c, x⟩ := p
      obtain ⟨i, u, hx, hu, ht⟩ := pairSum_cons_inv ha
      have hrec := ih l₂ hu hb
      rw [List.cons_append]
      unfold pairSum
      rw [hx, hrec, ht]
      rw [Int.add_assoc]

theorem pairSum_append_inv {s : Store} :
    ∀ (l₁ l₂ : List (Int × Ident)) {b : Int},
      pairSum s (l₁ ++ l₂) = some b →
      ∃ a c, pairSum s l₁ = some a ∧ pairSum s l₂ = some c ∧
        b = a + c := by
  intro l₁
  induction l₁ with
  | nil =>
      intro l₂ b h
      exact ⟨0, b, rfl, h, by omega⟩
  | cons p rest ih =>
      intro l₂ b h
      obtain ⟨c, x⟩ := p
      rw [List.cons_append] at h
      obtain ⟨i, u, hx, hu, hb⟩ := pairSum_cons_inv h
      obtain ⟨a0, c0, ha0, hc0, hu'⟩ := ih l₂ hu
      refine ⟨c * i + a0, c0, ?_, hc0, ?_⟩
      · unfold pairSum
        rw [hx, ha0]
      · rw [hb, hu']
        omega

theorem pairSum_isInt {s : Store} {ps : List (Int × Ident)} {t : Int}
    (h : pairSum s ps = some t) {p : Int × Ident} (hp : p ∈ ps) :
    ∃ i, s p.2 = some (.int i) := by
  induction ps generalizing t with
  | nil => cases hp
  | cons q rest ih =>
      obtain ⟨c, x⟩ := q
      rw [List.mem_cons] at hp
      rcases hp with rfl | hp
      · obtain ⟨i, -, hx, -, -⟩ := pairSum_cons_inv h
        exact ⟨i, hx⟩
      · obtain ⟨i, u, hx, hu, ht⟩ := pairSum_cons_inv h
        exact ih hu hp

/-- The parsed rows have the shapes the checker expects. -/
theorem pairsOfRow_spec {cs xs : ArrayLiteral} {ps : List (Int × Ident)}
    (h : pairsOfRow cs xs = some ps) :
    cs = ps.map (fun p => BasicExpr.lit (.int p.1)) ∧
    xs = ps.map (fun p => BasicExpr.ident p.2) := by
  induction cs generalizing xs ps with
  | nil =>
      cases xs <;> simp [pairsOfRow] at h
      subst h
      simp
  | cons c cs ih =>
      cases c with
      | lit l =>
          cases l with
          | int k =>
              cases xs with
              | nil => simp [pairsOfRow] at h
              | cons x xs =>
                  cases x with
                  | ident y =>
                      simp only [pairsOfRow, Option.map_eq_some_iff] at h
                      obtain ⟨ps0, h0, rfl⟩ := h
                      obtain ⟨hcs, hxs⟩ := ih h0
                      simp [hcs, hxs]
                  | lit l => simp [pairsOfRow] at h
          | bool b => simp [pairsOfRow] at h
          | set s => simp [pairsOfRow] at h
      | ident y => simp [pairsOfRow] at h

/-- The first list of a split, reconstructed. -/
theorem splitPair_spec {x : Ident} {ps : List (Int × Ident)}
    {pre : List (Int × Ident)} {cj : Int} {post : List (Int × Ident)}
    (h : splitPair x ps = some (pre, cj, post)) :
    ps = pre ++ (cj, x) :: post := by
  induction ps generalizing pre cj post with
  | nil => simp [splitPair] at h
  | cons p ps ih =>
      obtain ⟨c, y⟩ := p
      unfold splitPair at h
      split at h
      · rename_i hname
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        rw [Ident.eq_of_name_eq hname]
        rfl
      · rename_i hname
        obtain ⟨t, ht, heq⟩ := Option.map_eq_some_iff.mp h
        obtain ⟨pre0, cj0, post0⟩ := t
        simp only [Prod.mk.injEq] at heq
        obtain ⟨rfl, rfl, rfl⟩ := heq
        have hrec := ih ht
        rw [hrec]
        rfl

theorem mapM_lit_int (s : Store) (ps : List (Int × Ident)) :
    (ps.map (fun p => BasicExpr.lit (.int p.1))).mapM (BasicExpr.eval s) =
      some (ps.map (fun p => Value.int p.1)) := by
  induction ps with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨c, x⟩ := p
      simp only [List.map_cons, List.mapM_cons, BasicExpr.eval,
        BasicLiteral.denote, ih]
      rfl

/-- The evaluated variable list of a parsed row, seen as a dot product. -/
theorem dotProduct_mapM_pairs {s : Store} {ps : List (Int × Ident)}
    {vs : List Value} {b : Int}
    (hmap : (ps.map (fun p => BasicExpr.ident p.2)).mapM
      (BasicExpr.eval s) = some vs)
    (hdot : dotProduct (ps.map (fun p => Value.int p.1)) vs = some b) :
    pairSum s ps = some b := by
  induction ps generalizing vs b with
  | nil =>
      simp only [List.map, List.mapM_nil] at hmap
      have hvs : vs = [] := by simpa using hmap.symm
      subst hvs
      simpa [pairSum, dotProduct] using hdot
  | cons p rest ih =>
      obtain ⟨c, x⟩ := p
      rw [List.map_cons, List.mapM_cons] at hmap
      obtain ⟨v, hv, hmap1⟩ := Option.bind_eq_some_iff.mp hmap
      obtain ⟨vs', hvs', hmap2⟩ := Option.bind_eq_some_iff.mp hmap1
      have hvs : vs = v :: vs' := (Option.some.inj hmap2).symm
      subst hvs
      cases v with
      | int i =>
          simp only [List.map_cons] at hdot
          rw [dotProduct] at hdot
          split at hdot
          · rename_i b' hd
            have hb : b = c * i + b' := (Option.some.inj hdot).symm
            have hrec := ih hvs' hd
            have hv' : s x = some (.int i) := hv
            unfold pairSum
            rw [hv', hrec, hb]
          · cases hdot
      | bool bv => simp [dotProduct] at hdot
      | setOfInt sv => simp [dotProduct] at hdot
      | array av => simp [dotProduct] at hdot

theorem termLo?_spec {env : List BoundEntry} {p : Int × Ident} {a : Int}
    (h : termLo? env p = some a) :
    ∃ e, lookupEntry p.2 env = some e ∧ e.sort = .int ∧
      a = (if 0 ≤ p.1 then p.1 * e.lo else p.1 * e.hi) := by
  unfold termLo? at h
  split at h
  · rename_i e he
    split at h
    · rename_i hs
      exact ⟨e, he, hs, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem termHi?_spec {env : List BoundEntry} {p : Int × Ident} {a : Int}
    (h : termHi? env p = some a) :
    ∃ e, lookupEntry p.2 env = some e ∧ e.sort = .int ∧
      a = (if 0 ≤ p.1 then p.1 * e.hi else p.1 * e.lo) := by
  unfold termHi? at h
  split at h
  · rename_i e he
    split at h
    · rename_i hs
      exact ⟨e, he, hs, (Option.some.inj h).symm⟩
    · cases h
  · cases h

theorem pairSum_le_of_sumLo {s : Store} {env : List BoundEntry}
    (henv : EnvSound s env) :
    ∀ (ps : List (Int × Ident)) {sl : Int}, sumLo? env ps = some sl →
      ∃ t, pairSum s ps = some t ∧ sl ≤ t := by
  intro ps
  induction ps with
  | nil =>
      intro sl h
      unfold sumLo? at h
      have hsl : sl = 0 := (Option.some.inj h).symm
      subst hsl
      exact ⟨0, rfl, Int.le_refl 0⟩
  | cons p rest ih =>
      intro sl h
      unfold sumLo? at h
      obtain ⟨a, ha, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, hab⟩ := Option.bind_eq_some_iff.mp hrest
      have hsl : sl = a + b := (Option.some.inj hab).symm
      obtain ⟨e, he, hs, hae⟩ := termLo?_spec ha
      obtain ⟨i, hip, hlo, hhi⟩ := int_sound_of_lookup henv he hs
      have hterm : a ≤ p.1 * i := by
        rw [hae]
        split
        · rename_i hc
          exact Int.mul_le_mul_of_nonneg_left hlo hc
        · rename_i hc
          have hc' : p.1 ≤ 0 := by omega
          exact Int.mul_le_mul_of_nonpos_left (a := p.1) (b := e.hi) (c := i)
            hc' hhi
      obtain ⟨t, ht, hbt⟩ := ih hb
      refine ⟨p.1 * i + t, ?_, ?_⟩
      · unfold pairSum
        rw [hip, ht]
      · rw [hsl]
        exact Int.add_le_add hterm hbt

theorem pairSum_ge_of_sumHi {s : Store} {env : List BoundEntry}
    (henv : EnvSound s env) :
    ∀ (ps : List (Int × Ident)) {sh : Int}, sumHi? env ps = some sh →
      ∃ t, pairSum s ps = some t ∧ t ≤ sh := by
  intro ps
  induction ps with
  | nil =>
      intro sh h
      unfold sumHi? at h
      have hsh : sh = 0 := (Option.some.inj h).symm
      subst hsh
      exact ⟨0, rfl, Int.le_refl 0⟩
  | cons p rest ih =>
      intro sh h
      unfold sumHi? at h
      obtain ⟨a, ha, hrest⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, hb, hab⟩ := Option.bind_eq_some_iff.mp hrest
      have hsh : sh = a + b := (Option.some.inj hab).symm
      obtain ⟨e, he, hs, hae⟩ := termHi?_spec ha
      obtain ⟨i, hip, hlo, hhi⟩ := int_sound_of_lookup henv he hs
      have hterm : p.1 * i ≤ a := by
        rw [hae]
        split
        · rename_i hc
          exact Int.mul_le_mul_of_nonneg_left hhi hc
        · rename_i hc
          have hc' : p.1 ≤ 0 := by omega
          exact Int.mul_le_mul_of_nonpos_left (a := p.1) (b := i) (c := e.lo)
            hc' hlo
      obtain ⟨t, ht, hbt⟩ := ih hb
      refine ⟨p.1 * i + t, ?_, ?_⟩
      · unfold pairSum
        rw [hip, ht]
      · rw [hsh]
        exact Int.add_le_add hterm hbt

/-! ## Shape specifications of the recognizer helpers -/

theorem anchorOf_spec {b : BasicExpr} {a : BoundAnchor}
    (h : anchorOf b = some a) :
    (∃ k : Int, b = .lit (.int k) ∧ a = .lit k) ∨
    (∃ x : Ident, b = .ident x ∧ a = .var x) := by
  cases b with
  | lit l =>
      cases l with
      | int k =>
          simp only [anchorOf, Option.some.injEq] at h
          subst h
          exact Or.inl ⟨k, rfl, rfl⟩
      | bool bb => simp [anchorOf] at h
      | set ss => simp [anchorOf] at h
  | ident x =>
      simp only [anchorOf, Option.some.injEq] at h
      subst h
      exact Or.inr ⟨x, rfl, rfl⟩

theorem anchorBounds_spec {env : List BoundEntry} {a : BoundAnchor}
    {lo hi : Int} (h : anchorBounds env a = some (lo, hi)) :
    (a = .lit lo ∧ lo = hi) ∨
    ∃ e : BoundEntry, a = .var e.var ∧ lookupEntry e.var env = some e ∧
      e.sort = .int ∧ e.lo = lo ∧ e.hi = hi := by
  cases a with
  | lit k =>
      simp only [anchorBounds, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl ⟨rfl, rfl⟩
  | var x =>
      simp only [anchorBounds] at h
      split at h
      · rename_i e he
        split at h
        · rename_i hs
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨hl, hh⟩ := h
          have hvar : e.var = x := Ident.eq_of_name_eq (lookupEntry_name he)
          refine Or.inr ⟨e, ?_, ?_, hs, hl, hh⟩
          · rw [hvar]
          · rw [hvar]
            exact he
        · cases h
      · cases h

theorem eqReifRow_spec {c : ConstraintItem} {x : Ident} {r : Ident}
    {a : BoundAnchor} (h : eqReifRow c x = some (r, a)) :
    c.name.name = "int_eq_reif" ∧
    ∃ (y : Ident) (b : BasicExpr),
      c.args = [.basic (.ident y), .basic b, .basic (.ident r)] ∧
      y.name = x.name ∧ anchorOf b = some a := by
  unfold eqReifRow at h
  split at h
  · rename_i y b rr hname hargs
    split at h
    · rename_i hyname
      obtain ⟨a0, ha0, hpair⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at hpair
      obtain ⟨hr, ha⟩ := hpair
      subst hr
      subst ha
      exact ⟨hname, y, b, hargs, hyname, ha0⟩
    · cases h
  · cases h

theorem clauseSplit1_spec {c : ConstraintItem} {r cc : Ident}
    (h : clauseSplit1 c = some (r, cc)) :
    c.name.name = "bool_clause" ∧
      c.args = [.array [.ident r], .array [.ident cc]] := by
  unfold clauseSplit1 at h
  split at h
  · rename_i hname hargs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hname, hargs⟩
  · cases h

theorem clauseSplit2_spec {c : ConstraintItem} {cc r : Ident}
    (h : clauseSplit2 c = some (cc, r)) :
    c.name.name = "bool_clause" ∧
      c.args = [.array [.ident cc, .ident r], .array []] := by
  unfold clauseSplit2 at h
  split at h
  · rename_i hname hargs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hname, hargs⟩
  · cases h

theorem clauseSplit1Neg_spec {c : ConstraintItem} {cc r : Ident}
    (h : clauseSplit1Neg c = some (cc, r)) :
    c.name.name = "bool_clause" ∧
      c.args = [.array [], .array [.ident cc, .ident r]] := by
  unfold clauseSplit1Neg at h
  split at h
  · rename_i hname hargs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hname, hargs⟩
  · cases h

theorem clauseSplit2Neg_spec {c : ConstraintItem} {cc r : Ident}
    (h : clauseSplit2Neg c = some (cc, r)) :
    c.name.name = "bool_clause" ∧
      c.args = [.array [.ident cc], .array [.ident r]] := by
  unfold clauseSplit2Neg at h
  split at h
  · rename_i hname hargs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨hname, hargs⟩
  · cases h

theorem linearRow_spec {c : ConstraintItem} {ps : List (Int × Ident)} {b : Int}
    (h : linearRow c = some (ps, b)) :
    c.name.name = "int_lin_eq" ∧
    ∃ cs xs : ArrayLiteral,
      c.args = [.array cs, .array xs, .basic (.lit (.int b))] ∧
      pairsOfRow cs xs = some ps := by
  unfold linearRow at h
  split at h
  · rename_i cs xs bb hname hargs
    obtain ⟨ps0, hps0, hpair⟩ := Option.map_eq_some_iff.mp h
    simp only [Prod.mk.injEq] at hpair
    obtain ⟨rfl, rfl⟩ := hpair
    exact ⟨hname, cs, xs, hargs, hps0⟩
  · cases h

/-- Division by a negative coefficient reverses the inequality. -/
theorem le_of_mul_le_mul_of_neg {c a b : Int} (hc : c < 0)
    (h : c * a ≤ c * b) : b ≤ a := by
  have hc' : 0 < -c := by omega
  have h' : (-c) * b ≤ (-c) * a := by
    rw [Int.neg_mul, Int.neg_mul]
    exact Int.neg_le_neg h
  exact Int.le_of_mul_le_mul_left h' hc'

/-- The semantic value of an anchor lies in its checked interval. -/
theorem anchorBounds_sound {store : Store} {env : List BoundEntry}
    (henv : EnvSound store env) {a : BoundAnchor} {lo hi : Int}
    (hb : anchorBounds env a = some (lo, hi)) {b : BasicExpr} {i : Int}
    (hev : b.eval store = some (.int i)) (han : anchorOf b = some a) :
    lo ≤ i ∧ i ≤ hi := by
  rcases anchorOf_spec han with ⟨k, rfl, rfl⟩ | ⟨x, rfl, rfl⟩
  · rcases anchorBounds_spec hb with ⟨hkeq, hkhi⟩ | ⟨e, hcontra, -⟩
    · have hk : k = lo := by injection hkeq
      have hik : i = k := by
        have h1 : (Value.int k) = Value.int i := Option.some.inj hev
        exact (by injection h1 with h; exact h.symm)
      omega
    · cases hcontra
  · have hx : store x = some (.int i) := by simpa [BasicExpr.eval] using hev
    rcases anchorBounds_spec hb with ⟨hcontra, -⟩ | ⟨e, ha, hlook, hsort, hlo, hhi⟩
    · cases hcontra
    · have hxv : x = e.var := by injection ha
      subst hxv
      obtain ⟨j, hj, hlj, hjh⟩ := int_sound_of_lookup henv hlook hsort
      have hij : i = j := by
        have h1 : (Value.int i) = Value.int j :=
          Option.some.inj (hx.symm.trans hj)
        injection h1 with h
      omega

/-- The `caseSplit` rule: two reified equalities of `x` plus the two
    clauses place `x` in the hull of the two anchors. -/
theorem caseSplit_sound {store : Store} {m : Model} {env : List BoundEntry}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    (henv : EnvSound store env)
    {x : Ident} {lo hi : Int}
    {r1 r2 cc : Ident} {a1 a2 : BoundAnchor}
    {row1 row2 cl1 cl2 : ConstraintItem}
    {lo1 hi1 lo2 hi2 : Int}
    (hrow1 : row1 ∈ m.constraints) (hrow2 : row2 ∈ m.constraints)
    (hcl1 : cl1 ∈ m.constraints) (hcl2 : cl2 ∈ m.constraints)
    (hreif1 : eqReifRow row1 x = some (r1, a1))
    (hreif2 : eqReifRow row2 x = some (r2, a2))
    (hclause1 : clauseSplit1 cl1 = some (r1, cc))
    (hclause2 : clauseSplit2 cl2 = some (cc, r2))
    (hb1 : anchorBounds env a1 = some (lo1, hi1))
    (hb2 : anchorBounds env a2 = some (lo2, hi2))
    (hlo : lo ≤ min lo1 lo2) (hhi : max hi1 hi2 ≤ hi) :
    ∃ i, store x = some (.int i) ∧ lo ≤ i ∧ i ≤ hi := by
  obtain ⟨hname1, y1, b1, hargs1, hyname1, hanch1⟩ := eqReifRow_spec hreif1
  obtain ⟨hname2, y2, b2, hargs2, hyname2, hanch2⟩ := eqReifRow_spec hreif2
  obtain ⟨hnamec1, hargsc1⟩ := clauseSplit1_spec hclause1
  obtain ⟨hnamec2, hargsc2⟩ := clauseSplit2_spec hclause2
  obtain ⟨vr1, vc1, hvr1, hvc1, hd1⟩ :=
    holds_clause1 hnamec1 hargsc1 (hcons cl1 hcl1)
  obtain ⟨vc2, vr2, hvc2, hvr2, hd2⟩ :=
    holds_clause2 hnamec2 hargsc2 (hcons cl2 hcl2)
  rcases hd1 with hvr1t | hvc1f
  · have hr1 : store r1 = some (.bool true) := by
      rw [hvr1t] at hvr1
      exact hvr1
    obtain ⟨i, hy, ha⟩ := holds_int_eq_reif_true hname1 hargs1
      (hcons row1 hrow1) hr1
    have hxy : y1 = x := Ident.eq_of_name_eq hyname1
    subst hxy
    have hbnd := anchorBounds_sound henv hb1 ha hanch1
    exact ⟨i, hy, Int.le_trans hlo (Int.le_trans (Int.min_le_left _ _) hbnd.1),
      Int.le_trans (Int.le_trans hbnd.2 (Int.le_max_left _ _)) hhi⟩
  · have hvc1' : store cc = some (.bool false) := by
      rw [hvc1f] at hvc1
      exact hvc1
    have hvc2' : vc2 = .bool false :=
      Option.some.inj (hvc2.symm.trans hvc1')
    rcases hd2 with hvc2t | hvr2t
    · rw [hvc2'] at hvc2t
      cases hvc2t
    · have hr2 : store r2 = some (.bool true) := by
        rw [hvr2t] at hvr2
        exact hvr2
      obtain ⟨i, hy, ha⟩ := holds_int_eq_reif_true hname2 hargs2
        (hcons row2 hrow2) hr2
      have hxy : y2 = x := Ident.eq_of_name_eq hyname2
      subst hxy
      have hbnd := anchorBounds_sound henv hb2 ha hanch2
      exact ⟨i, hy, Int.le_trans hlo (Int.le_trans (Int.min_le_right _ _) hbnd.1),
        Int.le_trans (Int.le_trans hbnd.2 (Int.le_max_right _ _)) hhi⟩

/-- The `forced` rule: two complementary clauses force the tracked Boolean
    variable to the claimed value. -/
theorem forced_sound {store : Store} {m : Model}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    {r cc : Ident} {value : Bool} {lo hi : Int}
    {cl1 cl2 : ConstraintItem}
    (hcl1 : cl1 ∈ m.constraints) (hcl2 : cl2 ∈ m.constraints)
    (hcond :
      (value = true ∧ clauseSplit1 cl1 = some (r, cc) ∧
        clauseSplit2 cl2 = some (cc, r) ∧ lo ≤ 1 ∧ 1 ≤ hi) ∨
      (value = false ∧ clauseSplit1Neg cl1 = some (cc, r) ∧
        clauseSplit2Neg cl2 = some (cc, r) ∧ lo ≤ 0 ∧ 0 ≤ hi)) :
    ∃ b : Bool, store r = some (.bool b) ∧
      lo ≤ (if b then (1 : Int) else 0) ∧
      (if b then (1 : Int) else 0) ≤ hi := by
  rcases hcond with ⟨-, hc1, hc2, hlo, hhi⟩ | ⟨-, hc1, hc2, hlo, hhi⟩
  · obtain ⟨hnamec1, hargsc1⟩ := clauseSplit1_spec hc1
    obtain ⟨hnamec2, hargsc2⟩ := clauseSplit2_spec hc2
    obtain ⟨vr1, vc1, hvr1, hvc1, hd1⟩ :=
      holds_clause1 hnamec1 hargsc1 (hcons cl1 hcl1)
    obtain ⟨vc2, vr2, hvc2, hvr2, hd2⟩ :=
      holds_clause2 hnamec2 hargsc2 (hcons cl2 hcl2)
    rcases hd1 with hvr1t | hvc1f
    · have hr : store r = some (.bool true) := by
        rw [hvr1t] at hvr1
        exact hvr1
      exact ⟨true, hr, by simpa using hlo, by simpa using hhi⟩
    · have hvc1' : store cc = some (.bool false) := by
        rw [hvc1f] at hvc1
        exact hvc1
      have hvc2' : vc2 = .bool false :=
        Option.some.inj (hvc2.symm.trans hvc1')
      rcases hd2 with hvc2t | hvr2t
      · rw [hvc2'] at hvc2t
        cases hvc2t
      · have hr : store r = some (.bool true) := by
          rw [hvr2t] at hvr2
          exact hvr2
        exact ⟨true, hr, by simpa using hlo, by simpa using hhi⟩
  · obtain ⟨hnamec1, hargsc1⟩ := clauseSplit1Neg_spec hc1
    obtain ⟨hnamec2, hargsc2⟩ := clauseSplit2Neg_spec hc2
    obtain ⟨vc1, vr1, hvc1, hvr1, hd1⟩ :=
      holds_clause1Neg hnamec1 hargsc1 (hcons cl1 hcl1)
    obtain ⟨vc2, vr2, hvc2, hvr2, hd2⟩ :=
      holds_clause2Neg hnamec2 hargsc2 (hcons cl2 hcl2)
    rcases hd1 with hvc1f | hvr1f
    · have hvc1' : store cc = some (.bool false) := by
        rw [hvc1f] at hvc1
        exact hvc1
      have hvc2' : vc2 = .bool false :=
        Option.some.inj (hvc2.symm.trans hvc1')
      rcases hd2 with hvc2t | hvr2f
      · rw [hvc2'] at hvc2t
        cases hvc2t
      · have hr : store r = some (.bool false) := by
          rw [hvr2f] at hvr2
          exact hvr2
        exact ⟨false, hr, by simpa using hlo, by simpa using hhi⟩
    · have hr : store r = some (.bool false) := by
        rw [hvr1f] at hvr1
        exact hvr1
      exact ⟨false, hr, by simpa using hlo, by simpa using hhi⟩

/-- The `linear` rule: a checked `int_lin_eq` row with a nonzero
    coefficient bounds the tracked variable. -/
theorem linear_sound {store : Store} {m : Model} {env : List BoundEntry}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    (henv : EnvSound store env)
    {x : Ident} {lo hi coeff : Int} {row : ConstraintItem}
    {ps : List (Int × Ident)} {b : Int}
    (hrow : row ∈ m.constraints)
    (hlin : linearRow row = some (ps, b))
    {pre post : List (Int × Ident)} {cj : Int}
    (hsplit : splitPair x ps = some (pre, cj, post))
    {loPre hiPre loPost hiPost : Int}
    (hloPre : sumLo? env pre = some loPre)
    (hhiPre : sumHi? env pre = some hiPre)
    (hloPost : sumLo? env post = some loPost)
    (hhiPost : sumHi? env post = some hiPost)
    (hcond : cj = coeff ∧ coeff ≠ 0 ∧
      (0 < coeff →
        coeff * (lo - 1) < b - (hiPre + hiPost) ∧
        b - (loPre + loPost) < coeff * (hi + 1)) ∧
      (coeff < 0 →
        coeff * (hi + 1) < b - (hiPre + hiPost) ∧
        b - (loPre + loPost) < coeff * (lo - 1))) :
    ∃ i, store x = some (.int i) ∧ lo ≤ i ∧ i ≤ hi := by
  obtain ⟨hname, cs, xs, hargs, hps⟩ := linearRow_spec hlin
  obtain ⟨vs1, vs2, hks, hxs, hdot⟩ :=
    holds_int_lin_eq hname hargs (hcons row hrow)
  obtain ⟨hcs, hxs'⟩ := pairsOfRow_spec hps
  rw [hcs] at hks
  rw [hxs'] at hxs
  have hvs1 : vs1 = ps.map (fun p => Value.int p.1) := by
    rw [mapM_lit_int] at hks
    exact (Option.some.inj hks).symm
  rw [hvs1] at hdot
  have hPS : pairSum store ps = some b :=
    dotProduct_mapM_pairs hxs hdot
  have hpsEq : ps = pre ++ (cj, x) :: post := splitPair_spec hsplit
  rw [hpsEq] at hPS
  obtain ⟨a, c, hpre, hrest, hb⟩ :=
    pairSum_append_inv pre ((cj, x) :: post) hPS
  obtain ⟨i, u, hxi, hpost, hcEq⟩ := pairSum_cons_inv hrest
  obtain ⟨ta, hta, htaLo⟩ := pairSum_le_of_sumLo henv pre hloPre
  obtain ⟨ta', hta', htaHi⟩ := pairSum_ge_of_sumHi henv pre hhiPre
  obtain ⟨tu, htu, htuLo⟩ := pairSum_le_of_sumLo henv post hloPost
  obtain ⟨tu', htu', htuHi⟩ := pairSum_ge_of_sumHi henv post hhiPost
  have ha : a = ta := Option.some.inj (hpre.symm.trans hta)
  have ha' : a = ta' := Option.some.inj (hpre.symm.trans hta')
  have hu : u = tu := Option.some.inj (hpost.symm.trans htu)
  have hu' : u = tu' := Option.some.inj (hpost.symm.trans htu')
  have hloA : loPre ≤ a := by rw [← ha] at htaLo; exact htaLo
  have hhiA : a ≤ hiPre := by rw [← ha'] at htaHi; exact htaHi
  have hloU : loPost ≤ u := by rw [← hu] at htuLo; exact htuLo
  have hhiU : u ≤ hiPost := by rw [← hu'] at htuHi; exact htuHi
  have hterm : cj * i = b - (a + u) := by omega
  have hge : b - (hiPre + hiPost) ≤ cj * i := by omega
  have hle : cj * i ≤ b - (loPre + loPost) := by omega
  have hne : cj ≠ 0 := by
    intro h0
    have hc0 : coeff = 0 := by rw [← hcond.1, h0]
    exact hcond.2.1 hc0
  by_cases hpos : 0 < cj
  · have h1 : cj * (lo - 1) < b - (hiPre + hiPost) := by
      have hp' : 0 < coeff := by omega
      have := (hcond.2.2.1 hp').1
      rwa [← hcond.1] at this
    have h2 : b - (loPre + loPost) < cj * (hi + 1) := by
      have hp' : 0 < coeff := by omega
      have := (hcond.2.2.1 hp').2
      rwa [← hcond.1] at this
    refine ⟨i, hxi, ?_, ?_⟩
    · by_cases hlt : i < lo
      · have hle' : i ≤ lo - 1 := Int.le_sub_one_of_lt hlt
        have hmul : cj * i ≤ cj * (lo - 1) :=
          Int.mul_le_mul_of_nonneg_left hle' (Int.le_of_lt hpos)
        exact absurd (Int.lt_of_le_of_lt hmul h1) (Int.not_lt.mpr hge)
      · exact Int.le_of_not_gt hlt
    · by_cases hlt : hi < i
      · have hle' : hi + 1 ≤ i := Int.add_one_le_iff.mpr hlt
        have hmul : cj * (hi + 1) ≤ cj * i :=
          Int.mul_le_mul_of_nonneg_left hle' (Int.le_of_lt hpos)
        exact absurd (Int.lt_of_lt_of_le h2 hmul) (Int.not_lt.mpr hle)
      · exact Int.le_of_not_gt hlt
  · have hneg : cj < 0 := by omega
    have h1 : cj * (hi + 1) < b - (hiPre + hiPost) := by
      have hn' : coeff < 0 := by omega
      have := (hcond.2.2.2 hn').1
      rwa [← hcond.1] at this
    have h2 : b - (loPre + loPost) < cj * (lo - 1) := by
      have hn' : coeff < 0 := by omega
      have := (hcond.2.2.2 hn').2
      rwa [← hcond.1] at this
    refine ⟨i, hxi, ?_, ?_⟩
    · by_cases hlt : i < lo
      · have hle' : i ≤ lo - 1 := Int.le_sub_one_of_lt hlt
        have hmul : cj * (lo - 1) ≤ cj * i :=
          Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hneg) hle'
        exact absurd (Int.lt_of_lt_of_le h2 hmul) (Int.not_lt.mpr hle)
      · exact Int.le_of_not_gt hlt
    · by_cases hlt : hi < i
      · have hle' : hi + 1 ≤ i := Int.add_one_le_iff.mpr hlt
        have hmul : cj * i ≤ cj * (hi + 1) :=
          Int.mul_le_mul_of_nonpos_left (Int.le_of_lt hneg) hle'
        exact absurd (Int.lt_of_le_of_lt hmul h1) (Int.not_lt.mpr hge)
      · exact Int.le_of_not_gt hlt

/-- Soundness of one certificate replay. -/
theorem checkCert_sound {m : Model} {env : List BoundEntry} {cert : BoundCert}
    {e : BoundEntry} {store : Store}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    (henv : EnvSound store env)
    (hcheck : checkCert m env cert = some e) : e.Sound store := by
  obtain ⟨var, sort, lo, hi, rule⟩ := cert
  cases rule with
  | caseSplit i1 r1 a1 i2 r2 a2 cc j1 j2 =>
      simp only [checkCert] at hcheck
      split at hcheck
      · rename_i hsort
        cases h1 : m.constraints[i1]? with
        | none => simp only [h1] at hcheck; cases hcheck
        | some row1 =>
          simp only [h1] at hcheck
          cases h2 : m.constraints[i2]? with
          | none => simp only [h2] at hcheck; cases hcheck
          | some row2 =>
            simp only [h2] at hcheck
            cases h3 : m.constraints[j1]? with
            | none => simp only [h3] at hcheck; cases hcheck
            | some cl1 =>
              simp only [h3] at hcheck
              cases h4 : m.constraints[j2]? with
              | none => simp only [h4] at hcheck; cases hcheck
              | some cl2 =>
                simp only [h4] at hcheck
                cases h5 : anchorBounds env a1 with
                | none => simp only [h5] at hcheck; cases hcheck
                | some b1 =>
                  simp only [h5] at hcheck
                  cases b1 with
                  | mk lo1 hi1 =>
                    cases h6 : anchorBounds env a2 with
                    | none => simp only [h6] at hcheck; cases hcheck
                    | some b2 =>
                      simp only [h6] at hcheck
                      cases b2 with
                      | mk lo2 hi2 =>
                        split at hcheck
                        · rename_i hcond
                          simp only [Option.some.injEq] at hcheck
                          subst e
                          dsimp only at hcond
                          have hlo : lo ≤ min lo1 lo2 := hcond.2.2.2.2.1
                          have hhi : max hi1 hi2 ≤ hi := hcond.2.2.2.2.2
                          have hmem1 : row1 ∈ m.constraints :=
                            List.mem_of_getElem? h1
                          have hmem2 : row2 ∈ m.constraints :=
                            List.mem_of_getElem? h2
                          have hmemc1 : cl1 ∈ m.constraints :=
                            List.mem_of_getElem? h3
                          have hmemc2 : cl2 ∈ m.constraints :=
                            List.mem_of_getElem? h4
                          show BoundEntry.Sound store ⟨var, sort, lo, hi⟩
                          rw [hsort]
                          exact caseSplit_sound hcons henv hmem1 hmem2 hmemc1
                            hmemc2 hcond.1 hcond.2.1 hcond.2.2.1 hcond.2.2.2.1
                            h5 h6 hlo hhi
                        · cases hcheck
      · cases hcheck
  | forced r cc value j1 j2 =>
      simp only [checkCert] at hcheck
      split at hcheck
      · rename_i hsort
        split at hcheck
        · rename_i hname
          cases h1 : m.constraints[j1]? with
          | none => simp only [h1] at hcheck; cases hcheck
          | some cl1 =>
            simp only [h1] at hcheck
            cases h2 : m.constraints[j2]? with
            | none => simp only [h2] at hcheck; cases hcheck
            | some cl2 =>
              simp only [h2] at hcheck
              split at hcheck
              · rename_i hcond
                simp only [Option.some.injEq] at hcheck
                subst e
                have hmemc1 : cl1 ∈ m.constraints := List.mem_of_getElem? h1
                have hmemc2 : cl2 ∈ m.constraints := List.mem_of_getElem? h2
                have hvar : var = r := Ident.eq_of_name_eq hname
                show BoundEntry.Sound store ⟨var, sort, lo, hi⟩
                rw [hsort, hvar]
                exact forced_sound hcons hmemc1 hmemc2 hcond
              · cases hcheck
        · cases hcheck
      · cases hcheck
  | linear row coeff =>
      simp only [checkCert] at hcheck
      split at hcheck
      · rename_i hsort
        cases h1 : m.constraints[row]? with
        | none => simp only [h1] at hcheck; cases hcheck
        | some con =>
          simp only [h1] at hcheck
          cases h2 : linearRow con with
          | none => simp only [h2] at hcheck; cases hcheck
          | some pb =>
            cases pb with
            | mk ps b =>
              simp only [h2] at hcheck
              cases h3 : splitPair var ps with
              | none => simp only [h3] at hcheck; cases hcheck
              | some spl =>
                cases spl with
                | mk pre rest =>
                  cases rest with
                  | mk cj post =>
                    simp only [h3] at hcheck
                    cases h4 : sumLo? env pre with
                    | none => simp only [h4] at hcheck; cases hcheck
                    | some loPre =>
                      simp only [h4] at hcheck
                      cases h5 : sumHi? env pre with
                      | none => simp only [h5] at hcheck; cases hcheck
                      | some hiPre =>
                        simp only [h5] at hcheck
                        cases h6 : sumLo? env post with
                        | none => simp only [h6] at hcheck; cases hcheck
                        | some loPost =>
                          simp only [h6] at hcheck
                          cases h7 : sumHi? env post with
                          | none => simp only [h7] at hcheck; cases hcheck
                          | some hiPost =>
                            simp only [h7] at hcheck
                            split at hcheck
                            · rename_i hcond
                              simp only [Option.some.injEq] at hcheck
                              subst e
                              have hmem : con ∈ m.constraints :=
                                List.mem_of_getElem? h1
                              show BoundEntry.Sound store ⟨var, sort, lo, hi⟩
                              rw [hsort]
                              exact linear_sound hcons henv hmem h2 h3 h4 h5
                                h6 h7 hcond
                            · cases hcheck
      · cases hcheck

/-- Soundness of the whole certificate replay. -/
theorem checkCerts_sound {m : Model} {env env' : List BoundEntry}
    {certs : List BoundCert} {store : Store}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    (henv : EnvSound store env)
    (hcheck : checkCerts m env certs = some env') : EnvSound store env' := by
  induction certs generalizing env with
  | nil =>
      simp only [checkCerts] at hcheck
      have heq : env = env' := Option.some.inj hcheck
      subst heq
      exact henv
  | cons cert rest ih =>
      simp only [checkCerts] at hcheck
      split at hcheck
      · rename_i e he
        have hes : e.Sound store := checkCert_sound hcons henv he
        have henv' : EnvSound store (env ++ [e]) :=
          envSound_append henv (envSound_singleton hes)
        exact ih henv' hcheck
      · cases hcheck

/-! ## Tightening preserves the model -/

theorem checkedIntBound_spec {env : List BoundEntry} {x : Ident} {lo hi : Int}
    (h : checkedIntBound env x = some (lo, hi)) :
    ∃ e, lookupEntry x env = some e ∧ e.sort = .int ∧ e.lo = lo ∧ e.hi = hi := by
  unfold checkedIntBound at h
  split at h
  · rename_i e he
    split at h
    · rename_i hs
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨hl, hh⟩ := h
      exact ⟨e, he, hs, hl, hh⟩
    · cases h
  · cases h

theorem hasIntEntry_spec {env : List BoundEntry} {x : Ident}
    (h : hasIntEntry env x = true) :
    ∃ e, e ∈ env ∧ e.var.name = x.name ∧ e.sort = .int := by
  unfold hasIntEntry at h
  rw [List.any_eq_true] at h
  obtain ⟨e, he, hcond⟩ := h
  simp only [Bool.and_eq_true] at hcond
  have hname : e.var.name = x.name := by simpa using hcond.1
  cases hs : e.sort with
  | int => exact ⟨e, he, hname, hs⟩
  | bool =>
      exfalso
      have hb : (BoundSort.bool == BoundSort.int) = false := by decide
      rw [hs, hb] at hcond
      exact Bool.false_ne_true hcond.2

theorem tightenDecl_domain_forward {store : Store} {env : List BoundEntry}
    (henv : EnvSound store env) (d : VarDeclItem) :
    DeclDomain store d → DeclDomain store (tightenDecl env d) := by
  intro hd
  cases d with
  | array ty n anns es =>
      simpa [DeclDomain, tightenDecl] using hd
  | basic ty n anns v =>
      cases ty with
      | par t =>
          cases t with
          | int =>
              cases hcb : checkedIntBound env n with
              | none => simpa [DeclDomain, tightenDecl, hcb] using hd
              | some b =>
                  obtain ⟨lo, hi⟩ := b
                  simp only [DeclDomain, tightenDecl, hcb]
                  obtain ⟨e, hlook, hs, hl, hh⟩ := checkedIntBound_spec hcb
                  obtain ⟨val, hval, hcont⟩ := hd
                  cases val with
                  | int i =>
                      obtain ⟨i', hi', hlo', hhi'⟩ :=
                        int_sound_of_lookup henv hlook hs
                      refine ⟨.int i', hi', ?_⟩
                      simp only [BasicVarType.contains]
                      exact ⟨by rw [← hl]; exact hlo',
                        by rw [← hh]; exact hhi'⟩
                  | bool b => simp [BasicVarType.contains] at hcont
                  | setOfInt s => simp [BasicVarType.contains] at hcont
                  | array vs => simp [BasicVarType.contains] at hcont
          | bool => simpa [DeclDomain, tightenDecl] using hd
          | setOfInt => simpa [DeclDomain, tightenDecl] using hd
      | intRange lo hi => simpa [DeclDomain, tightenDecl] using hd
      | intSet xs => simpa [DeclDomain, tightenDecl] using hd
      | setOfIntRange lo hi => simpa [DeclDomain, tightenDecl] using hd
      | setOfIntSet xs => simpa [DeclDomain, tightenDecl] using hd

theorem tightenDecl_domain_backward {store : Store} {env : List BoundEntry}
    (d : VarDeclItem) :
    DeclDomain store (tightenDecl env d) → DeclDomain store d := by
  intro hd
  cases d with
  | array ty n anns es =>
      simpa [DeclDomain, tightenDecl] using hd
  | basic ty n anns v =>
      cases ty with
      | par t =>
          cases t with
          | int =>
              cases hcb : checkedIntBound env n with
              | none => simpa [DeclDomain, tightenDecl, hcb] using hd
              | some b =>
                  obtain ⟨lo, hi⟩ := b
                  simp only [DeclDomain, tightenDecl, hcb] at hd
                  obtain ⟨val, hval, hcont⟩ := hd
                  cases val with
                  | int i => exact ⟨.int i, hval, trivial⟩
                  | bool b => simp [BasicVarType.contains] at hcont
                  | setOfInt s => simp [BasicVarType.contains] at hcont
                  | array vs => simp [BasicVarType.contains] at hcont
          | bool => simpa [DeclDomain, tightenDecl] using hd
          | setOfInt => simpa [DeclDomain, tightenDecl] using hd
      | intRange lo hi => simpa [DeclDomain, tightenDecl] using hd
      | intSet xs => simpa [DeclDomain, tightenDecl] using hd
      | setOfIntRange lo hi => simpa [DeclDomain, tightenDecl] using hd
      | setOfIntSet xs => simpa [DeclDomain, tightenDecl] using hd

theorem tightenDecl_name (env : List BoundEntry) (d : VarDeclItem) :
    (tightenDecl env d).name = d.name := by
  cases d with
  | basic ty n anns v =>
      cases ty with
      | par t =>
          cases t <;> simp [tightenDecl] <;> (try split <;> rfl) <;> rfl
      | intRange lo hi => simp [tightenDecl]
      | intSet xs => simp [tightenDecl]
      | setOfIntRange lo hi => simp [tightenDecl]
      | setOfIntSet xs => simp [tightenDecl]
  | array ty n anns es => rfl

theorem tightenDecl_type (env : List BoundEntry) (d : VarDeclItem) :
    (tightenDecl env d).type = d.type := by
  cases d with
  | basic ty n anns v =>
      cases ty with
      | par t =>
          cases t <;> simp [tightenDecl] <;> (try split <;> rfl) <;> rfl
      | intRange lo hi => simp [tightenDecl]
      | intSet xs => simp [tightenDecl]
      | setOfIntRange lo hi => simp [tightenDecl]
      | setOfIntSet xs => simp [tightenDecl]
  | array ty n anns es => rfl

theorem tightenDecl_base {env : List BoundEntry} {ty : BasicVarType} {n : Ident}
    {anns : List Annotation} {v : Option BasicExpr} :
    ∃ ty', tightenDecl env (.basic ty n anns v) = .basic ty' n anns v ∧
      ty'.base = ty.base := by
  cases ty with
  | par t =>
      cases t with
      | bool => exact ⟨.par .bool, by simp [tightenDecl], rfl⟩
      | int =>
          cases h : checkedIntBound env n with
          | none => exact ⟨.par .int, by simp [tightenDecl, h], rfl⟩
          | some b =>
              cases b with
              | mk lo hi =>
                  exact ⟨.intRange lo hi, by simp [tightenDecl, h], rfl⟩
      | setOfInt => exact ⟨.par .setOfInt, by simp [tightenDecl], rfl⟩
  | intRange lo hi => exact ⟨.intRange lo hi, by simp [tightenDecl], rfl⟩
  | intSet xs => exact ⟨.intSet xs, by simp [tightenDecl], rfl⟩
  | setOfIntRange lo hi =>
      exact ⟨.setOfIntRange lo hi, by simp [tightenDecl], rfl⟩
  | setOfIntSet xs => exact ⟨.setOfIntSet xs, by simp [tightenDecl], rfl⟩

theorem variableArrayLengths_basic (ty : BasicVarType) (n : Ident)
    (anns : List Annotation) (init : Option BasicExpr) :
    (match VarDeclItem.basic ty n anns init with
     | .array ty _ _ values => values.length = ty.idx.length
     | _ => True) := by
  cases ty <;> simp

theorem variableInitializers_basic_some {env : StaticEnv} (ty : BasicVarType)
    (n : Ident) (anns : List Annotation) (e : BasicExpr)
    (h : e.hasBaseType env ty.base) :
    (match VarDeclItem.basic ty n anns (some e) with
     | .basic t _ _ (some v) => v.hasBaseType env t.base
     | .array ty _ _ values => ∀ v, v ∈ values → v.hasBaseType env ty.elem.base
     | _ => True) := by
  cases ty <;> simpa using h

theorem variableInitializers_basic_none {env : StaticEnv} (ty : BasicVarType)
    (n : Ident) (anns : List Annotation) :
    (match VarDeclItem.basic ty n anns none with
     | .basic t _ _ (some v) => v.hasBaseType env t.base
     | .array ty _ _ values => ∀ v, v ∈ values → v.hasBaseType env ty.elem.base
     | _ => True) := by
  cases ty <;> simp

theorem initializerHolds_basic_congr (store : Store) (ty ty' : BasicVarType)
    (n : Ident) (anns : List Annotation) (v : Option BasicExpr) :
    VarDeclItem.initializerHolds store (.basic ty n anns v) ↔
      VarDeclItem.initializerHolds store (.basic ty' n anns v) := by
  cases v with
  | none => simp [VarDeclItem.initializerHolds]
  | some e => simp [VarDeclItem.initializerHolds]

theorem tightenDecl_initializer (env : List BoundEntry) (d : VarDeclItem)
    (store : Store) :
    (tightenDecl env d).initializerHolds store ↔ d.initializerHolds store := by
  cases d with
  | basic ty n anns v =>
      obtain ⟨ty', hdecl, _⟩ :=
        tightenDecl_base (env := env) (ty := ty) (n := n)
          (anns := anns) (v := v)
      rw [hdecl]
      exact initializerHolds_basic_congr store ty' ty n anns v
  | array ty n anns es => simp [tightenDecl]

/-- The rewrite preserves the global static environment. -/
theorem staticEnv_bounds (m : Model) (env : List BoundEntry) :
    (tightenModel m env).staticEnv = m.staticEnv := by
  funext x
  show (match lookupIdent x ((tightenModel m env).parameters.map
          (fun (d : ParDeclItem) => (d.name, (d.type, false)))) with
        | some info => some info
        | none => lookupIdent x ((tightenModel m env).variables.map
            (fun (d : VarDeclItem) => (d.name, (d.type, true))))) =
       (match lookupIdent x (m.parameters.map
          (fun (d : ParDeclItem) => (d.name, (d.type, false)))) with
        | some info => some info
        | none => lookupIdent x (m.variables.map
            (fun (d : VarDeclItem) => (d.name, (d.type, true)))))
  have hp : (tightenModel m env).parameters = m.parameters := rfl
  have hv : ((tightenModel m env).variables.map
        (fun d => (d.name, (d.type, true)))) =
      m.variables.map (fun d => (d.name, (d.type, true))) := by
    rw [show (tightenModel m env).variables =
      m.variables.map (tightenDecl env) from rfl]
    rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    simp only [Function.comp_apply, tightenDecl_name, tightenDecl_type]
  rw [hp, hv]

/-- Static well-formedness is preserved by the bounds rewrite (the
    rewrite keeps names, base types, array lengths and initializers). -/
theorem wf_bounds {m : Model} {env : List BoundEntry}
    (hwf : WellFormed fullSig m) :
    WellFormed fullSig (tightenModel m env) := by
  have hp : (tightenModel m env).parameters = m.parameters := rfl
  have hv : ((tightenModel m env).variables.map VarDeclItem.name) =
      m.variables.map VarDeclItem.name := by
    rw [show (tightenModel m env).variables =
      m.variables.map (tightenDecl env) from rfl]
    rw [List.map_map]
    apply List.map_congr_left
    intro d hd
    simp only [Function.comp_apply, tightenDecl_name]
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
        simpa [tightenDecl] using hwf.variableArrayLengths _ hd0
    | basic ty n anns init =>
        obtain ⟨ty', hdecl, _⟩ :=
          tightenDecl_base (env := env) (ty := ty) (n := n)
            (anns := anns) (v := init)
        rw [hdecl]
        exact variableArrayLengths_basic ty' n anns init
  · intro d hd
    obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
    cases d0 with
    | array ty n anns es =>
        rw [staticEnv_bounds]
        simpa [tightenDecl] using hwf.variableInitializers _ hd0
    | basic ty n anns init =>
        cases init with
        | none =>
            obtain ⟨ty', hdecl, _⟩ :=
              tightenDecl_base (env := env) (ty := ty) (n := n)
                (anns := anns) (v := none)
            rw [staticEnv_bounds, hdecl]
            exact variableInitializers_basic_none (env := m.staticEnv) ty' n anns
        | some e =>
            obtain ⟨ty', hdecl, hbase⟩ :=
              tightenDecl_base (env := env) (ty := ty) (n := n)
                (anns := anns) (v := some e)
            have hinit : e.hasBaseType m.staticEnv ty'.base := by
              simpa [hbase] using hwf.variableInitializers _ hd0
            rw [staticEnv_bounds, hdecl]
            exact variableInitializers_basic_some ty' n anns e hinit
  · rw [staticEnv_bounds]
    exact hwf.objectiveType
  · intro c hc
    obtain ⟨params, hsig, hca⟩ := hwf.constraintsChecked c hc
    exact ⟨params, hsig, by simpa [staticEnv_bounds] using hca⟩

/-! ## The bounds pass preserves and reflects satisfaction -/

theorem boundsModel_sound {m m' : Model} {store : Store}
    (hbm : boundsModel m = some m')
    (hsat : SatisfiesDyn fullInterp m store) :
    SatisfiesDyn fullInterp m' store := by
  obtain ⟨hcons, hdom, hinit⟩ := hsat
  unfold boundsModel at hbm
  dsimp only at hbm
  split at hbm
  · rename_i hempty
    simp only [Option.some.injEq] at hbm
    subst hbm
    exact ⟨hcons, hdom, hinit⟩
  · rename_i hempty
    split at hbm
    · cases hbm
    · rename_i env hcheck
      split at hbm
      · rename_i hall
        simp only [Option.some.injEq] at hbm
        subst hbm
        have hsound : EnvSound store env :=
          checkCerts_sound hcons (nativeEnv_sound hdom) hcheck
        refine ⟨?_, ?_, ?_⟩
        · simpa [tightenModel] using hcons
        · intro d hd
          unfold tightenModel at hd
          obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
          exact tightenDecl_domain_forward hsound d0
            (varDomains_iff.mp hdom d0 hd0)
        · intro d hd
          unfold tightenModel at hd
          obtain ⟨d0, hd0, rfl⟩ := List.mem_map.mp hd
          exact (tightenDecl_initializer env d0 store).mpr (hinit d0 hd0)
      · cases hbm

theorem boundsModel_exact {m m' : Model} {store : Store}
    (hbm : boundsModel m = some m')
    (hsat : SatisfiesDyn fullInterp m' store) :
    SatisfiesDyn fullInterp m store := by
  obtain ⟨hcons, hdom, hinit⟩ := hsat
  unfold boundsModel at hbm
  dsimp only at hbm
  split at hbm
  · rename_i hempty
    simp only [Option.some.injEq] at hbm
    subst hbm
    exact ⟨hcons, hdom, hinit⟩
  · rename_i hempty
    split at hbm
    · cases hbm
    · rename_i env hcheck
      split at hbm
      · rename_i hall
        simp only [Option.some.injEq] at hbm
        subst hbm
        refine ⟨?_, ?_, ?_⟩
        · simpa [tightenModel] using hcons
        · intro d hd
          have hd' : tightenDecl env d ∈ (tightenModel m env).variables := by
            unfold tightenModel
            exact List.mem_map_of_mem hd
          exact tightenDecl_domain_backward d
            (varDomains_iff.mp hdom (tightenDecl env d) hd')
        · intro d hd
          have hd' : tightenDecl env d ∈ (tightenModel m env).variables := by
            unfold tightenModel
            exact List.mem_map_of_mem hd
          exact (tightenDecl_initializer env d store).mp (hinit _ hd')
      · cases hbm

/-! ## Framing facts about the bounds pass -/

/-- `boundsModel` either leaves the model unchanged or rewrites its
    variable declarations through `tightenModel`. -/
theorem boundsModel_inv {m m' : Model} (h : boundsModel m = some m') :
    m' = m ∨ ∃ env, m' = tightenModel m env := by
  unfold boundsModel at h
  dsimp only at h
  split at h
  · left
    exact (Option.some.inj h).symm
  · split at h
    · cases h
    · split at h
      · right
        exact ⟨_, (Option.some.inj h).symm⟩
      · cases h

theorem boundsModel_parameters {m m' : Model} (h : boundsModel m = some m') :
    m'.parameters = m.parameters := by
  rcases boundsModel_inv h with rfl | ⟨env, rfl⟩ <;> rfl

theorem boundsModel_constraints {m m' : Model} (h : boundsModel m = some m') :
    m'.constraints = m.constraints := by
  rcases boundsModel_inv h with rfl | ⟨env, rfl⟩ <;> rfl

theorem boundsModel_predicates {m m' : Model} (h : boundsModel m = some m') :
    m'.predicates = m.predicates := by
  rcases boundsModel_inv h with rfl | ⟨env, rfl⟩ <;> rfl

theorem boundsModel_solve {m m' : Model} (h : boundsModel m = some m') :
    m'.solve = m.solve := by
  rcases boundsModel_inv h with rfl | ⟨env, rfl⟩ <;> rfl

theorem boundsModel_staticEnv {m m' : Model} (h : boundsModel m = some m') :
    m'.staticEnv = m.staticEnv := by
  rcases boundsModel_inv h with rfl | ⟨env, rfl⟩
  · rfl
  · exact staticEnv_bounds m env

theorem wf_boundsModel {m m' : Model} (h : boundsModel m = some m')
    (hwf : WellFormed fullSig m) : WellFormed fullSig m' := by
  rcases boundsModel_inv h with rfl | ⟨env, rfl⟩
  · exact hwf
  · exact wf_bounds hwf

/-- Every source declaration survives the bounds pass with the same name
    (possibly with a tightened type). -/
theorem boundsModel_variables_mem {m m' : Model} (h : boundsModel m = some m')
    {d : VarDeclItem} (hd : d ∈ m.variables) :
    ∃ d' ∈ m'.variables, d'.name = d.name := by
  rcases boundsModel_inv h with rfl | ⟨env, rfl⟩
  · exact ⟨d, hd, rfl⟩
  · exact ⟨tightenDecl env d, List.mem_map_of_mem hd,
      tightenDecl_name env d⟩

end LeanFzn.Compiler
