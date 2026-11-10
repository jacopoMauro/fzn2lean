/-
File: LeanFzn/Compiler/Proofs/SetShape.lean

Purpose:
  Correctness of the set-shape pre-pass (`Compiler/SetShape.lean`): every
  recognized set constraint is rewritten into an equisatisfiable scalar
  encoding whose fresh auxiliaries are functionally determined, and
  static well-formedness is preserved.  The pass runs before the verified
  S3 set expansion; its proofs are independent of S3.

Dependencies:
  - LeanFzn.Compiler.SetShape
  - LeanFzn.Compiler.Proofs.SetExpand (universe and interval facts)
-/

import LeanFzn.Compiler.SetShape
import LeanFzn.Compiler.Proofs.SetExpand
import LeanFzn.Compiler.Proofs.Bounds
import Std.Data.String.ToNat

set_option maxHeartbeats 1000000

namespace LeanFzn.Compiler
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation
open LeanFzn.Semantics.Globals
open LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The functional meaning of one shape auxiliary -/

/-- The value an auxiliary takes in a store, when its inputs are defined. -/
def ShapeAux.value (s : Store) : ShapeAux → Option Value
  | ⟨_, _, .member S v⟩ =>
      match s (Ident.mk S) with
      | some (.setOfInt sv) => some (.bool (decide (sv.Contains v)))
      | _ => none
  | ⟨_, _, .eq x v⟩ =>
      match s (Ident.mk x) with
      | some (.int i) => some (.bool (decide (i = v)))
      | _ => none
  | ⟨_, _, .and x y⟩ =>
      match s (Ident.mk x), s (Ident.mk y) with
      | some (.bool p), some (.bool q) => some (.bool (p && q))
      | _, _ => none
  | ⟨_, _, .bit x⟩ =>
      match s (Ident.mk x) with
      | some (.bool p) => some (.int (if p then 1 else 0))
      | _ => none
  | ⟨_, _, .const v⟩ => some (.bool v)

/-- The auxiliary reads its own name with its functional value. -/
def ShapeAux.defined (a : ShapeAux) (s : Store) : Prop :=
  s (Ident.mk a.name) = a.value s

/-- A state's auxiliaries are all functionally defined. -/
def ShapeState.defined (st : ShapeState) (s : Store) : Prop :=
  ∀ a ∈ st.aux, a.defined s

/-! ## Agreement of `fullInterp` with `stdInterp` on the emitted names -/

theorem fullInterp_eq_std_of_not_global {n : String}
    (h : n ∉ (globalsNames : List String)) :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  unfold fullInterp
  rw [if_neg (by simpa using h)]

macro "fullInterp_name" n:str : tactic =>
  `(tactic| rw [fullInterp_eq_std_of_not_global (n := $n) (by decide)])

theorem fullInterp_set_in_reif :
    fullInterp (Ident.mk "set_in_reif") =
      stdInterp (Ident.mk "set_in_reif") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_int_eq_reif :
    fullInterp (Ident.mk "int_eq_reif") =
      stdInterp (Ident.mk "int_eq_reif") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_bool_and :
    fullInterp (Ident.mk "bool_and") =
      stdInterp (Ident.mk "bool_and") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_bool_or :
    fullInterp (Ident.mk "bool_or") =
      stdInterp (Ident.mk "bool_or") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_bool_not :
    fullInterp (Ident.mk "bool_not") =
      stdInterp (Ident.mk "bool_not") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_bool_clause :
    fullInterp (Ident.mk "bool_clause") =
      stdInterp (Ident.mk "bool_clause") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_bool2int :
    fullInterp (Ident.mk "bool2int") =
      stdInterp (Ident.mk "bool2int") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_int_lin_eq :
    fullInterp (Ident.mk "int_lin_eq") =
      stdInterp (Ident.mk "int_lin_eq") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_int_eq :
    fullInterp (Ident.mk "int_eq") =
      stdInterp (Ident.mk "int_eq") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_int_le :
    fullInterp (Ident.mk "int_le") =
      stdInterp (Ident.mk "int_le") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_array_var_bool_element :
    fullInterp (Ident.mk "array_var_bool_element") =
      stdInterp (Ident.mk "array_var_bool_element") :=
  fullInterp_eq_std_of_not_global (by decide)

theorem fullInterp_array_var_set_element :
    fullInterp (Ident.mk "array_var_set_element") =
      stdInterp (Ident.mk "array_var_set_element") :=
  fullInterp_eq_std_of_not_global (by decide)

/-! ## The defining constraint determines the auxiliary -/

/-- A membership definition: its constraint holds exactly when the set
    has a set value and the auxiliary is the membership decision. -/
theorem ShapeAux.holds_member (S : String) (v : Int) (n : String)
    (s : Store) :
    (shapeConstraint "set_in_reif"
        [shapeE (shapeInt v), shapeE (shapeName S),
          shapeE (shapeName n)]).Holds fullInterp s ↔
      ∃ sv : IntSetValue, s (Ident.mk S) = some (.setOfInt sv) ∧
        s (Ident.mk n) = some (.bool (decide (sv.Contains v))) := by
  rw [ConstraintItem.Holds]
  simp only [shapeConstraint]
  rw [fullInterp_set_in_reif]
  constructor
  · rintro ⟨args, hargs, hp⟩
    rcases hS : s (Ident.mk S) with _ | bS | iS | svS | arrS <;>
      rcases hN : s (Ident.mk n) with _ | bN | iN | svN | arrN
    all_goals
      simp [shapeE, shapeInt, shapeName, Expr.eval, BasicExpr.eval,
        BasicLiteral.denote, hS, hN, List.mapM_cons] at hargs hp
    all_goals subst hargs
    all_goals try cases svS <;> try cases bN
    all_goals
      simp [stdInterp, IntSetValue.Contains, decide_eq_true_iff] at hp ⊢
    all_goals simp_all [decide_eq_true_iff]
  · rintro ⟨sv, hS, hn⟩
    refine ⟨[.int v, .setOfInt sv, .bool (decide (sv.Contains v))], ?_, ?_⟩
    · simp [shapeE, shapeInt, shapeName, Expr.eval, BasicExpr.eval,
        BasicLiteral.denote, hS, hn, List.mapM_cons]
    · by_cases hc : sv.Contains v <;> simp [stdInterp, hS, hn, hc]

/-- An equality definition: its constraint holds exactly when the integer
    has a value and the auxiliary is the equality decision. -/
theorem ShapeAux.holds_eq (x : String) (v : Int) (n : String)
    (s : Store) :
    (shapeConstraint "int_eq_reif"
        [shapeE (shapeName x), shapeE (shapeInt v),
          shapeE (shapeName n)]).Holds fullInterp s ↔
      ∃ i : Int, s (Ident.mk x) = some (.int i) ∧
        s (Ident.mk n) = some (.bool (decide (i = v))) := by
  rw [ConstraintItem.Holds]
  simp only [shapeConstraint]
  rw [fullInterp_int_eq_reif]
  constructor
  · rintro ⟨args, hargs, hp⟩
    rcases hx : s (Ident.mk x) with _ | bx | ix | svx | arrx <;>
      rcases hn : s (Ident.mk n) with _ | bn | iN | svn | arrn
    all_goals
      simp [shapeE, shapeInt, shapeName, Expr.eval, BasicExpr.eval,
        BasicLiteral.denote, hx, hn, List.mapM_cons] at hargs hp
    all_goals subst hargs
    all_goals try cases bn
    all_goals simp [stdInterp, decide_eq_true_iff] at hp ⊢
    all_goals simp_all [decide_eq_true_iff]
  · rintro ⟨i, hx, hn⟩
    refine ⟨[.int i, .int v, .bool (decide (i = v))], ?_, ?_⟩
    · simp [shapeE, shapeInt, shapeName, Expr.eval, BasicExpr.eval,
        BasicLiteral.denote, hx, hn, List.mapM_cons]
    · by_cases h : i = v <;> simp [stdInterp, hx, hn, h]

/-- A conjunction definition. -/
theorem ShapeAux.holds_and (x y n : String) (s : Store) :
    (shapeConstraint "bool_and"
        [shapeE (shapeName x), shapeE (shapeName y),
          shapeE (shapeName n)]).Holds fullInterp s ↔
      ∃ p q : Bool, s (Ident.mk x) = some (.bool p) ∧
        s (Ident.mk y) = some (.bool q) ∧
        s (Ident.mk n) = some (.bool (p && q)) := by
  rw [ConstraintItem.Holds]
  simp only [shapeConstraint]
  rw [fullInterp_bool_and]
  constructor
  · rintro ⟨args, hargs, hp⟩
    rcases hx : s (Ident.mk x) with _ | bx | ix | svx | arrx <;>
      rcases hy : s (Ident.mk y) with _ | bY | iy | svy | arry <;>
        rcases hn : s (Ident.mk n) with _ | bn | iN | svn | arrn
    all_goals
      simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hy, hn, List.mapM_cons] at hargs hp
    all_goals subst hargs
    all_goals try cases bx <;> try cases bY <;> try cases bn
    all_goals simp [stdInterp] at hp ⊢
    all_goals simp_all
  · rintro ⟨p, q, hx, hy, hn⟩
    refine ⟨[.bool p, .bool q, .bool (p && q)], ?_, ?_⟩
    · simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hy, hn, List.mapM_cons]
    · cases p <;> cases q <;> simp [stdInterp, hx, hy, hn]

/-- A `bool2int` definition. -/
theorem ShapeAux.holds_bit (x n : String) (s : Store) :
    (shapeConstraint "bool2int"
        [shapeE (shapeName x), shapeE (shapeName n)]).Holds fullInterp s ↔
      ∃ p : Bool, s (Ident.mk x) = some (.bool p) ∧
        s (Ident.mk n) = some (.int (if p then 1 else 0)) := by
  rw [ConstraintItem.Holds]
  simp only [shapeConstraint]
  rw [fullInterp_bool2int]
  constructor
  · rintro ⟨args, hargs, hp⟩
    rcases hx : s (Ident.mk x) with _ | bx | ix | svx | arrx <;>
      rcases hn : s (Ident.mk n) with _ | bn | iN | svn | arrn
    all_goals
      simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hn, List.mapM_cons] at hargs hp
    all_goals subst hargs
    all_goals try cases bx <;> try cases iN
    all_goals simp [stdInterp] at hp ⊢
    all_goals simp_all
  · rintro ⟨p, hx, hn⟩
    refine ⟨[.bool p, .int (if p then 1 else 0)], ?_, ?_⟩
    · simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hn, List.mapM_cons]
    · cases p <;> simp [stdInterp, hx, hn]

/-- A Boolean pin definition. -/
theorem ShapeAux.holds_const (v : Bool) (n : String) (s : Store) :
    (pinBoolConstraint n v).Holds fullInterp s ↔
      s (Ident.mk n) = some (.bool v) := by
  rw [ConstraintItem.Holds]
  simp only [pinBoolConstraint]
  rw [fullInterp_bool_not]
  constructor
  · rintro ⟨args, hargs, hp⟩
    rcases hn : s (Ident.mk n) with _ | bn | iN | svn | arrn
    all_goals
      simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        BasicLiteral.denote, hn, List.mapM_cons] at hargs hp
    all_goals subst hargs
    all_goals cases v
    all_goals try cases bn
    all_goals simp [stdInterp] at hp ⊢
    all_goals simp_all
  · intro hn
    refine ⟨[.bool v, .bool (!v)], ?_, ?_⟩
    · simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        BasicLiteral.denote, hn, List.mapM_cons]
    · cases v <;> simp [stdInterp, hn]

/-- The reading equation for a membership auxiliary. -/
theorem value_member_iff (s : Store) (S n : String) (v : Int)
    (hn : s (Ident.mk n) ≠ none) :
    s (Ident.mk n) =
        (match s (Ident.mk S) with
         | some (.setOfInt sv) => some (.bool (decide (sv.Contains v)))
         | _ => none) ↔
      ∃ sv : IntSetValue, s (Ident.mk S) = some (.setOfInt sv) ∧
        s (Ident.mk n) = some (.bool (decide (sv.Contains v))) := by
  rcases hS : s (Ident.mk S) with _ | sv
  · simp [hS, hn]
  · cases sv <;> simp [hS, hn]

/-- The reading equation for an equality auxiliary. -/
theorem value_eq_iff (s : Store) (x n : String) (v : Int)
    (hn : s (Ident.mk n) ≠ none) :
    s (Ident.mk n) =
        (match s (Ident.mk x) with
         | some (.int i) => some (.bool (decide (i = v)))
         | _ => none) ↔
      ∃ i : Int, s (Ident.mk x) = some (.int i) ∧
        s (Ident.mk n) = some (.bool (decide (i = v))) := by
  rcases hx : s (Ident.mk x) with _ | w
  · simp [hx, hn]
  · cases w <;> simp [hx, hn]

/-- The reading equation for a conjunction auxiliary. -/
theorem value_and_iff (s : Store) (x y n : String)
    (hn : s (Ident.mk n) ≠ none) :
    s (Ident.mk n) =
        (match s (Ident.mk x), s (Ident.mk y) with
         | some (.bool p), some (.bool q) => some (.bool (p && q))
         | _, _ => none) ↔
      ∃ p q : Bool, s (Ident.mk x) = some (.bool p) ∧
        s (Ident.mk y) = some (.bool q) ∧
        s (Ident.mk n) = some (.bool (p && q)) := by
  rcases hx : s (Ident.mk x) with _ | wx <;>
    rcases hy : s (Ident.mk y) with _ | wy
  · simp [hx, hy, hn]
  · simp [hx, hy, hn]
  · simp [hx, hy, hn]
  · cases wx <;> cases wy <;> simp [hx, hy, hn]

/-- The reading equation for a `bool2int` auxiliary. -/
theorem value_bit_iff (s : Store) (x n : String)
    (hn : s (Ident.mk n) ≠ none) :
    s (Ident.mk n) =
        (match s (Ident.mk x) with
         | some (.bool p) => some (.int (if p then 1 else 0))
         | _ => none) ↔
      ∃ p : Bool, s (Ident.mk x) = some (.bool p) ∧
        s (Ident.mk n) = some (.int (if p then 1 else 0)) := by
  rcases hx : s (Ident.mk x) with _ | wx
  · simp [hx, hn]
  · cases wx <;> simp [hx, hn]

/-- The defining constraint holds exactly when the auxiliary is
    functionally defined. -/
theorem ShapeAux.definition_holds {a : ShapeAux} {s : Store}
    (hn : s (Ident.mk a.name) ≠ none) :
    a.definition.Holds fullInterp s ↔ a.defined s := by
  cases a with
  | mk n ty k =>
      cases k with
      | member S v =>
          rw [ShapeAux.definition, ShapeAux.holds_member]
          simp only [ShapeAux.defined, ShapeAux.value]
          exact (value_member_iff s S n v hn).symm
      | eq x v =>
          rw [ShapeAux.definition, ShapeAux.holds_eq]
          simp only [ShapeAux.defined, ShapeAux.value]
          exact (value_eq_iff s x n v hn).symm
      | «and» x y =>
          rw [ShapeAux.definition, ShapeAux.holds_and]
          simp only [ShapeAux.defined, ShapeAux.value]
          exact (value_and_iff s x y n hn).symm
      | bit x =>
          rw [ShapeAux.definition, ShapeAux.holds_bit]
          simp only [ShapeAux.defined, ShapeAux.value]
          exact (value_bit_iff s x n hn).symm
      | const v =>
          rw [ShapeAux.definition, ShapeAux.holds_const]
          simp only [ShapeAux.defined, ShapeAux.value]

/-! ## Reading the declared finite domain of a source variable -/

/-- The finite integer values admitted by a scalar declaration type. -/
def finiteIntValues? : BasicVarType → Option (List Int)
  | .intRange lo hi => some (setElems (.interval lo hi))
  | .intSet xs => some ((IntSetValue.enumeration xs).sortElems)
  | _ => none

/-- The finite values of a type are duplicate-free. -/
theorem finiteIntValues?_nodup {ty : BasicVarType} {vals : List Int}
    (h : finiteIntValues? ty = some vals) : vals.Nodup := by
  cases ty with
  | par t => simp [finiteIntValues?] at h
  | intRange lo hi =>
      simp only [finiteIntValues?, Option.some.injEq] at h
      subst h
      exact nodup_setElems_interval lo hi
  | intSet xs =>
      simp only [finiteIntValues?, Option.some.injEq] at h
      subst h
      exact nodup_sortElems_enum xs
  | setOfIntRange lo hi => simp [finiteIntValues?] at h
  | setOfIntSet xs => simp [finiteIntValues?] at h

/-- Membership in the finite values of the declared type. -/
theorem finiteIntValues?_mem {ty : BasicVarType} {vals : List Int}
    (h : finiteIntValues? ty = some vals) {v : Int}
    (hv : ty.contains (.int v)) : v ∈ vals := by
  cases ty with
  | par t => simp [finiteIntValues?] at h
  | intRange lo hi =>
      simp only [finiteIntValues?, Option.some.injEq] at h
      subst h
      rw [mem_setElems_interval']
      simpa [BasicVarType.contains] using hv
  | intSet xs =>
      simp only [finiteIntValues?, Option.some.injEq] at h
      subst h
      rw [mem_sortElems_enum]
      simpa [BasicVarType.contains] using hv
  | setOfIntRange lo hi => simp [finiteIntValues?] at h
  | setOfIntSet xs => simp [finiteIntValues?] at h

/-- A declaration of `x` in a duplicate-free variable list determines the
    universe lookup. -/
theorem modelSetUniverse?_go_eq_of_mem {ds : List VarDeclItem}
    {ty : BasicVarType} {x : String} {anns : List Annotation}
    {init : Option BasicExpr}
    (hnd : (ds.map (fun d => d.name.name)).Nodup)
    (hd : (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ ds) :
    modelSetUniverse?.go x ds = setUniverse? ty := by
  induction ds with
  | nil => cases hd
  | cons d rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hnd'⟩ := hnd
      cases d with
      | array ty' n' anns' es =>
          have hd' : (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ rest := by
            rcases List.mem_cons.mp hd with h | h
            · cases h
            · exact h
          simp only [modelSetUniverse?.go]
          exact ih hnd' hd'
      | basic ty' n' anns' init' =>
          by_cases hx : n'.name = x
          · rcases List.mem_cons.mp hd with h | h
            · cases h
              simp [modelSetUniverse?.go]
            · exfalso
              have hnot' : x ∉ rest.map (fun d => d.name.name) := by
                simpa [VarDeclItem.name, hx] using hnot
              exact hnot' (List.mem_map.mpr ⟨_, h, rfl⟩)
          · have hd' : (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ rest := by
              rcases List.mem_cons.mp hd with h | h
              · exfalso
                apply hx
                have := congrArg (fun d => d.name.name) h
                simpa [VarDeclItem.name] using this.symm
              · exact h
            simp only [modelSetUniverse?.go]
            rw [if_neg hx]
            exact ih hnd' hd'

/-- A universe lookup comes from a matching declaration. -/
theorem modelSetUniverse?_go_some : ∀ (ds : List VarDeclItem) (x : String)
    (us : List Int), modelSetUniverse?.go x ds = some us →
    ∃ (ty : BasicVarType) (anns : List Annotation) (init : Option BasicExpr),
      (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ ds ∧
        setUniverse? ty = some us
  | [], x, us, h => by simp [modelSetUniverse?.go] at h
  | d :: ds, x, us, h => by
      cases d with
      | array ty n anns es =>
          simp only [modelSetUniverse?.go] at h
          obtain ⟨ty', anns', init, hd, hun⟩ := modelSetUniverse?_go_some ds x us h
          exact ⟨ty', anns', init, List.mem_cons_of_mem _ hd, hun⟩
      | basic ty n anns init =>
          by_cases hx : n.name = x
          · simp only [modelSetUniverse?.go, if_pos hx] at h
            have hn : n = Ident.mk x := by cases n; simpa using hx
            subst hn
            exact ⟨ty, anns, init, List.mem_cons_self .., h⟩
          · simp only [modelSetUniverse?.go, if_neg hx] at h
            obtain ⟨ty', anns', init', hd, hun⟩ := modelSetUniverse?_go_some ds x us h
            exact ⟨ty', anns', init', List.mem_cons_of_mem _ hd, hun⟩

/-- A universe lookup comes from a matching declaration. -/
theorem modelSetUniverse?_some {m : Model} {x : String} {us : List Int}
    (h : modelSetUniverse? m x = some us) :
    ∃ (ty : BasicVarType) (anns : List Annotation) (init : Option BasicExpr),
      (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ m.variables ∧
        setUniverse? ty = some us := by
  unfold modelSetUniverse? at h
  exact modelSetUniverse?_go_some _ _ _ h

/-- A declared universe is duplicate-free. -/
theorem modelSetUniverse?_nodup {m : Model} {x : String} {us : List Int}
    (h : modelSetUniverse? m x = some us) : us.Nodup := by
  obtain ⟨ty, anns, init, hd, hun⟩ := modelSetUniverse?_some h
  exact setUniverse?_nodup hun

/-- The declared universe is set-typed. -/
theorem modelSetUniverse?_base {m : Model} {x : String} {us : List Int}
    (h : modelSetUniverse? m x = some us) :
    ∃ (ty : BasicVarType) (anns : List Annotation) (init : Option BasicExpr),
      (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ m.variables ∧
        ty.base = .setOfInt := by
  obtain ⟨ty, anns, init, hd, hun⟩ := modelSetUniverse?_some h
  exact ⟨ty, anns, init, hd, setUniverse?_base hun⟩

/-- Membership in a declared universe from an admitted set value. -/
theorem modelSetUniverse?_mem_of_contains {m : Model} {S : String}
    {ty : BasicVarType} {anns : List Annotation} {us : List Int}
    {v : Int} {sv : IntSetValue} {init : Option BasicExpr}
    (hnd : (m.variables.map (fun d => d.name.name)).Nodup)
    (hd : (.basic ty (Ident.mk S) anns init : VarDeclItem) ∈ m.variables)
    (huni : modelSetUniverse? m S = some us)
    (hcont : ty.contains (.setOfInt sv)) (hv : sv.Contains v) : v ∈ us := by
  unfold modelSetUniverse? at huni
  have heq := modelSetUniverse?_go_eq_of_mem hnd hd
  rw [heq] at huni
  exact (setUniverse?_mem huni).mpr ⟨sv, hcont, hv⟩

/-- A finite-value lookup comes from a matching declaration. -/
theorem modelIntValues?_go_some : ∀ (ds : List VarDeclItem) (x : String)
    (vals : List Int), modelIntValues?.go x ds = some vals →
    ∃ (ty : BasicVarType) (anns : List Annotation) (init : Option BasicExpr),
      (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ ds ∧
        finiteIntValues? ty = some vals
  | [], x, vals, h => by simp [modelIntValues?.go] at h
  | d :: ds, x, vals, h => by
      cases d with
      | array ty n anns es =>
          simp only [modelIntValues?.go] at h
          obtain ⟨ty', anns', init, hd, hun⟩ := modelIntValues?_go_some ds x vals h
          exact ⟨ty', anns', init, List.mem_cons_of_mem _ hd, hun⟩
      | basic ty n anns init =>
          by_cases hx : n.name = x
          · simp only [modelIntValues?.go, if_pos hx] at h
            have hn : n = Ident.mk x := by cases n; simpa using hx
            subst hn
            exact ⟨ty, anns, init, List.mem_cons_self .., h⟩
          · simp only [modelIntValues?.go, if_neg hx] at h
            obtain ⟨ty', anns', init', hd, hun⟩ := modelIntValues?_go_some ds x vals h
            exact ⟨ty', anns', init', List.mem_cons_of_mem _ hd, hun⟩

/-- A finite-value lookup comes from a matching declaration. -/
theorem modelIntValues?_some {m : Model} {x : String} {vals : List Int}
    (h : modelIntValues? m x = some vals) :
    ∃ (ty : BasicVarType) (anns : List Annotation) (init : Option BasicExpr),
      (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ m.variables ∧
        finiteIntValues? ty = some vals := by
  unfold modelIntValues? at h
  exact modelIntValues?_go_some _ _ _ h

/-- A declaration of `x` in a duplicate-free variable list determines the
    finite integer values lookup. -/
theorem modelIntValues?_go_eq_of_mem {ds : List VarDeclItem}
    {ty : BasicVarType} {x : String} {anns : List Annotation}
    {init : Option BasicExpr}
    (hnd : (ds.map (fun d => d.name.name)).Nodup)
    (hd : (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ ds) :
    modelIntValues?.go x ds = finiteIntValues? ty := by
  induction ds with
  | nil => cases hd
  | cons d rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hnot, hnd'⟩ := hnd
      cases d with
      | array ty' n' anns' es =>
          have hd' : (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ rest := by
            rcases List.mem_cons.mp hd with h | h
            · cases h
            · exact h
          simp only [modelIntValues?.go]
          exact ih hnd' hd'
      | basic ty' n' anns' init' =>
          by_cases hx : n'.name = x
          · rcases List.mem_cons.mp hd with h | h
            · cases h
              simp only [modelIntValues?.go]
              rfl
            · exfalso
              have hnot' : x ∉ rest.map (fun d => d.name.name) := by
                simpa [VarDeclItem.name, hx] using hnot
              exact hnot' (List.mem_map.mpr ⟨_, h, rfl⟩)
          · have hd' : (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ rest := by
              rcases List.mem_cons.mp hd with h | h
              · exfalso
                apply hx
                have := congrArg (fun d => d.name.name) h
                simpa [VarDeclItem.name] using this.symm
              · exact h
            simp only [modelIntValues?.go]
            rw [if_neg hx]
            exact ih hnd' hd'

/-- A finite-value lookup is duplicate-free. -/
theorem modelIntValues?_nodup {m : Model} {x : String} {vals : List Int}
    (h : modelIntValues? m x = some vals) : vals.Nodup := by
  obtain ⟨ty, anns, init, hd, hv⟩ := modelIntValues?_some h
  exact finiteIntValues?_nodup hv

/-- Membership in the finite values from an admitted integer value. -/
theorem modelIntValues?_mem_of_contains {m : Model} {x : String}
    {ty : BasicVarType} {anns : List Annotation} {vals : List Int}
    {v : Int} {init : Option BasicExpr}
    (hnd : (m.variables.map (fun d => d.name.name)).Nodup)
    (hd : (.basic ty (Ident.mk x) anns init : VarDeclItem) ∈ m.variables)
    (hvals : modelIntValues? m x = some vals)
    (hcont : ty.contains (.int v)) : v ∈ vals := by
  unfold modelIntValues? at hvals
  have heq := modelIntValues?_go_eq_of_mem hnd hd
  rw [heq] at hvals
  exact finiteIntValues?_mem hvals hcont

/-! ## The canonical element list of a set value -/

/-- Membership in the sorted element list is set membership. -/
theorem mem_sortElems_setValue {sv : IntSetValue} {x : Int} :
    x ∈ sv.sortElems ↔ sv.Contains x := by
  cases sv with
  | enumeration xs =>
      show x ∈ xs.eraseDups.mergeSort (fun a b => decide (a ≤ b)) ↔ x ∈ xs
      rw [List.mem_mergeSort, List.mem_eraseDups]
  | interval lo hi =>
      show x ∈ (if hi < lo then [] else
        List.map (fun k : Nat => lo + (k : Int))
          (List.range ((hi - lo + 1).toNat))) ↔ lo ≤ x ∧ x ≤ hi
      exact mem_setElems_interval'

/-- The sorted element list is duplicate-free. -/
theorem sortElems_nodup_setValue (sv : IntSetValue) : sv.sortElems.Nodup := by
  cases sv with
  | enumeration xs => exact nodup_sortElems_enum xs
  | interval lo hi => exact nodup_setElems_interval lo hi

/-- The cardinality is the length of the sorted element list. -/
theorem card_eq_sortElems_length_setValue (sv : IntSetValue) :
    sv.card = sv.sortElems.length := by
  cases sv with
  | enumeration xs =>
      show xs.eraseDups.length =
        (xs.eraseDups.mergeSort (fun a b => decide (a ≤ b))).length
      rw [List.length_mergeSort]
  | interval lo hi =>
      show (if hi < lo then 0 else (hi - lo + 1).toNat) =
        (if hi < lo then [] else
          List.map (fun k : Nat => lo + (k : Int))
            (List.range ((hi - lo + 1).toNat))).length
      by_cases h : hi < lo
      · simp [h]
      · simp [h, List.length_map, List.length_range]

/-- Counting the elements of a duplicate-free covering universe gives the
    cardinality of the set. -/
theorem filter_contains_length_eq_card {us : List Int} {sv : IntSetValue}
    (hnd : us.Nodup) (hcover : ∀ x, sv.Contains x → x ∈ us) :
    (us.filter (fun v => decide (sv.Contains v))).length = sv.card := by
  have hl : (us.filter (fun v => decide (sv.Contains v))).Nodup :=
    List.filter_sublist.nodup hnd
  have hperm : (us.filter (fun v => decide (sv.Contains v))).Perm sv.sortElems := by
    rw [List.perm_ext_iff_of_nodup hl (sortElems_nodup_setValue sv)]
    intro a
    rw [List.mem_filter, decide_eq_true_iff, mem_sortElems_setValue]
    exact ⟨fun h => h.2, fun h => ⟨hcover a h, h⟩⟩
  calc (us.filter (fun v => decide (sv.Contains v))).length
      = sv.sortElems.length := hperm.length_eq
    _ = sv.card := (card_eq_sortElems_length_setValue sv).symm

/-- The sum of the indicator of a predicate over a list is the length of
    the filtered list. -/
theorem sum_ite_one_zero (xs : List Int) (p : Int → Bool) :
    (xs.map (fun v => if p v then (1 : Int) else 0)).sum =
      (xs.filter p).length := by
  induction xs with
  | nil => simp
  | cons a as ih =>
      by_cases h : p a = true
      · simp [h, ih]
        omega
      · have h' : p a = false := by cases hp : p a <;> simp_all
        simp [h', ih]

/-! ## Dependencies and interpretation of auxiliaries -/

/-- The names an auxiliary's functional definition reads. -/
def ShapeAux.deps : ShapeAux → List String
  | ⟨_, _, .member S _⟩ => [S]
  | ⟨_, _, .eq x _⟩ => [x]
  | ⟨_, _, .and x y⟩ => [x, y]
  | ⟨_, _, .bit x⟩ => [x]
  | ⟨_, _, .const _⟩ => []

/-- The functional value of an auxiliary depends only on its dependencies. -/
theorem ShapeAux.value_ext {a : ShapeAux} {s t : Store}
    (h : ∀ x ∈ a.deps, s (Ident.mk x) = t (Ident.mk x)) :
    a.value s = a.value t := by
  cases a with
  | mk n ty k =>
      cases k with
      | member S v =>
          simp only [ShapeAux.deps] at h
          simp only [ShapeAux.value]
          rw [h S List.mem_cons_self]
      | eq x v =>
          simp only [ShapeAux.deps] at h
          simp only [ShapeAux.value]
          rw [h x List.mem_cons_self]
      | «and» x y =>
          simp only [ShapeAux.deps, List.mem_cons, List.mem_singleton] at h
          simp only [ShapeAux.value]
          rw [h x (Or.inl rfl), h y (Or.inr (Or.inl rfl))]
      | bit x =>
          simp only [ShapeAux.deps] at h
          simp only [ShapeAux.value]
          rw [h x List.mem_cons_self]
      | const v => rfl

/-- An update at a name outside an auxiliary's dependencies leaves its
    functional value unchanged. -/
theorem ShapeAux.value_update {a : ShapeAux} {s : Store} {y : Ident} {v : Option Value}
    (hdeps : y.name ∉ a.deps) :
    a.value (fun x => if x = y then v else s x) = a.value s := by
  apply ShapeAux.value_ext
  intro x hx
  have hxy : Ident.mk x ≠ y := by
    intro h
    have hxe : x = y.name := by simpa using congrArg Ident.name h
    exact hdeps (hxe ▸ hx)
  simp [hxy]

/-- A defined auxiliary stays defined after an update outside its name
    and dependencies. -/
theorem ShapeAux.defined_update {a : ShapeAux} {s : Store} {y : Ident} {v : Option Value}
    (h : a.defined s) (hname : y.name ≠ a.name) (hdeps : y.name ∉ a.deps) :
    a.defined (fun x => if x = y then v else s x) := by
  unfold ShapeAux.defined at h ⊢
  rw [ShapeAux.value_update hdeps]
  have hxy : Ident.mk a.name ≠ y := by
    intro heq
    exact hname (by simpa using (congrArg Ident.name heq).symm)
  simp [hxy, h]

/-- A store satisfies every constraint accumulated in a shape state. -/
def ShapeState.Holds (s : Store) (st : ShapeState) : Prop :=
  ∀ c ∈ st.cons, c.Holds fullInterp s

/-- Every auxiliary's functional definition holds in the store. -/
def ShapeState.DefHolds (s : Store) (st : ShapeState) : Prop :=
  ∀ a ∈ st.aux, a.definition.Holds fullInterp s

/-- Definition satisfaction is inherited by older states. -/
theorem ShapeState.DefHolds.mono {st st' : ShapeState} {s : Store}
    (hsub : ∀ a ∈ st.aux, a ∈ st'.aux) (h : st'.DefHolds s) : st.DefHolds s :=
  fun a ha => h a (hsub a ha)

/-- Every auxiliary is functionally defined in the store. -/
def ShapeState.Defined (s : Store) (st : ShapeState) : Prop :=
  ∀ a ∈ st.aux, a.defined s

/-- Every auxiliary's definition is among the emitted constraints. -/
def ShapeState.Defs (st : ShapeState) : Prop :=
  ∀ a ∈ st.aux, a.definition ∈ st.cons

/-- The declarations are exactly the auxiliaries' declarations, in the
    same (reverse allocation) order. -/
def ShapeState.AuxDecls (st : ShapeState) : Prop :=
  st.decls = st.aux.map (fun a =>
    (VarDeclItem.basic a.ty (Ident.mk a.name) [] none))

/-- The auxiliary names are distinct. -/
def ShapeState.AuxNodup (st : ShapeState) : Prop :=
  (st.aux.map (fun a => a.name)).Nodup

/-- Every auxiliary name avoids the taken names. -/
def ShapeState.NamesAvoid (taken : List String) (st : ShapeState) : Prop :=
  ∀ a ∈ st.aux, a.name ∉ taken

/-- Along the (reverse allocation) auxiliary list, every dependency is a
    taken name or an older auxiliary. -/
def ShapeAux.depsOk (taken : List String) : List ShapeAux → Prop
  | [] => True
  | a :: rest =>
      (∀ d ∈ a.deps, d ∈ taken ∨ d ∈ rest.map (fun b => b.name)) ∧
        depsOk taken rest

/-- A membership auxiliary reads a declared set variable with a finite
    universe; an equality auxiliary reads a declared finite integer
    variable. -/
def ShapeKind.WellKind (m : Model) : ShapeKind → Prop
  | .member S _ => ∃ us, modelSetUniverse? m S = some us
  | .eq x _ => ∃ vs, modelIntValues? m x = some vs
  | _ => True

/-- The well-kindedness of one auxiliary. -/
def ShapeAux.WellKind (m : Model) (a : ShapeAux) : Prop :=
  ShapeKind.WellKind m a.kind

/-- The declared type of an auxiliary agrees with its kind: `bool2int`
    aliases are `0..1` integers, everything else is Boolean. -/
def ShapeAux.TyOk (a : ShapeAux) : Prop :=
  match a.kind with
  | .bit _ => a.ty = .intRange 0 1
  | _ => a.ty = .par .bool

/-- The names a shape kind reads as source variables. -/
def ShapeKind.sourceDeps : ShapeKind → List String
  | .member S _ => [S]
  | .eq x _ => [x]
  | _ => []

/-- The names a shape kind reads as older auxiliaries. -/
def ShapeKind.auxDeps : ShapeKind → List String
  | .and x y => [x, y]
  | .bit x => [x]
  | _ => []

/-- The names a shape kind's functional definition reads. -/
def ShapeKind.deps (k : ShapeKind) : List String :=
  k.sourceDeps ++ k.auxDeps

/-- The dependency list of an auxiliary is its kind's dependency list. -/
theorem ShapeAux.deps_mk (n : String) (ty : BasicVarType) (k : ShapeKind) :
    (⟨n, ty, k⟩ : ShapeAux).deps = k.deps := by
  cases k <;> rfl

/-- Source reads are taken names and auxiliary reads are older Boolean
    auxiliaries. -/
def ShapeAux.KindDeps (taken : List String) : List ShapeAux → Prop
  | [] => True
  | a :: rest =>
      (∀ d ∈ a.kind.sourceDeps, d ∈ taken) ∧
        (∀ d ∈ a.kind.auxDeps,
          ∃ c ∈ rest, c.name = d ∧ c.ty = .par .bool) ∧
        KindDeps taken rest

/-- All auxiliaries have the type dictated by their kind. -/
def ShapeState.TyOk (st : ShapeState) : Prop :=
  ∀ a ∈ st.aux, a.TyOk

/-- The length of a short shape-aux name. -/
theorem shapeAuxName_length (bound n : Nat) :
    (shapeAuxName bound n).length = 5 + (bound + 1) + (Nat.repr n).length := by
  unfold shapeAuxName
  rw [String.length_append, String.length_append, dollarRun_length]
  rfl

/-- A short shape-aux name is longer than every taken name, hence not
    taken itself. -/
theorem shapeAuxName_not_mem {taken : List String} {n : Nat} :
    shapeAuxName (maxStrLength taken) n ∉ taken := by
  intro hmem
  have hge := maxStrLength_ge taken _ hmem
  have hlen := shapeAuxName_length (maxStrLength taken) n
  have hpos := Nat.length_repr_pos (n := n)
  rw [hlen] at hge
  omega

/-- Distinct counters give distinct short shape-aux names. -/
theorem shapeAuxName_inj {bound n n' : Nat}
    (h : shapeAuxName bound n = shapeAuxName bound n') : n = n' := by
  let p := "_aux_" ++ dollarRun (bound + 1)
  have hp : shapeAuxName bound n = p ++ Nat.repr n := rfl
  have hp' : shapeAuxName bound n' = p ++ Nat.repr n' := rfl
  rw [hp, hp'] at h
  have hlist := congrArg String.toList h
  simp only [String.toList_append] at hlist
  have hrep : Nat.repr n = Nat.repr n' :=
    String.toList_injective (List.append_cancel_left hlist)
  exact Nat.repr_injective hrep

/-- Auxiliary names are an injective `shapeAuxName` family below the
    counter. -/
def ShapeState.AuxIdx (taken : List String) (st : ShapeState) : Prop :=
  ∃ js : List Nat,
    js.Nodup ∧
    (∀ j ∈ js, j < st.next) ∧
    st.aux.map (fun a => a.name) =
      js.map (fun j => shapeAuxName (maxStrLength taken) j)

/-- The static invariant of a shape state: definitions, declarations,
    freshness, acyclic dependencies and well-kinded source reads. -/
structure ShapeState.WF (taken : List String) (m : Model) (st : ShapeState) : Prop where
  defs : st.Defs
  auxDecls : st.AuxDecls
  auxIdx : st.AuxIdx taken
  maxLen : st.maxLen = maxStrLength taken
  depsOk : ShapeAux.depsOk taken st.aux
  kindDeps : ShapeAux.KindDeps taken st.aux
  tyOk : st.TyOk
  wellKind : ∀ a ∈ st.aux, a.WellKind m

/-- State satisfaction gives every auxiliary definition. -/
theorem ShapeState.DefHolds.of_holds {taken : List String} {m : Model}
    {st : ShapeState} {s : Store} (hwf : st.WF taken m) (h : st.Holds s) :
    st.DefHolds s :=
  fun a ha => h _ (hwf.defs a ha)

/-- Interpret a newest-first auxiliary list: older auxiliaries first, then
    each newer auxiliary by its functional value. -/
def encodeAuxStore (s : Store) : List ShapeAux → Store
  | [] => s
  | a :: rest =>
      let s0 := encodeAuxStore s rest
      fun x => if x = Ident.mk a.name then a.value s0 else s0 x

/-- The store determined by a shape state. -/
def ShapeState.encStore (st : ShapeState) (s : Store) : Store :=
  encodeAuxStore s st.aux

/-- The interpreted store agrees with the source store outside the
    auxiliary names. -/
theorem encodeAuxStore_not_mem (s : Store) :
    ∀ (as : List ShapeAux) (x : Ident),
      x.name ∉ as.map (fun a => a.name) → encodeAuxStore s as x = s x := by
  intro as
  induction as with
  | nil => intro x _; rfl
  | cons a rest ih =>
      intro x hx
      simp only [List.map_cons, List.mem_cons, not_or] at hx
      obtain ⟨hxa, hxr⟩ := hx
      dsimp only [encodeAuxStore]
      have hxy : x ≠ Ident.mk a.name := by
        intro h
        exact hxa (by simpa using congrArg Ident.name h)
      rw [if_neg hxy]
      exact ih x hxr

/-- The interpreted store gives the newest auxiliary its functional value. -/
theorem encodeAuxStore_self (s : Store) (a : ShapeAux) (rest : List ShapeAux) :
    encodeAuxStore s (a :: rest) (Ident.mk a.name) =
      a.value (encodeAuxStore s rest) := by
  dsimp only [encodeAuxStore]
  simp

/-- In the reverse-allocation list `a :: rest`, adding the newer auxiliary
    `a` does not change the interpretation at any other name. -/
theorem encodeAuxStore_cons_not_mem (s : Store) (a : ShapeAux) (rest : List ShapeAux)
    {x : Ident} (hx : x.name ≠ a.name) :
    encodeAuxStore s (a :: rest) x = encodeAuxStore s rest x := by
  dsimp only [encodeAuxStore]
  have hxy : x ≠ Ident.mk a.name := by
    intro h
    exact hx (by simpa using congrArg Ident.name h)
  rw [if_neg hxy]

/-- The interpretation is unchanged by prepending extra newer auxiliaries,
    at a name that belongs to the older auxiliary list. -/
theorem encodeAuxStore_append_not_mem (s : Store) (as : List ShapeAux) :
    ∀ (extra : List ShapeAux) (x : Ident),
      x.name ∈ as.map (fun a => a.name) →
      (∀ a ∈ extra, a.name ≠ x.name) →
      encodeAuxStore s (extra ++ as) x = encodeAuxStore s as x := by
  intro extra
  induction extra with
  | nil => intro x _ _; rfl
  | cons e rest ih =>
      intro x hx hne
      have hne' : x.name ≠ e.name := fun h => hne e List.mem_cons_self h.symm
      rw [List.cons_append, encodeAuxStore_cons_not_mem s e (rest ++ as) hne']
      exact ih x hx (fun a ha => hne a (List.mem_cons_of_mem _ ha))

/-- A dependency of an auxiliary of a state is a taken name or the name of
    another auxiliary of the state. -/
theorem ShapeAux.depsOk_mem {taken : List String} :
    ∀ {as : List ShapeAux} {a : ShapeAux}, ShapeAux.depsOk taken as → a ∈ as →
      ∀ d ∈ a.deps, d ∈ taken ∨ d ∈ as.map (fun b => b.name)
  | [], _, _, ha => by cases ha
  | b :: rest, a, hdeps, ha => by
      obtain ⟨hdepb, hdepsr⟩ := hdeps
      rcases List.mem_cons.mp ha with rfl | harest
      · intro d hd
        rcases hdepb d hd with hin | hin
        · exact Or.inl hin
        · exact Or.inr (List.mem_cons_of_mem _ hin)
      · intro d hd
        rcases ShapeAux.depsOk_mem hdepsr harest d hd with hin | hin
        · exact Or.inl hin
        · exact Or.inr (List.mem_cons_of_mem _ hin)

/-- Every auxiliary is defined in the interpreted store. -/
theorem encodeAuxStore_defined (s : Store) :
    ∀ (taken : List String) (as : List ShapeAux),
      (as.map (fun a => a.name)).Nodup →
      ShapeAux.depsOk taken as →
      (∀ a ∈ as, a.name ∉ taken) →
      ∀ a ∈ as, a.defined (encodeAuxStore s as) := by
  intro taken as
  induction as with
  | nil => intro _ _ _ a ha; cases ha
  | cons b rest ih =>
      intro hnd hdeps hnames a ha
      obtain ⟨hdepb, hdepsr⟩ := hdeps
      have hnd' : (rest.map (fun a => a.name)).Nodup := (List.nodup_cons.mp hnd).2
      have hbnot : b.name ∉ rest.map (fun b => b.name) := (List.nodup_cons.mp hnd).1
      have hbnames : b.name ∉ taken := hnames b List.mem_cons_self
      have hnames' : ∀ c ∈ rest, c.name ∉ taken :=
        fun c hc => hnames c (List.mem_cons_of_mem _ hc)
      rcases List.mem_cons.mp ha with heq | harest
      · -- the newest auxiliary: its value is read before `b` is added
        subst a
        unfold ShapeAux.defined
        rw [encodeAuxStore_self]
        apply Eq.symm
        apply ShapeAux.value_ext
        intro d hd
        apply encodeAuxStore_cons_not_mem
        intro heq
        have hdb : d = b.name := by simpa using heq
        rcases hdepb d hd with hin | hin
        · exact hbnames (hdb ▸ hin)
        · exact hbnot (hdb ▸ hin)
      · -- an older auxiliary: adding `b` does not touch it
        have hdefr : ∀ c ∈ rest, c.defined (encodeAuxStore s rest) :=
          ih hnd' hdepsr hnames'
        have hmem : a.name ∈ rest.map (fun c => c.name) :=
          List.mem_map.mpr ⟨a, harest, rfl⟩
        have haneb : a.name ≠ b.name := fun h => hbnot (h ▸ hmem)
        have hdv : encodeAuxStore s rest (Ident.mk a.name) =
            a.value (encodeAuxStore s rest) := hdefr a harest
        unfold ShapeAux.defined
        rw [encodeAuxStore_cons_not_mem s b rest (x := Ident.mk a.name)
          (by simpa using haneb), hdv]
        apply Eq.symm
        apply ShapeAux.value_ext
        intro d hd
        apply encodeAuxStore_cons_not_mem
        intro heq
        have hdb : d = b.name := by simpa using heq
        rcases ShapeAux.depsOk_mem hdepsr harest d hd with hin | hin
        · exact hbnames (hdb ▸ hin)
        · exact hbnot (hdb ▸ hin)

/-! ## Consequences of the name invariant -/

/-- The auxiliary names of an index-family state are duplicate-free. -/
theorem ShapeState.AuxIdx.names_nodup {taken : List String} {st : ShapeState}
    (h : st.AuxIdx taken) : (st.aux.map (fun a => a.name)).Nodup := by
  obtain ⟨js, hjs, _, heq⟩ := h
  rw [heq]
  exact List.Pairwise.map (shapeAuxName (maxStrLength taken))
    (fun a b hab hf => hab (shapeAuxName_inj hf)) hjs

/-- Every auxiliary name is a `shapeAuxName` slot below the counter. -/
theorem ShapeState.AuxIdx.name_mem {taken : List String} {st : ShapeState}
    (h : st.AuxIdx taken) {a : ShapeAux} (ha : a ∈ st.aux) :
    ∃ j, j < st.next ∧ a.name = shapeAuxName (maxStrLength taken) j := by
  obtain ⟨js, _, hlt, heq⟩ := h
  have hmem : a.name ∈ js.map (fun j => shapeAuxName (maxStrLength taken) j) := by
    rw [← heq]
    exact List.mem_map.mpr ⟨a, ha, rfl⟩
  obtain ⟨j, hj, hja⟩ := List.mem_map.mp hmem
  exact ⟨j, hlt j hj, hja.symm⟩

/-- An auxiliary name is never a taken source name. -/
theorem ShapeState.AuxIdx.name_not_mem_taken {taken : List String} {st : ShapeState}
    (h : st.AuxIdx taken) {a : ShapeAux} (ha : a ∈ st.aux)
    (ht : a.name ∈ taken) : False := by
  obtain ⟨j, _, hj⟩ := h.name_mem ha
  exact shapeAuxName_not_mem (hj ▸ ht)

/-- A well-formed state has duplicate-free auxiliary names. -/
theorem ShapeState.WF.auxNodup {taken : List String} {m : Model} {st : ShapeState}
    (h : st.WF taken m) : st.AuxNodup :=
  h.auxIdx.names_nodup

/-- A well-formed state's auxiliary names avoid all taken names. -/
theorem ShapeState.WF.namesAvoid {taken : List String} {m : Model} {st : ShapeState}
    (h : st.WF taken m) : st.NamesAvoid taken := by
  intro a ha ht
  exact h.auxIdx.name_not_mem_taken ha ht

/-- The interpreted store is unchanged by newer auxiliaries at any name
    that is taken or belongs to the older auxiliary list. -/
theorem ShapeState.encodeStore_extends {taken : List String} {st st' : ShapeState}
    {s : Store}
    (hpre : ∃ extra, st'.aux = extra ++ st.aux)
    (hidx : st'.AuxIdx taken)
    {x : Ident}
    (hx : x.name ∈ taken ∨ x.name ∈ st.aux.map (fun a => a.name)) :
    encodeAuxStore s st'.aux x = encodeAuxStore s st.aux x := by
  obtain ⟨extra, hextra⟩ := hpre
  obtain ⟨js, hjs, hlt, heq⟩ := hidx
  rw [hextra] at heq
  have hnd : ((extra ++ st.aux).map (fun a => a.name)).Nodup := by
    rw [heq]
    exact List.Pairwise.map (shapeAuxName (maxStrLength taken))
      (fun a b hab hf => hab (shapeAuxName_inj hf)) hjs
  rw [hextra]
  rcases hx with htake | hold
  · -- a taken name is not an auxiliary name at all
    have hnot : x.name ∉ (extra ++ st.aux).map (fun a => a.name) := by
      intro hmem
      rw [heq] at hmem
      obtain ⟨j, _, hja⟩ := List.mem_map.mp hmem
      exact shapeAuxName_not_mem (hja ▸ htake)
    have hnotold : x.name ∉ st.aux.map (fun a => a.name) := by
      intro hmem
      apply hnot
      rw [List.map_append]
      exact List.mem_append.mpr (Or.inr hmem)
    rw [encodeAuxStore_not_mem s (extra ++ st.aux) x hnot,
      encodeAuxStore_not_mem s st.aux x hnotold]
  · -- an older auxiliary name is untouched by the newer prefix
    have hnd' := hnd
    rw [List.map_append] at hnd'
    have hndisj := (List.nodup_append.mp hnd').2.2
    have hdisj : ∀ a ∈ extra, a.name ≠ x.name := by
      intro a ha han
      exact hndisj a.name (List.mem_map.mpr ⟨a, ha, rfl⟩) x.name hold han
    exact encodeAuxStore_append_not_mem s st.aux extra x hold hdisj

/-! ## Preservation of the state invariant -/

/-- The names a defining constraint mentions are the kind's dependencies
    and the auxiliary's own name. -/
theorem constraintNames_definition (a : ShapeAux) :
    constraintNames a.definition = a.deps ++ [a.name] := by
  cases a with
  | mk n ty k =>
      cases k <;>
        simp [ShapeAux.definition, ShapeKind.deps, ShapeAux.deps,
          constraintNames, exprNames, basicNames, pinBoolConstraint,
          shapeConstraint, shapeE, shapeInt, shapeName]

/-- Emitting a constraint preserves well-formedness. -/
theorem ShapeState.emit_wf {taken : List String} {m : Model} {st : ShapeState}
    {c : ConstraintItem} (hwf : st.WF taken m) :
    (st.emit c).WF taken m := by
  have hcons : (st.emit c).cons = c :: st.cons := rfl
  have haux : (st.emit c).aux = st.aux := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ShapeState.Defs
    rw [hcons, haux]
    intro a ha
    exact List.mem_cons_of_mem _ (hwf.defs a ha)
  · exact hwf.auxDecls
  · exact hwf.auxIdx
  · exact hwf.maxLen
  · exact hwf.depsOk
  · exact hwf.kindDeps
  · exact hwf.tyOk
  · exact hwf.wellKind

/-- Emitting a list of constraints preserves well-formedness. -/
theorem ShapeState.emitList_wf {taken : List String} {m : Model} {st : ShapeState}
    {cs : List ConstraintItem} (hwf : st.WF taken m) :
    (st.emitList cs).WF taken m := by
  have hcons : (st.emitList cs).cons = cs.reverse ++ st.cons := rfl
  have haux : (st.emitList cs).aux = st.aux := rfl
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ShapeState.Defs
    rw [hcons, haux]
    intro a ha
    exact List.mem_append.mpr (Or.inr (hwf.defs a ha))
  · exact hwf.auxDecls
  · exact hwf.auxIdx
  · exact hwf.maxLen
  · exact hwf.depsOk
  · exact hwf.kindDeps
  · exact hwf.tyOk
  · exact hwf.wellKind

/-- A fresh Boolean auxiliary preserves well-formedness, given that its
    dependencies are taken names or existing auxiliary names and that it
    reads only well-kinded source variables. -/
theorem ShapeState.freshBool_wf {taken : List String} {m : Model} {st : ShapeState}
    (hwf : st.WF taken m) (kind : ShapeKind)
    (hdeps : ∀ d ∈ kind.deps, d ∈ taken ∨ d ∈ st.aux.map (fun a => a.name))
    (hsrc : ∀ d ∈ kind.sourceDeps, d ∈ taken)
    (hauxdeps : ∀ d ∈ kind.auxDeps,
      ∃ c ∈ st.aux, c.name = d ∧ c.ty = .par .bool)
    (hty : ShapeAux.TyOk
      { name := shapeAuxName st.maxLen st.next, ty := .par .bool, kind := kind })
    (hkind : ShapeKind.WellKind m kind) :
    (st.freshBool taken kind).2.WF taken m := by
  let n := shapeAuxName st.maxLen st.next
  let a : ShapeAux := { name := n, ty := .par .bool, kind := kind }
  have haux : (st.freshBool taken kind).2.aux = a :: st.aux := rfl
  have hcons : (st.freshBool taken kind).2.cons = a.definition :: st.cons := rfl
  have hdecls : (st.freshBool taken kind).2.decls =
      VarDeclItem.basic a.ty (Ident.mk a.name) [] none :: st.decls := rfl
  have hnext : (st.freshBool taken kind).2.next = st.next + 1 := rfl
  have hadeps : a.deps = kind.deps := ShapeAux.deps_mk n (.par .bool) kind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ShapeState.Defs
    rw [haux, hcons]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hbold
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hwf.defs b hbold)
  · unfold ShapeState.AuxDecls
    rw [haux, hdecls, hwf.auxDecls]
    rfl
  · unfold ShapeState.AuxIdx
    obtain ⟨js, hjs, hlt, heq⟩ := hwf.auxIdx
    refine ⟨st.next :: js, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun h => absurd (hlt st.next h) (by omega), hjs⟩
    · intro j hj
      rw [hnext]
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := hlt j hj; omega
    · rw [haux]
      show shapeAuxName st.maxLen st.next :: st.aux.map (fun a => a.name) =
        shapeAuxName (maxStrLength taken) st.next ::
          js.map (fun j => shapeAuxName (maxStrLength taken) j)
      rw [heq, hwf.maxLen]
  · exact hwf.maxLen
  · unfold ShapeAux.depsOk
    rw [haux]
    refine ⟨?_, hwf.depsOk⟩
    intro d hd
    have hdepeq : a.deps = kind.deps := ShapeAux.deps_mk n a.ty kind
    exact hdeps d (hdepeq ▸ hd)
  · unfold ShapeAux.KindDeps
    rw [haux]
    refine ⟨?_, ?_, hwf.kindDeps⟩
    · intro d hd
      exact hsrc d (by simpa [a] using hd)
    · intro d hd
      obtain ⟨c, hc, hcname, hcty⟩ := hauxdeps d (by simpa [a] using hd)
      exact ⟨c, hc, hcname, hcty⟩
  · unfold ShapeState.TyOk
    rw [haux]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hbold
    · simpa [a] using hty
    · exact hwf.tyOk b hbold
  · unfold ShapeAux.WellKind
    rw [haux]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hbold
    · simpa [a, ShapeAux.WellKind] using hkind
    · exact hwf.wellKind b hbold

/-- A fresh `0..1` integer auxiliary preserves well-formedness. -/
theorem ShapeState.freshInt01_wf {taken : List String} {m : Model} {st : ShapeState}
    (hwf : st.WF taken m) (kind : ShapeKind)
    (hdeps : ∀ d ∈ kind.deps, d ∈ taken ∨ d ∈ st.aux.map (fun a => a.name))
    (hsrc : ∀ d ∈ kind.sourceDeps, d ∈ taken)
    (hauxdeps : ∀ d ∈ kind.auxDeps,
      ∃ c ∈ st.aux, c.name = d ∧ c.ty = .par .bool)
    (hty : ShapeAux.TyOk
      { name := shapeAuxName st.maxLen st.next, ty := .intRange 0 1, kind := kind })
    (hkind : ShapeKind.WellKind m kind) :
    (st.freshInt01 taken kind).2.WF taken m := by
  let n := shapeAuxName st.maxLen st.next
  let a : ShapeAux := { name := n, ty := .intRange 0 1, kind := kind }
  have haux : (st.freshInt01 taken kind).2.aux = a :: st.aux := rfl
  have hcons : (st.freshInt01 taken kind).2.cons = a.definition :: st.cons := rfl
  have hdecls : (st.freshInt01 taken kind).2.decls =
      VarDeclItem.basic a.ty (Ident.mk a.name) [] none :: st.decls := rfl
  have hnext : (st.freshInt01 taken kind).2.next = st.next + 1 := rfl
  have hadeps : a.deps = kind.deps := ShapeAux.deps_mk n (.intRange 0 1) kind
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold ShapeState.Defs
    rw [haux, hcons]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hbold
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (hwf.defs b hbold)
  · unfold ShapeState.AuxDecls
    rw [haux, hdecls, hwf.auxDecls]
    rfl
  · unfold ShapeState.AuxIdx
    obtain ⟨js, hjs, hlt, heq⟩ := hwf.auxIdx
    refine ⟨st.next :: js, ?_, ?_, ?_⟩
    · rw [List.nodup_cons]
      exact ⟨fun h => absurd (hlt st.next h) (by omega), hjs⟩
    · intro j hj
      rw [hnext]
      rcases List.mem_cons.mp hj with rfl | hj
      · omega
      · have := hlt j hj; omega
    · rw [haux]
      show shapeAuxName st.maxLen st.next :: st.aux.map (fun a => a.name) =
        shapeAuxName (maxStrLength taken) st.next ::
          js.map (fun j => shapeAuxName (maxStrLength taken) j)
      rw [heq, hwf.maxLen]
  · exact hwf.maxLen
  · unfold ShapeAux.depsOk
    rw [haux]
    refine ⟨?_, hwf.depsOk⟩
    intro d hd
    have hdepeq : a.deps = kind.deps := ShapeAux.deps_mk n a.ty kind
    exact hdeps d (hdepeq ▸ hd)
  · unfold ShapeAux.KindDeps
    rw [haux]
    refine ⟨?_, ?_, hwf.kindDeps⟩
    · intro d hd
      exact hsrc d (by simpa [a] using hd)
    · intro d hd
      obtain ⟨c, hc, hcname, hcty⟩ := hauxdeps d (by simpa [a] using hd)
      exact ⟨c, hc, hcname, hcty⟩
  · unfold ShapeState.TyOk
    rw [haux]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hbold
    · simpa [a] using hty
    · exact hwf.tyOk b hbold
  · unfold ShapeAux.WellKind
    rw [haux]
    intro b hb
    rcases List.mem_cons.mp hb with rfl | hbold
    · simpa [a, ShapeAux.WellKind] using hkind
    · exact hwf.wellKind b hbold


/-! ## Evaluating source expressions under the auxiliary store -/

/-- A basic expression whose names are not auxiliary names evaluates the
    same in the auxiliary store. -/
theorem basicNames_eval_encodeAux {s : Store} {as : List ShapeAux} {b : BasicExpr}
    (h : ∀ x ∈ basicNames b, x ∉ as.map (fun a => a.name)) :
    b.eval (encodeAuxStore s as) = b.eval s := by
  cases b with
  | lit l => rfl
  | ident y =>
      have hy : y.name ∉ as.map (fun a => a.name) := by
        simpa [basicNames] using h y.name (by simp [basicNames])
      simp only [BasicExpr.eval]
      exact encodeAuxStore_not_mem s as y hy

/-- An expression whose names are not auxiliary names evaluates the same
    in the auxiliary store. -/
theorem exprNames_eval_encodeAux {s : Store} {as : List ShapeAux} {e : Expr}
    (h : ∀ x ∈ exprNames e, x ∉ as.map (fun a => a.name)) :
    e.eval (encodeAuxStore s as) = e.eval s := by
  cases e with
  | basic b =>
      exact basicNames_eval_encodeAux (by
        intro x hx
        exact h x (by simpa [exprNames] using hx))
  | array es =>
      show (es.mapM (BasicExpr.eval (encodeAuxStore s as))).map Value.array =
        (es.mapM (BasicExpr.eval s)).map Value.array
      have hall : ∀ b ∈ es,
          BasicExpr.eval (encodeAuxStore s as) b = BasicExpr.eval s b := by
        intro b hb
        exact basicNames_eval_encodeAux (by
          intro x hx
          exact h x (by
            simp only [exprNames, List.mem_flatMap]
            exact ⟨b, hb, hx⟩))
      rw [mapM_congr_set hall]

/-- A constraint whose names are not auxiliary names holds in the
    auxiliary store exactly when it holds in the source store. -/
theorem holds_encodeAux_free {s : Store} {as : List ShapeAux}
    {pred : PredicateInterpretation} {c : ConstraintItem}
    (h : ∀ x ∈ constraintNames c, x ∉ as.map (fun a => a.name)) :
    c.Holds pred (encodeAuxStore s as) ↔ c.Holds pred s := by
  have hargs : c.args.mapM (Expr.eval (encodeAuxStore s as)) =
      c.args.mapM (Expr.eval s) := by
    apply mapM_congr_set
    intro e he
    exact exprNames_eval_encodeAux (by
      intro x hx
      exact h x (by
        simp only [constraintNames, List.mem_flatMap]
        exact ⟨e, he, hx⟩))
  unfold ConstraintItem.Holds
  rw [hargs]

/-- A declared source name reads the same in the auxiliary store. -/
theorem ShapeState.encStore_at_taken {taken : List String} {m : Model} {st : ShapeState}
    {s : Store} (hwf : st.WF taken m) {x : Ident} (hx : x.name ∈ taken) :
    st.encStore s x = s x := by
  unfold ShapeState.encStore
  apply encodeAuxStore_not_mem
  intro hmem
  obtain ⟨a, ha, han⟩ := List.mem_map.mp hmem
  exact hwf.namesAvoid a ha (han ▸ hx)

/-! ## Totality of the functional auxiliary values -/

/-- The value of a set-typed source variable is a set value. -/
theorem contains_of_setUniverse {ty : BasicVarType} {us : List Int}
    (h : setUniverse? ty = some us) {v : Value} (hc : ty.contains v) :
    ∃ sv, v = .setOfInt sv := by
  cases ty with
  | par t => simp [setUniverse?] at h
  | intRange lo hi => simp [setUniverse?] at h
  | intSet xs => simp [setUniverse?] at h
  | setOfIntRange lo hi =>
      cases v with
      | bool b => simp [BasicVarType.contains] at hc
      | int i => simp [BasicVarType.contains] at hc
      | setOfInt sv => exact ⟨sv, rfl⟩
      | array xs => simp [BasicVarType.contains] at hc
  | setOfIntSet xs =>
      cases v with
      | bool b => simp [BasicVarType.contains] at hc
      | int i => simp [BasicVarType.contains] at hc
      | setOfInt sv => exact ⟨sv, rfl⟩
      | array xs => simp [BasicVarType.contains] at hc

/-- The value of a finite-domain source integer is an integer value. -/
theorem contains_of_finiteIntValues {ty : BasicVarType} {vals : List Int}
    (h : finiteIntValues? ty = some vals) {v : Value} (hc : ty.contains v) :
    ∃ i, v = .int i := by
  cases ty with
  | par t => simp [finiteIntValues?] at h
  | intRange lo hi =>
      cases v with
      | bool b => simp [BasicVarType.contains] at hc
      | int i => exact ⟨i, rfl⟩
      | setOfInt sv => simp [BasicVarType.contains] at hc
      | array xs => simp [BasicVarType.contains] at hc
  | intSet xs =>
      cases v with
      | bool b => simp [BasicVarType.contains] at hc
      | int i => exact ⟨i, rfl⟩
      | setOfInt sv => simp [BasicVarType.contains] at hc
      | array xs => simp [BasicVarType.contains] at hc
  | setOfIntRange lo hi => simp [finiteIntValues?] at h
  | setOfIntSet xs => simp [finiteIntValues?] at h

/-- A declared basic variable has a value of its declared type in any
    satisfying store. -/
theorem satisfiesDyn_basic {m : Model} {s : Store}
    (hsat : SatisfiesDyn fullInterp m s)
    {ty : BasicVarType} {n : Ident} {anns : List Annotation} {init : Option BasicExpr}
    (hd : (.basic ty n anns init : VarDeclItem) ∈ m.variables) :
    ∃ v, s n = some v ∧ ty.contains v :=
  hsat.2.1 (.basic ty n anns init) hd

/-- A well-typed auxiliary's value lies in its declared type. -/
theorem ShapeAux.value_contains {a : ShapeAux} (hty : a.TyOk) {s : Store} {v : Value}
    (h : a.value s = some v) : a.ty.contains v := by
  obtain ⟨n, ty, k⟩ := a
  cases k with
  | member S w =>
      simp only [ShapeAux.TyOk] at hty
      subst hty
      simp only [ShapeAux.value] at h
      rcases hs : s (Ident.mk S) with _ | b | i | sv | arr
      all_goals simp [hs] at h
      cases h
      trivial
  | eq x w =>
      simp only [ShapeAux.TyOk] at hty
      subst hty
      simp only [ShapeAux.value] at h
      rcases hs : s (Ident.mk x) with _ | b | i | sv | arr
      all_goals simp [hs] at h
      cases h
      trivial
  | «and» x y =>
      simp only [ShapeAux.TyOk] at hty
      subst hty
      simp only [ShapeAux.value] at h
      rcases hx : s (Ident.mk x) with _ | bx | ix | svx | arrx <;>
        rcases hy : s (Ident.mk y) with _ | byy | iy | svy | arry
      all_goals simp [hx, hy] at h
      cases h
      trivial
  | bit x =>
      simp only [ShapeAux.TyOk] at hty
      subst hty
      simp only [ShapeAux.value] at h
      rcases hx : s (Ident.mk x) with _ | bx | ix | svx | arrx
      all_goals simp [hx] at h
      cases h
      by_cases hb : bx <;> simp [BasicVarType.contains, hb]
  | const w =>
      simp only [ShapeAux.TyOk] at hty
      subst hty
      simp only [ShapeAux.value] at h
      cases h
      trivial

/-- A Boolean-typed auxiliary's value is a Boolean. -/
theorem ShapeAux.value_bool_of_ty {a : ShapeAux} (hty : a.ty = .par .bool)
    (htyok : a.TyOk) {s : Store} {v : Value} (h : a.value s = some v) :
    ∃ p, v = .bool p := by
  have hc := ShapeAux.value_contains htyok h
  rw [hty] at hc
  cases v with
  | bool p => exact ⟨p, rfl⟩
  | int i => simp [BasicVarType.contains] at hc
  | setOfInt sv => simp [BasicVarType.contains] at hc
  | array xs => simp [BasicVarType.contains] at hc

theorem ShapeAux.value_member_some {s : Store} {S n : String} {v : Int}
    (hS : ∃ sv, s (Ident.mk S) = some (.setOfInt sv)) :
    (⟨n, .par .bool, .member S v⟩ : ShapeAux).value s ≠ none := by
  obtain ⟨sv, hsv⟩ := hS
  simp [ShapeAux.value, hsv]

theorem ShapeAux.value_eq_some {s : Store} {x n : String} {v : Int}
    (hx : ∃ i, s (Ident.mk x) = some (.int i)) :
    (⟨n, .par .bool, .eq x v⟩ : ShapeAux).value s ≠ none := by
  obtain ⟨i, hi⟩ := hx
  simp [ShapeAux.value, hi]

theorem ShapeAux.value_and_some {s : Store} {x y n : String}
    (hx : ∃ p, s (Ident.mk x) = some (.bool p))
    (hy : ∃ q, s (Ident.mk y) = some (.bool q)) :
    (⟨n, .par .bool, .and x y⟩ : ShapeAux).value s ≠ none := by
  obtain ⟨p, hp⟩ := hx
  obtain ⟨q, hq⟩ := hy
  simp [ShapeAux.value, hp, hq]

theorem ShapeAux.value_bit_some {s : Store} {x n : String}
    (hx : ∃ p, s (Ident.mk x) = some (.bool p)) :
    (⟨n, .intRange 0 1, .bit x⟩ : ShapeAux).value s ≠ none := by
  obtain ⟨p, hp⟩ := hx
  simp [ShapeAux.value, hp]

/-- An older Boolean auxiliary reads as a Boolean in the interpreted
    store. -/
theorem encodeAuxStore_bool_at {taken : List String} {s : Store} {rest : List ShapeAux}
    {d : String}
    (hnd : (rest.map (fun a => a.name)).Nodup)
    (hdeps : ShapeAux.depsOk taken rest)
    (hnames : ∀ a ∈ rest, a.name ∉ taken)
    (hval : ∀ a ∈ rest, a.value (encodeAuxStore s rest) ≠ none)
    (hty : ∀ a ∈ rest, a.TyOk)
    (hmem : ∃ c ∈ rest, c.name = d ∧ c.ty = .par .bool) :
    ∃ p, encodeAuxStore s rest (Ident.mk d) = some (.bool p) := by
  obtain ⟨c, hc, hcd, hcty⟩ := hmem
  have hdef := encodeAuxStore_defined s taken rest hnd hdeps hnames c hc
  have hvalc := hval c hc
  cases hv : c.value (encodeAuxStore s rest) with
  | none => exact absurd hv hvalc
  | some w =>
      obtain ⟨p, rfl⟩ := ShapeAux.value_bool_of_ty hcty (hty c hc) hv
      refine ⟨p, ?_⟩
      unfold ShapeAux.defined at hdef
      rw [hcd, hv] at hdef
      exact hdef

/-- The newest auxiliary's functional value is defined, given source
    satisfaction for its source reads and older Boolean auxiliaries for
    its auxiliary reads. -/
theorem ShapeAux.value_some_head {m : Model} {s : Store} {taken : List String}
    {b : ShapeAux} {rest : List ShapeAux}
    (hvars : (m.variables.map (fun d => d.name.name)).Nodup)
    (hsat : SatisfiesDyn fullInterp m s)
    (hbty : b.TyOk)
    (hwell : b.WellKind m)
    (hsrc : ∀ d ∈ b.kind.sourceDeps, d ∈ taken)
    (haux : ∀ d ∈ b.kind.auxDeps,
      ∃ c ∈ rest, c.name = d ∧ c.ty = .par .bool)
    (hval : ∀ c ∈ rest, c.value (encodeAuxStore s rest) ≠ none)
    (hty : ∀ c ∈ rest, c.TyOk)
    (hnd : (rest.map (fun a => a.name)).Nodup)
    (hdeps : ShapeAux.depsOk taken rest)
    (hnames : ∀ c ∈ rest, c.name ∉ taken) :
    b.value (encodeAuxStore s rest) ≠ none := by
  obtain ⟨bn, bty, bk⟩ := b
  cases bk with
  | member S v =>
      simp only [ShapeAux.TyOk] at hbty
      subst hbty
      have hS : S ∈ taken := hsrc S (by simp [ShapeKind.sourceDeps])
      have hSnot : S ∉ rest.map (fun a => a.name) := by
        intro hmem
        obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hmem
        exact hnames c hc (hcn ▸ hS)
      have hSrest : encodeAuxStore s rest (Ident.mk S) = s (Ident.mk S) :=
        encodeAuxStore_not_mem s rest (Ident.mk S) hSnot
      have huni : ∃ us, modelSetUniverse? m S = some us := by
        simpa [ShapeAux.WellKind, ShapeKind.WellKind] using hwell
      obtain ⟨us, hus⟩ := huni
      obtain ⟨ty, anns, init, hdmem, hset⟩ := modelSetUniverse?_some hus
      obtain ⟨w, hw, hcont⟩ := satisfiesDyn_basic hsat hdmem
      obtain ⟨sv, rfl⟩ := contains_of_setUniverse hset hcont
      refine ShapeAux.value_member_some ⟨sv, ?_⟩
      rw [hSrest]
      exact hw
  | eq x v =>
      simp only [ShapeAux.TyOk] at hbty
      subst hbty
      have hx : x ∈ taken := hsrc x (by simp [ShapeKind.sourceDeps])
      have hxnot : x ∉ rest.map (fun a => a.name) := by
        intro hmem
        obtain ⟨c, hc, hcn⟩ := List.mem_map.mp hmem
        exact hnames c hc (hcn ▸ hx)
      have hxrest : encodeAuxStore s rest (Ident.mk x) = s (Ident.mk x) :=
        encodeAuxStore_not_mem s rest (Ident.mk x) hxnot
      have hvals : ∃ vals, modelIntValues? m x = some vals := by
        simpa [ShapeAux.WellKind, ShapeKind.WellKind] using hwell
      obtain ⟨vals, hvs⟩ := hvals
      obtain ⟨ty, anns, init, hdmem, hfin⟩ := modelIntValues?_some hvs
      obtain ⟨w, hw, hcont⟩ := satisfiesDyn_basic hsat hdmem
      obtain ⟨i, rfl⟩ := contains_of_finiteIntValues hfin hcont
      refine ShapeAux.value_eq_some ⟨i, ?_⟩
      rw [hxrest]
      exact hw
  | «and» x y =>
      simp only [ShapeAux.TyOk] at hbty
      subst hbty
      obtain ⟨px, hpx⟩ := encodeAuxStore_bool_at hnd hdeps hnames hval hty
        (haux x (by simp [ShapeKind.auxDeps]))
      obtain ⟨py, hpy⟩ := encodeAuxStore_bool_at hnd hdeps hnames hval hty
        (haux y (by simp [ShapeKind.auxDeps]))
      exact ShapeAux.value_and_some ⟨px, hpx⟩ ⟨py, hpy⟩
  | bit x =>
      simp only [ShapeAux.TyOk] at hbty
      subst hbty
      obtain ⟨px, hpx⟩ := encodeAuxStore_bool_at hnd hdeps hnames hval hty
        (haux x (by simp [ShapeKind.auxDeps]))
      exact ShapeAux.value_bit_some ⟨px, hpx⟩
  | const v =>
      simp only [ShapeAux.TyOk] at hbty
      subst hbty
      simp [ShapeAux.value]

/-- Every auxiliary of a well-formed state is functionally defined in
    the interpreted store, when the source store satisfies the source
    declarations. -/
theorem encodeAuxStore_total {m : Model} {s : Store} {taken : List String}
    (hvars : (m.variables.map (fun d => d.name.name)).Nodup)
    (hsat : SatisfiesDyn fullInterp m s) :
    ∀ (as : List ShapeAux),
      (as.map (fun a => a.name)).Nodup →
      ShapeAux.depsOk taken as →
      ShapeAux.KindDeps taken as →
      (∀ a ∈ as, a.TyOk) →
      (∀ a ∈ as, a.WellKind m) →
      (∀ a ∈ as, a.name ∉ taken) →
      ∀ a ∈ as, a.value (encodeAuxStore s as) ≠ none := by
  intro as
  induction as with
  | nil => intro _ _ _ _ _ _ a ha; cases ha
  | cons b rest ih =>
      intro hnd hdeps hkdeps hty hwell hnames a ha
      obtain ⟨hbnot, hndr⟩ := List.nodup_cons.mp hnd
      obtain ⟨hdepsb, hdepsr⟩ := hdeps
      obtain ⟨hsrc, haux, hkdepsr⟩ := hkdeps
      have hnamesr : ∀ c ∈ rest, c.name ∉ taken :=
        fun c hc => hnames c (List.mem_cons_of_mem _ hc)
      have htyr : ∀ c ∈ rest, c.TyOk :=
        fun c hc => hty c (List.mem_cons_of_mem _ hc)
      have hwellr : ∀ c ∈ rest, c.WellKind m :=
        fun c hc => hwell c (List.mem_cons_of_mem _ hc)
      have hvalr := ih hndr hdepsr hkdepsr htyr hwellr hnamesr
      rcases List.mem_cons.mp ha with heq | harest
      · subst a
        have hveq : b.value (encodeAuxStore s (b :: rest)) =
            b.value (encodeAuxStore s rest) := by
          apply ShapeAux.value_ext
          intro d hd
          apply encodeAuxStore_cons_not_mem
          intro hdb
          have hdb' : d = b.name := hdb
          rcases hdepsb d hd with hin | hin
          · rw [hdb'] at hin
            exact hnames b (List.mem_cons_self ..) hin
          · rw [hdb'] at hin
            exact hbnot hin
        rw [hveq]
        exact ShapeAux.value_some_head hvars hsat
          (hty b (List.mem_cons_self ..)) (hwell b (List.mem_cons_self ..))
          hsrc haux hvalr htyr hndr hdepsr hnamesr
      · have hveq : a.value (encodeAuxStore s (b :: rest)) =
            a.value (encodeAuxStore s rest) := by
          apply ShapeAux.value_ext
          intro d hd
          apply encodeAuxStore_cons_not_mem
          intro hdb
          have hdb' : d = b.name := hdb
          rcases ShapeAux.depsOk_mem hdepsr harest d hd with hin | hin
          · rw [hdb'] at hin
            exact hnames b (List.mem_cons_self ..) hin
          · rw [hdb'] at hin
            exact hbnot hin
        rw [hveq]
        exact hvalr a harest


/-! ## The defining constraints hold in the interpreted store -/

/-- The source and auxiliary reads of an auxiliary of a well-formed list. -/
theorem ShapeAux.kindDeps_mem {taken : List String} :
    ∀ {as : List ShapeAux} {a : ShapeAux}, ShapeAux.KindDeps taken as → a ∈ as →
      (∀ d ∈ a.kind.sourceDeps, d ∈ taken) ∧
      (∀ d ∈ a.kind.auxDeps,
        ∃ c ∈ as, c.name = d ∧ c.ty = .par .bool) := by
  intro as
  induction as with
  | nil => intro a _ ha; cases ha
  | cons b rest ih =>
      intro a hdeps ha
      obtain ⟨hsrcb, hauxb, hdepsr⟩ := hdeps
      rcases List.mem_cons.mp ha with heq | harest
      · subst a
        refine ⟨hsrcb, ?_⟩
        intro d hd
        obtain ⟨c, hc, hcn, hct⟩ := hauxb d hd
        exact ⟨c, List.mem_cons_of_mem _ hc, hcn, hct⟩
      · obtain ⟨hsrca, hauxa⟩ := ih hdepsr harest
        refine ⟨hsrca, ?_⟩
        intro d hd
        obtain ⟨c, hc, hcn, hct⟩ := hauxa d hd
        exact ⟨c, List.mem_cons_of_mem _ hc, hcn, hct⟩

/-- An auxiliary is functionally defined in the interpreted store. -/
theorem ShapeState.encStore_aux_defined {taken : List String} {m : Model} {st : ShapeState}
    {s : Store} (hwf : st.WF taken m) {a : ShapeAux} (ha : a ∈ st.aux) :
    a.defined (st.encStore s) :=
  encodeAuxStore_defined s taken st.aux hwf.auxNodup hwf.depsOk hwf.namesAvoid a ha

/-- An auxiliary's functional value is defined in the interpreted store. -/
theorem ShapeState.encStore_aux_total {taken : List String} {m : Model} {st : ShapeState}
    {s : Store} (hvars : (m.variables.map (fun d => d.name.name)).Nodup)
    (hsat : SatisfiesDyn fullInterp m s)
    (hwf : st.WF taken m) {a : ShapeAux} (ha : a ∈ st.aux) :
    a.value (st.encStore s) ≠ none :=
  encodeAuxStore_total hvars hsat st.aux hwf.auxNodup hwf.depsOk hwf.kindDeps
    hwf.tyOk hwf.wellKind hwf.namesAvoid a ha

/-- A Boolean auxiliary named by a dependency reads as a Boolean in the
    interpreted store. -/
theorem ShapeState.encStore_bool_at {taken : List String} {m : Model} {st : ShapeState}
    {s : Store} (hvars : (m.variables.map (fun d => d.name.name)).Nodup)
    (hsat : SatisfiesDyn fullInterp m s)
    (hwf : st.WF taken m) {d : String}
    (hmem : ∃ c ∈ st.aux, c.name = d ∧ c.ty = .par .bool) :
    ∃ p, st.encStore s (Ident.mk d) = some (.bool p) := by
  obtain ⟨c, hc, hcd, hcty⟩ := hmem
  have hdef : c.defined (st.encStore s) :=
    ShapeState.encStore_aux_defined (s := s) hwf hc
  have hval : c.value (st.encStore s) ≠ none :=
    ShapeState.encStore_aux_total (s := s) hvars hsat hwf hc
  cases hv : c.value (st.encStore s) with
  | none => exact absurd hv hval
  | some w =>
      obtain ⟨p, rfl⟩ := ShapeAux.value_bool_of_ty hcty (hwf.tyOk c hc) hv
      refine ⟨p, ?_⟩
      unfold ShapeAux.defined at hdef
      rw [hcd, hv] at hdef
      exact hdef

/-- Every auxiliary's defining constraint holds in the interpreted
    store. -/
theorem ShapeState.aux_definition_holds {taken : List String} {m : Model} {st : ShapeState}
    {s : Store} (hvars : (m.variables.map (fun d => d.name.name)).Nodup)
    (hsat : SatisfiesDyn fullInterp m s)
    (hwf : st.WF taken m) {a : ShapeAux} (ha : a ∈ st.aux) :
    a.definition.Holds fullInterp (st.encStore s) := by
  obtain ⟨hdeps, hkdeps⟩ := ShapeAux.kindDeps_mem hwf.kindDeps ha
  have hwell := hwf.wellKind a ha
  have hdef : a.defined (st.encStore s) :=
    ShapeState.encStore_aux_defined (s := s) hwf ha
  have hval : a.value (st.encStore s) ≠ none :=
    ShapeState.encStore_aux_total (s := s) hvars hsat hwf ha
  obtain ⟨n, ty, k⟩ := a
  cases k with
  | member S w =>
      have hS : S ∈ taken := hdeps S (by simp [ShapeKind.sourceDeps])
      have huni : ∃ us, modelSetUniverse? m S = some us := by
        simpa [ShapeAux.WellKind, ShapeKind.WellKind] using hwell
      obtain ⟨us, hus⟩ := huni
      obtain ⟨sty, anns, init, hdmem, hset⟩ := modelSetUniverse?_some hus
      obtain ⟨sw, hsw, hcont⟩ := satisfiesDyn_basic hsat hdmem
      obtain ⟨sv, rfl⟩ := contains_of_setUniverse hset hcont
      have hSenc : st.encStore s (Ident.mk S) = some (.setOfInt sv) := by
        rw [ShapeState.encStore_at_taken hwf hS]
        exact hsw
      have hnenc : st.encStore s (Ident.mk n) = some (.bool (decide (sv.Contains w))) := by
        unfold ShapeAux.defined at hdef
        rw [hdef]
        simp [ShapeAux.value, hSenc]
      exact (ShapeAux.holds_member S w n _).mpr ⟨sv, hSenc, hnenc⟩
  | eq x w =>
      have hx : x ∈ taken := hdeps x (by simp [ShapeKind.sourceDeps])
      have hvals : ∃ vals, modelIntValues? m x = some vals := by
        simpa [ShapeAux.WellKind, ShapeKind.WellKind] using hwell
      obtain ⟨vals, hvs⟩ := hvals
      obtain ⟨ity, anns, init, hdmem, hfin⟩ := modelIntValues?_some hvs
      obtain ⟨iw, hiw, hcont⟩ := satisfiesDyn_basic hsat hdmem
      obtain ⟨i, rfl⟩ := contains_of_finiteIntValues hfin hcont
      have hxenc : st.encStore s (Ident.mk x) = some (.int i) := by
        rw [ShapeState.encStore_at_taken hwf hx]
        exact hiw
      have hnenc : st.encStore s (Ident.mk n) = some (.bool (decide (i = w))) := by
        unfold ShapeAux.defined at hdef
        rw [hdef]
        simp [ShapeAux.value, hxenc]
      exact (ShapeAux.holds_eq x w n _).mpr ⟨i, hxenc, hnenc⟩
  | «and» x y =>
      obtain ⟨px, hpx⟩ := ShapeState.encStore_bool_at hvars hsat hwf
        (hkdeps x (by simp [ShapeKind.auxDeps]))
      obtain ⟨py, hpy⟩ := ShapeState.encStore_bool_at hvars hsat hwf
        (hkdeps y (by simp [ShapeKind.auxDeps]))
      have hnenc : st.encStore s (Ident.mk n) = some (.bool (px && py)) := by
        unfold ShapeAux.defined at hdef
        rw [hdef]
        simp [ShapeAux.value, hpx, hpy]
      exact (ShapeAux.holds_and x y n _).mpr ⟨px, py, hpx, hpy, hnenc⟩
  | bit x =>
      obtain ⟨px, hpx⟩ := ShapeState.encStore_bool_at hvars hsat hwf
        (hkdeps x (by simp [ShapeKind.auxDeps]))
      have hnenc : st.encStore s (Ident.mk n) = some (.int (if px then 1 else 0)) := by
        unfold ShapeAux.defined at hdef
        rw [hdef]
        simp [ShapeAux.value, hpx]
      exact (ShapeAux.holds_bit x n _).mpr ⟨px, hpx, hnenc⟩
  | const w =>
      have hnenc : st.encStore s (Ident.mk n) = some (.bool w) := by
        unfold ShapeAux.defined at hdef
        rw [hdef]
        simp [ShapeAux.value]
      exact (ShapeAux.holds_const w n _).mpr hnenc


/-! ## Store agreement and state extension -/

/-- Basic expressions agree under stores that agree on their names. -/
theorem basicNames_eval_agree {s t : Store} {b : BasicExpr}
    (h : ∀ x ∈ basicNames b, s (Ident.mk x) = t (Ident.mk x)) :
    b.eval s = b.eval t := by
  cases b with
  | lit l => rfl
  | ident y =>
      have hy : s (Ident.mk y.name) = t (Ident.mk y.name) :=
        h y.name (by simp [basicNames])
      simpa [BasicExpr.eval] using hy

/-- Expressions agree under stores that agree on their names. -/
theorem exprNames_eval_agree {s t : Store} {e : Expr}
    (h : ∀ x ∈ exprNames e, s (Ident.mk x) = t (Ident.mk x)) :
    e.eval s = e.eval t := by
  cases e with
  | basic b =>
      exact basicNames_eval_agree (by
        intro x hx
        exact h x (by simpa [exprNames] using hx))
  | array es =>
      show (es.mapM (BasicExpr.eval s)).map Value.array =
        (es.mapM (BasicExpr.eval t)).map Value.array
      have hall : ∀ b ∈ es, BasicExpr.eval s b = BasicExpr.eval t b := by
        intro b hb
        exact basicNames_eval_agree (by
          intro x hx
          exact h x (by
            simp only [exprNames, List.mem_flatMap]
            exact ⟨b, hb, hx⟩))
      rw [mapM_congr_set hall]

/-- A constraint holds equally under stores that agree on its names. -/
theorem holds_of_names_agree {s t : Store} {pred : PredicateInterpretation}
    {c : ConstraintItem}
    (h : ∀ x ∈ constraintNames c, s (Ident.mk x) = t (Ident.mk x)) :
    c.Holds pred s ↔ c.Holds pred t := by
  have hargs : c.args.mapM (Expr.eval s) = c.args.mapM (Expr.eval t) := by
    apply mapM_congr_set
    intro e he
    exact exprNames_eval_agree (by
      intro x hx
      exact h x (by
        simp only [constraintNames, List.mem_flatMap]
        exact ⟨e, he, hx⟩))
  unfold ConstraintItem.Holds
  rw [hargs]

/-- Every constraint accumulated in a state mentions a taken name or one
    of the state's auxiliary names. -/
def ShapeState.MentionsWithin (taken : List String) (st : ShapeState) : Prop :=
  ∀ c ∈ st.cons, ∀ x ∈ constraintNames c,
    x ∈ taken ∨ x ∈ st.aux.map (fun a => a.name)

/-- Emitting one constraint preserves the mention invariant. -/
theorem ShapeState.mentionsWithin_emit {taken : List String} {st : ShapeState}
    (h : ShapeState.MentionsWithin taken st) {c : ConstraintItem}
    (hc : ∀ x ∈ constraintNames c, x ∈ taken ∨ x ∈ st.aux.map (fun a => a.name)) :
    ShapeState.MentionsWithin taken (st.emit c) := by
  intro c' hc' x hx
  have hcons : (st.emit c).cons = c :: st.cons := rfl
  rw [hcons] at hc'
  rcases List.mem_cons.mp hc' with rfl | hc''
  · exact hc x hx
  · exact h c' hc'' x hx

/-- Emitting a list of constraints preserves the mention invariant. -/
theorem ShapeState.mentionsWithin_emitList {taken : List String} {st : ShapeState}
    (h : ShapeState.MentionsWithin taken st) {cs : List ConstraintItem}
    (hcs : ∀ c ∈ cs, ∀ x ∈ constraintNames c,
      x ∈ taken ∨ x ∈ st.aux.map (fun a => a.name)) :
    ShapeState.MentionsWithin taken (st.emitList cs) := by
  intro c' hc' x hx
  have hcons : (st.emitList cs).cons = cs.reverse ++ st.cons := rfl
  rw [hcons] at hc'
  rcases List.mem_append.mp hc' with hin | hin
  · exact hcs c' (List.mem_reverse.mp hin) x hx
  · exact h c' hin x hx

/-- Allocating a fresh Boolean preserves the mention invariant. -/
theorem ShapeState.freshBool_mentionsWithin {taken : List String} {st : ShapeState}
    (h : ShapeState.MentionsWithin taken st) (kind : ShapeKind)
    (hdeps : ∀ d ∈ kind.deps, d ∈ taken ∨ d ∈ st.aux.map (fun a => a.name)) :
    ShapeState.MentionsWithin taken (st.freshBool taken kind).2 := by
  let n := shapeAuxName st.maxLen st.next
  let a : ShapeAux := { name := n, ty := .par .bool, kind := kind }
  have haux : (st.freshBool taken kind).2.aux = a :: st.aux := rfl
  have hcons : (st.freshBool taken kind).2.cons = a.definition :: st.cons := rfl
  have hadeps : a.deps = kind.deps := ShapeAux.deps_mk n (.par .bool) kind
  intro c hc x hx
  rw [hcons] at hc
  rcases List.mem_cons.mp hc with rfl | hc''
  · have hnames : constraintNames a.definition = a.deps ++ [a.name] :=
      constraintNames_definition a
    rw [hnames] at hx
    rcases List.mem_append.mp hx with hin | hin
    · rcases hdeps x (hadeps ▸ hin) with htake | hold
      · exact Or.inl htake
      · exact Or.inr (by rw [haux]; exact List.mem_cons_of_mem _ hold)
    · rw [List.mem_singleton] at hin
      exact Or.inr (by rw [haux, hin]; exact List.mem_cons_self ..)
  · rcases h c hc'' x hx with htake | hold
    · exact Or.inl htake
    · exact Or.inr (by rw [haux]; exact List.mem_cons_of_mem _ hold)

/-- Allocating a fresh `0..1` integer preserves the mention invariant. -/
theorem ShapeState.freshInt01_mentionsWithin {taken : List String} {st : ShapeState}
    (h : ShapeState.MentionsWithin taken st) (kind : ShapeKind)
    (hdeps : ∀ d ∈ kind.deps, d ∈ taken ∨ d ∈ st.aux.map (fun a => a.name)) :
    ShapeState.MentionsWithin taken (st.freshInt01 taken kind).2 := by
  let n := shapeAuxName st.maxLen st.next
  let a : ShapeAux := { name := n, ty := .intRange 0 1, kind := kind }
  have haux : (st.freshInt01 taken kind).2.aux = a :: st.aux := rfl
  have hcons : (st.freshInt01 taken kind).2.cons = a.definition :: st.cons := rfl
  have hadeps : a.deps = kind.deps := ShapeAux.deps_mk n (.intRange 0 1) kind
  intro c hc x hx
  rw [hcons] at hc
  rcases List.mem_cons.mp hc with rfl | hc''
  · have hnames : constraintNames a.definition = a.deps ++ [a.name] :=
      constraintNames_definition a
    rw [hnames] at hx
    rcases List.mem_append.mp hx with hin | hin
    · rcases hdeps x (hadeps ▸ hin) with htake | hold
      · exact Or.inl htake
      · exact Or.inr (by rw [haux]; exact List.mem_cons_of_mem _ hold)
    · rw [List.mem_singleton] at hin
      exact Or.inr (by rw [haux, hin]; exact List.mem_cons_self ..)
  · rcases h c hc'' x hx with htake | hold
    · exact Or.inl htake
    · exact Or.inr (by rw [haux]; exact List.mem_cons_of_mem _ hold)

/-- The mention invariant transfers a given satisfaction to the newer
    interpreted store. -/
theorem ShapeState.holds_mono_encStore {taken : List String} {m : Model}
    {st st' : ShapeState} {s : Store}
    (haux : ∃ extra, st'.aux = extra ++ st.aux)
    (hidx : st'.AuxIdx taken)
    (hmono : ShapeState.MentionsWithin taken st)
    (hholds : st.Holds (st.encStore s)) :
    st.Holds (st'.encStore s) := by
  intro c hc
  apply (holds_of_names_agree (s := st'.encStore s) (t := st.encStore s)
    (pred := fullInterp) (c := c) ?_).mpr (hholds c hc)
  intro x hx
  exact ShapeState.encodeStore_extends haux hidx (hmono c hc x hx)


/-! ## Newly emitted constraints -/

/-- Every constraint of `st'` is an old constraint or holds in the
    store. -/
def ShapeState.NewHolds (st st' : ShapeState) (s : Store) : Prop :=
  ∀ c ∈ st'.cons, c ∈ st.cons ∨ c.Holds fullInterp s

/-- Old satisfaction and newly emitted constraints give satisfaction of
    the extended state. -/
theorem ShapeState.holds_of_new {st st' : ShapeState} {s : Store}
    (h : st.Holds s) (hn : st.NewHolds st' s) : st'.Holds s := by
  intro c hc
  rcases hn c hc with hc' | hc'
  · exact h c hc'
  · exact hc'

/-- Transitivity of `NewHolds`. -/
theorem ShapeState.newHolds_trans {st st' st'' : ShapeState} {s : Store}
    (h1 : st.NewHolds st' s) (h2 : st'.NewHolds st'' s) : st.NewHolds st'' s := by
  intro c hc
  rcases h2 c hc with hc' | hc'
  · exact h1 c hc'
  · exact Or.inr hc'

/-! ## Clause lists over model names -/

/-- Evaluating a list of identifier terms. -/
theorem mapM_shapeName_of {s : Store} {xs : List String} {f : String → Value}
    (h : ∀ x ∈ xs, s (Ident.mk x) = some (f x)) :
    (xs.map shapeName).mapM (BasicExpr.eval s) = some (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.mapM_cons]
      have hx : BasicExpr.eval s (shapeName x) = some (f x) := h x (by simp)
      rw [hx]
      have hrest : (List.map shapeName rest).mapM (BasicExpr.eval s) =
          some (List.map f rest) :=
        ih (fun y hy => h y (by simp [hy]))
      rw [hrest]
      rfl

/-- A true entry of the evaluated name list comes from a true variable. -/
theorem exists_true_of_mapM_any {s : Store} {xs : List String} {vs : List Value}
    (hmap : (xs.map shapeName).mapM (BasicExpr.eval s) = some vs)
    (hany : vs.any (fun v => v.eqB (.bool true)) = true) :
    ∃ x ∈ xs, s (Ident.mk x) = some (.bool true) := by
  induction xs generalizing vs with
  | nil =>
      have hvs : vs = [] := Option.some.inj hmap.symm
      subst hvs
      simpa using hany
  | cons x rest ih =>
      simp only [List.map_cons, List.mapM_cons] at hmap
      obtain ⟨v, hv, hmap'⟩ := Option.bind_eq_some_iff.mp hmap
      obtain ⟨vs', hvs', hvs⟩ := Option.bind_eq_some_iff.mp hmap'
      have hvs'' : vs = v :: vs' := Option.some.inj hvs.symm
      rw [hvs''] at hany
      simp only [List.any_cons, Bool.or_eq_true] at hany
      rcases hany with htrue | hrest
      · have hv' : v = .bool true := (eqB_bool_true_iff v).mp htrue
        subst hv'
        exact ⟨x, by simp, by simpa [shapeName, BasicExpr.eval] using hv⟩
      · obtain ⟨y, hy, hsy⟩ := ih hvs' hrest
        exact ⟨y, List.mem_cons_of_mem _ hy, hsy⟩

/-- A false entry of the evaluated name list comes from a false variable. -/
theorem exists_false_of_mapM_any {s : Store} {xs : List String} {vs : List Value}
    (hmap : (xs.map shapeName).mapM (BasicExpr.eval s) = some vs)
    (hany : vs.any (fun v => v.eqB (.bool false)) = true) :
    ∃ x ∈ xs, s (Ident.mk x) = some (.bool false) := by
  induction xs generalizing vs with
  | nil =>
      have hvs : vs = [] := Option.some.inj hmap.symm
      subst hvs
      simpa using hany
  | cons x rest ih =>
      simp only [List.map_cons, List.mapM_cons] at hmap
      obtain ⟨v, hv, hmap'⟩ := Option.bind_eq_some_iff.mp hmap
      obtain ⟨vs', hvs', hvs⟩ := Option.bind_eq_some_iff.mp hmap'
      have hvs'' : vs = v :: vs' := Option.some.inj hvs.symm
      rw [hvs''] at hany
      simp only [List.any_cons, Bool.or_eq_true] at hany
      rcases hany with hfalse | hrest
      · have hv' : v = .bool false := (eqB_bool_false_iff v).mp hfalse
        subst hv'
        exact ⟨x, by simp, by simpa [shapeName, BasicExpr.eval] using hv⟩
      · obtain ⟨y, hy, hsy⟩ := ih hvs' hrest
        exact ⟨y, List.mem_cons_of_mem _ hy, hsy⟩

/-- A clause over identifier lists holding with a true positive. -/
theorem holds_bool_clause_shape {s : Store} {pos neg : List String}
    {c : ConstraintItem}
    (hname : c.name.name = "bool_clause")
    (hargs : c.args = [.array (pos.map shapeName), .array (neg.map shapeName)])
    (h : c.Holds fullInterp s) :
    (∃ x ∈ pos, s (Ident.mk x) = some (.bool true)) ∨
      (∃ y ∈ neg, s (Ident.mk y) = some (.bool false)) := by
  obtain ⟨vs, ws, hvs, hws, hany⟩ := holds_bool_clause hname hargs h
  rw [Bool.or_eq_true] at hany
  rcases hany with hany | hany
  · exact Or.inl (exists_true_of_mapM_any hvs hany)
  · exact Or.inr (exists_false_of_mapM_any hws hany)

/-- A clause over identifier lists holds when a true positive or a false
    negative exists. -/
theorem holds_bool_clause_shape_of {s : Store} {pos neg : List String}
    {fpos fneg : String → Value}
    (hpv : ∀ x ∈ pos, s (Ident.mk x) = some (fpos x))
    (hnv : ∀ y ∈ neg, s (Ident.mk y) = some (fneg y))
    (hany : (((pos.map fpos).any (fun v => v.eqB (.bool true))) ||
      ((neg.map fneg).any (fun v => v.eqB (.bool false)))) = true) :
    (shapeConstraint "bool_clause"
      [.array (pos.map shapeName), .array (neg.map shapeName)]).Holds fullInterp s := by
  have hpos := mapM_shapeName_of hpv
  have hneg := mapM_shapeName_of hnv
  refine ⟨[.array (pos.map fpos), .array (neg.map fneg)], ?_, ?_⟩
  · simp only [shapeConstraint, List.mapM_cons, List.mapM_nil, Expr.eval]
    rw [hpos, hneg]
    rfl
  · show fullInterp (Ident.mk "bool_clause")
      [.array (pos.map fpos), .array (neg.map fneg)]
    rw [fullInterp_bool_clause, stdInterp_bool_clause_apply]
    exact hany

/-- The defining constraint allocated by `freshBool` is the head of the
    new constraint list. -/
theorem ShapeState.freshBool_cons {taken : List String} {st : ShapeState} {kind : ShapeKind}
    {n : String} {st' : ShapeState} (h : st.freshBool taken kind = (n, st')) :
    st'.cons = (⟨n, .par .bool, kind⟩ : ShapeAux).definition :: st.cons := by
  simp only [ShapeState.freshBool, ShapeState.freshDecl, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- The defining constraint allocated by `freshInt01` is the head of the
    new constraint list. -/
theorem ShapeState.freshInt01_cons {taken : List String} {st : ShapeState} {kind : ShapeKind}
    {n : String} {st' : ShapeState} (h : st.freshInt01 taken kind = (n, st')) :
    st'.cons = (⟨n, .intRange 0 1, kind⟩ : ShapeAux).definition :: st.cons := by
  simp only [ShapeState.freshInt01, ShapeState.freshDecl, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- The auxiliary list allocated by `freshBool` gains one head. -/
theorem ShapeState.freshBool_aux {taken : List String} {st : ShapeState} {kind : ShapeKind}
    {n : String} {st' : ShapeState} (h : st.freshBool taken kind = (n, st')) :
    st'.aux = (⟨n, .par .bool, kind⟩ : ShapeAux) :: st.aux := by
  simp only [ShapeState.freshBool, ShapeState.freshDecl, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- The auxiliary list allocated by `freshInt01` gains one head. -/
theorem ShapeState.freshInt01_aux {taken : List String} {st : ShapeState} {kind : ShapeKind}
    {n : String} {st' : ShapeState} (h : st.freshInt01 taken kind = (n, st')) :
    st'.aux = (⟨n, .intRange 0 1, kind⟩ : ShapeAux) :: st.aux := by
  simp only [ShapeState.freshInt01, ShapeState.freshDecl, Prod.mk.injEq] at h
  obtain ⟨rfl, rfl⟩ := h
  rfl

/-- `freshBool` keeps every old auxiliary. -/
theorem ShapeState.freshBool_aux_subset {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState}
    (h : st.freshBool taken kind = (n, st')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  intro a ha
  rw [ShapeState.freshBool_aux h]
  exact List.mem_cons_of_mem _ ha

/-- `freshInt01` keeps every old auxiliary. -/
theorem ShapeState.freshInt01_aux_subset {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState}
    (h : st.freshInt01 taken kind = (n, st')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  intro a ha
  rw [ShapeState.freshInt01_aux h]
  exact List.mem_cons_of_mem _ ha

/-- `freshBool` only adds its own defining constraint. -/
theorem ShapeState.freshBool_newHolds {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState} {s : Store}
    (h : st.freshBool taken kind = (n, st'))
    (hdef : (⟨n, .par .bool, kind⟩ : ShapeAux).definition.Holds fullInterp s) :
    st.NewHolds st' s := by
  intro c hc
  rw [ShapeState.freshBool_cons h] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact Or.inr hdef
  · exact Or.inl hc

/-- `freshInt01` only adds its own defining constraint. -/
theorem ShapeState.freshInt01_newHolds {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState} {s : Store}
    (h : st.freshInt01 taken kind = (n, st'))
    (hdef : (⟨n, .intRange 0 1, kind⟩ : ShapeAux).definition.Holds fullInterp s) :
    st.NewHolds st' s := by
  intro c hc
  rw [ShapeState.freshInt01_cons h] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact Or.inr hdef
  · exact Or.inl hc

/-! ## The Boolean result target -/

/-- A result target evaluates like its source expression. -/
theorem resultTarget_eval {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState} {s' : Store}
    (h : resultTarget taken st r = some (n, st'))
    (hholds : st'.Holds s') :
    ∀ v, r.eval s' = some v → s' (Ident.mk n) = some v := by
  intro v hv
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simpa [shapeName, BasicExpr.eval] using hv
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget, Option.some.injEq] at h
            have hcons := ShapeState.freshBool_cons h
            have hpin : (⟨n, .par .bool, .const false⟩ : ShapeAux).definition.Holds
                fullInterp s' :=
              hholds _ (by rw [hcons]; exact List.mem_cons_self)
            have hn := (ShapeAux.holds_const false n s').mp (by
              simpa [ShapeAux.definition] using hpin)
            have hv' : (.bool false) = v := by
              simpa [BasicExpr.eval, BasicLiteral.denote] using hv
            subst hv'
            exact hn
          · simp only [resultTarget, Option.some.injEq] at h
            have hcons := ShapeState.freshBool_cons h
            have hpin : (⟨n, .par .bool, .const true⟩ : ShapeAux).definition.Holds
                fullInterp s' :=
              hholds _ (by rw [hcons]; exact List.mem_cons_self)
            have hn := (ShapeAux.holds_const true n s').mp (by
              simpa [ShapeAux.definition] using hpin)
            have hv' : (.bool true) = v := by
              simpa [BasicExpr.eval, BasicLiteral.denote] using hv
            subst hv'
            exact hn
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-! ## Membership terms -/

/-- The semantic membership of a finite set argument. -/
def setArgContains (s : Store) : Expr → Int → Prop
  | .basic (.ident S), v =>
      ∃ sv, s S = some (.setOfInt sv) ∧ sv.Contains v
  | .basic (.lit (.set l)), v => l.denote.Contains v
  | _, _ => False

/-- A fresh membership auxiliary holds its source membership. -/
theorem freshBool_member_holds {taken : List String} {st : ShapeState}
    {S : String} {v : Int} {n : String} {st' : ShapeState} {s' : Store}
    (h : st.freshBool taken (.member S v) = (n, st'))
    (hholds : st'.Holds s') :
    ∃ sv, s' (Ident.mk S) = some (.setOfInt sv) ∧
      s' (Ident.mk n) = some (.bool (decide (sv.Contains v))) := by
  have hcons := ShapeState.freshBool_cons h
  have hdef : (⟨n, .par .bool, .member S v⟩ : ShapeAux).definition.Holds fullInterp s' :=
    hholds _ (by rw [hcons]; exact List.mem_cons_self)
  exact (ShapeAux.holds_member S v n s').mp (by
    simpa [ShapeAux.definition] using hdef)

/-- A fresh pinned auxiliary holds its literal. -/
theorem freshBool_const_holds {taken : List String} {st : ShapeState}
    {v : Bool} {n : String} {st' : ShapeState} {s' : Store}
    (h : st.freshBool taken (.const v) = (n, st'))
    (hholds : st'.Holds s') :
    s' (Ident.mk n) = some (.bool v) := by
  have hcons := ShapeState.freshBool_cons h
  have hdef : (⟨n, .par .bool, .const v⟩ : ShapeAux).definition.Holds fullInterp s' :=
    hholds _ (by rw [hcons]; exact List.mem_cons_self)
  exact (ShapeAux.holds_const v n s').mp (by
    simpa [ShapeAux.definition] using hdef)

/-- Membership in a set variable, at a known set value. -/
theorem setArgContains_ident_iff {s : Store} {S : Ident} {sv : IntSetValue} {v : Int}
    (hsv : s S = some (.setOfInt sv)) :
    setArgContains s (.basic (.ident S)) v ↔ sv.Contains v := by
  constructor
  · rintro ⟨sv', hsv', hc⟩
    rw [hsv] at hsv'
    have hsv'' : sv' = sv := by simpa using hsv'.symm
    subst hsv''
    exact hc
  · intro hc
    exact ⟨sv, hsv, hc⟩

/-- A membership term is the membership decision of its set argument. -/
theorem memberTerm_sound {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState} {s' : Store}
    (h : memberTerm taken m st sa v = some (n, st'))
    (hholds : st'.Holds s')
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s' (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    (setArgContains s' sa v ∧ s' (Ident.mk n) = some (.bool true)) ∨
      (¬ setArgContains s' sa v ∧ s' (Ident.mk n) = some (.bool false)) := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              by_cases hv : v ∈ us
              · simp only [memberTerm, hus, if_pos hv, Option.some.injEq] at h
                obtain ⟨sv, hsv, hn⟩ := freshBool_member_holds h hholds
                by_cases hc : sv.Contains v
                · left
                  refine ⟨(setArgContains_ident_iff hsv).mpr hc, ?_⟩
                  simpa [hc] using hn
                · right
                  refine ⟨fun hcont => hc ((setArgContains_ident_iff hsv).mp hcont), ?_⟩
                  simpa [hc] using hn
              · simp only [memberTerm, hus, if_neg hv, Option.some.injEq] at h
                have hn := freshBool_const_holds h hholds
                have hnot : ¬ setArgContains s' (.basic (.ident S)) v := by
                  rintro ⟨sv, hsv, hcont⟩
                  exact hv (hdecl S.name us hus sv hsv v hcont)
                exact Or.inr ⟨hnot, hn⟩
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm, Option.some.injEq] at h
              have hn := freshBool_const_holds h hholds
              by_cases hc : sl.denote.Contains v
              · left
                exact ⟨by simpa [setArgContains] using hc, by simpa [hc] using hn⟩
              · exact Or.inr ⟨by simpa [setArgContains] using hc, by simpa [hc] using hn⟩
  | array es => simp [memberTerm] at h


/-! ## Clauses over Boolean-valued names -/

/-- Boolean disjunction equal to true, in propositional form. -/
theorem bool_or_eq_true_iff (a b : Bool) : (a || b) = true ↔ (a = true ∨ b = true) := by
  constructor
  · intro h
    cases a <;> cases b <;> simp_all
  · rintro (h | h) <;> simp [h]

/-- A `bool_clause` over names with Boolean values holds from a true
    positive or a false negative. -/
theorem holds_bool_clause_shape_bool {s : Store} {pos neg : List String}
    {bp bn : String → Bool}
    (hp : ∀ x ∈ pos, s (Ident.mk x) = some (.bool (bp x)))
    (hn : ∀ y ∈ neg, s (Ident.mk y) = some (.bool (bn y)))
    (h : (∃ x ∈ pos, bp x = true) ∨ (∃ y ∈ neg, bn y = false)) :
    (shapeConstraint "bool_clause"
      [.array (pos.map shapeName), .array (neg.map shapeName)]).Holds fullInterp s := by
  apply holds_bool_clause_shape_of
    (fpos := fun x => .bool (bp x)) (fneg := fun y => .bool (bn y)) hp hn
  rw [bool_or_eq_true_iff]
  rcases h with ⟨x, hx, hb⟩ | ⟨y, hy, hb⟩
  · left
    rw [List.any_map, List.any_eq_true]
    exact ⟨x, hx, by cases hp' : bp x <;> simp_all [Value.eqB]⟩
  · right
    rw [List.any_map, List.any_eq_true]
    exact ⟨y, hy, by cases hn' : bn y <;> simp_all [Value.eqB]⟩

/-- The result target and its source expression read the same Boolean. -/
theorem resultTarget_eval_iff {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState} {s' : Store}
    (h : resultTarget taken st r = some (n, st'))
    (hdefs : st'.DefHolds s') :
    ∀ v, r.eval s' = some v ↔ s' (Ident.mk n) = some v := by
  intro v
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      constructor <;> intro hv <;> simpa [BasicExpr.eval] using hv
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget, Option.some.injEq] at h
            have hn : s' (Ident.mk n) = some (.bool false) := by
              have haux : (⟨n, .par .bool, .const false⟩ : ShapeAux) ∈ st'.aux := by
                rw [ShapeState.freshBool_aux h]
                exact List.mem_cons_self ..
              have hdef : (⟨n, .par .bool, .const false⟩ : ShapeAux).definition.Holds
                  fullInterp s' := hdefs _ haux
              exact (ShapeAux.holds_const false n s').mp (by
                simpa [ShapeAux.definition] using hdef)
            constructor
            · intro hv
              have hv' : (.bool false) = v := by
                simpa [BasicExpr.eval, BasicLiteral.denote] using hv
              subst hv'
              exact hn
            · intro hv
              have hv' : v = .bool false := by
                simpa using hv.symm.trans hn
              subst hv'
              simp [BasicExpr.eval, BasicLiteral.denote]
          · simp only [resultTarget, Option.some.injEq] at h
            have hn : s' (Ident.mk n) = some (.bool true) := by
              have haux : (⟨n, .par .bool, .const true⟩ : ShapeAux) ∈ st'.aux := by
                rw [ShapeState.freshBool_aux h]
                exact List.mem_cons_self ..
              have hdef : (⟨n, .par .bool, .const true⟩ : ShapeAux).definition.Holds
                  fullInterp s' := hdefs _ haux
              exact (ShapeAux.holds_const true n s').mp (by
                simpa [ShapeAux.definition] using hdef)
            constructor
            · intro hv
              have hv' : (.bool true) = v := by
                simpa [BasicExpr.eval, BasicLiteral.denote] using hv
              subst hv'
              exact hn
            · intro hv
              have hv' : v = .bool true := by
                simpa using hv.symm.trans hn
              subst hv'
              simp [BasicExpr.eval, BasicLiteral.denote]
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-- `resultTarget` keeps every old auxiliary. -/
theorem resultTarget_aux_subset {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState}
    (h : resultTarget taken st r = some (n, st')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget, Option.some.injEq] at h
            intro a ha
            rw [ShapeState.freshBool_aux h]
            exact List.mem_cons_of_mem _ ha
          · simp only [resultTarget, Option.some.injEq] at h
            intro a ha
            rw [ShapeState.freshBool_aux h]
            exact List.mem_cons_of_mem _ ha
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-- `resultTarget` only adds its own pinned definition. -/
theorem resultTarget_newHolds {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState} {s' : Store}
    (h : resultTarget taken st r = some (n, st'))
    (hdefs : st'.DefHolds s') :
    st.NewHolds st' s' := by
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
            have haux : (⟨n, .par .bool, .const false⟩ : ShapeAux) ∈ st'.aux := by
              rw [ShapeState.freshBool_aux h]
              exact List.mem_cons_self ..
            intro c hc
            rw [ShapeState.freshBool_cons h] at hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inr (hdefs _ haux)
            · exact Or.inl hc
          · simp only [resultTarget, Option.some.injEq] at h
            have haux : (⟨n, .par .bool, .const true⟩ : ShapeAux) ∈ st'.aux := by
              rw [ShapeState.freshBool_aux h]
              exact List.mem_cons_self ..
            intro c hc
            rw [ShapeState.freshBool_cons h] at hc
            rcases List.mem_cons.mp hc with rfl | hc
            · exact Or.inr (hdefs _ haux)
            · exact Or.inl hc
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-! ## Linking a target to a disjunction -/

/-- The constraints emitted by `linkOr` all hold.  In a store where the
    terms are Booleans, the target is Boolean and is their disjunction. -/
theorem linkOr_sound {st : ShapeState} {terms : List String} {target : String}
    {s : Store} {bp : String → Bool}
    (hholds : (linkOr st terms target).Holds s)
    (hterms : ∀ t ∈ terms, s (Ident.mk t) = some (.bool (bp t))) :
    ∃ b, s (Ident.mk target) = some (.bool b) ∧
      (b = true ↔ ∃ t ∈ terms, bp t = true) := by
  cases terms with
  | nil =>
      have hpin : (pinBoolConstraint target false).Holds fullInterp s :=
        hholds _ (by simp [linkOr, ShapeState.emit])
      have ht := (ShapeAux.holds_const false target s).mp hpin
      refine ⟨false, ht, ?_⟩
      constructor
      · intro h; cases h
      · rintro ⟨t, ht', _⟩; cases ht'
  | cons t0 ts =>
      have hclause : (shapeConstraint "bool_clause"
          [.array ((t0 :: ts).map shapeName), .array [shapeName target]]).Holds
            fullInterp s :=
        hholds _ (by simp [linkOr, ShapeState.emitList, List.mem_append])
      have hlink : ∀ t ∈ (t0 :: ts),
          (shapeConstraint "bool_clause"
            [.array [shapeName target], .array [shapeName t]]).Holds fullInterp s := by
        intro t ht
        exact hholds _ (by
          simp only [linkOr, ShapeState.emitList, List.mem_append, List.mem_reverse,
            List.mem_map, List.mem_cons]
          left
          right
          exact ⟨t, List.mem_cons.mp ht, rfl⟩)
      have hc := holds_bool_clause_shape (s := s) (pos := t0 :: ts) (neg := [target])
        (c := shapeConstraint "bool_clause"
          [.array ((t0 :: ts).map shapeName), .array [shapeName target]]) rfl rfl hclause
      have hl : ∀ t ∈ (t0 :: ts),
          s (Ident.mk target) = some (.bool true) ∨
            s (Ident.mk t) = some (.bool false) := by
        intro t ht
        have := holds_bool_clause_shape (s := s) (pos := [target]) (neg := [t])
          (c := shapeConstraint "bool_clause"
            [.array [shapeName target], .array [shapeName t]]) rfl rfl (hlink t ht)
        simpa using this
      -- the clause, in terms of the Boolean name values
      have hc' : (∃ t ∈ (t0 :: ts), bp t = true) ∨
          s (Ident.mk target) = some (.bool false) := by
        rcases hc with ⟨t, ht, htv⟩ | hneg
        · left
          refine ⟨t, ht, ?_⟩
          have hb := (hterms t ht).symm.trans htv
          simpa using Option.some.inj hb
        · obtain ⟨y, hy, hyv⟩ := hneg
          simp only [List.mem_singleton] at hy
          subst y
          exact Or.inr hyv
      cases htarget : s (Ident.mk target) with
      | none =>
          have hex := hc'.resolve_right (by rw [htarget]; exact fun h => nomatch h)
          obtain ⟨t, ht, hbt⟩ := hex
          have hlt := (hl t ht).resolve_left (by rw [htarget]; exact fun h => nomatch h)
          have hb := (hterms t ht).symm.trans hlt
          have : bp t = false := by simpa using Option.some.inj hb
          rw [hbt] at this
          cases this
      | some w =>
          cases w with
          | bool b =>
              have hlt : ∀ t ∈ (t0 :: ts),
                  (b = true) ∨ (bp t = false) := by
                intro t ht
                rcases hl t ht with h | h
                · left
                  rw [htarget] at h
                  simpa using Option.some.inj h
                · right
                  have hb := (hterms t ht).symm.trans h
                  simpa using Option.some.inj hb
              have hcb : (∃ t ∈ (t0 :: ts), bp t = true) ∨ b = false := by
                rcases hc' with h | h
                · exact Or.inl h
                · right
                  rw [htarget] at h
                  simpa using Option.some.inj h
              refine ⟨b, rfl, ?_⟩
              constructor
              · intro hb
                rcases hcb with h | h
                · exact h
                · rw [hb] at h; cases h
              · rintro ⟨t, ht, hbt⟩
                rcases hlt t ht with h | h
                · exact h
                · rw [hbt] at h; cases h
          | int i =>
              have hex := hc'.resolve_right (by rw [htarget]; exact fun h => nomatch h)
              obtain ⟨t, ht, hbt⟩ := hex
              rcases hl t ht with h | h
              · rw [htarget] at h; cases h
              · have hb := (hterms t ht).symm.trans h
                have : bp t = false := by simpa using Option.some.inj hb
                rw [hbt] at this; cases this
          | setOfInt sv =>
              have hex := hc'.resolve_right (by rw [htarget]; exact fun h => nomatch h)
              obtain ⟨t, ht, hbt⟩ := hex
              rcases hl t ht with h | h
              · rw [htarget] at h; cases h
              · have hb := (hterms t ht).symm.trans h
                have : bp t = false := by simpa using Option.some.inj hb
                rw [hbt] at this; cases this
          | array vs =>
              have hex := hc'.resolve_right (by rw [htarget]; exact fun h => nomatch h)
              obtain ⟨t, ht, hbt⟩ := hex
              rcases hl t ht with h | h
              · rw [htarget] at h; cases h
              · have hb := (hterms t ht).symm.trans h
                have : bp t = false := by simpa using Option.some.inj hb
                rw [hbt] at this; cases this

/-- `linkOr` emits only constraints that hold in a store where the target
    is the disjunction of the Boolean terms. -/
theorem linkOr_newHolds {st : ShapeState} {terms : List String} {target : String}
    {s : Store} {b : Bool} {bp : String → Bool}
    (hterms : ∀ t ∈ terms, s (Ident.mk t) = some (.bool (bp t)))
    (htarget : s (Ident.mk target) = some (.bool b))
    (hiff : (b = true ↔ ∃ t ∈ terms, bp t = true)) :
    st.NewHolds (linkOr st terms target) s := by
  intro c hc
  cases terms with
  | nil =>
      have hcons : (linkOr st [] target).cons = pinBoolConstraint target false :: st.cons :=
        rfl
      rw [hcons] at hc
      rcases List.mem_cons.mp hc with h | h
      · subst h
        have hb : b = false := by
          cases b
          · rfl
          · exfalso
            obtain ⟨t, ht, _⟩ := hiff.mp rfl
            cases ht
        subst hb
        exact Or.inr ((ShapeAux.holds_const false target s).mpr htarget)
      · exact Or.inl h
  | cons t0 ts =>
      have hclause : (shapeConstraint "bool_clause"
          [.array ((t0 :: ts).map shapeName), .array [shapeName target]]).Holds
            fullInterp s := by
        have h := holds_bool_clause_shape_bool (s := s) (pos := t0 :: ts)
          (neg := [target]) (bp := bp) (bn := fun _ => b) ?_ ?_ ?_
        · simpa [List.map_cons, List.map_nil] using h
        · exact hterms
        · intro y hy
          simp only [List.mem_singleton] at hy
          rw [hy]
          exact htarget
        · by_cases hb : b = true
          · left
            exact hiff.mp hb
          · right
            have hbf : b = false := by cases b <;> simp_all
            exact ⟨target, by simp, hbf⟩
      have hlink : ∀ t ∈ (t0 :: ts),
          (shapeConstraint "bool_clause"
            [.array [shapeName target], .array [shapeName t]]).Holds fullInterp s := by
        intro t ht
        have h := holds_bool_clause_shape_bool (s := s) (pos := [target])
          (neg := [t]) (bp := fun _ => b) (bn := fun _ => bp t) ?_ ?_ ?_
        · simpa [List.map_cons, List.map_nil] using h
        · intro x hx
          simp only [List.mem_singleton] at hx
          subst hx
          exact htarget
        · intro y hy
          simp only [List.mem_singleton] at hy
          rw [hy]
          exact hterms t ht
        · by_cases hb : bp t = true
          · left
            exact ⟨target, by simp, hiff.mpr ⟨t, ht, hb⟩⟩
          · right
            have hbf : bp t = false := by simpa using hb
            exact ⟨t, by simp, hbf⟩
      simp only [linkOr, ShapeState.emitList, List.mem_append, List.mem_reverse,
        List.mem_cons, List.mem_map] at hc
      rcases hc with (rfl | ⟨a, ha, rfl⟩) | hc
      · exact Or.inr hclause
      · exact Or.inr (hlink a (List.mem_cons.mpr ha))
      · exact Or.inl hc

/-! ## Constraint-list monotonicity -/

/-- Satisfaction is monotone in the accumulated constraint list. -/
theorem ShapeState.holds_mono {st st' : ShapeState} {s : Store}
    (hsub : ∀ c ∈ st.cons, c ∈ st'.cons) (h : st'.Holds s) : st.Holds s :=
  fun c hc => h c (hsub c hc)

/-- `freshBool` keeps every old constraint. -/
theorem ShapeState.freshBool_cons_subset {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState}
    (h : st.freshBool taken kind = (n, st')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  intro c hc
  rw [ShapeState.freshBool_cons h]
  exact List.mem_cons_of_mem _ hc

/-- `freshInt01` keeps every old constraint. -/
theorem ShapeState.freshInt01_cons_subset {taken : List String} {st : ShapeState}
    {kind : ShapeKind} {n : String} {st' : ShapeState}
    (h : st.freshInt01 taken kind = (n, st')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  intro c hc
  rw [ShapeState.freshInt01_cons h]
  exact List.mem_cons_of_mem _ hc

/-- `emit` keeps every old constraint. -/
theorem ShapeState.emit_cons_subset {st : ShapeState} {c : ConstraintItem} :
    ∀ c' ∈ st.cons, c' ∈ (st.emit c).cons := by
  intro c' hc'
  exact List.mem_cons_of_mem _ hc'

/-- `emitList` keeps every old constraint. -/
theorem ShapeState.emitList_cons_subset {st : ShapeState} {cs : List ConstraintItem} :
    ∀ c' ∈ st.cons, c' ∈ (st.emitList cs).cons := by
  intro c' hc'
  exact List.mem_append_right _ hc'

/-! ## Membership terms -/

/-- The membership term allocated for one value reads the source set's
    membership decision. -/
theorem memberTerm_holds {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {v : Int} {us : List Int} {n : String} {st' : ShapeState}
    {s' : Store} {sv : IntSetValue}
    (hus : modelSetUniverse? m S = some us)
    (h : memberTerm taken m st (.basic (.ident (Ident.mk S))) v = some (n, st'))
    (hdefs : st'.DefHolds s')
    (hS : s' (Ident.mk S) = some (.setOfInt sv))
    (hdecl : ∀ w, w ∉ us → ¬ sv.Contains w) :
    s' (Ident.mk n) = some (.bool (decide (sv.Contains v))) := by
  simp only [memberTerm, hus] at h
  by_cases hv : v ∈ us
  · rw [if_pos hv] at h
    have h' : st.freshBool taken (.member S v) = (n, st') := Option.some.inj h
    have haux : (⟨n, .par .bool, .member S v⟩ : ShapeAux) ∈ st'.aux := by
      rw [ShapeState.freshBool_aux h']
      exact List.mem_cons_self ..
    have hdef : (⟨n, .par .bool, .member S v⟩ : ShapeAux).definition.Holds fullInterp s' :=
      hdefs _ haux
    obtain ⟨sv', hsv', hn⟩ := (ShapeAux.holds_member S v n s').mp hdef
    have hsv : sv' = sv := by
      have h := Option.some.inj (hsv'.symm.trans hS)
      simpa using h
    subst hsv
    exact hn
  · rw [if_neg hv] at h
    have h' : st.freshBool taken (.const false) = (n, st') := Option.some.inj h
    have haux : (⟨n, .par .bool, .const false⟩ : ShapeAux) ∈ st'.aux := by
      rw [ShapeState.freshBool_aux h']
      exact List.mem_cons_self ..
    have hdef : (⟨n, .par .bool, .const false⟩ : ShapeAux).definition.Holds fullInterp s' :=
      hdefs _ haux
    have hn : s' (Ident.mk n) = some (.bool false) :=
      (ShapeAux.holds_const false n s').mp hdef
    have hnc : ¬ sv.Contains v := hdecl v hv
    rw [hn]
    simp [hnc]

/-- A membership term keeps every old auxiliary. -/
theorem memberTerm_aux_subset {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState}
    (h : memberTerm taken m st sa v = some (n, st')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              by_cases hv : v ∈ us
              · simp only [memberTerm, hus, if_pos hv] at h
                intro a ha
                rw [ShapeState.freshBool_aux (Option.some.inj h)]
                exact List.mem_cons_of_mem _ ha
              · simp only [memberTerm, hus, if_neg hv] at h
                intro a ha
                rw [ShapeState.freshBool_aux (Option.some.inj h)]
                exact List.mem_cons_of_mem _ ha
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm] at h
              intro a ha
              rw [ShapeState.freshBool_aux (Option.some.inj h)]
              exact List.mem_cons_of_mem _ ha
  | array es => simp [memberTerm] at h

/-- A membership term only adds its own definition. -/
theorem memberTerm_newHolds {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState} {s' : Store}
    (h : memberTerm taken m st sa v = some (n, st'))
    (hdefs : st'.DefHolds s') :
    st.NewHolds st' s' := by
  have step : ∀ {kind : ShapeKind}, st.freshBool taken kind = (n, st') →
      st.NewHolds st' s' := by
    intro kind hf c hc
    have haux : (⟨n, .par .bool, kind⟩ : ShapeAux) ∈ st'.aux := by
      rw [ShapeState.freshBool_aux hf]
      exact List.mem_cons_self ..
    rw [ShapeState.freshBool_cons hf] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Or.inr (hdefs _ haux)
    · exact Or.inl hc
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              by_cases hv : v ∈ us
              · simp only [memberTerm, hus, if_pos hv] at h
                exact step (Option.some.inj h)
              · simp only [memberTerm, hus, if_neg hv] at h
                exact step (Option.some.inj h)
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm] at h
              exact step (Option.some.inj h)
  | array es => simp [memberTerm] at h

/-- A membership term keeps every old constraint. -/
theorem memberTerm_cons_subset {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState}
    (h : memberTerm taken m st sa v = some (n, st')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              by_cases hv : v ∈ us
              · simp only [memberTerm, hus, if_pos hv] at h
                exact ShapeState.freshBool_cons_subset (Option.some.inj h)
              · simp only [memberTerm, hus, if_neg hv] at h
                exact ShapeState.freshBool_cons_subset (Option.some.inj h)
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm] at h
              exact ShapeState.freshBool_cons_subset (Option.some.inj h)
  | array es => simp [memberTerm] at h

/-! ## Variable membership -/

/-- One recursive step of `varMemberTerms`. -/
theorem varMemberTerms_cons_eq {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {v : Int} {vs : List Int} {e : String} {st1 : ShapeState}
    {a : String} {st2 : ShapeState} {t : String} {st3 : ShapeState}
    {ts : List String} {st4 : ShapeState}
    (hfb : st.freshBool taken (.eq x v) = (e, st1))
    (hm : memberTerm taken m st1 (.basic (.ident (Ident.mk s))) v = some (a, st2))
    (ha : st2.freshBool taken (.and e a) = (t, st3))
    (hr : varMemberTerms taken m x s st3 vs = some (ts, st4)) :
    varMemberTerms taken m x s st (v :: vs) = some (t :: ts, st4) := by
  simp [varMemberTerms, hfb, hm, ha, hr]

/-- Decompose one successful `varMemberTerms` step. -/
theorem varMemberTerms_cons_decomp {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {v : Int} {vs : List Int} {terms : List String}
    {st' : ShapeState}
    (h : varMemberTerms taken m x s st (v :: vs) = some (terms, st')) :
    ∃ (e : String) (st1 : ShapeState) (a : String) (st2 : ShapeState)
      (t : String) (st3 : ShapeState) (ts : List String) (st4 : ShapeState),
      st.freshBool taken (.eq x v) = (e, st1) ∧
      memberTerm taken m st1 (.basic (.ident (Ident.mk s))) v = some (a, st2) ∧
      st2.freshBool taken (.and e a) = (t, st3) ∧
      varMemberTerms taken m x s st3 vs = some (ts, st4) ∧
      terms = t :: ts ∧ st' = st4 := by
  cases hfb : st.freshBool taken (.eq x v) with
  | mk e st1 =>
    cases hm : memberTerm taken m st1 (.basic (.ident (Ident.mk s))) v with
    | none => simp [varMemberTerms, hfb, hm] at h
    | some p =>
      cases p with
      | mk a st2 =>
        cases ha : st2.freshBool taken (.and e a) with
        | mk t st3 =>
          cases hr : varMemberTerms taken m x s st3 vs with
          | none => simp [varMemberTerms, hfb, hm, ha, hr] at h
          | some q =>
            cases q with
            | mk ts st4 =>
              simp [varMemberTerms, hfb, hm, ha, hr] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ⟨e, st1, a, st2, t, st3, ts, st4, rfl, hm, ha, hr, rfl, rfl⟩

/-- `varMemberTerms` keeps every old constraint. -/
theorem varMemberTerms_cons_subset {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    (h : varMemberTerms taken m x s st vals = some (terms, st')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c hc => hc
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      intro c hc
      have h1 : c ∈ st1.cons := ShapeState.freshBool_cons_subset hfb c hc
      have h2 : c ∈ st2.cons := memberTerm_cons_subset hm c h1
      have h3 : c ∈ st3.cons := ShapeState.freshBool_cons_subset ha c h2
      exact ih hr c h3

/-- `varMemberTerms` keeps every old auxiliary. -/
theorem varMemberTerms_aux_subset {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    (h : varMemberTerms taken m x s st vals = some (terms, st')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      intro b hb
      exact ih hr b
        (ShapeState.freshBool_aux_subset ha b
          (memberTerm_aux_subset hm b
            (ShapeState.freshBool_aux_subset hfb b hb)))

/-- `varMemberTerms` only adds definitions. -/
theorem varMemberTerms_newHolds {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    {s' : Store}
    (h : varMemberTerms taken m x s st vals = some (terms, st'))
    (hdefs : st'.DefHolds s') :
    st.NewHolds st' s' := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro c hc
      exact Or.inl hc
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      have hax2 : ∀ b ∈ st2.aux, b ∈ st'.aux := by
        intro b hb
        exact varMemberTerms_aux_subset hr b
          (ShapeState.freshBool_aux_subset ha b hb)
      have hep : (⟨e, .par .bool, .eq x v⟩ : ShapeAux) ∈ st'.aux := by
        apply varMemberTerms_aux_subset hr
        apply ShapeState.freshBool_aux_subset ha
        apply memberTerm_aux_subset hm
        rw [ShapeState.freshBool_aux hfb]
        exact List.mem_cons_self ..
      have htp : (⟨t, .par .bool, .and e a⟩ : ShapeAux) ∈ st'.aux := by
        apply varMemberTerms_aux_subset hr
        rw [ShapeState.freshBool_aux ha]
        exact List.mem_cons_self ..
      exact ShapeState.newHolds_trans
        (ShapeState.freshBool_newHolds hfb (hdefs _ hep))
        (ShapeState.newHolds_trans
          (memberTerm_newHolds hm (ShapeState.DefHolds.mono hax2 hdefs))
          (ShapeState.newHolds_trans
            (ShapeState.freshBool_newHolds ha (hdefs _ htp))
            (ih hr hdefs)))

/-- The terms allocated for the finite values of a variable integer read
    the equality and membership decisions. -/
theorem varMemberTerms_sound {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    {s' : Store} {i : Int} {sv : IntSetValue} {us : List Int}
    (h : varMemberTerms taken m x s st vals = some (terms, st'))
    (hdefs : st'.DefHolds s')
    (hx : s' (Ident.mk x) = some (.int i))
    (hS : s' (Ident.mk s) = some (.setOfInt sv))
    (hus : modelSetUniverse? m s = some us)
    (hdecl : ∀ w, w ∉ us → ¬ sv.Contains w) :
    Forall2 (fun t v => s' (Ident.mk t) =
      some (.bool (decide (i = v) && decide (sv.Contains v)))) terms vals := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Forall2]
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      have hax2 : ∀ b ∈ st2.aux, b ∈ st'.aux := by
        intro b hb
        exact varMemberTerms_aux_subset hr b
          (ShapeState.freshBool_aux_subset ha b hb)
      have hep : (⟨e, .par .bool, .eq x v⟩ : ShapeAux) ∈ st'.aux := by
        apply varMemberTerms_aux_subset hr
        apply ShapeState.freshBool_aux_subset ha
        apply memberTerm_aux_subset hm
        rw [ShapeState.freshBool_aux hfb]
        exact List.mem_cons_self ..
      have htp : (⟨t, .par .bool, .and e a⟩ : ShapeAux) ∈ st'.aux := by
        apply varMemberTerms_aux_subset hr
        rw [ShapeState.freshBool_aux ha]
        exact List.mem_cons_self ..
      -- the equality bit reads `x = v`
      have hedef : (⟨e, .par .bool, .eq x v⟩ : ShapeAux).definition.Holds fullInterp s' :=
        hdefs _ hep
      obtain ⟨j, hxj, hej⟩ := (ShapeAux.holds_eq x v e s').mp hedef
      have hji : j = i := by
        have h := Option.some.inj (hxj.symm.trans hx)
        simpa using h
      have hej' : s' (Ident.mk e) = some (.bool (decide (i = v))) := by
        rw [hej, hji]
      -- the membership bit reads `v ∈ S`
      have ham : s' (Ident.mk a) = some (.bool (decide (sv.Contains v))) :=
        memberTerm_holds hus hm (ShapeState.DefHolds.mono hax2 hdefs) hS hdecl
      -- the conjunction
      have htdef : (⟨t, .par .bool, .and e a⟩ : ShapeAux).definition.Holds fullInterp s' :=
        hdefs _ htp
      obtain ⟨pe, pa, hep', hap, htp'⟩ := (ShapeAux.holds_and e a t s').mp htdef
      have hpe : pe = decide (i = v) := by
        rw [hej'] at hep'
        simpa using (Option.some.inj hep').symm
      have hpa : pa = decide (sv.Contains v) := by
        rw [ham] at hap
        simpa using (Option.some.inj hap).symm
      rw [hpe, hpa] at htp'
      refine ⟨htp', ?_⟩
      exact ih hr hdefs


/-! ## Variable membership: structural invariants -/

/-- A membership term is a Boolean auxiliary of the resulting state. -/
theorem memberTerm_aux {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState}
    (h : memberTerm taken m st sa v = some (n, st')) :
    ∃ c ∈ st'.aux, c.name = n ∧ c.ty = .par .bool := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              by_cases hv : v ∈ us
              · simp only [memberTerm, hus, if_pos hv, Option.some.injEq] at h
                refine ⟨⟨n, .par .bool, .member S.name v⟩, ?_, rfl, rfl⟩
                rw [ShapeState.freshBool_aux h]
                exact List.mem_cons_self ..
              · simp only [memberTerm, hus, if_neg hv, Option.some.injEq] at h
                refine ⟨⟨n, .par .bool, .const false⟩, ?_, rfl, rfl⟩
                rw [ShapeState.freshBool_aux h]
                exact List.mem_cons_self ..
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm, Option.some.injEq] at h
              refine ⟨⟨n, .par .bool, .const (decide (sl.denote.Contains v))⟩, ?_, rfl, rfl⟩
              rw [ShapeState.freshBool_aux h]
              exact List.mem_cons_self ..
  | array es => simp [memberTerm] at h

/-- A membership term preserves well-formedness when its source name is
    taken. -/
theorem memberTerm_wf_ident {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {v : Int} {n : String} {st' : ShapeState}
    (hwf : st.WF taken m) (hS : S ∈ taken)
    (h : memberTerm taken m st (.basic (.ident (Ident.mk S))) v = some (n, st')) :
    st'.WF taken m := by
  cases hus : modelSetUniverse? m S with
  | none => simp [memberTerm, hus] at h
  | some us =>
      by_cases hv : v ∈ us
      · simp only [memberTerm, hus, if_pos hv, Option.some.injEq] at h
        have hsnd : st' = (st.freshBool taken (.member S v)).2 := by rw [h]
        rw [hsnd]
        refine ShapeState.freshBool_wf hwf (.member S v) ?_ ?_ ?_ ?_ ⟨us, hus⟩
        · intro d hd
          simp only [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps,
            List.append_nil, List.mem_singleton] at hd
          subst hd
          exact Or.inl hS
        · intro d hd
          simp only [ShapeKind.sourceDeps, List.mem_singleton] at hd
          subst hd
          exact hS
        · intro d hd
          simp [ShapeKind.auxDeps] at hd
        · simp [ShapeAux.TyOk]
      · simp only [memberTerm, hus, if_neg hv, Option.some.injEq] at h
        have hsnd : st' = (st.freshBool taken (.const false)).2 := by rw [h]
        rw [hsnd]
        refine ShapeState.freshBool_wf hwf (.const false) ?_ ?_ ?_ ?_ trivial
        · intro d hd
          simp [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] at hd
        · intro d hd
          simp [ShapeKind.sourceDeps] at hd
        · intro d hd
          simp [ShapeKind.auxDeps] at hd
        · simp [ShapeAux.TyOk]

/-- A membership term preserves the mention invariant. -/
theorem memberTerm_mentionsWithin_ident {taken : List String} {m : Model}
    {st : ShapeState} {S : String} {v : Int} {n : String} {st' : ShapeState}
    (hm : ShapeState.MentionsWithin taken st) (hS : S ∈ taken)
    (h : memberTerm taken m st (.basic (.ident (Ident.mk S))) v = some (n, st')) :
    ShapeState.MentionsWithin taken st' := by
  cases hus : modelSetUniverse? m S with
  | none => simp [memberTerm, hus] at h
  | some us =>
      by_cases hv : v ∈ us
      · simp only [memberTerm, hus, if_pos hv, Option.some.injEq] at h
        have hsnd : st' = (st.freshBool taken (.member S v)).2 := by rw [h]
        rw [hsnd]
        refine ShapeState.freshBool_mentionsWithin hm (.member S v) ?_
        intro d hd
        simp only [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps,
          List.append_nil, List.mem_singleton] at hd
        subst hd
        exact Or.inl hS
      · simp only [memberTerm, hus, if_neg hv, Option.some.injEq] at h
        have hsnd : st' = (st.freshBool taken (.const false)).2 := by rw [h]
        rw [hsnd]
        refine ShapeState.freshBool_mentionsWithin hm (.const false) ?_
        intro d hd
        simp [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] at hd

/-- `varMemberTerms` preserves well-formedness. -/
theorem varMemberTerms_wf {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    {us : List Int}
    (hwf : st.WF taken m) (hx : x ∈ taken) (hs : s ∈ taken)
    (hvals : ∃ vals, modelIntValues? m x = some vals)
    (hus : modelSetUniverse? m s = some us)
    (h : varMemberTerms taken m x s st vals = some (terms, st')) :
    st'.WF taken m := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hm, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      have hwf1 : st1.WF taken m := by
        have hsnd : st1 = (st.freshBool taken (.eq x v)).2 := by rw [hfb]
        rw [hsnd]
        refine ShapeState.freshBool_wf hwf (.eq x v) ?_ ?_ ?_ ?_ hvals
        · intro d hd
          have hd' : d = x := by
            simpa [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] using hd
          subst hd'
          exact Or.inl hx
        · intro d hd
          have hd' : d = x := by simpa [ShapeKind.sourceDeps] using hd
          subst hd'
          exact hx
        · intro d hd
          simp [ShapeKind.auxDeps] at hd
        · simp [ShapeAux.TyOk]
      have hwf2 : st2.WF taken m :=
        memberTerm_wf_ident hwf1 hs hm
      obtain ⟨ce, hce, hcename, hcety⟩ : ∃ c ∈ st2.aux,
          c.name = e ∧ c.ty = .par .bool := by
        refine ⟨⟨e, .par .bool, .eq x v⟩, ?_, rfl, rfl⟩
        apply memberTerm_aux_subset hm
        rw [ShapeState.freshBool_aux hfb]
        exact List.mem_cons_self ..
      obtain ⟨ca, hca, hcaname, hcaty⟩ : ∃ c ∈ st2.aux,
          c.name = a ∧ c.ty = .par .bool := memberTerm_aux hm
      have hwf3 : st3.WF taken m := by
        have hsnd : st3 = (st2.freshBool taken (.and e a)).2 := by rw [ha]
        rw [hsnd]
        refine ShapeState.freshBool_wf hwf2 (.and e a) ?_ ?_ ?_ ?_ trivial
        · intro d hd
          have hd' : d = e ∨ d = a := by
            simpa [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] using hd
          rcases hd' with rfl | rfl
          · exact Or.inr (List.mem_map.mpr ⟨ce, hce, hcename⟩)
          · exact Or.inr (List.mem_map.mpr ⟨ca, hca, hcaname⟩)
        · intro d hd
          simp [ShapeKind.sourceDeps] at hd
        · intro d hd
          have hd' : d = e ∨ d = a := by
            simpa [ShapeKind.auxDeps] using hd
          rcases hd' with rfl | rfl
          · exact ⟨ce, hce, hcename, hcety⟩
          · exact ⟨ca, hca, hcaname, hcaty⟩
        · simp [ShapeAux.TyOk]
      exact ih hwf3 hr

/-- `varMemberTerms` preserves the mention invariant. -/
theorem varMemberTerms_mentionsWithin {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    (hm : ShapeState.MentionsWithin taken st) (hx : x ∈ taken) (hs : s ∈ taken)
    (h : varMemberTerms taken m x s st vals = some (terms, st')) :
    ShapeState.MentionsWithin taken st' := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hm
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hmem, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      have hm1 : ShapeState.MentionsWithin taken st1 := by
        have hsnd : st1 = (st.freshBool taken (.eq x v)).2 := by rw [hfb]
        rw [hsnd]
        refine ShapeState.freshBool_mentionsWithin hm (.eq x v) ?_
        intro d hd
        have hd' : d = x := by
          simpa [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] using hd
        subst hd'
        exact Or.inl hx
      have hm2 : ShapeState.MentionsWithin taken st2 :=
        memberTerm_mentionsWithin_ident hm1 hs hmem
      obtain ⟨ce, hce, hcename, _⟩ : ∃ c ∈ st2.aux,
          c.name = e ∧ c.ty = .par .bool := by
        refine ⟨⟨e, .par .bool, .eq x v⟩, ?_, rfl, rfl⟩
        apply memberTerm_aux_subset hmem
        rw [ShapeState.freshBool_aux hfb]
        exact List.mem_cons_self ..
      obtain ⟨ca, hca, hcaname, _⟩ : ∃ c ∈ st2.aux,
          c.name = a ∧ c.ty = .par .bool := memberTerm_aux hmem
      have hm3 : ShapeState.MentionsWithin taken st3 := by
        have hsnd : st3 = (st2.freshBool taken (.and e a)).2 := by rw [ha]
        rw [hsnd]
        refine ShapeState.freshBool_mentionsWithin hm2 (.and e a) ?_
        intro d hd
        have hd' : d = e ∨ d = a := by
          simpa [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] using hd
        rcases hd' with rfl | rfl
        · exact Or.inr (List.mem_map.mpr ⟨ce, hce, hcename⟩)
        · exact Or.inr (List.mem_map.mpr ⟨ca, hca, hcaname⟩)
      exact ih hm3 hr

/-- Every term allocated by `varMemberTerms` is an auxiliary of the
    resulting state. -/
theorem varMemberTerms_terms_aux {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {vals : List Int} {terms : List String} {st' : ShapeState}
    (h : varMemberTerms taken m x s st vals = some (terms, st')) :
    ∀ t ∈ terms, t ∈ st'.aux.map (fun a => a.name) := by
  induction vals generalizing st terms st' with
  | nil =>
      simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      intro t ht
      cases ht
  | cons v vs ih =>
      obtain ⟨e, st1, a, st2, t, st3, ts, st4, hfb, hmem, ha, hr, rfl, rfl⟩ :=
        varMemberTerms_cons_decomp h
      intro u hu
      rcases List.mem_cons.mp hu with rfl | hu
      · have haux : (⟨u, .par .bool, .and e a⟩ : ShapeAux) ∈ st'.aux := by
          apply varMemberTerms_aux_subset hr
          rw [ShapeState.freshBool_aux ha]
          exact List.mem_cons_self ..
        exact List.mem_map.mpr ⟨_, haux, rfl⟩
      · exact ih hr u hu

/-- `varMemberTerms` with an empty value list returns the terms in order. -/
theorem varMemberTerms_nil_inv {taken : List String} {m : Model} {x s : String}
    {st : ShapeState} {terms : List String} {st' : ShapeState}
    (h : varMemberTerms taken m x s st [] = some (terms, st')) :
    terms = [] ∧ st' = st := by
  simp only [varMemberTerms, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, h.2.symm⟩


/-! ## The result target: invariants -/

/-- `resultTarget` preserves well-formedness. -/
theorem resultTarget_wf {taken : List String} {m : Model} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState}
    (hwf : st.WF taken m) (h : resultTarget taken st r = some (n, st')) :
    st'.WF taken m := by
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget, Option.some.injEq] at h
            have hsnd : st' = (st.freshBool taken (.const false)).2 := by rw [h]
            rw [hsnd]
            refine ShapeState.freshBool_wf hwf (.const false) ?_ ?_ ?_ ?_ trivial
            · intro d hd; simp [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] at hd
            · intro d hd; simp [ShapeKind.sourceDeps] at hd
            · intro d hd; simp [ShapeKind.auxDeps] at hd
            · simp [ShapeAux.TyOk]
          · simp only [resultTarget, Option.some.injEq] at h
            have hsnd : st' = (st.freshBool taken (.const true)).2 := by rw [h]
            rw [hsnd]
            refine ShapeState.freshBool_wf hwf (.const true) ?_ ?_ ?_ ?_ trivial
            · intro d hd; simp [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] at hd
            · intro d hd; simp [ShapeKind.sourceDeps] at hd
            · intro d hd; simp [ShapeKind.auxDeps] at hd
            · simp [ShapeAux.TyOk]
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-- `resultTarget` preserves the mention invariant. -/
theorem resultTarget_mentionsWithin {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState}
    (hm : ShapeState.MentionsWithin taken st) (h : resultTarget taken st r = some (n, st')) :
    ShapeState.MentionsWithin taken st' := by
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hm
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget, Option.some.injEq] at h
            have hsnd : st' = (st.freshBool taken (.const false)).2 := by rw [h]
            rw [hsnd]
            refine ShapeState.freshBool_mentionsWithin hm (.const false) ?_
            intro d hd
            simp [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] at hd
          · simp only [resultTarget, Option.some.injEq] at h
            have hsnd : st' = (st.freshBool taken (.const true)).2 := by rw [h]
            rw [hsnd]
            refine ShapeState.freshBool_mentionsWithin hm (.const true) ?_
            intro d hd
            simp [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] at hd
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-- The result target is a taken name or an auxiliary of the new state. -/
theorem resultTarget_target_mem {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState}
    (h : resultTarget taken st r = some (n, st'))
    (hsrc : ∀ d ∈ basicNames r, d ∈ taken) :
    n ∈ taken ∨ n ∈ st'.aux.map (fun a => a.name) := by
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl (hsrc b.name (by simp [basicNames]))
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget, Option.some.injEq] at h
            right
            rw [ShapeState.freshBool_aux h]
            exact List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩
          · simp only [resultTarget, Option.some.injEq] at h
            right
            rw [ShapeState.freshBool_aux h]
            exact List.mem_map.mpr ⟨_, List.mem_cons_self .., rfl⟩
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-! ## Linking a target to a disjunction: invariants -/

/-- `linkOr` does not allocate auxiliaries. -/
theorem linkOr_aux (st : ShapeState) (terms : List String) (target : String) :
    (linkOr st terms target).aux = st.aux := by
  cases terms <;> rfl

/-- `linkOr` preserves well-formedness. -/
theorem linkOr_wf {taken : List String} {m : Model} {st : ShapeState}
    {terms : List String} {target : String} (hwf : st.WF taken m) :
    (linkOr st terms target).WF taken m := by
  cases terms with
  | nil => exact ShapeState.emit_wf hwf
  | cons t ts => exact ShapeState.emitList_wf hwf

/-- The names of a list of shape identifiers. -/
theorem flatMap_basicNames_map_shapeName (xs : List String) :
    (xs.map shapeName).flatMap basicNames = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [shapeName, basicNames, ih]

/-- The names of a `bool_clause` constraint. -/
theorem constraintNames_bool_clause (pos neg : List String) :
    constraintNames (shapeConstraint "bool_clause"
      [.array (pos.map shapeName), .array (neg.map shapeName)]) = pos ++ neg := by
  simp [constraintNames, exprNames, shapeConstraint, flatMap_basicNames_map_shapeName]

/-- The name of a pinned Boolean constraint. -/
theorem constraintNames_pinBool (n : String) (v : Bool) :
    constraintNames (pinBoolConstraint n v) = [n] := by
  simp [pinBoolConstraint, constraintNames, exprNames, basicNames]

/-- `linkOr` preserves the mention invariant. -/
theorem linkOr_mentionsWithin {taken : List String} {st : ShapeState}
    {terms : List String} {target : String}
    (hm : ShapeState.MentionsWithin taken st)
    (hnames : ∀ x ∈ terms ++ [target],
      x ∈ taken ∨ x ∈ st.aux.map (fun a => a.name)) :
    ShapeState.MentionsWithin taken (linkOr st terms target) := by
  cases terms with
  | nil =>
      apply ShapeState.mentionsWithin_emit hm
      intro x hx
      rw [constraintNames_pinBool] at hx
      exact hnames x (by simpa using hx)
  | cons t ts =>
      show ShapeState.MentionsWithin taken (st.emitList
        (shapeConstraint "bool_clause"
            [.array ((t :: ts).map shapeName), .array ([target].map shapeName)] ::
          (t :: ts).map (fun u => shapeConstraint "bool_clause"
            [.array ([target].map shapeName), .array ([u].map shapeName)])))
      apply ShapeState.mentionsWithin_emitList hm
      intro c hc x hx
      have hxall : x ∈ (t :: ts) ++ [target] := by
        simp only [List.mem_cons, List.mem_map] at hc
        rcases hc with rfl | ⟨u, hu, rfl⟩
        · simpa only [constraintNames_bool_clause] using hx
        · have hx' : x ∈ [target] ++ [u] := by
            simpa only [constraintNames_bool_clause] using hx
          have hx'' : x = target ∨ x = u := by
            simpa only [List.mem_append, List.mem_singleton] using hx'
          rcases hx'' with rfl | rfl
          · simp
          · rcases hu with rfl | hu
            · simp
            · exact List.mem_append_left _ (List.mem_cons_of_mem _ hu)
      exact hnames x hxall

/-! ## Variable membership rewrite -/

/-- Decompose a successful `rewriteVarMember`. -/
theorem rewriteVarMember_decomp {taken : List String} {m : Model} {st : ShapeState}
    {x s : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteVarMember taken m st x s vals r = some (st', cs')) :
    ∃ tms st1 target st2,
      varMemberTerms taken m x s st vals = some (tms, st1) ∧
      resultTarget taken st1 r = some (target, st2) ∧
      st' = linkOr st2 tms target ∧ cs' = [] := by
  unfold rewriteVarMember at h
  cases hterms : varMemberTerms taken m x s st vals with
  | none => simp [hterms] at h
  | some p =>
      obtain ⟨tms, st1⟩ := p
      cases hres : resultTarget taken st1 r with
      | none => simp [hterms, hres] at h
      | some q =>
          obtain ⟨target, st2⟩ := q
          simp only [hterms, hres, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨tms, st1, target, st2, rfl, hres, rfl, rfl⟩

/-- `rewriteVarMember` preserves well-formedness. -/
theorem rewriteVarMember_wf {taken : List String} {m : Model} {st : ShapeState}
    {x s : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (hwf : st.WF taken m) (hx : x ∈ taken) (hs : s ∈ taken)
    (hvals : ∃ vs, modelIntValues? m x = some vs)
    (hus : modelSetUniverse? m s = some us)
    (h : rewriteVarMember taken m st x s vals r = some (st', cs')) :
    st'.WF taken m := by
  obtain ⟨terms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  exact linkOr_wf (resultTarget_wf (varMemberTerms_wf hwf hx hs hvals hus hterms) hres)

/-- `rewriteVarMember` preserves the mention invariant. -/
theorem rewriteVarMember_mentionsWithin {taken : List String} {m : Model}
    {st : ShapeState} {x s : String} {vals : List Int} {r : BasicExpr}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (hm : ShapeState.MentionsWithin taken st) (hx : x ∈ taken) (hs : s ∈ taken)
    (hr : ∀ d ∈ basicNames r, d ∈ taken)
    (h : rewriteVarMember taken m st x s vals r = some (st', cs')) :
    ShapeState.MentionsWithin taken st' := by
  obtain ⟨terms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  have hm1 := varMemberTerms_mentionsWithin hm hx hs hterms
  have hm2 := resultTarget_mentionsWithin hm1 hres
  have hterms_aux : ∀ t ∈ terms, t ∈ st2.aux.map (fun a => a.name) := by
    intro t ht
    obtain ⟨a, ha, han⟩ := List.mem_map.mp (varMemberTerms_terms_aux hterms t ht)
    exact List.mem_map.mpr ⟨a, resultTarget_aux_subset hres a ha, han⟩
  have htarget := resultTarget_target_mem hres hr
  refine linkOr_mentionsWithin hm2 ?_
  intro y hy
  rcases List.mem_append.mp hy with hyt | hyt
  · exact Or.inr (hterms_aux y hyt)
  · simp only [List.mem_singleton] at hyt
    subst hyt
    exact htarget

/-! ## Reified membership at an arbitrary first argument -/

/-- The truth of `set_in_reif(x, S, R)` where `x` evaluates to an integer
    value. -/
theorem setInReif_expr_holds_iff {x S R : BasicExpr} {s : Store}
    {anns : List Annotation} :
    (ConstraintItem.mk (Ident.mk "set_in_reif")
        [.basic x, .basic S, .basic R] anns).Holds fullInterp s ↔
      ∃ k sv r, BasicExpr.eval s x = some (.int k) ∧
        BasicExpr.eval s S = some (.setOfInt sv) ∧
        BasicExpr.eval s R = some (.bool r) ∧
        ((r = true ∧ sv.Contains k) ∨ (r = false ∧ ¬ sv.Contains k)) := by
  rw [holds_basic_three (by decide)]
  constructor
  · rintro ⟨v₁, v₂, v₃, h₁, h₂, h₃, hP⟩
    cases v₁ with
    | int k =>
        cases v₂ with
        | setOfInt sv =>
            cases v₃ with
            | bool r =>
                exact ⟨k, sv, r, h₁, h₂, h₃, by simpa [stdInterp] using hP⟩
            | int i => simp [stdInterp] at hP
            | setOfInt x => simp [stdInterp] at hP
            | array x => simp [stdInterp] at hP
        | bool b => simp [stdInterp] at hP
        | int i => simp [stdInterp] at hP
        | array l => simp [stdInterp] at hP
    | bool b => simp [stdInterp] at hP
    | setOfInt sv => simp [stdInterp] at hP
    | array l => simp [stdInterp] at hP
  · rintro ⟨k, sv, r, h₁, h₂, h₃, hP⟩
    exact ⟨.int k, .setOfInt sv, .bool r, h₁, h₂, h₃,
      by simpa [stdInterp] using hP⟩

/-! ## Linear rows over coefficient/variable pairs -/

/-- `mapM` over three elements. -/
theorem mapM_three_iff {α β : Type} (f : α → Option β) (a b c : α) (args : List β) :
    [a, b, c].mapM f = some args ↔
      ∃ x y z, f a = some x ∧ f b = some y ∧ f c = some z ∧ args = [x, y, z] := by
  cases h1 : f a with
  | none => simp [List.mapM_cons, h1]
  | some x =>
    cases h2 : f b with
    | none => simp [List.mapM_cons, h1, h2]
    | some y =>
      cases h3 : f c with
      | none => simp [List.mapM_cons, h1, h2, h3]
      | some z => simp [List.mapM_cons, h1, h2, h3, eq_comm]

/-- A successful `mapM` of identifier arguments starts with the head. -/
theorem mapM_shapeName_cons {s : Store} {vs : List Value}
    {c : Int} {x : Ident} {rest : List (Int × Ident)}
    (h : (((c, x) :: rest).map (fun p => BasicExpr.ident p.2)).mapM
        (BasicExpr.eval s) = some vs) :
    ∃ v vs', vs = v :: vs' ∧ s x = some v ∧
      (rest.map (fun p => BasicExpr.ident p.2)).mapM (BasicExpr.eval s) = some vs' := by
  simp only [List.map_cons, List.mapM_cons, BasicExpr.eval] at h
  obtain ⟨v, hv, hf⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨vs', hvs', hcons⟩ := Option.bind_eq_some_iff.mp hf
  exact ⟨v, vs', (Option.some.inj hcons).symm, hv, hvs'⟩

/-- `pairSum` agrees with evaluating the coefficient/variable row and
    taking its dot product. -/
theorem pairSum_holds_iff {s : Store} :
    ∀ (ps : List (Int × Ident)) (b : Int), pairSum s ps = some b ↔
      ∃ vs, (ps.map (fun p => BasicExpr.ident p.2)).mapM (BasicExpr.eval s) = some vs ∧
        dotProduct (ps.map (fun p => Value.int p.1)) vs = some b := by
  intro ps
  induction ps with
  | nil =>
      intro b
      constructor
      · intro h
        exact ⟨[], by rfl, by simpa [pairSum, dotProduct] using h⟩
      · rintro ⟨vs, hvs, hdot⟩
        simp only [List.map_nil, List.mapM_nil, pure, Option.some.injEq] at hvs
        subst hvs
        simpa [pairSum, dotProduct] using hdot
  | cons p ps ih =>
      intro b
      obtain ⟨c, x⟩ := p
      constructor
      · intro h
        rw [pairSum.eq_2] at h
        cases hx : s x with
        | none => simp [hx] at h
        | some v =>
            cases v with
            | int i =>
                simp only [hx] at h
                cases hp : pairSum s ps with
                | none => simp [hp] at h
                | some t =>
                    simp only [hp, Option.some.injEq] at h
                    obtain ⟨vs, hvs, hdot⟩ := (ih t).mp hp
                    refine ⟨.int i :: vs, ?_, ?_⟩
                    · simp [BasicExpr.eval, hx, hvs]
                    · simp only [List.map_cons]
                      rw [dotProduct.eq_1, hdot]
                      simp [h]
            | bool bv => simp [hx] at h
            | setOfInt sv => simp [hx] at h
            | array xs => simp [hx] at h
      · rintro ⟨vs, hvs, hdot⟩
        obtain ⟨w, vs', hvsEq, hw, hrest⟩ := mapM_shapeName_cons hvs
        rw [hvsEq] at hdot
        cases w with
        | int i =>
            simp only [List.map_cons] at hdot
            rw [dotProduct.eq_1] at hdot
            split at hdot
            · rename_i t' ht'
              have hb : b = c * i + t' := (Option.some.inj hdot).symm
              have hps' : pairSum s ps = some t' := (ih t').mpr ⟨vs', hrest, ht'⟩
              rw [pairSum.eq_2, hw, hps', hb]
            · cases hdot
        | bool bv => simp [dotProduct] at hdot
        | setOfInt sv => simp [dotProduct] at hdot
        | array xs => simp [dotProduct] at hdot

/-- The emitted `int_lin_eq` row over coefficient/variable pairs. -/
theorem shapeLinEq_pairs_holds_iff {s : Store} {ps : List (Int × Ident)} {rhs : Int} :
    (shapeLinEq (ps.map (fun p => p.1)) (ps.map (fun p => p.2.name)) rhs).Holds
        fullInterp s ↔ pairSum s ps = some rhs := by
  have hargs : (shapeLinEq (ps.map (fun p => p.1)) (ps.map (fun p => p.2.name)) rhs).args =
      [.array (ps.map (fun p => BasicExpr.lit (.int p.1))),
       .array (ps.map (fun p => BasicExpr.ident p.2)),
       shapeE (shapeInt rhs)] := by
    simp only [shapeLinEq, shapeConstraint, List.map_map]
    rfl
  have hname : (shapeLinEq (ps.map (fun p => p.1)) (ps.map (fun p => p.2.name)) rhs).name =
      Ident.mk "int_lin_eq" := rfl
  unfold ConstraintItem.Holds
  rw [hargs, hname, fullInterp_int_lin_eq]
  simp only [mapM_three_iff]
  constructor
  · rintro ⟨args, ⟨v1, v2, v3, h1, h2, h3, rfl⟩, hp⟩
    simp only [Expr.eval] at h1
    obtain ⟨cs, hcs, rfl⟩ := Option.map_eq_some_iff.mp h1
    rw [mapM_lit_int] at hcs
    simp only [Option.some.injEq] at hcs
    subst hcs
    simp only [Expr.eval] at h2
    obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h2
    simp only [shapeE, shapeInt, Expr.eval, BasicExpr.eval, BasicLiteral.denote,
      Option.some.injEq] at h3
    subst h3
    simp only [stdInterp] at hp
    exact (pairSum_holds_iff ps rhs).mpr ⟨xs, hxs, hp⟩
  · intro hsum
    obtain ⟨xs, hxs, hdot⟩ := (pairSum_holds_iff ps rhs).mp hsum
    refine ⟨[.array (ps.map (fun p => Value.int p.1)), .array xs, .int rhs],
      ⟨.array (ps.map (fun p => Value.int p.1)), .array xs, .int rhs, ?_, ?_, ?_, rfl⟩, ?_⟩
    · simp only [Expr.eval]
      rw [mapM_lit_int]
      rfl
    · simp only [Expr.eval]
      simpa using congrArg (Option.map Value.array) hxs
    · simp [shapeE, shapeInt, Expr.eval, BasicExpr.eval, BasicLiteral.denote]
    · simpa [stdInterp] using hdot

/-! ## Variable membership rewrite: soundness and completeness -/

/-- Right-to-left membership for the local `Forall2`. -/
theorem forall2_mem_right {α β : Type} (R : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β), Forall2 R l1 l2 →
    ∀ b ∈ l2, ∃ a ∈ l1, R a b := by
  intro l1
  induction l1 with
  | nil =>
      intro l2 h b hb
      cases l2 with
      | nil => cases hb
      | cons y ys => cases h
  | cons x xs ih =>
      intro l2 h b hb
      cases l2 with
      | nil => cases hb
      | cons y ys =>
          rw [Forall2] at h
          obtain ⟨hxy, hrest⟩ := h
          rcases List.mem_cons.mp hb with rfl | hb'
          · exact ⟨x, List.mem_cons_self, hxy⟩
          · obtain ⟨a, ha, hR⟩ := ih ys hrest b hb'
            exact ⟨a, List.mem_cons_of_mem _ ha, hR⟩

/-- **Soundness of the variable-membership rewrite**: the emitted
    per-value terms and clause force the source `set_in_reif`
    constraint. -/
theorem rewriteVarMember_sound {taken : List String} {m : Model} {st : ShapeState}
    {x S : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem} {str : Store} {us : List Int} {anns : List Annotation}
    (h : rewriteVarMember taken m st x S vals r = some (st', cs'))
    (hdefs : st'.DefHolds str)
    (hholds : (st'.emitList cs').Holds str)
    (hx : ∃ i, str (Ident.mk x) = some (.int i))
    (hval : ∀ i, str (Ident.mk x) = some (.int i) → i ∈ vals)
    (hS : ∃ sv, str (Ident.mk S) = some (.setOfInt sv))
    (hus : modelSetUniverse? m S = some us)
    (hdecl : ∀ sv, str (Ident.mk S) = some (.setOfInt sv) →
      ∀ w, w ∉ us → ¬ sv.Contains w) :
    (ConstraintItem.mk (Ident.mk "set_in_reif")
      [.basic (.ident (Ident.mk x)), .basic (.ident (Ident.mk S)),
        .basic r] anns).Holds fullInterp str := by
  obtain ⟨terms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  obtain ⟨i, hi⟩ := hx
  obtain ⟨sv, hsv⟩ := hS
  have hdefs2 : st2.DefHolds str := by
    intro a ha
    exact hdefs a (by rw [linkOr_aux]; exact ha)
  have hdefs1 : st1.DefHolds str :=
    ShapeState.DefHolds.mono (fun a ha => resultTarget_aux_subset hres a ha) hdefs2
  have htsound := varMemberTerms_sound hterms hdefs1 hi hsv hus
    (by intro w hw hc; exact hdecl sv hsv w hw hc)
  -- every term reads a Boolean
  have htermsBool : ∀ t ∈ terms, ∃ p, str (Ident.mk t) = some (.bool p) := by
    intro t ht
    obtain ⟨v, _, htv⟩ := forall2_mem _ terms vals htsound t ht
    exact ⟨_, htv⟩
  let bp : String → Bool := fun t => match str (Ident.mk t) with
    | some (.bool p) => p
    | _ => false
  have hbp : ∀ t ∈ terms, str (Ident.mk t) = some (.bool (bp t)) := by
    intro t ht
    obtain ⟨p, hp⟩ := htermsBool t ht
    simp [bp, hp]
  have hlink := linkOr_sound (st := st2) (terms := terms) (target := target)
    (s := str) (bp := bp) (by simpa [ShapeState.emitList] using hholds) hbp
  obtain ⟨b, htarget, hiff⟩ := hlink
  -- the terms encode `i ∈ sv`
  have hex : (∃ t ∈ terms, bp t = true) ↔ sv.Contains i := by
    constructor
    · rintro ⟨t, ht, hbt⟩
      obtain ⟨v, _, htv⟩ := forall2_mem _ terms vals htsound t ht
      have hbpv : (decide (i = v) && decide (sv.Contains v)) = bp t := by
        have hv := Option.some.inj (htv.symm.trans (hbp t ht))
        simpa using hv
      rw [← hbpv] at hbt
      rw [Bool.and_eq_true] at hbt
      obtain ⟨hiv, hcv⟩ := hbt
      rw [← of_decide_eq_true hiv] at hcv
      exact of_decide_eq_true hcv
    · intro hc
      have hiv : i ∈ vals := hval i hi
      obtain ⟨t, ht, htv⟩ := forall2_mem_right _ terms vals htsound i hiv
      refine ⟨t, ht, ?_⟩
      have hbpv : (decide (i = i) && decide (sv.Contains i)) = bp t := by
        have hv := Option.some.inj (htv.symm.trans (hbp t ht))
        simpa using hv
      rw [← hbpv]
      simp [hc]
  have hcond : (b = true ∧ sv.Contains i) ∨ (b = false ∧ ¬ sv.Contains i) := by
    cases b with
    | true =>
        exact Or.inl ⟨rfl, hex.mp (hiff.mp rfl)⟩
    | false =>
        refine Or.inr ⟨rfl, ?_⟩
        intro hc
        have hfalse : (false : Bool) = true := hiff.mpr (hex.mpr hc)
        cases hfalse
  rw [setInReif_expr_holds_iff]
  exact ⟨i, sv, b,
    by simpa [BasicExpr.eval] using hi,
    by simpa [BasicExpr.eval] using hsv,
    (resultTarget_eval_iff hres hdefs2 (.bool b)).mpr htarget,
    hcond⟩

/-- **Completeness of the variable-membership rewrite**: in the
    functionally extended store the emitted rows hold whenever the source
    `set_in_reif` constraint holds. -/
theorem rewriteVarMember_newHolds {taken : List String} {m : Model} {st : ShapeState}
    {x S : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem} {s s' : Store} {us : List Int} {anns : List Annotation}
    (h : rewriteVarMember taken m st x S vals r = some (st', cs'))
    (hdefs : st'.DefHolds s')
    (hsrc : (ConstraintItem.mk (Ident.mk "set_in_reif")
      [.basic (.ident (Ident.mk x)), .basic (.ident (Ident.mk S)),
        .basic r] anns).Holds fullInterp s)
    (hxval : ∃ i, s (Ident.mk x) = some (.int i))
    (hSval : ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hxagg : s' (Ident.mk x) = s (Ident.mk x))
    (hSagg : s' (Ident.mk S) = s (Ident.mk S))
    (hr_eval : r.eval s' = r.eval s)
    (hval : ∀ i, s (Ident.mk x) = some (.int i) → i ∈ vals)
    (hus : modelSetUniverse? m S = some us)
    (hdecl : ∀ sv, s (Ident.mk S) = some (.setOfInt sv) →
      ∀ w, w ∉ us → ¬ sv.Contains w) :
    st.NewHolds (st'.emitList cs') s' := by
  obtain ⟨terms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  have hdefs2 : st2.DefHolds s' := by
    intro a ha
    exact hdefs a (by rw [linkOr_aux]; exact ha)
  have hdefs1 : st1.DefHolds s' :=
    ShapeState.DefHolds.mono (fun a ha => resultTarget_aux_subset hres a ha) hdefs2
  obtain ⟨i, hi⟩ := hxval
  obtain ⟨sv, hsv⟩ := hSval
  have hi' : s' (Ident.mk x) = some (.int i) := by rw [hxagg]; exact hi
  have hsv' : s' (Ident.mk S) = some (.setOfInt sv) := by rw [hSagg]; exact hsv
  have htsound := varMemberTerms_sound hterms hdefs1 hi' hsv' hus
    (by intro w hw hc; exact hdecl sv hsv w hw hc)
  -- the source constraint, at the source store
  obtain ⟨k, sv0, rr, hxk, hSk, hRk, hcond⟩ :=
    setInReif_expr_holds_iff.mp hsrc
  have hki : k = i := Value.int.inj (Option.some.inj (hxk.symm.trans hi))
  have hsv0 : sv0 = sv := Value.setOfInt.inj (Option.some.inj (hSk.symm.trans hsv))
  rw [hki, hsv0] at hcond
  -- every term reads a Boolean
  have htermsBool : ∀ t ∈ terms, ∃ p, s' (Ident.mk t) = some (.bool p) := by
    intro t ht
    obtain ⟨v, _, htv⟩ := forall2_mem _ terms vals htsound t ht
    exact ⟨_, htv⟩
  let bp : String → Bool := fun t => match s' (Ident.mk t) with
    | some (.bool p) => p
    | _ => false
  have hbp : ∀ t ∈ terms, s' (Ident.mk t) = some (.bool (bp t)) := by
    intro t ht
    obtain ⟨p, hp⟩ := htermsBool t ht
    simp [bp, hp]
  -- the target evaluates to the source result Boolean
  have hReval : r.eval s' = some (.bool rr) := by
    rw [hr_eval]
    simpa [BasicExpr.eval] using hRk
  have htarget : s' (Ident.mk target) = some (.bool rr) :=
    (resultTarget_eval_iff hres hdefs2 (.bool rr)).mp hReval
  -- the target is the disjunction of the encoded memberships
  have hex : (∃ t ∈ terms, bp t = true) ↔ sv.Contains i := by
    constructor
    · rintro ⟨t, ht, hbt⟩
      obtain ⟨v, _, htv⟩ := forall2_mem _ terms vals htsound t ht
      have hbpv : (decide (i = v) && decide (sv.Contains v)) = bp t := by
        have hv := Option.some.inj (htv.symm.trans (hbp t ht))
        simpa using hv
      rw [← hbpv] at hbt
      rw [Bool.and_eq_true] at hbt
      obtain ⟨hiv, hcv⟩ := hbt
      rw [← of_decide_eq_true hiv] at hcv
      exact of_decide_eq_true hcv
    · intro hc
      have hiv : i ∈ vals := hval i hi
      obtain ⟨t, ht, htv⟩ := forall2_mem_right _ terms vals htsound i hiv
      refine ⟨t, ht, ?_⟩
      have hbpv : (decide (i = i) && decide (sv.Contains i)) = bp t := by
        have hv := Option.some.inj (htv.symm.trans (hbp t ht))
        simpa using hv
      rw [← hbpv]
      simp [hc]
  have hiff : (rr = true ↔ ∃ t ∈ terms, bp t = true) := by
    rw [hex]
    rcases hcond with ⟨hr, hc⟩ | ⟨hr, hc⟩
    · subst hr
      exact ⟨fun _ => hc, fun _ => rfl⟩
    · subst hr
      exact ⟨fun h => absurd h (by decide), fun hc' => absurd hc' hc⟩
  have hnew := varMemberTerms_newHolds hterms hdefs1
  have hnew2 := resultTarget_newHolds hres hdefs2
  have hnew3 := linkOr_newHolds (st := st2) (terms := terms) (target := target)
    (s := s') (b := rr) (bp := bp) hbp htarget hiff
  have hchain := ShapeState.newHolds_trans hnew
    (ShapeState.newHolds_trans hnew2 hnew3)
  simpa [ShapeState.emitList] using hchain

/-! ## Cardinality rewrite -/

/-- Summing unit coefficients over a list of names paired with an
    indicator list. -/
theorem pairSum_map_one_forall2 {s : Store} (f : Int → Int) :
    ∀ {cs : List String} {us : List Int},
      Forall2 (fun c v => s (Ident.mk c) = some (.int (f v))) cs us →
      pairSum s (cs.map (fun c => (1, Ident.mk c))) = some ((us.map f).sum) := by
  intro cs
  induction cs with
  | nil =>
      intro us h
      cases us with
      | nil => simp [pairSum]
      | cons u us => cases h
  | cons c cs ih =>
      intro us h
      cases us with
      | nil => cases h
      | cons u us =>
          rw [Forall2] at h
          obtain ⟨hc, hrest⟩ := h
          have hrec := ih hrest
          rw [List.map_cons]
          unfold pairSum
          rw [hc, hrec]
          simp

/-- Constants projected out of the card membership pair list. -/
theorem map_fst_cardPairs (cs : List String) :
    cs.map ((fun p : Int × Ident => p.1) ∘ fun c => ((1 : Int), Ident.mk c)) =
      cs.map (fun _ => 1) := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- Names projected out of the card membership pair list. -/
theorem map_snd_cardPairs (cs : List String) :
    cs.map ((fun p : Int × Ident => p.2.name) ∘ fun c => ((1 : Int), Ident.mk c)) = cs := by
  induction cs with
  | nil => rfl
  | cons c cs ih => simp [ih]

/-- The `int_lin_eq` row of a literal-cardinality rewrite. -/
theorem shapeLinEq_card_lit_holds_iff {s : Store} {cs : List String} {n : Int} :
    (shapeLinEq (cs.map (fun _ => 1)) cs n).Holds fullInterp s ↔
      pairSum s (cs.map (fun c => (1, Ident.mk c))) = some n := by
  have h := shapeLinEq_pairs_holds_iff (s := s)
    (ps := cs.map (fun c => (1, Ident.mk c))) (rhs := n)
  rw [List.map_map, List.map_map, map_fst_cardPairs, map_snd_cardPairs] at h
  exact h

/-- The `int_lin_eq` row of a variable-cardinality rewrite. -/
theorem shapeLinEq_card_var_holds_iff {s : Store} {cs : List String} {kn : String} :
    (shapeLinEq (cs.map (fun _ => 1) ++ [-1]) (cs ++ [kn]) 0).Holds fullInterp s ↔
      pairSum s (cs.map (fun c => (1, Ident.mk c)) ++ [(-1, Ident.mk kn)]) = some 0 := by
  have h := shapeLinEq_pairs_holds_iff (s := s)
    (ps := cs.map (fun c => (1, Ident.mk c)) ++ [(-1, Ident.mk kn)]) (rhs := 0)
  have hps1 : (cs.map (fun c => (1, Ident.mk c)) ++ [(-1, Ident.mk kn)]).map
      (fun p : Int × Ident => p.1) = cs.map (fun _ => 1) ++ [-1] := by
    rw [List.map_append, List.map_map, map_fst_cardPairs]
    simp
  have hps2 : (cs.map (fun c => (1, Ident.mk c)) ++ [(-1, Ident.mk kn)]).map
      (fun p : Int × Ident => p.2.name) = cs ++ [kn] := by
    rw [List.map_append, List.map_map, map_snd_cardPairs]
    simp
  rw [hps1, hps2] at h
  exact h

/-- `cardBits` keeps every old constraint. -/
theorem cardBits_cons_subset {taken : List String} {m : Model} {s : String}
    {st : ShapeState} {vals : List Int} {cs : List String} {st' : ShapeState}
    (h : cardBits taken m s st vals = some (cs, st')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  induction vals generalizing st cs st' with
  | nil =>
      simp only [cardBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c hc => hc
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
                  intro c hc
                  have h1 : ∀ x ∈ st.cons, x ∈ st1.cons := memberTerm_cons_subset hm
                  have h2 : ∀ x ∈ st1.cons, x ∈ st2.cons :=
                    ShapeState.freshInt01_cons_subset hb
                  exact ih hr c (h2 c (h1 c hc))

/-- `cardBits` keeps every old auxiliary. -/
theorem cardBits_aux_subset {taken : List String} {m : Model} {s : String}
    {st : ShapeState} {vals : List Int} {cs : List String} {st' : ShapeState}
    (h : cardBits taken m s st vals = some (cs, st')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  induction vals generalizing st cs st' with
  | nil =>
      simp only [cardBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
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
                  intro b hb'
                  have h1 : ∀ x ∈ st.aux, x ∈ st1.aux := memberTerm_aux_subset hm
                  have h2 : ∀ x ∈ st1.aux, x ∈ st2.aux :=
                    ShapeState.freshInt01_aux_subset hb
                  exact ih hr b (h2 b (h1 b hb'))

/-- The Boolean-to-integer aliases of a cardinality rewrite read the
    membership indicators of the declared universe. -/
theorem cardBits_sound {taken : List String} {m : Model} {st : ShapeState}
    {s : String} {us vals : List Int} {cs : List String} {st' : ShapeState}
    {s' : Store} {sv : IntSetValue}
    (h : cardBits taken m s st vals = some (cs, st'))
    (hdefs : st'.DefHolds s')
    (hS : s' (Ident.mk s) = some (.setOfInt sv))
    (hus : modelSetUniverse? m s = some us)
    (hdecl : ∀ w, w ∉ us → ¬ sv.Contains w) :
    Forall2 (fun c v => s' (Ident.mk c) =
      some (.int (if sv.Contains v then 1 else 0))) cs vals := by
  induction vals generalizing st cs st' with
  | nil =>
      simp only [cardBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      simp [Forall2]
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
                  have hdefs2 : st2.DefHolds s' :=
                    ShapeState.DefHolds.mono (cardBits_aux_subset hr) hdefs
                  have hsubf := ShapeState.freshInt01_aux_subset hb
                  have hdefs1 : st1.DefHolds s' :=
                    ShapeState.DefHolds.mono hsubf hdefs2
                  have hval : s' (Ident.mk a) =
                      some (.bool (decide (sv.Contains v))) :=
                    memberTerm_holds hus hm hdefs1 hS hdecl
                  have hbit : s' (Ident.mk c) =
                      some (.int (if sv.Contains v then 1 else 0)) := by
                    have haux : (⟨c, .intRange 0 1, .bit a⟩ : ShapeAux) ∈ st2.aux := by
                      rw [ShapeState.freshInt01_aux hb]
                      exact List.mem_cons_self ..
                    have hdef : (⟨c, .intRange 0 1, .bit a⟩ : ShapeAux).definition.Holds
                        fullInterp s' := hdefs2 _ haux
                    obtain ⟨p, hp, hc⟩ :=
                      (ShapeAux.holds_bit a c s').mp (by
                        simpa [ShapeAux.definition] using hdef)
                    have hpe : p = decide (sv.Contains v) := by
                      have h := Option.some.inj (hp.symm.trans hval)
                      simpa using h
                    rw [hpe] at hc
                    by_cases hcv : sv.Contains v
                    · simpa [hcv] using hc
                    · simpa [hcv] using hc
                  exact ⟨hbit, ih hr hdefs⟩

/-- `cardBits` only adds auxiliary definitions. -/
theorem cardBits_newHolds {taken : List String} {m : Model} {s : String}
    {st : ShapeState} {vals : List Int} {cs : List String} {st' : ShapeState}
    {s' : Store}
    (h : cardBits taken m s st vals = some (cs, st'))
    (hdefs : st'.DefHolds s') :
    st.NewHolds st' s' := by
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
          | mk c st2 =>
              cases hr : cardBits taken m s st2 vs with
              | none => simp [hm, hb, hr] at h
              | some q =>
                  obtain ⟨cs, st3⟩ := q
                  simp only [hm, hb, hr, Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hdefs2 : st2.DefHolds s' :=
                    ShapeState.DefHolds.mono (cardBits_aux_subset hr) hdefs
                  have hsubf := ShapeState.freshInt01_aux_subset hb
                  have hdefs1 : st1.DefHolds s' :=
                    ShapeState.DefHolds.mono hsubf hdefs2
                  have haux : (⟨c, .intRange 0 1, .bit a⟩ : ShapeAux) ∈ st2.aux := by
                    rw [ShapeState.freshInt01_aux hb]
                    exact List.mem_cons_self ..
                  have hd : (⟨c, .intRange 0 1, .bit a⟩ : ShapeAux).definition.Holds
                      fullInterp s' := hdefs2 _ haux
                  exact ShapeState.newHolds_trans
                    (memberTerm_newHolds hm hdefs1)
                    (ShapeState.newHolds_trans
                      (ShapeState.freshInt01_newHolds hb hd)
                      (ih hr hdefs))

/-- `cardBits` preserves well-formedness. -/
theorem cardBits_wf {taken : List String} {m : Model} {s : String}
    {st : ShapeState} {vals : List Int} {cs : List String} {st' : ShapeState}
    {us : List Int}
    (hwf : st.WF taken m) (hs : s ∈ taken)
    (hus : modelSetUniverse? m s = some us)
    (h : cardBits taken m s st vals = some (cs, st')) :
    st'.WF taken m := by
  induction vals generalizing st cs st' with
  | nil =>
      simp only [cardBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
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
                  have hwf1 : st1.WF taken m := memberTerm_wf_ident hwf hs hm
                  have hwf2 : st2.WF taken m := by
                    have hsnd : st2 = (st1.freshInt01 taken (.bit a)).2 := by rw [hb]
                    rw [hsnd]
                    refine ShapeState.freshInt01_wf hwf1 (.bit a) ?_ ?_ ?_ ?_ trivial
                    · intro d hd
                      have hd' : d = a := by simpa [ShapeKind.deps, ShapeKind.sourceDeps,
                        ShapeKind.auxDeps] using hd
                      subst hd'
                      obtain ⟨ca, hca, hcname, _⟩ := memberTerm_aux hm
                      exact Or.inr (List.mem_map.mpr ⟨ca, hca, hcname⟩)
                    · intro d hd
                      simp [ShapeKind.sourceDeps] at hd
                    · intro d hd
                      have hd' : d = a := by simpa [ShapeKind.auxDeps] using hd
                      subst hd'
                      exact memberTerm_aux hm
                    · simp [ShapeAux.TyOk]
                  exact ih hwf2 hr

/-! ## Cardinality rewrite correctness -/

/-- The `set_card` predicate on integer values. -/
theorem fullInterp_set_card :
    fullInterp (Ident.mk "set_card") = stdInterp (Ident.mk "set_card") :=
  fullInterp_eq_std_of_not_global (by decide)

/-- `set_card` on a set value and an integer value. -/
theorem set_card_val_iff (sv : IntSetValue) (n : Int) :
    fullInterp (Ident.mk "set_card") [.setOfInt sv, .int n] ↔ n = sv.card := by
  rw [fullInterp_set_card]
  simp [stdInterp]

/-- The source `set_card` constraint with an identifier set argument. -/
theorem setCard_ident_holds_iff {s : Store} {S : String} {k : BasicExpr}
    {anns : List Annotation} :
    (ConstraintItem.mk (Ident.mk "set_card")
      [.basic (.ident (Ident.mk S)), .basic k] anns).Holds fullInterp s ↔
      ∃ sv n, s (Ident.mk S) = some (.setOfInt sv) ∧
        k.eval s = some (.int n) ∧ n = sv.card := by
  rw [holds_two_iff]
  constructor
  · rintro ⟨v1, v2, h1, h2, hp⟩
    simp only [Expr.eval, BasicExpr.eval] at h1
    cases hS : s (Ident.mk S) with
    | none => rw [hS] at h1; cases h1
    | some v =>
        rw [hS] at h1
        have hv1 : v = v1 := Option.some.inj h1
        subst hv1
        cases v with
        | setOfInt sv =>
            cases v2 with
            | int n => exact ⟨sv, n, rfl, h2, (set_card_val_iff sv n).mp hp⟩
            | bool b =>
                rw [fullInterp_set_card] at hp
                simp [stdInterp] at hp
            | setOfInt sv2 =>
                rw [fullInterp_set_card] at hp
                simp [stdInterp] at hp
            | array xs =>
                rw [fullInterp_set_card] at hp
                simp [stdInterp] at hp
        | int i =>
            rw [fullInterp_set_card] at hp
            simp [stdInterp] at hp
        | bool b =>
            rw [fullInterp_set_card] at hp
            simp [stdInterp] at hp
        | array xs =>
            rw [fullInterp_set_card] at hp
            simp [stdInterp] at hp
  · rintro ⟨sv, n, hS, hk, hn⟩
    refine ⟨.setOfInt sv, .int n, ?_, ?_, ?_⟩
    · simpa [Expr.eval, BasicExpr.eval] using hS
    · simpa [Expr.eval, BasicExpr.eval] using hk
    · exact (set_card_val_iff sv n).mpr hn

/-- The integer row of the empty-universe cardinality rewrite. -/
theorem shapeIntEq_zero_holds_iff {s : Store} {kn : String} :
    (shapeConstraint "int_eq" [shapeE (shapeName kn), shapeE (shapeInt 0)]).Holds
        fullInterp s ↔ s (Ident.mk kn) = some (.int 0) := by
  simp only [shapeConstraint, shapeE, shapeName, shapeInt]
  rw [holds_two_iff]
  constructor
  · rintro ⟨v1, v2, h1, h2, hp⟩
    simp only [Expr.eval, BasicExpr.eval] at h1 h2
    have hv2 : v2 = .int 0 := by
      have h2' := Option.some.inj h2
      simpa [BasicLiteral.denote] using h2'.symm
    subst hv2
    rw [fullInterp_int_eq] at hp
    cases hkn : s (Ident.mk kn) with
    | none => rw [hkn] at h1; cases h1
    | some v =>
        rw [hkn] at h1
        have hv : v = v1 := Option.some.inj h1
        subst hv
        cases v with
        | int i =>
            simp [stdInterp] at hp
            rw [hp]
        | bool b => simp [stdInterp] at hp
        | setOfInt sv => simp [stdInterp] at hp
        | array xs => simp [stdInterp] at hp
  · intro h
    refine ⟨.int 0, .int 0, ?_, rfl, ?_⟩
    · simpa [Expr.eval, BasicExpr.eval] using h
    · rw [fullInterp_int_eq]
      simp [stdInterp]

/-- The cardinality of a set covered by an empty universe is zero. -/
theorem card_eq_zero_of_empty_universe {sv : IntSetValue}
    (hdecl : ∀ w, w ∉ ([] : List Int) → ¬ sv.Contains w) :
    sv.card = 0 := by
  have hcover : ∀ x, sv.Contains x → x ∈ ([] : List Int) := by
    intro x hx
    exact Classical.byContradiction (fun hmem => hdecl x hmem hx)
  have := filter_contains_length_eq_card (us := []) (sv := sv) (by simp) hcover
  simpa using this.symm

/-- `rewriteCard` is sound: the emitted scalar encoding implies the source
    `set_card` constraint. -/
theorem rewriteCard_sound {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {k : BasicExpr} {st' : ShapeState} {cs' : List ConstraintItem}
    {str : Store} {us : List Int} {anns : List Annotation}
    (h : rewriteCard taken m st S k = some (st', cs'))
    (hdefs : st'.DefHolds str)
    (hholds : (st'.emitList cs').Holds str)
    (hS : ∃ sv, str (Ident.mk S) = some (.setOfInt sv))
    (hus : modelSetUniverse? m S = some us)
    (hdecl : ∀ sv, str (Ident.mk S) = some (.setOfInt sv) →
      ∀ w, w ∉ us → ¬ sv.Contains w) :
    (ConstraintItem.mk (Ident.mk "set_card")
      [.basic (.ident (Ident.mk S)), .basic k] anns).Holds fullInterp str := by
  unfold rewriteCard at h
  rw [hus] at h
  simp only [Option.getD_some] at h
  cases us with
  | nil =>
      simp only [List.isEmpty_nil, ite_true] at h
      cases k with
      | ident kn =>
          simp only [] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hrow : (shapeConstraint "int_eq"
              [shapeE (shapeName kn.name), shapeE (shapeInt 0)]).Holds fullInterp str :=
            hholds _ (by simp [ShapeState.emitList, ShapeState.emit])
          have hkn := shapeIntEq_zero_holds_iff.mp hrow
          obtain ⟨sv, hsv⟩ := hS
          have hcard := card_eq_zero_of_empty_universe (hdecl := hdecl sv hsv)
          refine (setCard_ident_holds_iff (s := str) (S := S)
            (k := .ident kn) (anns := anns)).mpr ⟨sv, 0, hsv, ?_, ?_⟩
          · simpa [BasicExpr.eval] using hkn
          · simp [hcard]
      | lit l =>
          cases l with
          | int j =>
              by_cases hj : j = 0
              · simp only [hj, ite_true] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                obtain ⟨sv, hsv⟩ := hS
                have hcard := card_eq_zero_of_empty_universe (hdecl := hdecl sv hsv)
                refine (setCard_ident_holds_iff (s := str) (S := S)
                  (k := .lit (.int j)) (anns := anns)).mpr ⟨sv, 0, hsv, ?_, ?_⟩
                · subst hj
                  simp [BasicExpr.eval, BasicLiteral.denote]
                · simp [hcard]
              · simp only [if_neg hj] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                have hfalse := hholds falseConstraint
                  (by simp [ShapeState.emitList, ShapeState.emit])
                exact absurd hfalse (falseConstraint_holds_false str)
          | bool b => simp only [] at h; simp at h
          | set sl => simp only [] at h; simp at h
  | cons u us =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
      cases hb : cardBits taken m S st (u :: us) with
      | none => simp [hb] at h
      | some p =>
          obtain ⟨cs, st1⟩ := p
          simp only [hb] at h
          cases k with
          | ident kn =>
              simp only [] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hdefs1 : st1.DefHolds str := hdefs
              obtain ⟨sv, hsv⟩ := hS
              have hrow : (shapeLinEq (cs.map (fun _ => 1) ++ [-1])
                  (cs ++ [kn.name]) 0).Holds fullInterp str :=
                hholds _ (by simp [ShapeState.emitList, ShapeState.emit])
              have hpair := shapeLinEq_card_var_holds_iff.mp hrow
              have hsound := cardBits_sound hb hdefs1 hsv hus (hdecl sv hsv)
              have hsum := pairSum_map_one_forall2 (s := str)
                (f := fun v => if sv.Contains v then (1 : Int) else 0) hsound
              have hcov : ∀ x, sv.Contains x → x ∈ (u :: us) := by
                intro x hx
                exact Classical.byContradiction (fun hmem => hdecl sv hsv x hmem hx)
              have hcard : sv.card =
                  ((u :: us).filter (fun v => decide (sv.Contains v))).length :=
                (filter_contains_length_eq_card (modelSetUniverse?_nodup hus) hcov).symm
              have hsumcard :
                  ((u :: us).map (fun v => if sv.Contains v then (1 : Int) else 0)).sum =
                    sv.card := by
                have hs := sum_ite_one_zero (u :: us) (fun v => decide (sv.Contains v))
                rw [hcard]
                simpa using hs
              obtain ⟨a, c, ha, hc, h0⟩ := pairSum_append_inv _ _ hpair
              have hasum : a =
                  ((u :: us).map (fun v => if sv.Contains v then (1 : Int) else 0)).sum :=
                Option.some.inj (ha.symm.trans hsum)
              obtain ⟨i, u0, hik, hu0, hcval⟩ := pairSum_cons_inv hc
              have hu0z : u0 = 0 := by
                have hz : some (0 : Int) = some u0 := by simpa [pairSum] using hu0
                exact (Option.some.inj hz).symm
              have hc' : c = -1 * i := by rw [hcval, hu0z]; omega
              have hicard : i = sv.card := by
                rw [hasum, hc', hsumcard] at h0
                omega
              refine (setCard_ident_holds_iff (s := str) (S := S)
                (k := .ident kn) (anns := anns)).mpr ⟨sv, i, hsv, ?_, hicard⟩
              simpa [BasicExpr.eval] using hik
          | lit l =>
              cases l with
              | int j =>
                  simp only [] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hdefs1 : st1.DefHolds str := hdefs
                  obtain ⟨sv, hsv⟩ := hS
                  have hrow : (shapeLinEq (cs.map (fun _ => 1)) cs j).Holds
                      fullInterp str :=
                    hholds _ (by simp [ShapeState.emitList, ShapeState.emit])
                  have hpair := shapeLinEq_card_lit_holds_iff.mp hrow
                  have hsound := cardBits_sound hb hdefs1 hsv hus (hdecl sv hsv)
                  have hsum := pairSum_map_one_forall2 (s := str)
                    (f := fun v => if sv.Contains v then (1 : Int) else 0) hsound
                  have hcov : ∀ x, sv.Contains x → x ∈ (u :: us) := by
                    intro x hx
                    exact Classical.byContradiction (fun hmem => hdecl sv hsv x hmem hx)
                  have hcard : sv.card =
                      ((u :: us).filter (fun v => decide (sv.Contains v))).length :=
                    (filter_contains_length_eq_card (modelSetUniverse?_nodup hus) hcov).symm
                  have hsumcard :
                      ((u :: us).map (fun v => if sv.Contains v then (1 : Int) else 0)).sum =
                        sv.card := by
                    have hs := sum_ite_one_zero (u :: us) (fun v => decide (sv.Contains v))
                    rw [hcard]
                    simpa using hs
                  have hsumj :
                      ((u :: us).map (fun v => if sv.Contains v then (1 : Int) else 0)).sum =
                        j := Option.some.inj (hsum.symm.trans hpair)
                  have hval : j = sv.card := by rw [← hsumj, hsumcard]
                  refine (setCard_ident_holds_iff (s := str) (S := S)
                    (k := .lit (.int j)) (anns := anns)).mpr ⟨sv, j, hsv, ?_, hval⟩
                  simp [BasicExpr.eval, BasicLiteral.denote]
              | bool b =>
                  simp only [] at h
                  simp at h
              | set sl =>
                  simp only [] at h
                  simp at h

/-- Emitting one satisfied constraint only adds known constraints. -/
theorem ShapeState.newHolds_emit {st : ShapeState} {s : Store}
    {c : ConstraintItem} (hc : c.Holds fullInterp s) :
    st.NewHolds (st.emit c) s := by
  intro d hd
  rcases List.mem_cons.mp (by simpa [ShapeState.emit] using hd) with rfl | hd'
  · exact Or.inr hc
  · exact Or.inl hd'

/-- `rewriteCard` introduces only old or satisfied constraints. -/
theorem rewriteCard_newHolds {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {k : BasicExpr} {st' : ShapeState} {cs' : List ConstraintItem}
    {s s' : Store} {us : List Int} {anns : List Annotation}
    (h : rewriteCard taken m st S k = some (st', cs'))
    (hdefs : st'.DefHolds s')
    (hsrc : (ConstraintItem.mk (Ident.mk "set_card")
      [.basic (.ident (Ident.mk S)), .basic k] anns).Holds fullInterp s)
    (hSval : ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hSagg : s' (Ident.mk S) = s (Ident.mk S))
    (hkagg : k.eval s' = k.eval s)
    (hus : modelSetUniverse? m S = some us)
    (hdecl : ∀ sv, s (Ident.mk S) = some (.setOfInt sv) →
      ∀ w, w ∉ us → ¬ sv.Contains w) :
    st.NewHolds (st'.emitList cs') s' := by
  obtain ⟨sv, n, hSv, hkv, hn⟩ :=
    (setCard_ident_holds_iff (s := s) (S := S) (k := k) (anns := anns)).mp hsrc
  unfold rewriteCard at h
  rw [hus] at h
  simp only [Option.getD_some] at h
  cases us with
  | nil =>
      simp only [List.isEmpty_nil, ite_true] at h
      cases k with
      | ident kn =>
          simp only [] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          have hkn : s (Ident.mk kn.name) = some (.int n) := by
            simpa [BasicExpr.eval] using hkv
          have hkagg' : s' (Ident.mk kn.name) = s (Ident.mk kn.name) := by
            simpa [BasicExpr.eval] using hkagg
          have hkn' : s' (Ident.mk kn.name) = some (.int n) := by
            rw [hkagg']; exact hkn
          have hcard := card_eq_zero_of_empty_universe (hdecl := hdecl sv hSv)
          have hval : n = 0 := by omega
          have hrow : (shapeConstraint "int_eq"
              [shapeE (shapeName kn.name), shapeE (shapeInt 0)]).Holds
              fullInterp s' :=
            shapeIntEq_zero_holds_iff.mpr (by rw [hkn', hval])
          exact ShapeState.newHolds_emit hrow
      | lit l =>
          cases l with
          | int j =>
              have hjn : j = n := by
                have hv := Option.some.inj (by
                  simpa [BasicExpr.eval, BasicLiteral.denote] using hkv)
                simpa using hv
              have hcard := card_eq_zero_of_empty_universe (hdecl := hdecl sv hSv)
              have hj0 : j = 0 := by omega
              by_cases hz : j = 0
              · simp only [hz, ite_true] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                intro c hc
                exact Or.inl (by simpa [ShapeState.emitList] using hc)
              · exact absurd hj0 hz
          | bool b =>
              simp only [] at h
              simp at h
          | set sl =>
              simp only [] at h
              simp at h
  | cons u us =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
      cases hb : cardBits taken m S st (u :: us) with
      | none => simp [hb] at h
      | some p =>
          obtain ⟨cs, st1⟩ := p
          simp only [hb] at h
          have hS' : s' (Ident.mk S) = some (.setOfInt sv) := by rw [hSagg]; exact hSv
          have hdecl' : ∀ w, w ∉ (u :: us) → ¬ sv.Contains w :=
            fun w hw hc => hdecl sv hSv w hw hc
          cases k with
          | ident kn =>
              simp only [] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hdefs1 : st1.DefHolds s' := hdefs
              have hsound := cardBits_sound hb hdefs1 hS' hus hdecl'
              have hsum := pairSum_map_one_forall2 (s := s')
                (f := fun v => if sv.Contains v then (1 : Int) else 0) hsound
              have hcov : ∀ x, sv.Contains x → x ∈ (u :: us) := by
                intro x hx
                exact Classical.byContradiction (fun hmem => hdecl sv hSv x hmem hx)
              have hcard : sv.card =
                  ((u :: us).filter (fun v => decide (sv.Contains v))).length :=
                (filter_contains_length_eq_card (modelSetUniverse?_nodup hus) hcov).symm
              have hsumcard :
                  ((u :: us).map (fun v => if sv.Contains v then (1 : Int) else 0)).sum =
                    sv.card := by
                have hs := sum_ite_one_zero (u :: us) (fun v => decide (sv.Contains v))
                rw [hcard]
                simpa using hs
              have hkn : s (Ident.mk kn.name) = some (.int n) := by
                simpa [BasicExpr.eval] using hkv
              have hkagg' : s' (Ident.mk kn.name) = s (Ident.mk kn.name) := by
                simpa [BasicExpr.eval] using hkagg
              have hkn' : s' (Ident.mk kn.name) = some (.int n) := by
                rw [hkagg']; exact hkn
              have hpair : pairSum s'
                  (cs.map (fun c => (1, Ident.mk c)) ++
                    [(-1, Ident.mk kn.name)]) = some 0 := by
                have hsingle : pairSum s' [(-1, Ident.mk kn.name)] = some (-1 * n) := by
                  unfold pairSum
                  rw [hkn']
                  simp [pairSum]
                have hs := pairSum_append _ _ hsum hsingle
                have hzero :
                    ((u :: us).map
                      (fun v => if sv.Contains v then (1 : Int) else 0)).sum +
                        (-1) * n = 0 := by omega
                rw [hs, hzero]
              have hrow : (shapeLinEq (cs.map (fun _ => 1) ++ [-1])
                  (cs ++ [kn.name]) 0).Holds fullInterp s' :=
                shapeLinEq_card_var_holds_iff.mpr hpair
              exact ShapeState.newHolds_trans (cardBits_newHolds hb hdefs1)
                (ShapeState.newHolds_emit hrow)
          | lit l =>
              cases l with
              | int j =>
                  simp only [] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  have hdefs1 : st1.DefHolds s' := hdefs
                  have hjn : j = n := by
                    have hv := Option.some.inj (by
                      simpa [BasicExpr.eval, BasicLiteral.denote] using hkv)
                    simpa using hv
                  have hval : j = sv.card := by rw [hjn, hn]
                  have hsound := cardBits_sound hb hdefs1 hS' hus hdecl'
                  have hsum := pairSum_map_one_forall2 (s := s')
                    (f := fun v => if sv.Contains v then (1 : Int) else 0) hsound
                  have hcov : ∀ x, sv.Contains x → x ∈ (u :: us) := by
                    intro x hx
                    exact Classical.byContradiction (fun hmem => hdecl sv hSv x hmem hx)
                  have hcard : sv.card =
                      ((u :: us).filter (fun v => decide (sv.Contains v))).length :=
                    (filter_contains_length_eq_card (modelSetUniverse?_nodup hus) hcov).symm
                  have hsumcard :
                      ((u :: us).map (fun v => if sv.Contains v then (1 : Int) else 0)).sum =
                        sv.card := by
                    have hs := sum_ite_one_zero (u :: us) (fun v => decide (sv.Contains v))
                    rw [hcard]
                    simpa using hs
                  have hpair : pairSum s' (cs.map (fun c => (1, Ident.mk c))) = some j := by
                    have hsj : ((u :: us).map
                        (fun v => if sv.Contains v then (1 : Int) else 0)).sum = j := by
                      rw [hsumcard, ← hval]
                    rw [hsum, hsj]
                  have hrow : (shapeLinEq (cs.map (fun _ => 1)) cs j).Holds
                      fullInterp s' :=
                    shapeLinEq_card_lit_holds_iff.mpr hpair
                  exact ShapeState.newHolds_trans (cardBits_newHolds hb hdefs1)
                    (ShapeState.newHolds_emit hrow)
              | bool b =>
                  simp only [] at h
                  simp at h
              | set sl =>
                  simp only [] at h
                  simp at h

/-- `rewriteCard` preserves well-formedness. -/
theorem rewriteCard_wf {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {k : BasicExpr} {st' : ShapeState} {cs' : List ConstraintItem}
    {us : List Int}
    (hwf : st.WF taken m) (hs : S ∈ taken)
    (hus : modelSetUniverse? m S = some us)
    (h : rewriteCard taken m st S k = some (st', cs')) :
    st'.WF taken m := by
  unfold rewriteCard at h
  rw [hus] at h
  simp only [Option.getD_some] at h
  cases us with
  | nil =>
      simp only [List.isEmpty_nil, ite_true] at h
      cases k with
      | ident kn =>
          simp only [] at h
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.emit_wf hwf
      | lit l =>
          cases l with
          | int j =>
              by_cases hj : j = 0
              · simp only [hj, ite_true] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact hwf
              · simp only [if_neg hj] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ShapeState.emit_wf hwf
          | bool b =>
              simp only [] at h
              simp at h
          | set sl =>
              simp only [] at h
              simp at h
  | cons u us =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ite_false] at h
      cases hb : cardBits taken m S st (u :: us) with
      | none => simp [hb] at h
      | some p =>
          obtain ⟨cs, st1⟩ := p
          simp only [hb] at h
          cases k with
          | ident kn =>
              simp only [] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              exact ShapeState.emit_wf (cardBits_wf hwf hs hus hb)
          | lit l =>
              cases l with
              | int j =>
                  simp only [] at h
                  simp only [Option.some.injEq, Prod.mk.injEq] at h
                  obtain ⟨rfl, rfl⟩ := h
                  exact ShapeState.emit_wf (cardBits_wf hwf hs hus hb)
              | bool b =>
                  simp only [] at h
                  simp at h
              | set sl =>
                  simp only [] at h
                  simp at h

/-! ## Membership terms at arbitrary finite set arguments -/

/-- A membership term preserves well-formedness for a finite set argument
    whose variable name is taken. -/
theorem memberTerm_wf {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState}
    (hwf : st.WF taken m)
    (htaken : ∀ S, sa = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (h : memberTerm taken m st sa v = some (n, st')) :
    st'.WF taken m := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          exact memberTerm_wf_ident hwf (htaken S.name (by cases S; rfl)) h
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm, Option.some.injEq] at h
              have hsnd : st' = (st.freshBool taken
                  (.const (decide (sl.denote.Contains v)))).2 := by rw [h]
              rw [hsnd]
              refine ShapeState.freshBool_wf hwf _ ?_ ?_ ?_ ?_ trivial
              · intro d hd
                simp [ShapeKind.deps, ShapeKind.sourceDeps, ShapeKind.auxDeps] at hd
              · intro d hd
                simp [ShapeKind.sourceDeps] at hd
              · intro d hd
                simp [ShapeKind.auxDeps] at hd
              · simp [ShapeAux.TyOk]
  | array es => simp [memberTerm] at h

/-- A membership term's Boolean value decides its source membership. -/
theorem memberTerm_value_iff {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState} {s' : Store}
    (h : memberTerm taken m st sa v = some (n, st'))
    (hholds : st'.Holds s')
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s' (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    ∃ b : Bool, s' (Ident.mk n) = some (.bool b) ∧
      (b = true ↔ setArgContains s' sa v) := by
  rcases memberTerm_sound h hholds hdecl with ⟨hc, hn⟩ | ⟨hnc, hn⟩
  · exact ⟨true, hn, by simp [hc]⟩
  · exact ⟨false, hn, by simp [hnc]⟩

/-- A membership term's Boolean value decides its source membership,
    using the functional definitions of the state's auxiliaries. -/
theorem memberTerm_value_defs {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' : ShapeState} {s : Store}
    (h : memberTerm taken m st sa v = some (n, st'))
    (hdefs : st'.DefHolds s)
    (hval : ∀ S, sa = .basic (.ident (Ident.mk S)) →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    ∃ b : Bool, s (Ident.mk n) = some (.bool b) ∧
      (b = true ↔ setArgContains s sa v) := by
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              obtain ⟨sv, hsv⟩ := hval S.name (by cases S; rfl)
              have hbit := memberTerm_holds hus h hdefs hsv
                (by
                  intro w hw hc
                  exact hw (hdecl S.name us hus sv hsv w hc))
              refine ⟨decide (sv.Contains v), hbit, ?_⟩
              rw [setArgContains_ident_iff hsv]
              simp
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm, Option.some.injEq] at h
              have haux : (⟨n, .par .bool,
                  .const (decide (sl.denote.Contains v))⟩ : ShapeAux) ∈ st'.aux := by
                rw [ShapeState.freshBool_aux h]
                exact List.mem_cons_self ..
              have hdef : (⟨n, .par .bool,
                  .const (decide (sl.denote.Contains v))⟩ : ShapeAux).definition.Holds
                  fullInterp s := hdefs _ haux
              have hn : s (Ident.mk n) =
                  some (.bool (decide (sl.denote.Contains v))) :=
                (ShapeAux.holds_const (decide (sl.denote.Contains v)) n s).mp hdef
              refine ⟨decide (sl.denote.Contains v), hn, ?_⟩
              simp [setArgContains]
  | array es => simp [memberTerm] at h

/-- The value of an identifier argument at a known set value. -/
theorem ident_value_of_eval {s : Store} {e : Expr} {S : String}
    {sv : IntSetValue}
    (h : e.eval s = some (.setOfInt sv))
    (he : e = .basic (.ident (Ident.mk S))) :
    s (Ident.mk S) = some (.setOfInt sv) := by
  subst he
  simpa [Expr.eval, BasicExpr.eval] using h

/-- A Boolean value agrees with a proposition. -/
theorem bool_true_iff_of_value {s : Store} {sa : Expr} {v : Int}
    {n : String} {b : Bool}
    (hval : s (Ident.mk n) = some (.bool b))
    (hsound : (setArgContains s sa v ∧
        s (Ident.mk n) = some (.bool true)) ∨
      (¬ setArgContains s sa v ∧ s (Ident.mk n) = some (.bool false))) :
    (b = true ↔ setArgContains s sa v) := by
  rcases hsound with ⟨hc, ht⟩ | ⟨hnc, hf⟩
  · have hb : b = true := by
      rw [hval] at ht
      simpa using ht
    simp [hb, hc]
  · have hb : b = false := by
      rw [hval] at hf
      simpa using hf
    simp [hb, hnc]

/-- The three-identifier `bool_or` constraint, semantically. -/
theorem holds_bool_or_shape {s : Store} {x y n : String} :
    (shapeConstraint "bool_or"
      [shapeE (shapeName x), shapeE (shapeName y),
        shapeE (shapeName n)]).Holds fullInterp s ↔
      ∃ p q r : Bool, s (Ident.mk x) = some (.bool p) ∧
        s (Ident.mk y) = some (.bool q) ∧
        s (Ident.mk n) = some (.bool r) ∧ r = (p || q) := by
  rw [ConstraintItem.Holds]
  simp only [shapeConstraint]
  rw [fullInterp_bool_or]
  constructor
  · rintro ⟨args, hargs, hp⟩
    rcases hx : s (Ident.mk x) with _ | px | ix | svx | arrx <;>
      rcases hy : s (Ident.mk y) with _ | qy | iy | svy | arry <;>
        rcases hn : s (Ident.mk n) with _ | rn | iN | svn | arrn
    all_goals
      simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hy, hn, List.mapM_cons] at hargs hp
    all_goals subst hargs
    all_goals try cases px <;> try cases qy <;> try cases rn
    all_goals simp [stdInterp] at hp ⊢
    all_goals simp_all
  · rintro ⟨p, q, r, hx, hy, hn, hr⟩
    refine ⟨[.bool p, .bool q, .bool r], ?_, ?_⟩
    · simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hy, hn, List.mapM_cons]
    · subst hr
      cases p <;> cases q <;> simp [stdInterp, hx, hy, hn]

/-- A `bool_or` row holds when its three names read the expected values. -/
theorem holds_bool_or_shape_of {s : Store} {x y n : String}
    {p q r : Bool}
    (hx : s (Ident.mk x) = some (.bool p))
    (hy : s (Ident.mk y) = some (.bool q))
    (hn : s (Ident.mk n) = some (.bool r))
    (hr : r = (p || q)) :
    (shapeConstraint "bool_or"
      [shapeE (shapeName x), shapeE (shapeName y),
        shapeE (shapeName n)]).Holds fullInterp s :=
  holds_bool_or_shape.mpr ⟨p, q, r, hx, hy, hn, hr⟩

/-- The three-identifier `bool_and` constraint, semantically. -/
theorem holds_bool_and_shape {s : Store} {x y n : String} :
    (shapeConstraint "bool_and"
      [shapeE (shapeName x), shapeE (shapeName y),
        shapeE (shapeName n)]).Holds fullInterp s ↔
      ∃ p q r : Bool, s (Ident.mk x) = some (.bool p) ∧
        s (Ident.mk y) = some (.bool q) ∧
        s (Ident.mk n) = some (.bool r) ∧ r = (p && q) := by
  rw [ConstraintItem.Holds]
  simp only [shapeConstraint]
  rw [fullInterp_bool_and]
  constructor
  · rintro ⟨args, hargs, hp⟩
    rcases hx : s (Ident.mk x) with _ | px | ix | svx | arrx <;>
      rcases hy : s (Ident.mk y) with _ | qy | iy | svy | arry <;>
        rcases hn : s (Ident.mk n) with _ | rn | iN | svn | arrn
    all_goals
      simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hy, hn, List.mapM_cons] at hargs hp
    all_goals subst hargs
    all_goals try cases px <;> try cases qy <;> try cases rn
    all_goals simp [stdInterp] at hp ⊢
    all_goals simp_all
  · rintro ⟨p, q, r, hx, hy, hn, hr⟩
    refine ⟨[.bool p, .bool q, .bool r], ?_, ?_⟩
    · simp [shapeE, shapeName, Expr.eval, BasicExpr.eval,
        hx, hy, hn, List.mapM_cons]
    · subst hr
      cases p <;> cases q <;> simp [stdInterp, hx, hy, hn]

/-- A `bool_and` row holds when its three names read the expected values. -/
theorem holds_bool_and_shape_of {s : Store} {x y n : String}
    {p q r : Bool}
    (hx : s (Ident.mk x) = some (.bool p))
    (hy : s (Ident.mk y) = some (.bool q))
    (hn : s (Ident.mk n) = some (.bool r))
    (hr : r = (p && q)) :
    (shapeConstraint "bool_and"
      [shapeE (shapeName x), shapeE (shapeName y),
        shapeE (shapeName n)]).Holds fullInterp s :=
  holds_bool_and_shape.mpr ⟨p, q, r, hx, hy, hn, hr⟩

/-- The truth table of Boolean conjunction. -/
theorem bool_and_eq_true_iff (a b : Bool) :
    (a && b) = true ↔ (a = true ∧ b = true) := by
  cases a <;> cases b <;> simp

/-! ## Union rows -/

/-- The `bool_or` row emitted for one value. -/
def unionRow (av bv cv : String) : ConstraintItem :=
  shapeConstraint "bool_or"
    [shapeE (shapeName av), shapeE (shapeName bv), shapeE (shapeName cv)]

/-- Decompose one successful `unionRows` step. -/
theorem unionRows_cons_decomp {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {v : Int} {vs : List Int}
    {st' : ShapeState}
    (h : unionRows taken m a b c st (v :: vs) = some st') :
    ∃ (av : String) (st1 : ShapeState) (bv : String) (st2 : ShapeState)
      (cv : String) (st3 : ShapeState),
      memberTerm taken m st a v = some (av, st1) ∧
      memberTerm taken m st1 b v = some (bv, st2) ∧
      memberTerm taken m st2 c v = some (cv, st3) ∧
      unionRows taken m a b c (st3.emit (unionRow av bv cv)) vs = some st' := by
  simp only [unionRows] at h
  cases hm1 : memberTerm taken m st a v with
  | none => simp [hm1] at h
  | some p =>
      obtain ⟨av, st1⟩ := p
      cases hm2 : memberTerm taken m st1 b v with
      | none => simp [hm1, hm2] at h
      | some q =>
          obtain ⟨bv, st2⟩ := q
          cases hm3 : memberTerm taken m st2 c v with
          | none => simp [hm1, hm2, hm3] at h
          | some r =>
              obtain ⟨cv, st3⟩ := r
              simp only [hm1, hm2, hm3, unionRow] at h
              refine ⟨av, st1, bv, st2, cv, st3, ?_, ?_, ?_, h⟩
              · first | rfl | exact hm1
              · first | rfl | exact hm2
              · first | rfl | exact hm3

/-- `unionRows` keeps every old constraint. -/
theorem unionRows_cons_subset {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (h : unionRows taken m a b c st vals = some st') :
    ∀ c' ∈ st.cons, c' ∈ st'.cons := by
  induction vals generalizing st st' with
  | nil =>
      simp only [unionRows, Option.some.injEq] at h
      subst h
      exact fun c' hc' => hc'
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        unionRows_cons_decomp h
      intro c' hc'
      have h1 : c' ∈ st1.cons := memberTerm_cons_subset hm1 c' hc'
      have h2 : c' ∈ st2.cons := memberTerm_cons_subset hm2 c' h1
      have h3 : c' ∈ st3.cons := memberTerm_cons_subset hm3 c' h2
      have h4 : c' ∈ (st3.emit (unionRow av bv cv)).cons :=
        ShapeState.emit_cons_subset c' h3
      exact ih hr c' h4

/-- `unionRows` keeps every old auxiliary. -/
theorem unionRows_aux_subset {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (h : unionRows taken m a b c st vals = some st') :
    ∀ x ∈ st.aux, x ∈ st'.aux := by
  induction vals generalizing st st' with
  | nil =>
      simp only [unionRows, Option.some.injEq] at h
      subst h
      exact fun x hx => hx
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        unionRows_cons_decomp h
      intro x hx
      have h1 : x ∈ st1.aux := memberTerm_aux_subset hm1 x hx
      have h2 : x ∈ st2.aux := memberTerm_aux_subset hm2 x h1
      have h3 : x ∈ st3.aux := memberTerm_aux_subset hm3 x h2
      exact ih hr x h3

/-- **Soundness of the union rows**: every emitted row forces the union
    relation at its value. -/
theorem unionRows_sound {taken : List String} {m : Model} {a b c : Expr}
    {st st' : ShapeState} {vals : List Int} {s : Store}
    (h : unionRows taken m a b c st vals = some st')
    (hholds : st'.Holds s)
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    ∀ v ∈ vals,
      setArgContains s c v ↔ setArgContains s a v ∨ setArgContains s b v := by
  induction vals generalizing st st' with
  | nil => intro v hv; cases hv
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        unionRows_cons_decomp h
      intro w hw
      rcases List.mem_cons.mp hw with hwv | hw
      · rw [hwv]
        have hsub1 : ∀ c' ∈ st1.cons, c' ∈ st'.cons := by
          intro c' hc'
          exact unionRows_cons_subset hr c'
            (ShapeState.emit_cons_subset c'
              (memberTerm_cons_subset hm3 c'
                (memberTerm_cons_subset hm2 c' hc')))
        have hsub2 : ∀ c' ∈ st2.cons, c' ∈ st'.cons := by
          intro c' hc'
          exact unionRows_cons_subset hr c'
            (ShapeState.emit_cons_subset c'
              (memberTerm_cons_subset hm3 c' hc'))
        have hsub3 : ∀ c' ∈ st3.cons, c' ∈ st'.cons := by
          intro c' hc'
          exact unionRows_cons_subset hr c'
            (ShapeState.emit_cons_subset c' hc')
        have h1 := memberTerm_sound hm1
          (ShapeState.holds_mono hsub1 hholds) hdecl
        have h2 := memberTerm_sound hm2
          (ShapeState.holds_mono hsub2 hholds) hdecl
        have h3 := memberTerm_sound hm3
          (ShapeState.holds_mono hsub3 hholds) hdecl
        have hrowmem : unionRow av bv cv ∈ st'.cons :=
          unionRows_cons_subset hr _ (by simp [unionRow, ShapeState.emit])
        have hrow := hholds _ hrowmem
        obtain ⟨p, q, r, hav, hbv, hcv, hpqr⟩ :=
          holds_bool_or_shape.mp hrow
        have hpa : (p = true ↔ setArgContains s a v) :=
          bool_true_iff_of_value (sa := a) hav h1
        have hpb : (q = true ↔ setArgContains s b v) :=
          bool_true_iff_of_value (sa := b) hbv h2
        have hpc : (r = true ↔ setArgContains s c v) :=
          bool_true_iff_of_value (sa := c) hcv h3
        have hpr : (r = true) ↔
            (setArgContains s a v ∨ setArgContains s b v) := by
          have h : (r = true) ↔ (p = true ∨ q = true) := by
            rw [hpqr, bool_or_eq_true_iff]
          rwa [hpa, hpb] at h
        rw [← hpc]
        exact hpr
      · exact ih hr hholds w hw

/-- The union rows only add auxiliary definitions and satisfied rows. -/
theorem unionRows_newHolds {taken : List String} {m : Model} {a b c : Expr}
    {st st' : ShapeState} {vals : List Int} {s : Store}
    (h : unionRows taken m a b c st vals = some st')
    (hdefs : st'.DefHolds s)
    (hrel : ∀ v ∈ vals,
      setArgContains s c v ↔ setArgContains s a v ∨ setArgContains s b v)
    (haVal : ∀ S, a = .basic (.ident (Ident.mk S)) →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hbVal : ∀ S, b = .basic (.ident (Ident.mk S)) →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hcVal : ∀ S, c = .basic (.ident (Ident.mk S)) →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    st.NewHolds st' s := by
  induction vals generalizing st st' with
  | nil =>
      simp only [unionRows, Option.some.injEq] at h
      subst h
      intro c' hc'
      exact Or.inl hc'
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        unionRows_cons_decomp h
      have hdefs3 : st3.DefHolds s :=
        ShapeState.DefHolds.mono (fun x hx => unionRows_aux_subset hr x hx) hdefs
      have hdefs2 : st2.DefHolds s :=
        ShapeState.DefHolds.mono (memberTerm_aux_subset hm3) hdefs3
      have hdefs1 : st1.DefHolds s :=
        ShapeState.DefHolds.mono (memberTerm_aux_subset hm2) hdefs2
      obtain ⟨pa, hav, hpa⟩ := memberTerm_value_defs hm1 hdefs1 haVal hdecl
      obtain ⟨pb, hbv, hpb⟩ := memberTerm_value_defs hm2 hdefs2 hbVal hdecl
      obtain ⟨pc, hcv, hpc⟩ := memberTerm_value_defs hm3 hdefs3 hcVal hdecl
      have hrelv := hrel v (List.mem_cons_self ..)
      have hpc' : (pc = true) ↔ (pa = true ∨ pb = true) := by
        rw [hpc]
        rw [hrelv]
        rw [← hpa, ← hpb]
      have hrow : (unionRow av bv cv).Holds fullInterp s := by
        have hr_eq : pc = (pa || pb) := by
          rw [Bool.eq_iff_iff, bool_or_eq_true_iff]
          exact hpc'
        exact holds_bool_or_shape_of hav hbv hcv hr_eq
      have htail : ∀ w ∈ vs,
          setArgContains s c w ↔
            setArgContains s a w ∨ setArgContains s b w := by
        intro w hw
        exact hrel w (List.mem_cons_of_mem _ hw)
      exact ShapeState.newHolds_trans (memberTerm_newHolds hm1 hdefs1)
        (ShapeState.newHolds_trans (memberTerm_newHolds hm2 hdefs2)
          (ShapeState.newHolds_trans (memberTerm_newHolds hm3 hdefs3)
            (ShapeState.newHolds_trans (ShapeState.newHolds_emit hrow)
              (ih hr hdefs htail))))

/-- `unionRows` preserves well-formedness. -/
theorem unionRows_wf {taken : List String} {m : Model} {a b c : Expr}
    {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (hwf : st.WF taken m)
    (ha : ∀ S, a = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hb : ∀ S, b = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hc : ∀ S, c = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (h : unionRows taken m a b c st vals = some st') :
    st'.WF taken m := by
  induction vals generalizing st st' with
  | nil =>
      simp only [unionRows, Option.some.injEq] at h
      subst h
      exact hwf
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        unionRows_cons_decomp h
      have hwf1 : st1.WF taken m := memberTerm_wf hwf ha hm1
      have hwf2 : st2.WF taken m := memberTerm_wf hwf1 hb hm2
      have hwf3 : st3.WF taken m := memberTerm_wf hwf2 hc hm3
      exact ih (ShapeState.emit_wf hwf3) hr

/-! ## Union rewrite correctness -/

/-- `rewriteUnion` decomposes into its row traversal. -/
theorem rewriteUnion_decomp {taken : List String} {m : Model}
    {st : ShapeState} {a b c : Expr} {ua ub uc : List Int}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs')) :
    ∃ st1, unionRows taken m a b c st (ua ++ ub ++ uc) = some st1 ∧
      st' = st1 ∧ cs' = [] := by
  cases hr : unionRows taken m a b c st (ua ++ ub ++ uc) with
  | none =>
      simp only [rewriteUnion, hr] at h
      cases h
  | some st1 =>
      simp only [rewriteUnion, hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨st1, rfl, rfl, rfl⟩

/-- `setArgValues?` bounds the memberships of its argument. -/
theorem setArgValues?_not_contains {m : Model} {e : Expr} {us : List Int}
    (h : setArgValues? m e = some us) {s : Store} {v : Int}
    (hnot : v ∉ us)
    (hdecl : ∀ S us', modelSetUniverse? m S = some us' →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) →
        ∀ w, sv.Contains w → w ∈ us') :
    ¬ setArgContains s e v := by
  cases e with
  | basic b =>
      cases b with
      | ident S =>
          simp only [setArgValues?] at h
          rintro ⟨sv, hsv, hc⟩
          exact hnot (hdecl S.name us h sv hsv v hc)
      | lit l =>
          cases l with
          | bool bb => simp [setArgValues?] at h
          | int i => simp [setArgValues?] at h
          | set sl =>
              cases sl with
              | intSet xs =>
                  simp only [setArgValues?] at h
                  intro hc
                  simp only [setArgContains] at hc
                  apply hnot
                  rw [← Option.some.inj h]
                  exact mem_sortElems_setValue.mpr hc
              | intRange lo hi =>
                  simp only [setArgValues?] at h
                  intro hc
                  simp only [setArgContains] at hc
                  apply hnot
                  rw [← Option.some.inj h]
                  exact mem_sortElems_setValue.mpr hc
  | array es => simp [setArgValues?] at h

/-- Membership through `setArgContains` agrees with the set value of the
    argument. -/
theorem setArgContains_iff_of_eval {s : Store} {e : Expr} {v : Int}
    {sv : IntSetValue} (hev : e.eval s = some (.setOfInt sv)) :
    setArgContains s e v ↔ sv.Contains v := by
  cases e with
  | basic b =>
      cases b with
      | ident S =>
          exact setArgContains_ident_iff hev
      | lit l =>
          cases l with
          | bool bb =>
              cases bb <;>
                simp [Expr.eval, BasicExpr.eval, BasicLiteral.denote] at hev
          | int i =>
              simp [Expr.eval, BasicExpr.eval, BasicLiteral.denote] at hev
          | set sl =>
              have hsl : sl.denote = sv := by
                simpa [Expr.eval, BasicExpr.eval, BasicLiteral.denote,
                  SetLiteral.denote] using hev
              subst hsl
              simp [setArgContains]
  | array es => simp [Expr.eval] at hev

/-- A `set_union` constraint holds from its pointwise membership relation. -/
theorem setUnion_holds_of_forall {s : Store} {a b c : Expr}
    {av bv cv : IntSetValue} {anns : List Annotation}
    (ha : a.eval s = some (.setOfInt av))
    (hb : b.eval s = some (.setOfInt bv))
    (hc : c.eval s = some (.setOfInt cv))
    (h : ∀ i, cv.Contains i ↔ av.Contains i ∨ bv.Contains i) :
    (ConstraintItem.mk (Ident.mk "set_union") [a, b, c] anns).Holds
      fullInterp s := by
  refine ⟨[.setOfInt av, .setOfInt bv, .setOfInt cv], ?_, ?_⟩
  · simp [List.mapM_cons, ha, hb, hc]
  · rw [fullInterp_eq_std_of_not_global (n := "set_union") (by decide)]
    simpa [stdInterp] using h

/-- A held `set_union` constraint gives its pointwise membership relation. -/
theorem setUnion_holds_elim {s : Store} {a b c : Expr}
    {av bv cv : IntSetValue} {anns : List Annotation}
    (hsrc : (ConstraintItem.mk (Ident.mk "set_union") [a, b, c] anns).Holds
      fullInterp s)
    (ha : a.eval s = some (.setOfInt av))
    (hb : b.eval s = some (.setOfInt bv))
    (hc : c.eval s = some (.setOfInt cv)) :
    ∀ i, cv.Contains i ↔ av.Contains i ∨ bv.Contains i := by
  obtain ⟨args, hargs, hp⟩ := hsrc
  have hval : [a, b, c].mapM (Expr.eval s) =
      some [.setOfInt av, .setOfInt bv, .setOfInt cv] := by
    simp [List.mapM_cons, ha, hb, hc]
  have hargs' : args = [.setOfInt av, .setOfInt bv, .setOfInt cv] :=
    Option.some.inj (hargs.symm.trans hval)
  subst hargs'
  rw [fullInterp_eq_std_of_not_global (n := "set_union") (by decide)] at hp
  simpa [stdInterp] using hp

/-- **Soundness of the union rewrite**: the emitted scalar rows force the
    source `set_union` constraint. -/
theorem rewriteUnion_sound {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem} {str : Store} {anns : List Annotation}
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs'))
    (hdefs : st'.DefHolds str)
    (hholds : (st'.emitList cs').Holds str)
    (hA : setArgValues? m a = some ua)
    (hB : setArgValues? m b = some ub)
    (hC : setArgValues? m c = some uc)
    (haVal : ∃ av, a.eval str = some (.setOfInt av))
    (hbVal : ∃ bv, b.eval str = some (.setOfInt bv))
    (hcVal : ∃ cv, c.eval str = some (.setOfInt cv))
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, str (Ident.mk S) = some (.setOfInt sv) →
        ∀ w, sv.Contains w → w ∈ us) :
    (ConstraintItem.mk (Ident.mk "set_union") [a, b, c] anns).Holds
      fullInterp str := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteUnion_decomp h
  obtain ⟨av, haE⟩ := haVal
  obtain ⟨bv, hbE⟩ := hbVal
  obtain ⟨cv, hcE⟩ := hcVal
  refine setUnion_holds_of_forall haE hbE hcE ?_
  intro i
  by_cases hi : i ∈ ua ++ ub ++ uc
  · have hrow := unionRows_sound hr (by simpa [ShapeState.emitList] using hholds)
      hdecl i hi
    simpa only [setArgContains_iff_of_eval haE, setArgContains_iff_of_eval hbE,
      setArgContains_iff_of_eval hcE] using hrow
  · have hiaMem : i ∉ ua := by
      intro hmem
      exact hi (by simp [hmem])
    have hibMem : i ∉ ub := by
      intro hmem
      exact hi (by simp [hmem])
    have hicMem : i ∉ uc := by
      intro hmem
      exact hi (by simp [hmem])
    have hia : ¬ av.Contains i := by
      intro hc
      exact (setArgValues?_not_contains hA hiaMem hdecl)
        ((setArgContains_iff_of_eval haE).mpr hc)
    have hib : ¬ bv.Contains i := by
      intro hc
      exact (setArgValues?_not_contains hB hibMem hdecl)
        ((setArgContains_iff_of_eval hbE).mpr hc)
    have hic : ¬ cv.Contains i := by
      intro hc
      exact (setArgValues?_not_contains hC hicMem hdecl)
        ((setArgContains_iff_of_eval hcE).mpr hc)
    simp [hia, hib, hic]

/-- **Completeness of the union rewrite**: when the source `set_union`
    holds, the functionally extended store satisfies every emitted row. -/
theorem rewriteUnion_newHolds {taken : List String} {m : Model}
    {st : ShapeState} {a b c : Expr} {ua ub uc : List Int}
    {st' : ShapeState} {cs' : List ConstraintItem} {s s' : Store}
    {anns : List Annotation}
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs'))
    (hdefs : st'.DefHolds s')
    (hsrc : (ConstraintItem.mk (Ident.mk "set_union") [a, b, c] anns).Holds
      fullInterp s)
    (haVal : ∃ av, a.eval s = some (.setOfInt av))
    (hbVal : ∃ bv, b.eval s = some (.setOfInt bv))
    (hcVal : ∃ cv, c.eval s = some (.setOfInt cv))
    (haAgg : a.eval s' = a.eval s)
    (hbAgg : b.eval s' = b.eval s)
    (hcAgg : c.eval s' = c.eval s)
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s' (Ident.mk S) = some (.setOfInt sv) →
        ∀ w, sv.Contains w → w ∈ us) :
    st.NewHolds (st'.emitList cs') s' := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteUnion_decomp h
  obtain ⟨av, haE⟩ := haVal
  obtain ⟨bv, hbE⟩ := hbVal
  obtain ⟨cv, hcE⟩ := hcVal
  have hrel := setUnion_holds_elim hsrc haE hbE hcE
  have haE' : a.eval s' = some (.setOfInt av) := by rw [haAgg]; exact haE
  have hbE' : b.eval s' = some (.setOfInt bv) := by rw [hbAgg]; exact hbE
  have hcE' : c.eval s' = some (.setOfInt cv) := by rw [hcAgg]; exact hcE
  have hrel' : ∀ i,
      setArgContains s' c i ↔ setArgContains s' a i ∨ setArgContains s' b i := by
    intro i
    rw [setArgContains_iff_of_eval haE', setArgContains_iff_of_eval hbE',
      setArgContains_iff_of_eval hcE']
    exact hrel i
  have haVal' : ∀ S, a = .basic (.ident (Ident.mk S)) →
      ∃ sv, s' (Ident.mk S) = some (.setOfInt sv) := by
    intro S hS
    exact ⟨av, ident_value_of_eval haE' hS⟩
  have hbVal' : ∀ S, b = .basic (.ident (Ident.mk S)) →
      ∃ sv, s' (Ident.mk S) = some (.setOfInt sv) := by
    intro S hS
    exact ⟨bv, ident_value_of_eval hbE' hS⟩
  have hcVal' : ∀ S, c = .basic (.ident (Ident.mk S)) →
      ∃ sv, s' (Ident.mk S) = some (.setOfInt sv) := by
    intro S hS
    exact ⟨cv, ident_value_of_eval hcE' hS⟩
  simpa [ShapeState.emitList] using
    unionRows_newHolds hr hdefs (fun i _ => hrel' i) haVal' hbVal' hcVal' hdecl

/-- `rewriteUnion` preserves well-formedness. -/
theorem rewriteUnion_wf {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (hwf : st.WF taken m)
    (ha : ∀ S, a = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hb : ∀ S, b = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hc : ∀ S, c = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs')) :
    st'.WF taken m := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteUnion_decomp h
  exact unionRows_wf hwf ha hb hc hr

/-! ## Intersection rows -/

/-- The `bool_and` row emitted for one value. -/
def intersectRow (av bv cv : String) : ConstraintItem :=
  shapeConstraint "bool_and"
    [shapeE (shapeName av), shapeE (shapeName bv), shapeE (shapeName cv)]

/-- Decompose one successful `intersectRows` step. -/
theorem intersectRows_cons_decomp {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {v : Int} {vs : List Int}
    {st' : ShapeState}
    (h : intersectRows taken m a b c st (v :: vs) = some st') :
    ∃ (av : String) (st1 : ShapeState) (bv : String) (st2 : ShapeState)
      (cv : String) (st3 : ShapeState),
      memberTerm taken m st a v = some (av, st1) ∧
      memberTerm taken m st1 b v = some (bv, st2) ∧
      memberTerm taken m st2 c v = some (cv, st3) ∧
      intersectRows taken m a b c (st3.emit (intersectRow av bv cv)) vs = some st' := by
  simp only [intersectRows] at h
  cases hm1 : memberTerm taken m st a v with
  | none => simp [hm1] at h
  | some p =>
      obtain ⟨av, st1⟩ := p
      cases hm2 : memberTerm taken m st1 b v with
      | none => simp [hm1, hm2] at h
      | some q =>
          obtain ⟨bv, st2⟩ := q
          cases hm3 : memberTerm taken m st2 c v with
          | none => simp [hm1, hm2, hm3] at h
          | some r =>
              obtain ⟨cv, st3⟩ := r
              simp only [hm1, hm2, hm3, intersectRow] at h
              refine ⟨av, st1, bv, st2, cv, st3, ?_, ?_, ?_, h⟩
              · first | rfl | exact hm1
              · first | rfl | exact hm2
              · first | rfl | exact hm3

/-- `intersectRows` keeps every old constraint. -/
theorem intersectRows_cons_subset {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (h : intersectRows taken m a b c st vals = some st') :
    ∀ c' ∈ st.cons, c' ∈ st'.cons := by
  induction vals generalizing st st' with
  | nil =>
      simp only [intersectRows, Option.some.injEq] at h
      subst h
      exact fun c' hc' => hc'
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        intersectRows_cons_decomp h
      intro c' hc'
      have h1 : c' ∈ st1.cons := memberTerm_cons_subset hm1 c' hc'
      have h2 : c' ∈ st2.cons := memberTerm_cons_subset hm2 c' h1
      have h3 : c' ∈ st3.cons := memberTerm_cons_subset hm3 c' h2
      have h4 : c' ∈ (st3.emit (intersectRow av bv cv)).cons :=
        ShapeState.emit_cons_subset c' h3
      exact ih hr c' h4

/-- `intersectRows` keeps every old auxiliary. -/
theorem intersectRows_aux_subset {taken : List String} {m : Model}
    {a b c : Expr} {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (h : intersectRows taken m a b c st vals = some st') :
    ∀ x ∈ st.aux, x ∈ st'.aux := by
  induction vals generalizing st st' with
  | nil =>
      simp only [intersectRows, Option.some.injEq] at h
      subst h
      exact fun x hx => hx
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        intersectRows_cons_decomp h
      intro x hx
      have h1 : x ∈ st1.aux := memberTerm_aux_subset hm1 x hx
      have h2 : x ∈ st2.aux := memberTerm_aux_subset hm2 x h1
      have h3 : x ∈ st3.aux := memberTerm_aux_subset hm3 x h2
      exact ih hr x h3

/-- **Soundness of the intersection rows**: every emitted row forces the
    intersection relation at its value. -/
theorem intersectRows_sound {taken : List String} {m : Model} {a b c : Expr}
    {st st' : ShapeState} {vals : List Int} {s : Store}
    (h : intersectRows taken m a b c st vals = some st')
    (hholds : st'.Holds s)
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    ∀ v ∈ vals,
      setArgContains s c v ↔ setArgContains s a v ∧ setArgContains s b v := by
  induction vals generalizing st st' with
  | nil => intro v hv; cases hv
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        intersectRows_cons_decomp h
      intro w hw
      rcases List.mem_cons.mp hw with hwv | hw
      · rw [hwv]
        have hsub1 : ∀ c' ∈ st1.cons, c' ∈ st'.cons := by
          intro c' hc'
          exact intersectRows_cons_subset hr c'
            (ShapeState.emit_cons_subset c'
              (memberTerm_cons_subset hm3 c'
                (memberTerm_cons_subset hm2 c' hc')))
        have hsub2 : ∀ c' ∈ st2.cons, c' ∈ st'.cons := by
          intro c' hc'
          exact intersectRows_cons_subset hr c'
            (ShapeState.emit_cons_subset c'
              (memberTerm_cons_subset hm3 c' hc'))
        have hsub3 : ∀ c' ∈ st3.cons, c' ∈ st'.cons := by
          intro c' hc'
          exact intersectRows_cons_subset hr c'
            (ShapeState.emit_cons_subset c' hc')
        have h1 := memberTerm_sound hm1
          (ShapeState.holds_mono hsub1 hholds) hdecl
        have h2 := memberTerm_sound hm2
          (ShapeState.holds_mono hsub2 hholds) hdecl
        have h3 := memberTerm_sound hm3
          (ShapeState.holds_mono hsub3 hholds) hdecl
        have hrowmem : intersectRow av bv cv ∈ st'.cons :=
          intersectRows_cons_subset hr _ (by simp [intersectRow, ShapeState.emit])
        have hrow := hholds _ hrowmem
        obtain ⟨p, q, r, hav, hbv, hcv, hpqr⟩ :=
          holds_bool_and_shape.mp hrow
        have hpa : (p = true ↔ setArgContains s a v) :=
          bool_true_iff_of_value (sa := a) hav h1
        have hpb : (q = true ↔ setArgContains s b v) :=
          bool_true_iff_of_value (sa := b) hbv h2
        have hpc : (r = true ↔ setArgContains s c v) :=
          bool_true_iff_of_value (sa := c) hcv h3
        have hpr : (r = true) ↔
            (setArgContains s a v ∧ setArgContains s b v) := by
          have h : (r = true) ↔ (p = true ∧ q = true) := by
            rw [hpqr, bool_and_eq_true_iff]
          rwa [hpa, hpb] at h
        rw [← hpc]
        exact hpr
      · exact ih hr hholds w hw

/-- The intersection rows only add auxiliary definitions and satisfied rows. -/
theorem intersectRows_newHolds {taken : List String} {m : Model} {a b c : Expr}
    {st st' : ShapeState} {vals : List Int} {s : Store}
    (h : intersectRows taken m a b c st vals = some st')
    (hdefs : st'.DefHolds s)
    (hrel : ∀ v ∈ vals,
      setArgContains s c v ↔ setArgContains s a v ∧ setArgContains s b v)
    (haVal : ∀ S, a = .basic (.ident (Ident.mk S)) →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hbVal : ∀ S, b = .basic (.ident (Ident.mk S)) →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hcVal : ∀ S, c = .basic (.ident (Ident.mk S)) →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv))
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) →
        ∀ w, sv.Contains w → w ∈ us) :
    st.NewHolds st' s := by
  induction vals generalizing st st' with
  | nil =>
      simp only [intersectRows, Option.some.injEq] at h
      subst h
      intro c' hc'
      exact Or.inl hc'
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        intersectRows_cons_decomp h
      have hdefs3 : st3.DefHolds s :=
        ShapeState.DefHolds.mono (fun x hx => intersectRows_aux_subset hr x hx) hdefs
      have hdefs2 : st2.DefHolds s :=
        ShapeState.DefHolds.mono (memberTerm_aux_subset hm3) hdefs3
      have hdefs1 : st1.DefHolds s :=
        ShapeState.DefHolds.mono (memberTerm_aux_subset hm2) hdefs2
      obtain ⟨pa, hav, hpa⟩ := memberTerm_value_defs hm1 hdefs1 haVal hdecl
      obtain ⟨pb, hbv, hpb⟩ := memberTerm_value_defs hm2 hdefs2 hbVal hdecl
      obtain ⟨pc, hcv, hpc⟩ := memberTerm_value_defs hm3 hdefs3 hcVal hdecl
      have hrelv := hrel v (List.mem_cons_self ..)
      have hpc' : (pc = true) ↔ (pa = true ∧ pb = true) := by
        rw [hpc]
        rw [hrelv]
        rw [← hpa, ← hpb]
      have hrow : (intersectRow av bv cv).Holds fullInterp s := by
        have hr_eq : pc = (pa && pb) := by
          rw [Bool.eq_iff_iff, bool_and_eq_true_iff]
          exact hpc'
        exact holds_bool_and_shape_of hav hbv hcv hr_eq
      have htail : ∀ w ∈ vs,
          setArgContains s c w ↔
            setArgContains s a w ∧ setArgContains s b w := by
        intro w hw
        exact hrel w (List.mem_cons_of_mem _ hw)
      exact ShapeState.newHolds_trans (memberTerm_newHolds hm1 hdefs1)
        (ShapeState.newHolds_trans (memberTerm_newHolds hm2 hdefs2)
          (ShapeState.newHolds_trans (memberTerm_newHolds hm3 hdefs3)
            (ShapeState.newHolds_trans (ShapeState.newHolds_emit hrow)
              (ih hr hdefs htail))))

/-- `intersectRows` preserves well-formedness. -/
theorem intersectRows_wf {taken : List String} {m : Model} {a b c : Expr}
    {st : ShapeState} {vals : List Int} {st' : ShapeState}
    (hwf : st.WF taken m)
    (ha : ∀ S, a = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hb : ∀ S, b = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hc : ∀ S, c = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (h : intersectRows taken m a b c st vals = some st') :
    st'.WF taken m := by
  induction vals generalizing st st' with
  | nil =>
      simp only [intersectRows, Option.some.injEq] at h
      subst h
      exact hwf
  | cons v vs ih =>
      obtain ⟨av, st1, bv, st2, cv, st3, hm1, hm2, hm3, hr⟩ :=
        intersectRows_cons_decomp h
      have hwf1 : st1.WF taken m := memberTerm_wf hwf ha hm1
      have hwf2 : st2.WF taken m := memberTerm_wf hwf1 hb hm2
      have hwf3 : st3.WF taken m := memberTerm_wf hwf2 hc hm3
      exact ih (ShapeState.emit_wf hwf3) hr

/-! ## Intersection rewrite correctness -/

/-- `rewriteIntersect` decomposes into its row traversal. -/
theorem rewriteIntersect_decomp {taken : List String} {m : Model}
    {st : ShapeState} {a b c : Expr} {ua ub uc : List Int}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs')) :
    ∃ st1, intersectRows taken m a b c st
        ((IntSetValue.enumeration (ua ++ ub ++ uc)).sortElems) = some st1 ∧
      st' = st1 ∧ cs' = [] := by
  cases hr : intersectRows taken m a b c st
      ((IntSetValue.enumeration (ua ++ ub ++ uc)).sortElems) with
  | none =>
      simp only [rewriteIntersect, hr] at h
      cases h
  | some st1 =>
      simp only [rewriteIntersect, hr, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨st1, rfl, rfl, rfl⟩

/-- A `set_intersect` constraint holds from its pointwise membership relation. -/
theorem setIntersect_holds_of_forall {s : Store} {a b c : Expr}
    {av bv cv : IntSetValue} {anns : List Annotation}
    (ha : a.eval s = some (.setOfInt av))
    (hb : b.eval s = some (.setOfInt bv))
    (hc : c.eval s = some (.setOfInt cv))
    (h : ∀ i, cv.Contains i ↔ av.Contains i ∧ bv.Contains i) :
    (ConstraintItem.mk (Ident.mk "set_intersect") [a, b, c] anns).Holds
      fullInterp s := by
  refine ⟨[.setOfInt av, .setOfInt bv, .setOfInt cv], ?_, ?_⟩
  · simp [List.mapM_cons, ha, hb, hc]
  · rw [fullInterp_eq_std_of_not_global (n := "set_intersect") (by decide)]
    simpa [stdInterp] using h

/-- A held `set_intersect` constraint gives its pointwise membership relation. -/
theorem setIntersect_holds_elim {s : Store} {a b c : Expr}
    {av bv cv : IntSetValue} {anns : List Annotation}
    (hsrc : (ConstraintItem.mk (Ident.mk "set_intersect") [a, b, c] anns).Holds
      fullInterp s)
    (ha : a.eval s = some (.setOfInt av))
    (hb : b.eval s = some (.setOfInt bv))
    (hc : c.eval s = some (.setOfInt cv)) :
    ∀ i, cv.Contains i ↔ av.Contains i ∧ bv.Contains i := by
  obtain ⟨args, hargs, hp⟩ := hsrc
  have hval : [a, b, c].mapM (Expr.eval s) =
      some [.setOfInt av, .setOfInt bv, .setOfInt cv] := by
    simp [List.mapM_cons, ha, hb, hc]
  have hargs' : args = [.setOfInt av, .setOfInt bv, .setOfInt cv] :=
    Option.some.inj (hargs.symm.trans hval)
  subst hargs'
  rw [fullInterp_eq_std_of_not_global (n := "set_intersect") (by decide)] at hp
  simpa [stdInterp] using hp

/-- **Soundness of the intersection rewrite**: the emitted scalar rows force
    the source `set_intersect` constraint. -/
theorem rewriteIntersect_sound {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem} {str : Store} {anns : List Annotation}
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs'))
    (hdefs : st'.DefHolds str)
    (hholds : (st'.emitList cs').Holds str)
    (hA : setArgValues? m a = some ua)
    (hB : setArgValues? m b = some ub)
    (hC : setArgValues? m c = some uc)
    (haVal : ∃ av, a.eval str = some (.setOfInt av))
    (hbVal : ∃ bv, b.eval str = some (.setOfInt bv))
    (hcVal : ∃ cv, c.eval str = some (.setOfInt cv))
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, str (Ident.mk S) = some (.setOfInt sv) →
        ∀ w, sv.Contains w → w ∈ us) :
    (ConstraintItem.mk (Ident.mk "set_intersect") [a, b, c] anns).Holds
      fullInterp str := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteIntersect_decomp h
  obtain ⟨av, haE⟩ := haVal
  obtain ⟨bv, hbE⟩ := hbVal
  obtain ⟨cv, hcE⟩ := hcVal
  refine setIntersect_holds_of_forall haE hbE hcE ?_
  intro i
  by_cases hi : i ∈ (IntSetValue.enumeration (ua ++ ub ++ uc)).sortElems
  · have hrow := intersectRows_sound hr
      (by simpa [ShapeState.emitList] using hholds) hdecl i hi
    simpa only [setArgContains_iff_of_eval haE, setArgContains_iff_of_eval hbE,
      setArgContains_iff_of_eval hcE] using hrow
  · have hiaMem : i ∉ ua := by
      intro hmem
      exact hi (by
        rw [mem_sortElems_enum]
        simp [hmem])
    have hibMem : i ∉ ub := by
      intro hmem
      exact hi (by
        rw [mem_sortElems_enum]
        simp [hmem])
    have hicMem : i ∉ uc := by
      intro hmem
      exact hi (by
        rw [mem_sortElems_enum]
        simp [hmem])
    have hia : ¬ av.Contains i := by
      intro hc
      exact (setArgValues?_not_contains hA hiaMem hdecl)
        ((setArgContains_iff_of_eval haE).mpr hc)
    have hib : ¬ bv.Contains i := by
      intro hc
      exact (setArgValues?_not_contains hB hibMem hdecl)
        ((setArgContains_iff_of_eval hbE).mpr hc)
    have hic : ¬ cv.Contains i := by
      intro hc
      exact (setArgValues?_not_contains hC hicMem hdecl)
        ((setArgContains_iff_of_eval hcE).mpr hc)
    simp [hia, hib, hic]

/-- **Completeness of the intersection rewrite**: when the source
    `set_intersect` holds, the functionally extended store satisfies every
    emitted row. -/
theorem rewriteIntersect_newHolds {taken : List String} {m : Model}
    {st : ShapeState} {a b c : Expr} {ua ub uc : List Int}
    {st' : ShapeState} {cs' : List ConstraintItem} {s s' : Store}
    {anns : List Annotation}
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs'))
    (hdefs : st'.DefHolds s')
    (hsrc : (ConstraintItem.mk (Ident.mk "set_intersect") [a, b, c] anns).Holds
      fullInterp s)
    (haVal : ∃ av, a.eval s = some (.setOfInt av))
    (hbVal : ∃ bv, b.eval s = some (.setOfInt bv))
    (hcVal : ∃ cv, c.eval s = some (.setOfInt cv))
    (haAgg : a.eval s' = a.eval s)
    (hbAgg : b.eval s' = b.eval s)
    (hcAgg : c.eval s' = c.eval s)
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s' (Ident.mk S) = some (.setOfInt sv) →
        ∀ w, sv.Contains w → w ∈ us) :
    st.NewHolds (st'.emitList cs') s' := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteIntersect_decomp h
  obtain ⟨av, haE⟩ := haVal
  obtain ⟨bv, hbE⟩ := hbVal
  obtain ⟨cv, hcE⟩ := hcVal
  have hrel := setIntersect_holds_elim hsrc haE hbE hcE
  have haE' : a.eval s' = some (.setOfInt av) := by rw [haAgg]; exact haE
  have hbE' : b.eval s' = some (.setOfInt bv) := by rw [hbAgg]; exact hbE
  have hcE' : c.eval s' = some (.setOfInt cv) := by rw [hcAgg]; exact hcE
  have hrel' : ∀ i,
      setArgContains s' c i ↔ setArgContains s' a i ∧ setArgContains s' b i := by
    intro i
    rw [setArgContains_iff_of_eval haE', setArgContains_iff_of_eval hbE',
      setArgContains_iff_of_eval hcE']
    exact hrel i
  have haVal' : ∀ S, a = .basic (.ident (Ident.mk S)) →
      ∃ sv, s' (Ident.mk S) = some (.setOfInt sv) := by
    intro S hS
    exact ⟨av, ident_value_of_eval haE' hS⟩
  have hbVal' : ∀ S, b = .basic (.ident (Ident.mk S)) →
      ∃ sv, s' (Ident.mk S) = some (.setOfInt sv) := by
    intro S hS
    exact ⟨bv, ident_value_of_eval hbE' hS⟩
  have hcVal' : ∀ S, c = .basic (.ident (Ident.mk S)) →
      ∃ sv, s' (Ident.mk S) = some (.setOfInt sv) := by
    intro S hS
    exact ⟨cv, ident_value_of_eval hcE' hS⟩
  simpa [ShapeState.emitList] using
    intersectRows_newHolds hr hdefs (fun i _ => hrel' i) haVal' hbVal' hcVal' hdecl

/-- `rewriteIntersect` preserves well-formedness. -/
theorem rewriteIntersect_wf {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (hwf : st.WF taken m)
    (ha : ∀ S, a = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hb : ∀ S, b = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (hc : ∀ S, c = .basic (.ident (Ident.mk S)) → S ∈ taken)
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs')) :
    st'.WF taken m := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteIntersect_decomp h
  exact intersectRows_wf hwf ha hb hc hr

/-- `rewriteIntersect` keeps every old auxiliary. -/
theorem rewriteIntersect_aux_subset {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs')) :
    ∀ x ∈ st.aux, x ∈ st'.aux := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteIntersect_decomp h
  exact intersectRows_aux_subset hr

/-- `rewriteIntersect` keeps every old constraint. -/
theorem rewriteIntersect_cons_subset {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteIntersect taken m st a b c ua ub uc = some (st', cs')) :
    ∀ x ∈ st.cons, x ∈ st'.cons := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteIntersect_decomp h
  exact intersectRows_cons_subset hr


/-! ## Source-store facts for the traversal

The traversal lemmas need two kinds of facts about a source store: every
finite integer variable has an integer value in its declared finite
domain, and every finite set variable has a set value whose elements lie
in the declared universe. -/

/-- Every finite integer variable of `m` has a value in its declared
    finite domain. -/
def ShapeIntDomains (m : Model) (s : Store) : Prop :=
  ∀ x vals, modelIntValues? m x = some vals →
    (∃ i, s (Ident.mk x) = some (.int i)) ∧
      (∀ i, s (Ident.mk x) = some (.int i) → i ∈ vals)

/-- Every finite set variable of `m` has a set value, and every element
    of that value lies in the declared universe. -/
def ShapeSetDomains (m : Model) (s : Store) : Prop :=
  (∀ S us, modelSetUniverse? m S = some us →
      ∃ sv, s (Ident.mk S) = some (.setOfInt sv)) ∧
    (∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) →
        ∀ w, sv.Contains w → w ∈ us)

/-- The negative form of universe coverage. -/
theorem ShapeSetDomains.not_contains {m : Model} {s : Store}
    (h : ShapeSetDomains m s) {S : String} {us : List Int}
    (hus : modelSetUniverse? m S = some us) {sv : IntSetValue}
    (hsv : s (Ident.mk S) = some (.setOfInt sv)) :
    ∀ w, w ∉ us → ¬ sv.Contains w :=
  fun w hw hc => hw (h.2 S us hus sv hsv w hc)

/-- A set argument with a known finite value list evaluates to a set in a
    store that gives every finite set variable a set value. -/
theorem setArgValues?_eval {m : Model} {e : Expr} {us : List Int}
    (h : setArgValues? m e = some us) {s : Store}
    (hset : ShapeSetDomains m s) :
    ∃ sv, e.eval s = some (.setOfInt sv) := by
  cases e with
  | basic b =>
      cases b with
      | ident S =>
          simp only [setArgValues?] at h
          exact hset.1 S.name us h
      | lit l =>
          cases l with
          | bool bb => simp [setArgValues?] at h
          | int i => simp [setArgValues?] at h
          | set sl => exact ⟨sl.denote, rfl⟩
  | array es => simp [setArgValues?] at h

/-- An identifier with a finite set universe is a taken name. -/
theorem setArgValues?_ident_taken {taken : List String} {m : Model}
    (hsup : ∀ x ∈ setTaken m, x ∈ taken) {e : Expr} {us : List Int}
    (h : setArgValues? m e = some us) :
    ∀ S, e = .basic (.ident (Ident.mk S)) → S ∈ taken := by
  intro S he
  subst e
  simp only [setArgValues?] at h
  obtain ⟨ty, anns, init, hd, hun⟩ := modelSetUniverse?_some h
  have hmem : S ∈ m.variables.map (fun d => d.name.name) :=
    List.mem_map.mpr ⟨_, hd, rfl⟩
  exact hsup S (List.mem_append_right _ hmem)

/-- A finite integer lookup names a declared variable, hence a taken name. -/
theorem modelIntValues?_name_taken {taken : List String} {m : Model}
    (hwf : WellFormed fullSig m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    {x : String} {vals : List Int} (h : modelIntValues? m x = some vals) :
    x ∈ taken := by
  obtain ⟨ty, anns, init, hd, hun⟩ := modelIntValues?_some h
  have hmem : x ∈ m.variables.map (fun d => d.name.name) :=
    List.mem_map.mpr ⟨_, hd, rfl⟩
  exact hsup x (List.mem_append_right _ hmem)

/-- A set universe lookup names a declared variable, hence a taken name. -/
theorem modelSetUniverse?_name_taken {taken : List String} {m : Model}
    (hwf : WellFormed fullSig m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    {x : String} {us : List Int} (h : modelSetUniverse? m x = some us) :
    x ∈ taken := by
  obtain ⟨ty, anns, init, hd, hun⟩ := modelSetUniverse?_some h
  have hmem : x ∈ m.variables.map (fun d => d.name.name) :=
    List.mem_map.mpr ⟨_, hd, rfl⟩
  exact hsup x (List.mem_append_right _ hmem)

/-! ## Plain set membership -/

/-- The truth of `set_in(x,S)`. -/
theorem setIn_expr_holds_iff {x S : BasicExpr} {s : Store} {anns : List Annotation} :
    (ConstraintItem.mk (Ident.mk "set_in") [.basic x, .basic S] anns).Holds
      fullInterp s ↔
      ∃ k sv, BasicExpr.eval s x = some (.int k) ∧
        BasicExpr.eval s S = some (.setOfInt sv) ∧ sv.Contains k := by
  rw [holds_basic_two (by decide)]
  constructor
  · rintro ⟨v₁, v₂, h₁, h₂, hP⟩
    cases v₁ with
    | int k =>
        cases v₂ with
        | setOfInt sv => exact ⟨k, sv, h₁, h₂, by simpa [stdInterp] using hP⟩
        | bool b => simp [stdInterp] at hP
        | int i => simp [stdInterp] at hP
        | array l => simp [stdInterp] at hP
    | bool b => simp [stdInterp] at hP
    | setOfInt sv => simp [stdInterp] at hP
    | array l => simp [stdInterp] at hP
  · rintro ⟨k, sv, h₁, h₂, hc⟩
    exact ⟨.int k, .setOfInt sv, h₁, h₂, by simpa [stdInterp] using hc⟩

/-- A true `set_in_reif` is a `set_in`. -/
theorem setIn_of_setIn_true {x S : BasicExpr} {s : Store} {anns : List Annotation}
    (h : (ConstraintItem.mk (Ident.mk "set_in_reif")
      [.basic x, .basic S, .basic (.lit (.bool true))] anns).Holds
      fullInterp s) :
    (ConstraintItem.mk (Ident.mk "set_in") [.basic x, .basic S] anns).Holds
      fullInterp s := by
  obtain ⟨k, sv, r, hx, hS, hr, hcond⟩ := setInReif_expr_holds_iff.mp h
  have hr' : r = true := by
    simpa [BasicExpr.eval, BasicLiteral.denote] using hr
  subst hr'
  rcases hcond with ⟨_, hc⟩ | ⟨hfalse, _⟩
  · rw [setIn_expr_holds_iff]
    exact ⟨k, sv, hx, hS, hc⟩
  · exact absurd hfalse (by decide)

/-- A `set_in` is a true `set_in_reif`. -/
theorem setIn_true_of_setIn {x S : BasicExpr} {s : Store} {anns : List Annotation}
    (h : (ConstraintItem.mk (Ident.mk "set_in") [.basic x, .basic S] anns).Holds
      fullInterp s) :
    (ConstraintItem.mk (Ident.mk "set_in_reif")
      [.basic x, .basic S, .basic (.lit (.bool true))] anns).Holds
      fullInterp s := by
  obtain ⟨k, sv, hx, hS, hc⟩ := setIn_expr_holds_iff.mp h
  rw [setInReif_expr_holds_iff]
  exact ⟨k, sv, true, hx, hS, rfl, Or.inl ⟨rfl, hc⟩⟩

/-! ## Set-array elements (S5)

The array-element encoding is proved against the native set semantics,
independently of the S3 expansion.  For every value in the union of the
element universes and the target universe, a Boolean element row reads
the membership bit of the selected element against the target bit. -/

/-- `mapM` preserves the length of a list. -/
theorem mapM_length_option {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM f = some vs → vs.length = l.length := by
  intro l
  induction l with
  | nil =>
      intro vs h
      simp [List.mapM_nil] at h
      subst h
      rfl
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

/-- The `k`-th result of a successful `mapM` is the image of the `k`-th
    input. -/
theorem mapM_getElem?_option {α β : Type} {f : α → Option β} :
    ∀ {l : List α} {vs : List β}, l.mapM f = some vs →
      ∀ (k : Nat), vs[k]? = (l[k]?).bind f := by
  intro l
  induction l with
  | nil =>
      intro vs h k
      simp [List.mapM_nil] at h
      subst h
      simp
  | cons a rest ih =>
      intro vs h k
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
              cases k with
              | zero => simp [hfa]
              | succ k =>
                  have hik := ih hr k
                  simpa using hik

/-- A successful union of element universes. -/
theorem arrayElemUnion_some {m : Model} {e : BasicExpr} {es : List BasicExpr}
    {us union : List Int}
    (h : setArgValues? m (.basic e) = some us)
    (htail : arrayElemUnion m es = some union) :
    arrayElemUnion m (e :: es) = some (us ++ union) := by
  simp [arrayElemUnion, h, htail]

/-- Membership in the union of element universes. -/
theorem arrayElemUnion_mem {m : Model} {es : List BasicExpr} {union : List Int}
    (h : arrayElemUnion m es = some union) :
    ∀ v, v ∈ union ↔
      ∃ e, e ∈ es ∧ ∃ us, setArgValues? m (.basic e) = some us ∧ v ∈ us := by
  induction es generalizing union with
  | nil =>
      intro v
      simp only [arrayElemUnion, Option.some.injEq] at h
      subst h
      simp
  | cons e rest ih =>
      intro v
      simp only [arrayElemUnion] at h
      cases hu : setArgValues? m (.basic e) with
      | none => rw [hu] at h; simp at h
      | some us =>
          rw [hu] at h
          cases hr : arrayElemUnion m rest with
          | none => rw [hr] at h; simp at h
          | some union' =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              rw [List.mem_append, ih hr v]
              constructor
              · rintro (hv | ⟨e', he', us', hu', hv⟩)
                · exact ⟨e, List.mem_cons_self, us, hu, hv⟩
                · exact ⟨e', List.mem_cons_of_mem _ he', us', hu', hv⟩
              · rintro ⟨e', he', us', hu', hv⟩
                rcases List.mem_cons.mp he' with rfl | he''
                · left
                  rw [Option.some.inj (hu'.symm.trans hu)] at hv
                  exact hv
                · exact Or.inr ⟨e', he'', us', hu', hv⟩

/-- The computed value list of an array element constraint is the sorted
    union of the element universes and the target universe. -/
theorem arrayElemValues_eq {m : Model} {es : List BasicExpr} {T : String}
    {ut union vals : List Int}
    (ht : modelSetUniverse? m T = some ut)
    (hu : arrayElemUnion m es = some union)
    (h : arrayElemValues m es T = some vals) :
    vals = (IntSetValue.enumeration (ut ++ union)).sortElems := by
  unfold arrayElemValues at h
  rw [ht] at h
  simp only at h
  rw [hu] at h
  exact (Option.some.inj h).symm

/-- Decomposition of a successful value-list computation. -/
theorem arrayElemValues_decomp {m : Model} {es : List BasicExpr} {T : String}
    {vals : List Int} (h : arrayElemValues m es T = some vals) :
    ∃ ut union, vals = (IntSetValue.enumeration (ut ++ union)).sortElems ∧
      modelSetUniverse? m T = some ut ∧ arrayElemUnion m es = some union := by
  unfold arrayElemValues at h
  cases ht : modelSetUniverse? m T with
  | none => rw [ht] at h; simp at h
  | some ut =>
      rw [ht] at h
      simp only at h
      cases hu : arrayElemUnion m es with
      | none => rw [hu] at h; simp at h
      | some union =>
          rw [hu] at h
          exact ⟨ut, union, (Option.some.inj h).symm, rfl, rfl⟩

/-- Membership in the computed value list, given its decomposition. -/
theorem arrayElemValues_mem_of {m : Model} {es : List BasicExpr} {T : String}
    {vals ut union : List Int}
    (hvals : vals = (IntSetValue.enumeration (ut ++ union)).sortElems)
    (ht : modelSetUniverse? m T = some ut)
    (hu : arrayElemUnion m es = some union) :
    ∀ v, v ∈ vals ↔
      (∃ ut', modelSetUniverse? m T = some ut' ∧ v ∈ ut') ∨
      (∃ e, e ∈ es ∧ ∃ us, setArgValues? m (.basic e) = some us ∧ v ∈ us) := by
  subst hvals
  intro v
  show v ∈ (IntSetValue.enumeration (ut ++ union)).sortElems ↔ _
  rw [mem_sortElems_setValue]
  show v ∈ ut ++ union ↔ _
  rw [List.mem_append, arrayElemUnion_mem hu v]
  constructor
  · rintro (hv | ⟨e, he, us, hu', hv⟩)
    · exact Or.inl ⟨ut, ht, hv⟩
    · exact Or.inr ⟨e, he, us, hu', hv⟩
  · intro h
    rcases h with ⟨ut', ht', hv⟩ | ⟨e, he, us, hu', hv⟩
    · left
      have hut : ut' = ut := Option.some.inj (ht'.symm.trans ht)
      subst hut
      exact hv
    · exact Or.inr ⟨e, he, us, hu', hv⟩

/-- Membership in the computed value list. -/
theorem arrayElemValues_mem {m : Model} {es : List BasicExpr} {T : String}
    {vals : List Int} (h : arrayElemValues m es T = some vals) :
    ∀ v, v ∈ vals ↔
      (∃ ut, modelSetUniverse? m T = some ut ∧ v ∈ ut) ∨
      (∃ e, e ∈ es ∧ ∃ us, setArgValues? m (.basic e) = some us ∧ v ∈ us) := by
  obtain ⟨ut, union, hvals, ht, hu⟩ := arrayElemValues_decomp h
  exact arrayElemValues_mem_of hvals ht hu

/-- A target-universe value belongs to the computed value list. -/
theorem arrayElemValues_mem_of_universe {m : Model} {es : List BasicExpr}
    {T : String} {vals ut : List Int} {v : Int}
    (h : arrayElemValues m es T = some vals)
    (ht : modelSetUniverse? m T = some ut) (hv : v ∈ ut) : v ∈ vals :=
  (arrayElemValues_mem h v).mpr (Or.inl ⟨ut, ht, hv⟩)

/-- A member of an element universe belongs to the computed value list. -/
theorem arrayElemValues_mem_of_elem {m : Model} {es : List BasicExpr}
    {T : String} {vals : List Int} {e : BasicExpr} {us : List Int} {v : Int}
    (h : arrayElemValues m es T = some vals) (he : e ∈ es)
    (hu : setArgValues? m (.basic e) = some us) (hv : v ∈ us) : v ∈ vals :=
  (arrayElemValues_mem h v).mpr (Or.inr ⟨e, he, us, hu, hv⟩)

/-- Every element of a successful union of element universes evaluates to
    a set value in a store satisfying the declared set domains. -/
theorem arrayElemUnion_eval {m : Model} {es : List BasicExpr} {union : List Int}
    (h : arrayElemUnion m es = some union) {s : Store}
    (hset : ShapeSetDomains m s) :
    ∀ e ∈ es, ∃ sv, e.eval s = some (.setOfInt sv) := by
  induction es generalizing union with
  | nil => intro e he; simp at he
  | cons a rest ih =>
      intro e he
      simp only [arrayElemUnion] at h
      cases hu : setArgValues? m (.basic a) with
      | none => rw [hu] at h; simp at h
      | some us =>
          rw [hu] at h
          cases hr : arrayElemUnion m rest with
          | none => rw [hr] at h; simp at h
          | some union' =>
              rw [hr] at h
              rcases List.mem_cons.mp he with rfl | he'
              · exact setArgValues?_eval hu hset
              · exact ih hr e he'

/-- A set-valued expression's membership lies in its computed universe. -/
theorem setArgValues?_contains {m : Model} {e : Expr} {us : List Int}
    (h : setArgValues? m e = some us) {s : Store}
    (hdecl : ∀ S us', modelSetUniverse? m S = some us' →
      ∀ sv, s (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us')
    {sv : IntSetValue} (hev : e.eval s = some (.setOfInt sv)) :
    ∀ x, sv.Contains x → x ∈ us := by
  cases e with
  | basic b =>
      cases b with
      | ident S =>
          simp only [setArgValues?] at h
          intro x hx
          exact hdecl S.name us h sv hev x hx
      | lit l =>
          cases l with
          | bool bb => simp [setArgValues?] at h
          | int i => simp [setArgValues?] at h
          | set sl =>
              cases sl with
              | intSet xs =>
                  simp only [setArgValues?] at h
                  have hsl : IntSetValue.enumeration xs = sv := by
                    simpa [Expr.eval, BasicExpr.eval, BasicLiteral.denote,
                      SetLiteral.denote] using hev
                  subst hsl
                  intro x hx
                  rw [← Option.some.inj h]
                  exact mem_sortElems_setValue.mpr hx
              | intRange lo hi =>
                  simp only [setArgValues?] at h
                  have hsl : IntSetValue.interval lo hi = sv := by
                    simpa [Expr.eval, BasicExpr.eval, BasicLiteral.denote,
                      SetLiteral.denote] using hev
                  subst hsl
                  intro x hx
                  rw [← Option.some.inj h]
                  exact mem_sortElems_setValue.mpr hx
  | array es => simp [setArgValues?] at h

/-- A positive one-based index reads the corresponding list element. -/
theorem valuesGet1_succ (xs : List Value) (k : Nat) :
    valuesGet1 xs ((k : Int) + 1) = xs[k]? := by
  unfold valuesGet1
  have hpos : 0 < ((k : Int) + 1) := by omega
  rw [if_pos hpos]
  have hto : ((k : Int) + 1).toNat - 1 = k := by
    have h1 : ((k : Int) + 1).toNat = k + 1 := by
      rw [show (k : Int) + 1 = ((k + 1 : Nat) : Int) by omega]
      exact Int.toNat_natCast (k + 1)
    omega
  rw [hto]

/-- A successful `valuesGet1` read lies between one and the list length. -/
theorem valuesGet1_bounds {xs : List Value} {i : Int} {v : Value}
    (h : valuesGet1 xs i = some v) :
    1 ≤ i ∧ i ≤ (xs.length : Int) := by
  unfold valuesGet1 at h
  by_cases hpos : 0 < i
  · rw [if_pos hpos] at h
    have hlt : i.toNat - 1 < xs.length := (List.getElem?_eq_some_iff.mp h).1
    have hpos' : 0 ≤ i := by omega
    have hto : (i.toNat : Int) = i := Int.toNat_of_nonneg hpos'
    constructor <;> omega
  · rw [if_neg hpos] at h
    simp at h

/-- A successful `mapM` over set-valued elements. -/
theorem mapM_eval_exists {es : List BasicExpr} {s : Store}
    (h : ∀ e ∈ es, ∃ sv, e.eval s = some (.setOfInt sv)) :
    ∃ xs, es.mapM (BasicExpr.eval s) = some xs := by
  induction es with
  | nil => exact ⟨[], by simp [List.mapM_nil]⟩
  | cons a rest ih =>
      obtain ⟨sv, hsv⟩ := h a List.mem_cons_self
      obtain ⟨xs, hxs⟩ := ih (fun e he => h e (List.mem_cons_of_mem _ he))
      exact ⟨.setOfInt sv :: xs, by rw [List.mapM_cons, hsv, hxs]; rfl⟩

/-- The `mapM` image of a set-valued element list reads the same at every
    in-range position. -/
theorem mapM_eval_getElem? {es : List BasicExpr} {s : Store} {xs : List Value}
    (h : es.mapM (BasicExpr.eval s) = some xs) :
    ∀ (k : Nat) e, es[k]? = some e → xs[k]? = e.eval s := by
  intro k e he
  rw [mapM_getElem?_option h k, he]
  rfl

/-! ### Membership bits of one array value -/

/-- The membership bit allocated for a finite set argument reads the
    argument's membership decision at every set value. -/
theorem memberTerm_decide_eval {taken : List String} {m : Model} {st : ShapeState}
    {sa : Expr} {v : Int} {n : String} {st' stF : ShapeState} {s' : Store}
    (h : memberTerm taken m st sa v = some (n, st'))
    (hsub : ∀ a ∈ st'.aux, a ∈ stF.aux)
    (hdefs : stF.DefHolds s')
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s' (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    ∀ sv : IntSetValue, sa.eval s' = some (.setOfInt sv) →
      s' (Ident.mk n) = some (.bool (decide (sv.Contains v))) := by
  have hdefs' : st'.DefHolds s' := ShapeState.DefHolds.mono hsub hdefs
  intro sv hev
  cases sa with
  | basic b =>
      cases b with
      | ident S =>
          cases hus : modelSetUniverse? m S.name with
          | none => simp [memberTerm, hus] at h
          | some us =>
              by_cases hv : v ∈ us
              · exact memberTerm_holds hus h hdefs'
                  (by simpa [Expr.eval, BasicExpr.eval] using hev)
                  (fun w hw hc => hw (hdecl S.name us hus sv
                    (by simpa [Expr.eval, BasicExpr.eval] using hev) w hc))
              · simp only [memberTerm, hus, if_neg hv] at h
                have h' : st.freshBool taken (.const false) = (n, st') := Option.some.inj h
                have haux : (⟨n, .par .bool, .const false⟩ : ShapeAux) ∈ st'.aux := by
                  rw [ShapeState.freshBool_aux h']
                  exact List.mem_cons_self ..
                have hn : s' (Ident.mk n) = some (.bool false) :=
                  (ShapeAux.holds_const false n s').mp (hdefs' _ haux)
                have hnc : ¬ sv.Contains v := by
                  intro hc
                  exact hv (hdecl S.name us hus sv
                    (by simpa [Expr.eval, BasicExpr.eval] using hev) v hc)
                rw [hn]
                simp [hnc]
      | lit l =>
          cases l with
          | bool bb => simp [memberTerm] at h
          | int i => simp [memberTerm] at h
          | set sl =>
              simp only [memberTerm] at h
              have h' : st.freshBool taken (.const (decide (sl.denote.Contains v))) =
                  (n, st') := Option.some.inj h
              have haux : (⟨n, .par .bool,
                  .const (decide (sl.denote.Contains v))⟩ : ShapeAux) ∈ st'.aux := by
                rw [ShapeState.freshBool_aux h']
                exact List.mem_cons_self ..
              have hn : s' (Ident.mk n) =
                  some (.bool (decide (sl.denote.Contains v))) :=
                (ShapeAux.holds_const (decide (sl.denote.Contains v)) n s').mp
                  (hdefs' _ haux)
              have hsl : sl.denote = sv := by
                simpa [Expr.eval, BasicExpr.eval, BasicLiteral.denote,
                  SetLiteral.denote] using hev
              rw [hn, hsl]
  | array es => simp [memberTerm] at h

/-- `arrayElemBits` keeps every old auxiliary. -/
theorem arrayElemBits_aux_subset {taken : List String} {m : Model} {v : Int} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      arrayElemBits taken m es st v = some (bits, st') →
      ∀ a ∈ st.aux, a ∈ st'.aux := by
  intro es
  induction es with
  | nil =>
      intro st bits st' h a ha
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ha
  | cons e rest ih =>
      intro st bits st' h a ha
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
              exact ih st1 bs st2 hr a (memberTerm_aux_subset hm a ha)

/-- The bits allocated for one value match the memberships of the element
    expressions. -/
theorem arrayElemBits_spec {taken : List String} {m : Model} {v : Int}
    {stF : ShapeState} {s' : Store}
    (hdefs : stF.DefHolds s')
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s' (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us) :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      arrayElemBits taken m es st v = some (bits, st') →
      (∀ a ∈ st'.aux, a ∈ stF.aux) →
      bits.length = es.length ∧
      ∀ (k : Nat) b, bits[k]? = some b → ∀ e sv, es[k]? = some e →
        BasicExpr.eval s' e = some (.setOfInt sv) →
        s' (Ident.mk b) = some (.bool (decide (sv.Contains v))) := by
  intro es
  induction es with
  | nil =>
      intro st bits st' h hsub
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, ?_⟩
      intro k b hb
      simp at hb
  | cons a rest ih =>
      intro st bits st' h hsub
      simp only [arrayElemBits] at h
      cases hm : memberTerm taken m st (.basic a) v with
      | none => simp only [hm] at h; simp at h
      | some p =>
          obtain ⟨b0, st1⟩ := p
          simp only [hm] at h
          cases hr : arrayElemBits taken m rest st1 v with
          | none => simp only [hr] at h; simp at h
          | some q =>
              obtain ⟨bs, st2⟩ := q
              simp only [hr] at h
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              have hsub1 : ∀ x ∈ st1.aux, x ∈ stF.aux := by
                intro x hx
                exact hsub x (arrayElemBits_aux_subset rest st1 bs st2 hr x hx)
              have hspec := ih st1 bs st2 hr hsub
              refine ⟨by simp [hspec.1], ?_⟩
              intro k b hb e sv he hev
              cases k with
              | zero =>
                  have hb0 : b = b0 := by simpa using hb.symm
                  have he0 : e = a := by simpa using he.symm
                  subst hb0
                  subst he0
                  exact memberTerm_decide_eval hm hsub1 hdefs hdecl sv hev
              | succ k =>
                  have hb' : bs[k]? = some b := by simpa using hb
                  have he' : rest[k]? = some e := by simpa using he
                  exact hspec.2 k b hb' e sv he' hev

/-! ### Auxiliary facts for the set-array encoding -/

/-- The universe of every element of a successful element union. -/
theorem arrayElemUnion_values {m : Model} {es : List BasicExpr} {union : List Int}
    (h : arrayElemUnion m es = some union) :
    ∀ e ∈ es, ∃ us, setArgValues? m (.basic e) = some us ∧ ∀ v ∈ us, v ∈ union := by
  induction es generalizing union with
  | nil => intro e he; simp at he
  | cons a rest ih =>
      intro e he
      simp only [arrayElemUnion] at h
      cases hu : setArgValues? m (.basic a) with
      | none => rw [hu] at h; simp at h
      | some us =>
          rw [hu] at h
          cases hr : arrayElemUnion m rest with
          | none => rw [hr] at h; simp at h
          | some union' =>
              rw [hr] at h
              simp only [Option.some.injEq] at h
              subst h
              rcases List.mem_cons.mp he with rfl | he'
              · exact ⟨us, hu, fun v hv => List.mem_append_left _ hv⟩
              · obtain ⟨us', hu', hv'⟩ := ih hr e he'
                exact ⟨us', hu', fun v hv => List.mem_append_right _ (hv' v hv)⟩

/-- `valuesGet1` at an in-range one-based index is the corresponding
    zero-based list read. -/
theorem valuesGet1_eq_getElem? {xs : List Value} {i : Int} (h1 : 1 ≤ i)
    (h2 : i ≤ (xs.length : Int)) :
    valuesGet1 xs i = xs[i.toNat - 1]? := by
  unfold valuesGet1
  rw [if_pos (by omega)]

/-- An in-range `valuesGet1` read is the list's element. -/
theorem valuesGet1_eq_some_of_bounds {xs : List Value} {i : Int} (h1 : 1 ≤ i)
    (h2 : i ≤ (xs.length : Int)) (h3 : i.toNat - 1 < xs.length) :
    valuesGet1 xs i = some xs[i.toNat - 1] := by
  rw [valuesGet1_eq_getElem? h1 h2]
  exact List.getElem?_eq_getElem h3

/-- A natural one-based index decomposes into its predecessor. -/
theorem int_eq_succ_toNat_sub_one {i : Int} (h : 1 ≤ i) :
    i = ((i.toNat - 1 : Nat) : Int) + 1 := by
  have h0 : 0 ≤ i := by omega
  have hi : (i.toNat : Int) = i := Int.toNat_of_nonneg h0
  have h1 : 1 ≤ i.toNat := by omega
  have hsub : i.toNat - 1 + 1 = i.toNat := Nat.sub_add_cancel h1
  omega

/-- The `int_le` row over two basic expressions. -/
theorem holds_int_le_shape {s : Store} {a b : BasicExpr}
    (h : (shapeConstraint "int_le" [shapeE a, shapeE b]).Holds fullInterp s) :
    ∃ ia ib, a.eval s = some (.int ia) ∧ b.eval s = some (.int ib) ∧ ia ≤ ib := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hargs : (shapeConstraint "int_le" [shapeE a, shapeE b]).args =
      [Expr.basic a, Expr.basic b] := rfl
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval] at hmap
  cases ha : a.eval s with
  | none => rw [ha] at hmap; simp at hmap
  | some va =>
      rw [ha] at hmap
      cases hb : b.eval s with
      | none => rw [hb] at hmap; simp at hmap
      | some vb =>
          rw [hb] at hmap
          have hargsv : args = [va, vb] := by simpa using hmap.symm
          subst hargsv
          have hname : (shapeConstraint "int_le" [shapeE a, shapeE b]).name =
              Ident.mk "int_le" := rfl
          rw [hname, fullInterp_int_le] at hinterp
          cases va with
          | int ia =>
              cases vb with
              | int ib =>
                  simp only [stdInterp] at hinterp
                  exact ⟨ia, ib, rfl, rfl, hinterp⟩
              | bool _ => simp only [stdInterp] at hinterp
              | setOfInt _ => simp only [stdInterp] at hinterp
              | array _ => simp only [stdInterp] at hinterp
          | bool _ => simp only [stdInterp] at hinterp
          | setOfInt _ => simp only [stdInterp] at hinterp
          | array _ => simp only [stdInterp] at hinterp

/-- A true `int_le` row over two basic expressions. -/
theorem holds_int_le_shape_of {s : Store} {a b : BasicExpr} {ia ib : Int}
    (ha : a.eval s = some (.int ia)) (hb : b.eval s = some (.int ib))
    (h : ia ≤ ib) :
    (shapeConstraint "int_le" [shapeE a, shapeE b]).Holds fullInterp s := by
  refine ⟨[.int ia, .int ib], ?_, ?_⟩
  · simp only [shapeConstraint, shapeE, List.mapM_cons, List.mapM_nil, Expr.eval,
      ha, hb]
    rfl
  · have hname : (shapeConstraint "int_le" [shapeE a, shapeE b]).name =
        Ident.mk "int_le" := rfl
    rw [hname, fullInterp_int_le]
    simpa [stdInterp] using h

/-- Inversion of an `array_var_bool_element` membership row. -/
theorem arrayElemRow_holds_inv {s : Store} {i : BasicExpr} {bits : List String}
    {tv : String} (h : (arrayElemRow i bits tv).Holds fullInterp s) :
    ∃ ii b xs, i.eval s = some (.int ii) ∧
      s (Ident.mk tv) = some (.bool b) ∧
      (bits.map shapeName).mapM (BasicExpr.eval s) = some xs ∧
      valuesGet1 xs ii = some (.bool b) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hargs : (arrayElemRow i bits tv).args =
      [Expr.basic i, Expr.array (bits.map shapeName), Expr.basic (shapeName tv)] := rfl
  rw [hargs, mapM_three_iff] at hmap
  obtain ⟨v1, v2, v3, h1, h2, h3, rfl⟩ := hmap
  simp only [Expr.eval] at h1 h2 h3
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h2
  have hname : (arrayElemRow i bits tv).name = Ident.mk "array_var_bool_element" := rfl
  rw [hname, fullInterp_array_var_bool_element] at hinterp
  cases v1 with
  | int ii =>
      cases v3 with
      | bool b =>
          simp only [stdInterp] at hinterp
          exact ⟨ii, b, xs, h1, by simpa [shapeName, BasicExpr.eval] using h3,
            hxs, hinterp⟩
      | int _ => simp only [stdInterp] at hinterp
      | setOfInt _ => simp only [stdInterp] at hinterp
      | array _ => simp only [stdInterp] at hinterp
  | bool _ => simp only [stdInterp] at hinterp
  | setOfInt _ => simp only [stdInterp] at hinterp
  | array _ => simp only [stdInterp] at hinterp

/-- An `array_var_bool_element` row holds when its bits read the given
    Boolean list at the index. -/
theorem arrayElemRow_holds_of {s : Store} {i : BasicExpr} {bits : List String}
    {tv : String} {ii : Int} {b : Bool} {xs : List Value}
    (hi : i.eval s = some (.int ii))
    (htv : s (Ident.mk tv) = some (.bool b))
    (hbits : (bits.map shapeName).mapM (BasicExpr.eval s) = some xs)
    (hget : valuesGet1 xs ii = some (.bool b)) :
    (arrayElemRow i bits tv).Holds fullInterp s := by
  refine ⟨[.int ii, .array xs, .bool b], ?_, ?_⟩
  · have hargs : (arrayElemRow i bits tv).args =
        [Expr.basic i, Expr.array (bits.map shapeName), Expr.basic (shapeName tv)] := rfl
    rw [hargs, mapM_three_iff]
    refine ⟨.int ii, .array xs, .bool b, ?_, ?_, ?_, rfl⟩
    · simpa [Expr.eval] using hi
    · simp only [Expr.eval]
      rw [hbits]
      rfl
    · simp only [Expr.eval]
      simpa [shapeName, BasicExpr.eval] using htv
  · have hname : (arrayElemRow i bits tv).name = Ident.mk "array_var_bool_element" := rfl
    rw [hname, fullInterp_array_var_bool_element]
    simpa [stdInterp] using hget

/-- A membership bit reads the corresponding entry of an evaluated list of
    identifier Booleans. -/
theorem mapM_shapeName_getElem? {s : Store} {xs : List String} {ys : List Value}
    (h : (xs.map shapeName).mapM (BasicExpr.eval s) = some ys) {k : Nat}
    {b : String} (hb : xs[k]? = some b) : ys[k]? = s (Ident.mk b) := by
  have hk := mapM_eval_getElem? h k (shapeName b) ?_
  · simpa [shapeName, BasicExpr.eval] using hk
  · rw [List.getElem?_map, hb]
    rfl

/-- A constraint emitted into a state's list holds. -/
theorem holds_of_emitList_mem {st : ShapeState} {cs : List ConstraintItem}
    {s : Store} (h : (st.emitList cs).Holds s) :
    ∀ c ∈ cs, c.Holds fullInterp s := by
  intro c hc
  exact h c (by
    simp only [ShapeState.emitList]
    exact List.mem_append_left _ (List.mem_reverse.mpr hc))

/-- The rows of an element row list are its constraints. -/
theorem arrayElemRow_mem_rowList {i : BasicExpr}
    {rows : List (Int × List String × String)} {r : Int × List String × String}
    (hr : r ∈ rows) : arrayElemRow i r.2.1 r.2.2 ∈ arrayElemRowList i rows := by
  induction rows with
  | nil => cases hr
  | cons a rest ih =>
      rcases List.mem_cons.mp hr with rfl | hr'
      · simp [arrayElemRowList]
      · simp only [arrayElemRowList]
        exact List.mem_cons_of_mem _ (ih hr')

/-- `arrayElemBits` keeps every old auxiliary. -/
theorem arrayElemBits_aux_subset_mem {taken : List String} {m : Model} {v : Int} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      arrayElemBits taken m es st v = some (bits, st') →
      ∀ a ∈ st.aux, a ∈ st'.aux := by
  intro es
  induction es with
  | nil =>
      intro st bits st' h a ha
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ha
  | cons e rest ih =>
      intro st bits st' h a ha
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
              exact ih st1 bs st2 hr a (memberTerm_aux_subset hm a ha)

/-- `arrayElemRows` keeps every old auxiliary. -/
theorem arrayElemRows_aux_subset {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState),
      arrayElemRows taken m i es T st vals = some (rows, st') →
      ∀ a ∈ st.aux, a ∈ st'.aux := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' h a ha
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ha
  | cons v vs ih =>
      intro st rows st' h a ha
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
                  exact ih st2 rows' st3 hr a
                    (memberTerm_aux_subset hm a
                      (arrayElemBits_aux_subset_mem es st bits st1 hb a ha))

/-- `arrayElemBits` keeps every old constraint. -/
theorem arrayElemBits_cons_subset_mem {taken : List String} {m : Model} {v : Int} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      arrayElemBits taken m es st v = some (bits, st') →
      ∀ c ∈ st.cons, c ∈ st'.cons := by
  intro es
  induction es with
  | nil =>
      intro st bits st' h c hc
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  | cons e rest ih =>
      intro st bits st' h c hc
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
              exact ih st1 bs st2 hr c (memberTerm_cons_subset hm c hc)

/-- `arrayElemRows` keeps every old constraint. -/
theorem arrayElemRows_cons_subset {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState),
      arrayElemRows taken m i es T st vals = some (rows, st') →
      ∀ c ∈ st.cons, c ∈ st'.cons := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' h c hc
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hc
  | cons v vs ih =>
      intro st rows st' h c hc
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
                  exact ih st2 rows' st3 hr c
                    (memberTerm_cons_subset hm c
                      (arrayElemBits_cons_subset_mem es st bits st1 hb c hc))

/-- A Boolean list entry that survives evaluation is the value of the
    corresponding name in the store. -/
theorem mapM_shapeName_exists {s : Store} {bits : List String} {ys : List Value}
    (h : (bits.map shapeName).mapM (BasicExpr.eval s) = some ys) {k : Nat} {v : Value}
    (hk : ys[k]? = some v) :
    ∃ b, bits[k]? = some b ∧ s (Ident.mk b) = some v := by
  rw [mapM_getElem?_option h k, List.getElem?_map] at hk
  cases hb : bits[k]? with
  | none => simp [hb] at hk
  | some b =>
      simp only [hb, Option.map_some, Option.bind_some] at hk
      exact ⟨b, rfl, by simpa [shapeName, BasicExpr.eval] using hk⟩

/-- The rows allocated by `arrayElemRows` cover every value of the value
    list exactly once, with membership bits that read the element set
    values and a target bit that reads the target set value. -/
theorem arrayElemRows_spec {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} {stF : ShapeState} {s' : Store}
    {svT : IntSetValue}
    (hdefs : stF.DefHolds s')
    (hdecl : ∀ S us, modelSetUniverse? m S = some us →
      ∀ sv, s' (Ident.mk S) = some (.setOfInt sv) → ∀ w, sv.Contains w → w ∈ us)
    (hT : s' (Ident.mk T) = some (.setOfInt svT)) :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState),
      arrayElemRows taken m i es T st vals = some (rows, st') →
      (∀ a ∈ st'.aux, a ∈ stF.aux) →
      rows.map (fun r => r.1) = vals ∧
      ∀ r ∈ rows,
        r.2.1.length = es.length ∧
        (∀ (k : Nat) b, r.2.1[k]? = some b → ∀ e sv, es[k]? = some e →
          BasicExpr.eval s' e = some (.setOfInt sv) →
          s' (Ident.mk b) = some (.bool (decide (sv.Contains r.1)))) ∧
        s' (Ident.mk r.2.2) = some (.bool (decide (svT.Contains r.1))) := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' h hsub
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      refine ⟨rfl, ?_⟩
      intro r hr
      simp at hr
  | cons v vs ih =>
      intro st rows st' h hsub
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
                  have hsub2 : ∀ a ∈ st2.aux, a ∈ stF.aux :=
                    fun a ha => hsub a
                      (arrayElemRows_aux_subset vs st2 rows' st3 hr a ha)
                  have hsub1 : ∀ a ∈ st1.aux, a ∈ stF.aux :=
                    fun a ha => hsub2 a (memberTerm_aux_subset hm a ha)
                  have hbits := arrayElemBits_spec (taken := taken) (m := m)
                    (v := v) (stF := stF) (s' := s') hdefs hdecl
                    es st bits st1 hb hsub1
                  have hspec := ih st2 rows' st3 hr hsub
                  refine ⟨?_, ?_⟩
                  · simp [hspec.1]
                  · intro r hr
                    rcases List.mem_cons.mp hr with rfl | hr'
                    · refine ⟨hbits.1, ?_, ?_⟩
                      · intro k b hbk e sv he hev
                        exact hbits.2 k b hbk e sv he hev
                      · exact memberTerm_decide_eval hm hsub2 hdefs hdecl svT hT
                    · exact hspec.2 r hr'

/-- The range checks of an element constraint force an integer index in
    `1..n`. -/
theorem shapeRangeChecks_bounds {i : BasicExpr} {n : Nat} {s : Store}
    (h : ∀ c ∈ shapeRangeChecks i n, c.Holds fullInterp s) :
    ∃ ii, i.eval s = some (.int ii) ∧ 1 ≤ ii ∧ ii ≤ (n : Int) := by
  cases i with
  | ident x =>
      have h1 : (shapeConstraint "int_le"
          [shapeE (shapeInt 1), shapeE (.ident x)]).Holds fullInterp s :=
        h _ (by simp [shapeRangeChecks])
      have h2 : (shapeConstraint "int_le"
          [shapeE (.ident x), shapeE (shapeInt (n : Int))]).Holds fullInterp s :=
        h _ (by simp [shapeRangeChecks])
      obtain ⟨ia, ib, h1a, h1b, hle1⟩ :=
        holds_int_le_shape (a := shapeInt 1) (b := .ident x) h1
      obtain ⟨ja, jb, h2a, h2b, hle2⟩ :=
        holds_int_le_shape (a := .ident x) (b := shapeInt (n : Int)) h2
      have h1i : (1 : Int) = ia := Value.int.inj (Option.some.inj h1a)
      have h2i : (n : Int) = jb := Value.int.inj (Option.some.inj h2b)
      have hji : ib = ja := Value.int.inj (Option.some.inj (h1b.symm.trans h2a))
      exact ⟨ib, h1b, by omega, by omega⟩
  | lit l =>
      cases l with
      | int k =>
          by_cases hk : 1 ≤ k ∧ k ≤ (n : Int)
          · exact ⟨k, rfl, hk.1, hk.2⟩
          · have hf : falseConstraint.Holds fullInterp s := by
              apply h
              simp only [shapeRangeChecks]
              rw [if_neg hk]
              simp
            exact False.elim (falseConstraint_holds_false s hf)
      | bool bb =>
          have h1 : (shapeConstraint "int_le"
              [shapeE (shapeInt 1), shapeE (.lit (.bool bb))]).Holds fullInterp s :=
            h _ (by simp [shapeRangeChecks])
          obtain ⟨ia, ib, h1a, h1b, hle1⟩ :=
            holds_int_le_shape (a := shapeInt 1) (b := .lit (.bool bb)) h1
          simp [BasicExpr.eval, BasicLiteral.denote] at h1b
      | set sl =>
          have h1 : (shapeConstraint "int_le"
              [shapeE (shapeInt 1), shapeE (.lit (.set sl))]).Holds fullInterp s :=
            h _ (by simp [shapeRangeChecks])
          obtain ⟨ia, ib, h1a, h1b, hle1⟩ :=
            holds_int_le_shape (a := shapeInt 1) (b := .lit (.set sl)) h1
          simp [BasicExpr.eval, BasicLiteral.denote] at h1b

/-- Decomposition of a successful array-element rewrite. -/
theorem rewriteArrayElem_decomp {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteArrayElem taken m st i es T = some (st', cs')) :
    ∃ vals rows, arrayElemValues m es T = some vals ∧
      arrayElemRows taken m i es T st vals = some (rows, st') ∧
      cs' = arrayElemRowList i rows ++ shapeRangeChecks i es.length := by
  unfold rewriteArrayElem at h
  cases hv : arrayElemValues m es T with
  | none => simp [hv] at h
  | some vals =>
      simp only [hv] at h
      cases hr : arrayElemRows taken m i es T st vals with
      | none => simp [hr] at h
      | some p =>
          obtain ⟨rows, st0⟩ := p
          simp only [hr, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ⟨vals, rows, rfl, hr, rfl⟩

/-- A list of names that all have values evaluates to a value list. -/
theorem mapM_shapeName_of_forall {s : Store} {bits : List String}
    (h : ∀ b ∈ bits, ∃ v, s (Ident.mk b) = some v) :
    ∃ ys, (bits.map shapeName).mapM (BasicExpr.eval s) = some ys := by
  induction bits with
  | nil => exact ⟨[], by simp [List.mapM_nil]⟩
  | cons b rest ih =>
      obtain ⟨v, hv⟩ := h b (by simp)
      obtain ⟨ys, hys⟩ := ih (fun c hc => h c (by simp [hc]))
      refine ⟨v :: ys, ?_⟩
      have hv' : BasicExpr.eval s (shapeName b) = some v := by
        simpa [shapeName, BasicExpr.eval] using hv
      simp only [List.map_cons, List.mapM_cons]
      rw [hv', hys]
      rfl

/-- Inversion of the source `array_var_set_element` constraint. -/
theorem arrayVarSetElement_holds_inv {s : Store} {i : BasicExpr}
    {es : List BasicExpr} {T : String} {anns : List Annotation}
    (h : (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns).Holds fullInterp s) :
    ∃ ii xs svT, i.eval s = some (.int ii) ∧
      es.mapM (BasicExpr.eval s) = some xs ∧
      s (Ident.mk T) = some (.setOfInt svT) ∧
      ∃ sv, valuesGet1 xs ii = some (.setOfInt sv) ∧
        ∀ j, sv.Contains j ↔ svT.Contains j := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hargs : (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns).args =
      [Expr.basic i, Expr.array es, Expr.basic (.ident (Ident.mk T))] := rfl
  rw [hargs, mapM_three_iff] at hmap
  obtain ⟨v1, v2, v3, h1, h2, h3, rfl⟩ := hmap
  simp only [Expr.eval] at h1 h2 h3
  obtain ⟨xs, hxs, rfl⟩ := Option.map_eq_some_iff.mp h2
  have hname : (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns).name =
      Ident.mk "array_var_set_element" := rfl
  rw [hname, fullInterp_array_var_set_element] at hinterp
  cases v1 with
  | int ii =>
      cases v3 with
      | setOfInt svT =>
          cases hg : valuesGet1 xs ii with
          | none => simp [stdInterp, hg] at hinterp
          | some v =>
              cases v with
              | bool b => simp [stdInterp, hg] at hinterp
              | int k => simp [stdInterp, hg] at hinterp
              | array ys => simp [stdInterp, hg] at hinterp
              | setOfInt sv =>
                  simp only [stdInterp, hg] at hinterp
                  exact ⟨ii, xs, svT, h1, hxs, by simpa [BasicExpr.eval] using h3,
                    sv, hg, hinterp⟩
      | bool _ => simp [stdInterp] at hinterp
      | int _ => simp [stdInterp] at hinterp
      | array _ => simp [stdInterp] at hinterp
  | bool _ => simp [stdInterp] at hinterp
  | array _ => simp [stdInterp] at hinterp
  | setOfInt _ => simp [stdInterp] at hinterp

/-- `arrayElemBits` adds only functional definitions of new auxiliaries. -/
theorem arrayElemBits_newHolds {taken : List String} {m : Model} {v : Int} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState) (s' : Store),
      arrayElemBits taken m es st v = some (bits, st') →
      st'.DefHolds s' → st.NewHolds st' s' := by
  intro es
  induction es with
  | nil =>
      intro st bits st' s' h hdefs c hc
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl hc
  | cons e rest ih =>
      intro st bits st' s' h hdefs c hc
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
              have hdefs1 : st1.DefHolds s' :=
                ShapeState.DefHolds.mono
                  (arrayElemBits_aux_subset rest st1 bs st2 hr) hdefs
              exact ShapeState.newHolds_trans (memberTerm_newHolds hm hdefs1)
                (ih st1 bs st2 s' hr hdefs) c hc

/-- `arrayElemRows` adds only functional definitions of new auxiliaries. -/
theorem arrayElemRows_newHolds {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState)
      (s' : Store),
      arrayElemRows taken m i es T st vals = some (rows, st') →
      st'.DefHolds s' → st.NewHolds st' s' := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' s' h hdefs c hc
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact Or.inl hc
  | cons v vs ih =>
      intro st rows st' s' h hdefs c hc
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
                  have hdefs1 : st1.DefHolds s' :=
                    ShapeState.DefHolds.mono
                      (fun a ha => arrayElemRows_aux_subset vs st2 rows' st3 hr a
                        (memberTerm_aux_subset hm a ha)) hdefs
                  have hdefs2 : st2.DefHolds s' :=
                    ShapeState.DefHolds.mono
                      (arrayElemRows_aux_subset vs st2 rows' st3 hr) hdefs
                  exact ShapeState.newHolds_trans
                    (arrayElemBits_newHolds es st bits st1 s' hb hdefs1)
                    (ShapeState.newHolds_trans (memberTerm_newHolds hm hdefs2)
                      (ih st2 rows' st3 s' hr hdefs)) c hc

/-- `arrayElemBits` preserves well-formedness. -/
theorem arrayElemBits_wf {taken : List String} {m : Model} {v : Int} :
    ∀ (es : List BasicExpr) (st : ShapeState) (bits : List String)
      (st' : ShapeState),
      (∀ e ∈ es, ∀ S, e = .ident (Ident.mk S) → S ∈ taken) →
      arrayElemBits taken m es st v = some (bits, st') →
      st.WF taken m → st'.WF taken m := by
  intro es
  induction es with
  | nil =>
      intro st bits st' hsrc h hwf
      simp only [arrayElemBits, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
  | cons e rest ih =>
      intro st bits st' hsrc h hwf
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
              have htake : ∀ S,
                  Expr.basic e = Expr.basic (BasicExpr.ident (Ident.mk S)) → S ∈ taken := by
                intro S hS
                exact hsrc e (by simp) S (by cases hS; rfl)
              have hwf1 : st1.WF taken m := memberTerm_wf hwf htake hm
              exact ih st1 bs st2
                (fun e' he' S hS => hsrc e' (by simp [he']) S hS) hr hwf1

/-- `arrayElemRows` preserves well-formedness. -/
theorem arrayElemRows_wf {taken : List String} {m : Model} {i : BasicExpr}
    {es : List BasicExpr} {T : String} :
    ∀ (vals : List Int) (st : ShapeState)
      (rows : List (Int × List String × String)) (st' : ShapeState),
      (∀ e ∈ es, ∀ S, e = .ident (Ident.mk S) → S ∈ taken) →
      T ∈ taken →
      arrayElemRows taken m i es T st vals = some (rows, st') →
      st.WF taken m → st'.WF taken m := by
  intro vals
  induction vals with
  | nil =>
      intro st rows st' hsrc hT h hwf
      simp only [arrayElemRows, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
  | cons v vs ih =>
      intro st rows st' hsrc hT h hwf
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
                  have hwf1 : st1.WF taken m :=
                    arrayElemBits_wf (es := es) (st := st) (bits := bits)
                      (st' := st1) hsrc hb hwf
                  have hwf2 : st2.WF taken m := memberTerm_wf_ident hwf1 hT hm
                  exact ih st2 rows' st3 hsrc hT hr hwf2

/-- `rewriteArrayElem` keeps every old auxiliary. -/
theorem rewriteArrayElem_aux_subset {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteArrayElem taken m st i es T = some (st', cs')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  obtain ⟨vals, rows, hvals, hrows, hcs⟩ := rewriteArrayElem_decomp h
  exact arrayElemRows_aux_subset vals st rows st' hrows

/-- `rewriteArrayElem` keeps every old constraint. -/
theorem rewriteArrayElem_cons_subset {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteArrayElem taken m st i es T = some (st', cs')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  obtain ⟨vals, rows, hvals, hrows, hcs⟩ := rewriteArrayElem_decomp h
  exact arrayElemRows_cons_subset vals st rows st' hrows

/-- `rewriteArrayElem` preserves well-formedness. -/
theorem rewriteArrayElem_wf {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem}
    (hwf : st.WF taken m) (hmwf : WellFormed fullSig m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : rewriteArrayElem taken m st i es T = some (st', cs')) :
    st'.WF taken m := by
  obtain ⟨vals, rows, hvals, hrows, hcs⟩ := rewriteArrayElem_decomp h
  obtain ⟨ut, union, hvalsEq, ht, hu⟩ := arrayElemValues_decomp hvals
  have hT : T ∈ taken := modelSetUniverse?_name_taken hmwf hsup ht
  have hsrc : ∀ e ∈ es, ∀ S, e = .ident (Ident.mk S) → S ∈ taken := by
    intro e he S hS
    obtain ⟨us, harg, _⟩ := arrayElemUnion_values hu e he
    subst hS
    exact setArgValues?_ident_taken hsup harg S rfl
  exact arrayElemRows_wf (vals := vals) (es := es) (st := st) (rows := rows) (st' := st')
    hsrc hT hrows hwf

/-- Emitting a list of constraints that all hold is a valid `NewHolds`
    step. -/
theorem ShapeState.newHolds_emitList {st : ShapeState}
    {cs : List ConstraintItem} {s : Store}
    (h : ∀ c ∈ cs, c.Holds fullInterp s) :
    st.NewHolds (st.emitList cs) s := by
  intro c hc
  have hc' : c ∈ cs.reverse ++ st.cons := by
    simpa [ShapeState.emitList] using hc
  rcases List.mem_append.mp hc' with hc'' | hc''
  · exact Or.inr (h c (List.mem_reverse.mp hc''))
  · exact Or.inl hc''

/-- Every member of an element row list comes from a stored row. -/
theorem mem_arrayElemRowList_elim {i : BasicExpr}
    {rows : List (Int × List String × String)} {c : ConstraintItem}
    (h : c ∈ arrayElemRowList i rows) :
    ∃ r ∈ rows, c = arrayElemRow i r.2.1 r.2.2 := by
  induction rows with
  | nil => simp [arrayElemRowList] at h
  | cons a rest ih =>
      simp only [arrayElemRowList, List.mem_cons] at h
      rcases h with rfl | h'
      · exact ⟨a, List.mem_cons_self, rfl⟩
      · obtain ⟨r, hr, hc⟩ := ih h'
        exact ⟨r, List.mem_cons_of_mem _ hr, hc⟩

/-- An element constraint mentions the index's names. -/
theorem mem_constraintNames_arrayElem_index {i : BasicExpr} {es : List BasicExpr}
    {T : String} {anns : List Annotation} {x : String} (hx : x ∈ basicNames i) :
    x ∈ constraintNames (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns) := by
  simp only [constraintNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    exprNames]
  exact List.mem_append_left _ hx

/-- An element constraint mentions every name of every element expression. -/
theorem mem_constraintNames_arrayElem {i : BasicExpr} {es : List BasicExpr}
    {T : String} {anns : List Annotation} {e : BasicExpr} (he : e ∈ es)
    {x : String} (hx : x ∈ basicNames e) :
    x ∈ constraintNames (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns) := by
  simp only [constraintNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    exprNames, basicNames]
  exact List.mem_append_right _ (List.mem_append_left _ (List.mem_flatMap.mpr ⟨e, he, hx⟩))

/-- An element constraint mentions the target set's name. -/
theorem mem_constraintNames_arrayElem_target {i : BasicExpr} {es : List BasicExpr}
    {T : String} {anns : List Annotation} :
    T ∈ constraintNames (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns) := by
  simp only [constraintNames, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    exprNames, basicNames]
  exact List.mem_append_right _ (List.mem_append_right _ (List.mem_singleton_self T))

/-- **Soundness of the array-element rewrite.** -/
theorem rewriteArrayElem_sound {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem} {str : Store}
    {anns : List Annotation}
    (h : rewriteArrayElem taken m st i es T = some (st', cs'))
    (hdefs : st'.DefHolds str)
    (hholds : (st'.emitList cs').Holds str)
    (hint : ShapeIntDomains m str) (hset : ShapeSetDomains m str) :
    (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns).Holds fullInterp str := by
  obtain ⟨vals, rows, hvals, hrows, hcs⟩ := rewriteArrayElem_decomp h
  subst hcs
  obtain ⟨ut, union, hvalsEq, ht, hu⟩ := arrayElemValues_decomp hvals
  obtain ⟨svT, hT⟩ := hset.1 T ut ht
  have hrange := shapeRangeChecks_bounds (i := i) (n := es.length) (s := str)
    (fun c hc => holds_of_emitList_mem hholds c (List.mem_append_right _ hc))
  obtain ⟨ii, hi, hii1, hiin⟩ := hrange
  have hev : ∀ e ∈ es, ∃ sv, e.eval str = some (.setOfInt sv) :=
    arrayElemUnion_eval hu hset
  obtain ⟨xs, hxs⟩ := mapM_eval_exists hev
  have hxslen : xs.length = es.length := mapM_length_option hxs
  have hrowspec := arrayElemRows_spec (taken := taken) (m := m) (i := i) (es := es)
    (T := T) (stF := st') (s' := str) (svT := svT) hdefs hset.2 hT
    vals st rows st' hrows (fun a ha => ha)
  generalize hkdef : ii.toNat - 1 = k
  have hii0 : 0 ≤ ii := by omega
  have htoNat : (ii.toNat : Int) = ii := Int.toNat_of_nonneg hii0
  have hk_es : k < es.length := by omega
  have hk_xs : k < xs.length := by omega
  have hesel : es[k]? = some es[k] := List.getElem?_eq_getElem hk_es
  have hxsel : xs[k]? = some xs[k] := List.getElem?_eq_getElem hk_xs
  have hxeval : xs[k]? = (es[k]).eval str :=
    mapM_eval_getElem? hxs k (es[k]) hesel
  obtain ⟨svE, hsvE⟩ := hev (es[k]) (List.mem_of_getElem? hesel)
  have hxset : xs[k] = .setOfInt svE :=
    Option.some.inj (hxsel.symm.trans (hxeval.trans hsvE))
  have hget1 : valuesGet1 xs ii = some (.setOfInt svE) := by
    rw [valuesGet1_eq_getElem? hii1 (by omega)]
    rw [hkdef]
    exact List.getElem?_eq_some_iff.mpr ⟨hk_xs, hxset⟩
  have hiff : ∀ j, svE.Contains j ↔ svT.Contains j := by
    intro j
    by_cases hj : j ∈ vals
    · obtain ⟨r, hr, hrval⟩ := List.mem_map.mp (by rw [hrowspec.1]; exact hj)
      have hrowHolds : (arrayElemRow i r.2.1 r.2.2).Holds fullInterp str :=
        holds_of_emitList_mem hholds _ (List.mem_append_left _ (arrayElemRow_mem_rowList hr))
      obtain ⟨ii', b, xs_b, hi', htv, hbits, hgetb⟩ := arrayElemRow_holds_inv hrowHolds
      have hii' : ii' = ii := Value.int.inj (Option.some.inj (hi'.symm.trans hi))
      subst hii'
      have hspecr := hrowspec.2 r hr
      have hbT : b = decide (svT.Contains r.1) :=
        Value.bool.inj (Option.some.inj (htv.symm.trans hspecr.2.2))
      have hxsblen : xs_b.length = r.2.1.length := by
        simpa using mapM_length_option hbits
      have hbk : xs_b[k]? = some (.bool b) := by
        rw [valuesGet1_eq_getElem? (valuesGet1_bounds hgetb).1 (by omega)] at hgetb
        simpa [hkdef] using hgetb
      obtain ⟨bk, hbkb, hbkval⟩ := mapM_shapeName_exists hbits hbk
      have hk_bits : k < r.2.1.length := by
        have hb := (valuesGet1_bounds hgetb).2
        rw [← hxsblen]
        omega
      have hsvEk : BasicExpr.eval str es[k] = some (.setOfInt svE) := by
        simpa [hkdef] using hsvE
      have hspecbit := hspecr.2.1 k bk hbkb (es[k]) svE hesel hsvEk
      have hbE : b = decide (svE.Contains r.1) :=
        Value.bool.inj (Option.some.inj (hbkval.symm.trans hspecbit))
      rw [hrval] at hbT hbE
      exact Iff.symm (decide_eq_decide.mp (hbT.symm.trans hbE))
    · constructor
      · intro hc
        have hmem_es : es[k] ∈ es := List.mem_of_getElem? hesel
        obtain ⟨us, harg, husub⟩ := arrayElemUnion_values hu (es[k]) hmem_es
        have hsvEk : BasicExpr.eval str es[k] = some (.setOfInt svE) := by
          simpa [hkdef] using hsvE
        have hjmem : j ∈ us :=
          setArgValues?_contains (h := harg) (s := str) hset.2
            (by simpa [Expr.eval] using hsvEk) j hc
        exact False.elim (hj ((arrayElemValues_mem hvals j).mpr
          (Or.inr ⟨es[k], hmem_es, us, harg, hjmem⟩)))
      · intro hc
        exact False.elim (hj (arrayElemValues_mem_of_universe hvals ht
          (hset.2 T ut ht svT hT j hc)))
  refine ⟨[.int ii, .array xs, .setOfInt svT], ?_, ?_⟩
  · have hargseq : (ConstraintItem.mk (Ident.mk "array_var_set_element")
        [.basic i, .array es, .basic (.ident (Ident.mk T))] anns).args =
        [Expr.basic i, Expr.array es, Expr.basic (.ident (Ident.mk T))] := rfl
    rw [hargseq, mapM_three_iff]
    refine ⟨.int ii, .array xs, .setOfInt svT, ?_, ?_, ?_, rfl⟩
    · simpa [Expr.eval] using hi
    · simpa [Expr.eval] using congrArg (Option.map Value.array) hxs
    · simpa [Expr.eval, BasicExpr.eval] using hT
  · have hname : (ConstraintItem.mk (Ident.mk "array_var_set_element")
        [.basic i, .array es, .basic (.ident (Ident.mk T))] anns).name =
        Ident.mk "array_var_set_element" := rfl
    rw [hname, fullInterp_array_var_set_element]
    simp only [stdInterp]
    rw [hget1]
    exact hiff

/-- **Completeness of the array-element rewrite.** -/
theorem rewriteArrayElem_newHolds {taken : List String} {m : Model}
    {st : ShapeState} {i : BasicExpr} {es : List BasicExpr} {T : String}
    {st' : ShapeState} {cs' : List ConstraintItem} {s s' : Store}
    {anns : List Annotation}
    (h : rewriteArrayElem taken m st i es T = some (st', cs'))
    (hdefs : st'.DefHolds s')
    (hsrc : (ConstraintItem.mk (Ident.mk "array_var_set_element")
      [.basic i, .array es, .basic (.ident (Ident.mk T))] anns).Holds fullInterp s)
    (hint : ShapeIntDomains m s) (hset : ShapeSetDomains m s)
    (hset' : ShapeSetDomains m s')
    (hagree : ∀ x ∈ basicNames i, s' (Ident.mk x) = s (Ident.mk x))
    (hagreeEs : ∀ e ∈ es, ∀ x ∈ basicNames e, s' (Ident.mk x) = s (Ident.mk x))
    (hagreeT : s' (Ident.mk T) = s (Ident.mk T)) :
    st.NewHolds (st'.emitList cs') s' := by
  obtain ⟨vals, rows, hvals, hrows, hcs⟩ := rewriteArrayElem_decomp h
  subst hcs
  obtain ⟨ut, union, hvalsEq, ht, hu⟩ := arrayElemValues_decomp hvals
  obtain ⟨ii, xs, svT, hi, hxs, hT, svE, hget1, hiff⟩ :=
    arrayVarSetElement_holds_inv hsrc
  have hT' : s' (Ident.mk T) = some (.setOfInt svT) := by
    rw [hagreeT]
    exact hT
  have hxslen : xs.length = es.length := mapM_length_option hxs
  have hrowspec := arrayElemRows_spec (taken := taken) (m := m) (i := i) (es := es)
    (T := T) (stF := st') (s' := s') (svT := svT) hdefs hset'.2 hT'
    vals st rows st' hrows (fun a ha => ha)
  have hi' : i.eval s' = some (.int ii) := by
    rw [basicNames_eval_agree (s := s') (t := s) (b := i) hagree]
    exact hi
  have hb1 : 1 ≤ ii := (valuesGet1_bounds hget1).1
  have hb2 : ii ≤ (es.length : Int) := by
    have h := (valuesGet1_bounds hget1).2
    have := mapM_length_option hxs
    omega
  have hii0 : 0 ≤ ii := by omega
  have htoNat : (ii.toNat : Int) = ii := Int.toNat_of_nonneg hii0
  have hesel : es[ii.toNat - 1]? = some es[ii.toNat - 1] :=
    List.getElem?_eq_getElem (by omega)
  have hxget : valuesGet1 xs ii = some xs[ii.toNat - 1] := by
    rw [valuesGet1_eq_getElem? hb1 (by omega)]
    exact List.getElem?_eq_getElem (by omega)
  have hxsk : xs[ii.toNat - 1] = .setOfInt svE :=
    Option.some.inj (hxget.symm.trans hget1)
  have hsvEs : BasicExpr.eval s es[ii.toNat - 1] = some (.setOfInt svE) := by
    have hxev : xs[ii.toNat - 1]? = (es[ii.toNat - 1]).eval s :=
      mapM_eval_getElem? hxs (ii.toNat - 1) (es[ii.toNat - 1]) hesel
    have hsome : some xs[ii.toNat - 1] = (es[ii.toNat - 1]).eval s := by
      rw [← hxev]
      exact (List.getElem?_eq_getElem (by omega)).symm
    rw [← hsome, hxsk]
  have hmem_es : es[ii.toNat - 1] ∈ es := List.mem_of_getElem? hesel
  have hsvEs' : BasicExpr.eval s' es[ii.toNat - 1] = some (.setOfInt svE) := by
    rw [basicNames_eval_agree (s := s') (t := s) (b := es[ii.toNat - 1])
      (fun x hx => hagreeEs (es[ii.toNat - 1]) hmem_es x hx)]
    exact hsvEs
  -- every membership bit of every row evaluates to a Boolean
  have hbitsVal : ∀ r ∈ rows, ∀ b ∈ r.2.1, ∃ v, s' (Ident.mk b) = some v := by
    intro r hr b hb
    have hspecr := hrowspec.2 r hr
    obtain ⟨kb, hkb⟩ := List.mem_iff_getElem?.mp hb
    have hklt : kb < es.length := by
      have hlen : r.2.1.length = es.length := hspecr.1
      rw [← hlen]
      exact (List.getElem?_eq_some_iff.mp hkb).1
    have hesk : es[kb]? = some es[kb] := List.getElem?_eq_getElem hklt
    have hmem : es[kb] ∈ es := List.mem_of_getElem? hesk
    obtain ⟨us, harg, husub⟩ := arrayElemUnion_values hu (es[kb]) hmem
    obtain ⟨svb, hsvb⟩ := setArgValues?_eval harg hset
    have hsvb' : BasicExpr.eval s' es[kb] = some (.setOfInt svb) := by
      rw [basicNames_eval_agree (s := s') (t := s) (b := es[kb])
        (fun x hx => hagreeEs (es[kb]) hmem x hx)]
      exact hsvb
    have hspecbit := hspecr.2.1 kb b hkb (es[kb]) svb hesk hsvb'
    exact ⟨_, hspecbit⟩
  have hrowsHold : ∀ r ∈ rows, (arrayElemRow i r.2.1 r.2.2).Holds fullInterp s' := by
    intro r hr
    have hspecr := hrowspec.2 r hr
    obtain ⟨ys, hys⟩ := mapM_shapeName_of_forall (hbitsVal r hr)
    have hkbits : ii.toNat - 1 < r.2.1.length := by
      have hlen : r.2.1.length = es.length := hspecr.1
      omega
    have hbkb : r.2.1[ii.toNat - 1]? = some r.2.1[ii.toNat - 1] :=
      List.getElem?_eq_getElem hkbits
    have hbval := hspecr.2.1 (ii.toNat - 1) (r.2.1[ii.toNat - 1]) hbkb
      (es[ii.toNat - 1]) svE hesel hsvEs'
    have hysval : ys[ii.toNat - 1]? = some (.bool (decide (svE.Contains r.1))) := by
      rw [mapM_shapeName_getElem? hys hbkb, hbval]
    have hgetys : valuesGet1 ys ii =
        some (.bool (decide (svE.Contains r.1))) := by
      rw [valuesGet1_eq_getElem? hb1 (by
        have hlen : ys.length = r.2.1.length := by
          simpa using mapM_length_option hys
        have hlen2 : r.2.1.length = es.length := hspecr.1
        omega)]
      exact hysval
    have hgetysT : valuesGet1 ys ii = some (.bool (decide (svT.Contains r.1))) := by
      rw [hgetys, decide_eq_decide.mpr (hiff r.1)]
    exact arrayElemRow_holds_of hi' hspecr.2.2 hys hgetysT
  have hrowsAll : ∀ c ∈ arrayElemRowList i rows, c.Holds fullInterp s' := by
    intro c hc
    obtain ⟨r, hr, rfl⟩ := mem_arrayElemRowList_elim hc
    exact hrowsHold r hr
  have hranges : ∀ c ∈ shapeRangeChecks i es.length, c.Holds fullInterp s' := by
    cases i with
    | ident x =>
        intro c hc
        simp only [shapeRangeChecks, List.mem_cons, List.mem_singleton,
          List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact holds_int_le_shape_of (a := shapeInt 1) (b := .ident x)
            (by simp [shapeInt, BasicExpr.eval, BasicLiteral.denote]) hi' hb1
        · exact holds_int_le_shape_of (a := .ident x) (b := shapeInt (es.length : Int))
            hi' (by simp [shapeInt, BasicExpr.eval, BasicLiteral.denote]) hb2
    | lit l =>
        cases l with
        | int kk =>
            have hkk : kk = ii := by
              have h := hi'
              simp only [BasicExpr.eval, BasicLiteral.denote] at h
              exact Value.int.inj (Option.some.inj h)
            have hcond : 1 ≤ kk ∧ kk ≤ (es.length : Int) := by
              rw [hkk]; exact ⟨hb1, hb2⟩
            intro c hc
            simp only [shapeRangeChecks] at hc
            rw [if_pos hcond] at hc
            simp at hc
        | bool bb =>
            simp only [BasicExpr.eval, BasicLiteral.denote] at hi'
            exact absurd hi' (by simp)
        | set sl =>
            simp only [BasicExpr.eval, BasicLiteral.denote] at hi'
            exact absurd hi' (by simp)
  have hnewDefs : st.NewHolds st' s' :=
    arrayElemRows_newHolds vals st rows st' s' hrows hdefs
  have hnewRows : st'.NewHolds (st'.emitList (arrayElemRowList i rows)) s' :=
    ShapeState.newHolds_emitList hrowsAll
  have hnewRanges : (st'.emitList (arrayElemRowList i rows)).NewHolds
      ((st'.emitList (arrayElemRowList i rows)).emitList
        (shapeRangeChecks i es.length)) s' :=
    ShapeState.newHolds_emitList hranges
  have hchain := ShapeState.newHolds_trans hnewDefs
    (ShapeState.newHolds_trans hnewRows hnewRanges)
  simpa [ShapeState.emitList, List.reverse_append] using hchain

/-! ## Per-constraint correctness of the shape rewrite -/

/-- **Soundness of the per-constraint rewrite**: the emitted rows, at the
    rewritten state's store, force the source constraint. -/
theorem shapeRewriteConstraint_sound {taken : List String} {m : Model}
    {st : ShapeState} {c : ConstraintItem} {st' : ShapeState}
    {cs' : List ConstraintItem} {str : Store}
    (h : shapeRewriteConstraint taken m st c = some (st', cs'))
    (hdefs : st'.DefHolds str)
    (hholds : (st'.emitList cs').Holds str)
    (hint : ShapeIntDomains m str) (hset : ShapeSetDomains m str) :
    c.Holds fullInterp str := by
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
        exact hholds _ (by simp [ShapeState.emitList])
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            obtain ⟨sv, hsv⟩ := hset.1 S.name us hus
            exact rewriteVarMember_sound h hdefs hholds
              (hint x.name vals hvals).1
              (hint x.name vals hvals).2
              ⟨sv, hsv⟩ hus
              (fun sv' hsv' w hw hc => hset.not_contains hus hsv' w hw hc)
          case h_2 => simp at h
        case h_2 =>
          rename_i i
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hholds _ (by simp [ShapeState.emitList])
        case h_3 => simp at h
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hholds _ (by simp [ShapeState.emitList])
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
        exact hholds _ (by simp [ShapeState.emitList])
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            obtain ⟨sv, hsv⟩ := hset.1 S.name us hus
            exact setIn_of_setIn_true (rewriteVarMember_sound
              (r := shapeBool true) h hdefs hholds
              (hint x.name vals hvals).1
              (hint x.name vals hvals).2
              ⟨sv, hsv⟩ hus
              (fun sv' hsv' w hw hc => hset.not_contains hus hsv' w hw hc))
          case h_2 => simp at h
        case h_2 =>
          rename_i i
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hholds _ (by simp [ShapeState.emitList])
        case h_3 => simp at h
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hholds _ (by simp [ShapeState.emitList])
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
        exact hholds _ (by simp [ShapeState.emitList])
      case h_2 =>
        rename_i us hus
        obtain ⟨sv, hsv⟩ := hset.1 S.name us hus
        exact rewriteCard_sound h hdefs hholds ⟨sv, hsv⟩ hus
          (fun sv' hsv' w hw hc => hset.not_contains hus hsv' w hw hc)
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hholds _ (by simp [ShapeState.emitList])
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
      exact rewriteUnion_sound h hdefs hholds hA hB hC
        (setArgValues?_eval hA hset) (setArgValues?_eval hB hset)
        (setArgValues?_eval hC hset)
        (fun S us hus sv hsv w hc => hset.2 S us hus sv hsv w hc)
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hholds _ (by simp [ShapeState.emitList])
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
          exact hholds _ (by simp [ShapeState.emitList])
        case h_2 =>
          rename_i vals hvals
          exact rewriteArrayElem_sound h hdefs hholds hint hset
      case h_2 =>
        rename_i x
        split at h
        case h_1 =>
          rename_i vals hvals
          split at h
          case h_1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hholds _ (by simp [ShapeState.emitList])
          case h_2 =>
            rename_i us hus
            exact rewriteArrayElem_sound h hdefs hholds hint hset
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hholds _ (by simp [ShapeState.emitList])
      case h_3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hholds _ (by simp [ShapeState.emitList])
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hholds _ (by simp [ShapeState.emitList])
  case h_6 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_intersect" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteIntersect_sound h hdefs hholds hA hB hC
        (setArgValues?_eval hA hset) (setArgValues?_eval hB hset)
        (setArgValues?_eval hC hset)
        (fun S us hus sv hsv w hc => hset.2 S us hus sv hsv w hc)
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hholds _ (by simp [ShapeState.emitList])
  case h_7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hholds _ (by simp [ShapeState.emitList])

/-- Keeping one constraint while emitting it is a valid `NewHolds` step,
    provided the constraint holds in the current store. -/
theorem ShapeState.newHolds_emitList_singleton {st : ShapeState}
    {c : ConstraintItem} {s : Store} (h : c.Holds fullInterp s) :
    st.NewHolds (st.emitList [c]) s := by
  intro c' hc'
  rcases List.mem_cons.mp (by simpa [ShapeState.emitList] using hc') with rfl | hc''
  · exact Or.inr h
  · exact Or.inl hc''

/-- **Completeness of the per-constraint rewrite**: when the source
    constraint holds, every emitted row holds in the functionally extended
    store. -/
theorem shapeRewriteConstraint_newHolds {taken : List String} {m : Model}
    {st : ShapeState} {c : ConstraintItem} {st' : ShapeState}
    {cs' : List ConstraintItem} {s s' : Store}
    (h : shapeRewriteConstraint taken m st c = some (st', cs'))
    (hdefs : st'.DefHolds s')
    (hsrc : c.Holds fullInterp s)
    (hint : ShapeIntDomains m s) (hset : ShapeSetDomains m s)
    (hset' : ShapeSetDomains m s')
    (hagree : ∀ x ∈ constraintNames c, s' (Ident.mk x) = s (Ident.mk x)) :
    st.NewHolds (st'.emitList cs') s' := by
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
        exact ShapeState.newHolds_emitList_singleton
          ((holds_of_names_agree (s := s') (t := s)
          (pred := fullInterp)
          (c := ConstraintItem.mk (Ident.mk "set_in_reif")
            [.basic xarg, .basic (.ident S), .basic rarg] anns)
          (fun x hx => hagree x (by
            simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            obtain ⟨sv, hsv⟩ := hset.1 S.name us hus
            exact rewriteVarMember_newHolds h hdefs hsrc
              (hint x.name vals hvals).1 ⟨sv, hsv⟩
              (hagree x.name (by simp [constraintNames, exprNames, basicNames]))
              (hagree S.name (by simp [constraintNames, exprNames, basicNames]))
              (basicNames_eval_agree (s := s') (t := s) (b := rarg) (by
                intro y hy
                exact hagree y (List.mem_flatMap.mpr
                  ⟨Expr.basic rarg, by simp, by simpa [exprNames] using hy⟩)))
              (hint x.name vals hvals).2 hus
              (fun sv' hsv' w hw hc => hset.not_contains hus hsv' w hw hc)
          case h_2 => simp at h
        case h_2 =>
          rename_i i
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.newHolds_emitList_singleton
            ((holds_of_names_agree (s := s') (t := s)
            (pred := fullInterp)
            (c := ConstraintItem.mk (Ident.mk "set_in_reif")
              [.basic (.lit (.int i)), .basic (.ident S), .basic rarg]
              anns)
            (fun x hx => hagree x (by
              simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
        case h_3 => simp at h
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newHolds_emitList_singleton
        ((holds_of_names_agree (s := s') (t := s)
        (pred := fullInterp)
        (c := ConstraintItem.mk (Ident.mk "set_in_reif")
          [.basic xarg, .basic (.lit (.set sl)), .basic rarg] anns)
        (fun x hx => hagree x (by
          simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
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
        exact ShapeState.newHolds_emitList_singleton
          ((holds_of_names_agree (s := s') (t := s)
          (pred := fullInterp)
          (c := ConstraintItem.mk (Ident.mk "set_in")
            [.basic xarg, .basic (.ident S)] anns)
          (fun x hx => hagree x (by
            simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            obtain ⟨sv, hsv⟩ := hset.1 S.name us hus
            exact rewriteVarMember_newHolds (r := shapeBool true)
              h hdefs (setIn_true_of_setIn hsrc)
              (hint x.name vals hvals).1 ⟨sv, hsv⟩
              (hagree x.name (by simp [constraintNames, exprNames, basicNames]))
              (hagree S.name (by simp [constraintNames, exprNames, basicNames]))
              rfl
              (hint x.name vals hvals).2 hus
              (fun sv' hsv' w hw hc => hset.not_contains hus hsv' w hw hc)
          case h_2 => simp at h
        case h_2 =>
          rename_i i
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.newHolds_emitList_singleton
            ((holds_of_names_agree (s := s') (t := s)
            (pred := fullInterp)
            (c := ConstraintItem.mk (Ident.mk "set_in")
              [.basic (.lit (.int i)), .basic (.ident S)] anns)
            (fun x hx => hagree x (by
              simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
        case h_3 => simp at h
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newHolds_emitList_singleton
        ((holds_of_names_agree (s := s') (t := s)
        (pred := fullInterp)
        (c := ConstraintItem.mk (Ident.mk "set_in")
          [.basic xarg, .basic (.lit (.set sl))] anns)
        (fun x hx => hagree x (by
          simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
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
        exact ShapeState.newHolds_emitList_singleton
          ((holds_of_names_agree (s := s') (t := s)
          (pred := fullInterp)
          (c := ConstraintItem.mk (Ident.mk "set_card")
            [.basic (.ident S), .basic karg] anns)
          (fun x hx => hagree x (by
            simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
      case h_2 =>
        rename_i us hus
        obtain ⟨sv, hsv⟩ := hset.1 S.name us hus
        exact rewriteCard_newHolds h hdefs hsrc ⟨sv, hsv⟩
          (hagree S.name (by simp [constraintNames, exprNames, basicNames]))
          (basicNames_eval_agree (s := s') (t := s) (b := karg) (by
            intro y hy
            exact hagree y (List.mem_flatMap.mpr
              ⟨Expr.basic karg, by simp, by simpa [exprNames] using hy⟩)))
          hus
          (fun sv' hsv' w hw hc => hset.not_contains hus hsv' w hw hc)
    case h_2 =>
      rename_i sl
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newHolds_emitList_singleton
        ((holds_of_names_agree (s := s') (t := s)
        (pred := fullInterp)
        (c := ConstraintItem.mk (Ident.mk "set_card")
          [.basic (.lit (.set sl)), .basic karg] anns)
        (fun x hx => hagree x (by
          simpa [constraintNames, exprNames, basicNames] using hx))).mpr hsrc)
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
      exact rewriteUnion_newHolds h hdefs hsrc
        (setArgValues?_eval hA hset) (setArgValues?_eval hB hset)
        (setArgValues?_eval hC hset)
        (exprNames_eval_agree (s := s') (t := s) (e := sa) (by
          intro x hx
          exact hagree x (by
            simp only [constraintNames, List.mem_flatMap] at ⊢
            exact ⟨sa, by simp, hx⟩)))
        (exprNames_eval_agree (s := s') (t := s) (e := sb) (by
          intro x hx
          exact hagree x (by
            simp only [constraintNames, List.mem_flatMap] at ⊢
            exact ⟨sb, by simp, hx⟩)))
        (exprNames_eval_agree (s := s') (t := s) (e := sc) (by
          intro x hx
          exact hagree x (by
            simp only [constraintNames, List.mem_flatMap] at ⊢
            exact ⟨sc, by simp, hx⟩)))
        (fun S us hus sv hsv w hc => hset'.2 S us hus sv hsv w hc)
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newHolds_emitList_singleton
        ((holds_of_names_agree (s := s') (t := s)
        (pred := fullInterp)
        (c := ConstraintItem.mk (Ident.mk "set_union") [sa, sb, sc] anns)
        (fun x hx => hagree x (by simpa [constraintNames] using hx))).mpr hsrc)
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
          exact ShapeState.newHolds_emitList_singleton
            ((holds_of_names_agree (s := s') (t := s) (pred := fullInterp)
              (c := _) (fun y hy => hagree y hy)).mpr hsrc)
        case h_2 =>
          rename_i vals hvals
          exact rewriteArrayElem_newHolds h hdefs hsrc hint hset hset'
            (fun x hx => by simp [basicNames] at hx)
            (fun e he x hx =>
              hagree x (mem_constraintNames_arrayElem (i := .lit (.int i)) he hx))
            (hagree T.name (mem_constraintNames_arrayElem_target (T := T.name)))
      case h_2 =>
        rename_i x
        split at h
        case h_1 =>
          rename_i vals hvals
          split at h
          case h_1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact ShapeState.newHolds_emitList_singleton
              ((holds_of_names_agree (s := s') (t := s) (pred := fullInterp)
                (c := _) (fun y hy => hagree y hy)).mpr hsrc)
          case h_2 =>
            rename_i us hus
            exact rewriteArrayElem_newHolds h hdefs hsrc hint hset hset'
              (fun y hy => by
                simp only [basicNames, List.mem_singleton] at hy
                rw [hy]
                exact hagree x.name
                  (mem_constraintNames_arrayElem_index (i := .ident x) (by simp [basicNames])))
              (fun e he y hy =>
                hagree y (mem_constraintNames_arrayElem (i := .ident x) he hy))
              (hagree T.name (mem_constraintNames_arrayElem_target (T := T.name)))
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact ShapeState.newHolds_emitList_singleton
            ((holds_of_names_agree (s := s') (t := s) (pred := fullInterp)
              (c := _) (fun y hy => hagree y hy)).mpr hsrc)
      case h_3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact ShapeState.newHolds_emitList_singleton
          ((holds_of_names_agree (s := s') (t := s) (pred := fullInterp)
            (c := _) (fun y hy => hagree y hy)).mpr hsrc)
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newHolds_emitList_singleton
        ((holds_of_names_agree (s := s') (t := s) (pred := fullInterp)
          (c := _) (fun y hy => hagree y hy)).mpr hsrc)
  case h_6 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_intersect" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteIntersect_newHolds h hdefs hsrc
        (setArgValues?_eval hA hset) (setArgValues?_eval hB hset)
        (setArgValues?_eval hC hset)
        (exprNames_eval_agree (s := s') (t := s) (e := sa) (by
          intro x hx
          exact hagree x (by
            simp only [constraintNames, List.mem_flatMap] at ⊢
            exact ⟨sa, by simp, hx⟩)))
        (exprNames_eval_agree (s := s') (t := s) (e := sb) (by
          intro x hx
          exact hagree x (by
            simp only [constraintNames, List.mem_flatMap] at ⊢
            exact ⟨sb, by simp, hx⟩)))
        (exprNames_eval_agree (s := s') (t := s) (e := sc) (by
          intro x hx
          exact hagree x (by
            simp only [constraintNames, List.mem_flatMap] at ⊢
            exact ⟨sc, by simp, hx⟩)))
        (fun S us hus sv hsv w hc => hset'.2 S us hus sv hsv w hc)
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ShapeState.newHolds_emitList_singleton
        ((holds_of_names_agree (s := s') (t := s)
        (pred := fullInterp)
        (c := ConstraintItem.mk (Ident.mk "set_intersect") [sa, sb, sc] anns)
        (fun x hx => hagree x (by simpa [constraintNames] using hx))).mpr hsrc)
  case h_7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ShapeState.newHolds_emitList_singleton
      ((holds_of_names_agree (s := s') (t := s) (pred := fullInterp)
      (c := ConstraintItem.mk nm args anns) (fun x hx => hagree x hx)).mpr hsrc)

/-! ## Preservation of the traversal invariants -/

/-- `resultTarget` keeps every old constraint. -/
theorem resultTarget_cons_subset {taken : List String} {st : ShapeState}
    {r : BasicExpr} {n : String} {st' : ShapeState}
    (h : resultTarget taken st r = some (n, st')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  cases r with
  | ident b =>
      simp only [resultTarget, Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c hc => hc
  | lit l =>
      cases l with
      | bool bb =>
          cases bb
          · simp only [resultTarget] at h
            cases hb : st.freshBool taken (.const false) with
            | mk n' st1 =>
                simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ShapeState.freshBool_cons_subset hb
          · simp only [resultTarget] at h
            cases hb : st.freshBool taken (.const true) with
            | mk n' st1 =>
                simp only [hb, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact ShapeState.freshBool_cons_subset hb
      | int i => simp [resultTarget] at h
      | set sl => simp [resultTarget] at h

/-- `rewriteVarMember` keeps every old auxiliary. -/
theorem rewriteVarMember_aux_subset {taken : List String} {m : Model} {st : ShapeState}
    {x s : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteVarMember taken m st x s vals r = some (st', cs')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  obtain ⟨tms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  intro a ha
  rw [linkOr_aux]
  exact resultTarget_aux_subset hres a (varMemberTerms_aux_subset hterms a ha)

/-- `rewriteVarMember` keeps every old constraint. -/
theorem rewriteVarMember_cons_subset {taken : List String} {m : Model} {st : ShapeState}
    {x s : String} {vals : List Int} {r : BasicExpr} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteVarMember taken m st x s vals r = some (st', cs')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  obtain ⟨tms, st1, target, st2, hterms, hres, rfl, rfl⟩ :=
    rewriteVarMember_decomp h
  have h1 : ∀ c ∈ st.cons, c ∈ st2.cons := fun c hc =>
    resultTarget_cons_subset hres c (varMemberTerms_cons_subset hterms c hc)
  cases tms with
  | nil =>
      intro c hc
      exact ShapeState.emit_cons_subset c (h1 c hc)
  | cons t ts =>
      intro c hc
      exact ShapeState.emitList_cons_subset c (h1 c hc)

/-- `rewriteCard` keeps every old auxiliary. -/
theorem rewriteCard_aux_subset {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {k : BasicExpr} {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteCard taken m st S k = some (st', cs')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
  unfold rewriteCard at h
  cases hm : modelSetUniverse? m S with
  | none =>
      simp only [hm, Option.getD_none, List.isEmpty_nil, ite_true] at h
      cases k with
      | ident kn =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun a ha => ha
      | lit l =>
          cases l with
          | int j =>
              by_cases hj : j = 0
              · simp only [hj, ite_true] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact fun a ha => ha
              · simp only [if_neg hj] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact fun a ha => ha
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
              exact fun a ha => ha
          | lit l =>
              cases l with
              | int j =>
                  by_cases hj : j = 0
                  · simp only [hj, ite_true] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact fun a ha => ha
                  · simp only [if_neg hj] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact fun a ha => ha
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
                  exact fun a ha => cardBits_aux_subset hb a ha
              | lit l =>
                  cases l with
                  | int j =>
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact fun a ha => cardBits_aux_subset hb a ha
                  | bool b => simp at h
                  | set sl => simp at h

/-- `rewriteCard` keeps every old constraint. -/
theorem rewriteCard_cons_subset {taken : List String} {m : Model} {st : ShapeState}
    {S : String} {k : BasicExpr} {st' : ShapeState} {cs' : List ConstraintItem}
    (h : rewriteCard taken m st S k = some (st', cs')) :
    ∀ c ∈ st.cons, c ∈ st'.cons := by
  unfold rewriteCard at h
  cases hm : modelSetUniverse? m S with
  | none =>
      simp only [hm, Option.getD_none, List.isEmpty_nil, ite_true] at h
      cases k with
      | ident kn =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun c hc => ShapeState.emit_cons_subset c hc
      | lit l =>
          cases l with
          | int j =>
              by_cases hj : j = 0
              · simp only [hj, ite_true] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact fun c hc => hc
              · simp only [if_neg hj] at h
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, rfl⟩ := h
                exact fun c hc => ShapeState.emit_cons_subset c hc
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
              exact fun c hc => ShapeState.emit_cons_subset c hc
          | lit l =>
              cases l with
              | int j =>
                  by_cases hj : j = 0
                  · simp only [hj, ite_true] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact fun c hc => hc
                  · simp only [if_neg hj] at h
                    simp only [Option.some.injEq, Prod.mk.injEq] at h
                    obtain ⟨rfl, rfl⟩ := h
                    exact fun c hc => ShapeState.emit_cons_subset c hc
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
                  exact fun c hc => ShapeState.emit_cons_subset c (cardBits_cons_subset hb c hc)
              | lit l =>
                  cases l with
                  | int j =>
                      simp only [Option.some.injEq, Prod.mk.injEq] at h
                      obtain ⟨rfl, rfl⟩ := h
                      exact fun c hc => ShapeState.emit_cons_subset c (cardBits_cons_subset hb c hc)
                  | bool b => simp at h
                  | set sl => simp at h

/-- `rewriteUnion` keeps every old auxiliary. -/
theorem rewriteUnion_aux_subset {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs')) :
    ∀ x ∈ st.aux, x ∈ st'.aux := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteUnion_decomp h
  exact unionRows_aux_subset hr

/-- `rewriteUnion` keeps every old constraint. -/
theorem rewriteUnion_cons_subset {taken : List String} {m : Model} {st : ShapeState}
    {a b c : Expr} {ua ub uc : List Int} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : rewriteUnion taken m st a b c ua ub uc = some (st', cs')) :
    ∀ x ∈ st.cons, x ∈ st'.cons := by
  obtain ⟨st1, hr, rfl, rfl⟩ := rewriteUnion_decomp h
  exact unionRows_cons_subset hr

/-- **The per-constraint rewrite preserves well-formedness.** -/
theorem shapeRewriteConstraint_wf {taken : List String} {m : Model}
    {st : ShapeState} {c : ConstraintItem} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (hwf : st.WF taken m) (hmwf : WellFormed fullSig m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : shapeRewriteConstraint taken m st c = some (st', cs')) :
    st'.WF taken m := by
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
        exact hwf
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_wf hwf
              (modelIntValues?_name_taken hmwf hsup hvals)
              (modelSetUniverse?_name_taken hmwf hsup hus)
              ⟨vals, hvals⟩ hus h
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hwf
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
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
        exact hwf
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_wf hwf
              (modelIntValues?_name_taken hmwf hsup hvals)
              (modelSetUniverse?_name_taken hmwf hsup hus)
              ⟨vals, hvals⟩ hus h
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hwf
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
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
        exact hwf
      case h_2 =>
        rename_i us hus
        exact rewriteCard_wf hwf (modelSetUniverse?_name_taken hmwf hsup hus) hus h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
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
      exact rewriteUnion_wf hwf (setArgValues?_ident_taken hsup hA)
        (setArgValues?_ident_taken hsup hB)
        (setArgValues?_ident_taken hsup hC) h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
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
          exact hwf
        case h_2 =>
          rename_i vals hvals
          exact rewriteArrayElem_wf hwf hmwf hsup h
      case h_2 =>
        rename_i x
        split at h
        case h_1 =>
          rename_i vals hvals
          split at h
          case h_1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact hwf
          case h_2 =>
            rename_i us hus
            exact rewriteArrayElem_wf hwf hmwf hsup h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact hwf
      case h_3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact hwf
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
  case h_6 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_intersect" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteIntersect_wf hwf (setArgValues?_ident_taken hsup hA)
        (setArgValues?_ident_taken hsup hB)
        (setArgValues?_ident_taken hsup hC) h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact hwf
  case h_7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact hwf

/-- **The per-constraint rewrite keeps every old auxiliary.** -/
theorem shapeRewriteConstraint_aux_subset {taken : List String} {m : Model}
    {st : ShapeState} {c : ConstraintItem} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : shapeRewriteConstraint taken m st c = some (st', cs')) :
    ∀ a ∈ st.aux, a ∈ st'.aux := by
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
        exact fun a ha => ha
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_aux_subset h
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun a ha => ha
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
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
        exact fun a ha => ha
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_aux_subset h
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun a ha => ha
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
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
        exact fun a ha => ha
      case h_2 =>
        rename_i us hus
        exact rewriteCard_aux_subset h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
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
      exact rewriteUnion_aux_subset h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
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
          exact fun a ha => ha
        case h_2 =>
          rename_i vals hvals
          exact rewriteArrayElem_aux_subset h
      case h_2 =>
        rename_i x
        split at h
        case h_1 =>
          rename_i vals hvals
          split at h
          case h_1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact fun a ha => ha
          case h_2 =>
            rename_i us hus
            exact rewriteArrayElem_aux_subset h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun a ha => ha
      case h_3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact fun a ha => ha
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
  case h_6 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_intersect" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteIntersect_aux_subset h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun a ha => ha
  case h_7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun a ha => ha

/-- **The per-constraint rewrite keeps every old constraint.** -/
theorem shapeRewriteConstraint_cons_subset {taken : List String} {m : Model}
    {st : ShapeState} {c : ConstraintItem} {st' : ShapeState}
    {cs' : List ConstraintItem}
    (h : shapeRewriteConstraint taken m st c = some (st', cs')) :
    ∀ c' ∈ st.cons, c' ∈ st'.cons := by
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
        exact fun c' hc' => hc'
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_cons_subset h
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun c' hc' => hc'
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c' hc' => hc'
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
        exact fun c' hc' => hc'
      case h_2 =>
        rename_i us hus
        split at h
        case h_1 =>
          rename_i x
          split at h
          case h_1 =>
            rename_i vals hvals
            exact rewriteVarMember_cons_subset h
          case h_2 => simp at h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun c' hc' => hc'
        case h_3 => simp at h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c' hc' => hc'
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
        exact fun c' hc' => hc'
      case h_2 =>
        rename_i us hus
        exact rewriteCard_cons_subset h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c' hc' => hc'
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
      exact rewriteUnion_cons_subset h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c' hc' => hc'
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
          exact fun c' hc' => hc'
        case h_2 =>
          rename_i vals hvals
          exact rewriteArrayElem_cons_subset h
      case h_2 =>
        rename_i x
        split at h
        case h_1 =>
          rename_i vals hvals
          split at h
          case h_1 =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            exact fun c' hc' => hc'
          case h_2 =>
            rename_i us hus
            exact rewriteArrayElem_cons_subset h
        case h_2 =>
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact fun c' hc' => hc'
      case h_3 =>
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        exact fun c' hc' => hc'
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c' hc' => hc'
  case h_6 =>
    rename_i sa sb sc hnm hargs
    have hnm' : nm = Ident.mk "set_intersect" := ident_eq_of_name hnm
    have hargs' : args = [sa, sb, sc] := hargs
    subst nm
    subst args
    split at h
    case h_1 =>
      rename_i ua ub uc hA hB hC
      exact rewriteIntersect_cons_subset h
    case h_2 =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact fun c' hc' => hc'
  case h_7 =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact fun c' hc' => hc'

/-! ## Traversal invariants and correctness -/

/-- The initial shape state. -/
def ShapeState.initial (taken : List String) : ShapeState :=
  { next := 0, aux := [], decls := [], cons := [], maxLen := maxStrLength taken }

/-- The initial shape state is well-formed. -/
theorem ShapeState.initial_wf (taken : List String) (m : Model) :
    (ShapeState.initial taken).WF taken m := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha; simp [ShapeState.initial] at ha
  · rfl
  · exact ⟨[], by simp, by simp, by simp [ShapeState.initial]⟩
  · rfl
  · simp [ShapeState.initial, ShapeAux.depsOk]
  · simp [ShapeState.initial, ShapeAux.KindDeps]
  · intro a ha; simp [ShapeState.initial] at ha
  · intro a ha; simp [ShapeState.initial] at ha

/-- **The shape traversal preserves well-formedness.** -/
theorem shapeExpandConstraints_wf {taken : List String} {m : Model}
    {cs : List ConstraintItem} {st stF : ShapeState}
    (hwf : st.WF taken m) (hmwf : WellFormed fullSig m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : shapeExpandConstraints taken m cs st = some stF) :
    stF.WF taken m := by
  induction cs generalizing st with
  | nil =>
      simp only [shapeExpandConstraints, Option.some.injEq] at h
      subst h
      exact hwf
  | cons c cs ih =>
      simp only [shapeExpandConstraints] at h
      cases hr : shapeRewriteConstraint taken m st c with
      | none => simp [hr] at h
      | some p =>
          obtain ⟨st1, cs'⟩ := p
          simp only [hr, Option.bind_some] at h
          exact ih (ShapeState.emitList_wf (shapeRewriteConstraint_wf hwf hmwf hsup hr)) h

/-- **The shape traversal keeps every old auxiliary.** -/
theorem shapeExpandConstraints_aux_subset {taken : List String} {m : Model}
    {cs : List ConstraintItem} {st stF : ShapeState}
    (h : shapeExpandConstraints taken m cs st = some stF) :
    ∀ a ∈ st.aux, a ∈ stF.aux := by
  induction cs generalizing st with
  | nil =>
      simp only [shapeExpandConstraints, Option.some.injEq] at h
      subst h
      exact fun a ha => ha
  | cons c cs ih =>
      simp only [shapeExpandConstraints] at h
      cases hr : shapeRewriteConstraint taken m st c with
      | none => simp [hr] at h
      | some p =>
          obtain ⟨st1, cs'⟩ := p
          simp only [hr, Option.bind_some] at h
          intro a ha
          exact ih h a (shapeRewriteConstraint_aux_subset hr a ha)

/-- **The shape traversal keeps every old constraint.** -/
theorem shapeExpandConstraints_cons_subset {taken : List String} {m : Model}
    {cs : List ConstraintItem} {st stF : ShapeState}
    (h : shapeExpandConstraints taken m cs st = some stF) :
    ∀ c ∈ st.cons, c ∈ stF.cons := by
  induction cs generalizing st with
  | nil =>
      simp only [shapeExpandConstraints, Option.some.injEq] at h
      subst h
      exact fun c hc => hc
  | cons c cs ih =>
      simp only [shapeExpandConstraints] at h
      cases hr : shapeRewriteConstraint taken m st c with
      | none => simp [hr] at h
      | some p =>
          obtain ⟨st1, cs'⟩ := p
          simp only [hr, Option.bind_some] at h
          intro c' hc'
          exact ih h c' (ShapeState.emitList_cons_subset c'
            (shapeRewriteConstraint_cons_subset hr c' hc'))

/-- **Soundness of the traversal**: satisfaction of the final emitted rows
    forces every source constraint. -/
theorem shapeExpandConstraints_sound {taken : List String} {m : Model}
    {cs : List ConstraintItem} {st stF : ShapeState} {s : Store}
    (h : shapeExpandConstraints taken m cs st = some stF)
    (hdefs : stF.DefHolds s) (hholds : stF.Holds s)
    (hint : ShapeIntDomains m s) (hset : ShapeSetDomains m s) :
    ∀ c ∈ cs, c.Holds fullInterp s := by
  induction cs generalizing st with
  | nil => intro c hc; simp at hc
  | cons c cs ih =>
      simp only [shapeExpandConstraints] at h
      cases hr : shapeRewriteConstraint taken m st c with
      | none => simp [hr] at h
      | some p =>
          obtain ⟨st1, cs'⟩ := p
          simp only [hr, Option.bind_some] at h
          have haux : ∀ a ∈ st1.aux, a ∈ stF.aux :=
            shapeExpandConstraints_aux_subset (st := st1.emitList cs') h
          have hcons' : ∀ c' ∈ (st1.emitList cs').cons, c' ∈ stF.cons :=
            shapeExpandConstraints_cons_subset (st := st1.emitList cs') h
          have hcons : ∀ c' ∈ st1.cons, c' ∈ stF.cons := fun c' hc' =>
            hcons' c' (ShapeState.emitList_cons_subset c' hc')
          have hdefs1 : st1.DefHolds s := ShapeState.DefHolds.mono haux hdefs
          have hholds1 : (st1.emitList cs').Holds s :=
            ShapeState.holds_mono hcons' hholds
          intro c' hc'
          rcases List.mem_cons.mp hc' with rfl | hc'in
          · exact shapeRewriteConstraint_sound hr hdefs1 hholds1 hint hset
          · exact ih (st := st1.emitList cs') h c' hc'in

/-- **Completeness of the traversal**: every source constraint yields a
    `NewHolds` chain from the initial state to the final state. -/
theorem shapeExpandConstraints_newHolds {taken : List String} {m : Model}
    {cs : List ConstraintItem} {st stF : ShapeState} {s s' : Store}
    (h : shapeExpandConstraints taken m cs st = some stF)
    (hdefs : stF.DefHolds s')
    (hsrc : ∀ c ∈ cs, c.Holds fullInterp s)
    (hint : ShapeIntDomains m s) (hset : ShapeSetDomains m s)
    (hset' : ShapeSetDomains m s')
    (hagree : ∀ x ∈ taken, s' (Ident.mk x) = s (Ident.mk x))
    (hnames : ∀ c ∈ cs, ∀ x ∈ constraintNames c, x ∈ taken) :
    st.NewHolds stF s' := by
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
          simp only [hr, Option.bind_some] at h
          have hsub : ∀ a ∈ st1.aux, a ∈ stF.aux :=
            shapeExpandConstraints_aux_subset (st := st1.emitList cs') h
          have hdefs1 : st1.DefHolds s' := ShapeState.DefHolds.mono hsub hdefs
          exact ShapeState.newHolds_trans
            (shapeRewriteConstraint_newHolds hr hdefs1 (hsrc c (by simp)) hint hset
              hset' (fun x hx => hagree x (hnames c (by simp) x hx)))
            (ih (st := st1.emitList cs') h
              (fun c' hc' => hsrc c' (List.mem_cons_of_mem _ hc'))
              (fun c' hc' => hnames c' (List.mem_cons_of_mem _ hc')))

/-! ## Domains from dynamic satisfaction

A `SatisfiesDyn` witness already contains the variable-domain component
needed by the traversal's soundness and completeness lemmas. -/

/-- The variable-domain component of `SatisfiesDyn`. -/
def ShapeVarDomains (m : Model) (s : Store) : Prop :=
  ∀ d ∈ m.variables, match d with
    | .basic ty n _ _ => ∃ v, s n = some v ∧ ty.contains v
    | .array ty n _ _ => ∃ vs, s n = some (.array vs) ∧
        vs.length = ty.idx.length ∧ ∀ v ∈ vs, ty.elem.contains v

/-- A satisfing store has the traversal's integer-domain fact. -/
theorem ShapeIntDomains.of_varDomains {m : Model} {s : Store}
    (hnd : (m.variables.map (fun d => d.name.name)).Nodup)
    (hdom : ShapeVarDomains m s) : ShapeIntDomains m s := by
  intro x vals hvals
  obtain ⟨ty, anns, init, hd, hfin⟩ := modelIntValues?_some hvals
  obtain ⟨v, hv, hcont⟩ := hdom (.basic ty (Ident.mk x) anns init) hd
  obtain ⟨i, rfl⟩ := contains_of_finiteIntValues hfin hcont
  refine ⟨⟨i, hv⟩, ?_⟩
  intro j hj
  have hji : j = i := Value.int.inj (Option.some.inj (hj.symm.trans hv))
  subst hji
  exact modelIntValues?_mem_of_contains hnd hd hvals hcont

/-- A satisfying store has the traversal's set-domain fact. -/
theorem ShapeSetDomains.of_varDomains {m : Model} {s : Store}
    (hnd : (m.variables.map (fun d => d.name.name)).Nodup)
    (hdom : ShapeVarDomains m s) : ShapeSetDomains m s := by
  refine ⟨?_, ?_⟩
  · intro S us hus
    obtain ⟨ty, anns, init, hd, hset⟩ := modelSetUniverse?_some hus
    obtain ⟨v, hv, hcont⟩ := hdom (.basic ty (Ident.mk S) anns init) hd
    obtain ⟨sv, rfl⟩ := contains_of_setUniverse hset hcont
    exact ⟨sv, hv⟩
  · intro S us hus sv hsv w hcw
    obtain ⟨ty, anns, init, hd, hset⟩ := modelSetUniverse?_some hus
    obtain ⟨v, hv, hcont⟩ := hdom (.basic ty (Ident.mk S) anns init) hd
    have hveq : v = .setOfInt sv :=
      Option.some.inj (hv.symm.trans hsv)
    subst hveq
    exact modelSetUniverse?_mem_of_contains hnd hd hus hcont hcw

/-- The traversal's integer-domain fact is inherited by the interpreted
    store. -/
theorem ShapeIntDomains.encStore {taken : List String} {m : Model}
    {st : ShapeState} {s : Store}
    (hwf : st.WF taken m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : ShapeIntDomains m s) : ShapeIntDomains m (st.encStore s) := by
  intro x vals hvals
  obtain ⟨ty, anns, init, hd, hfin⟩ := modelIntValues?_some hvals
  have hxmem : x ∈ m.variables.map (fun d => d.name.name) :=
    List.mem_map.mpr ⟨_, hd, rfl⟩
  have hxt : x ∈ taken := hsup x (List.mem_append_right _ hxmem)
  have heq : st.encStore s (Ident.mk x) = s (Ident.mk x) :=
    ShapeState.encStore_at_taken hwf hxt
  obtain ⟨hint, hmem⟩ := h x vals hvals
  refine ⟨?_, ?_⟩
  · rw [heq]; exact hint
  · intro i hi
    rw [heq] at hi
    exact hmem i hi

/-- The traversal's set-domain fact is inherited by the interpreted
    store. -/
theorem ShapeSetDomains.encStore {taken : List String} {m : Model}
    {st : ShapeState} {s : Store}
    (hwf : st.WF taken m) (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : ShapeSetDomains m s) : ShapeSetDomains m (st.encStore s) := by
  constructor
  · intro S us hus
    obtain ⟨ty, anns, init, hd, hun⟩ := modelSetUniverse?_some hus
    obtain ⟨sv, hsv⟩ := h.1 S us hus
    have hxmem : S ∈ m.variables.map (fun d => d.name.name) :=
      List.mem_map.mpr ⟨_, hd, rfl⟩
    have hxt : S ∈ taken := hsup S (List.mem_append_right _ hxmem)
    refine ⟨sv, ?_⟩
    rw [ShapeState.encStore_at_taken hwf hxt]
    exact hsv
  · intro S us hus sv hsv w hcw
    obtain ⟨ty, anns, init, hd, hun⟩ := modelSetUniverse?_some hus
    have hxmem : S ∈ m.variables.map (fun d => d.name.name) :=
      List.mem_map.mpr ⟨_, hd, rfl⟩
    have hxt : S ∈ taken := hsup S (List.mem_append_right _ hxmem)
    have heq : st.encStore s (Ident.mk S) = s (Ident.mk S) :=
      ShapeState.encStore_at_taken hwf hxt
    rw [heq] at hsv
    exact h.2 S us hus sv hsv w hcw

/-! ## Initializers under the interpreted store -/

/-- An initializer whose names are not auxiliary names has the same
    `initializerHolds` value in the interpreted store. -/
theorem initializerHolds_encodeAux_iff {s : Store} {as : List ShapeAux}
    {d : VarDeclItem}
    (hn : d.name.name ∉ as.map (fun a => a.name))
    (h : ∀ x ∈ varDeclNames d, x ∉ as.map (fun a => a.name)) :
    d.initializerHolds (encodeAuxStore s as) ↔ d.initializerHolds s := by
  cases d with
  | basic ty n anns init =>
      cases init with
      | none => simp [VarDeclItem.initializerHolds]
      | some e =>
          have he : e.eval (encodeAuxStore s as) = e.eval s :=
            basicNames_eval_encodeAux (by
              intro x hx
              exact h x (by simpa [varDeclNames] using hx))
          have hn' : encodeAuxStore s as n = s n :=
            encodeAuxStore_not_mem s as n (by simpa [VarDeclItem.name] using hn)
          simp only [VarDeclItem.initializerHolds]
          rw [he, hn']
  | array ty n anns es =>
      have hall : ∀ b ∈ es,
          BasicExpr.eval (encodeAuxStore s as) b = BasicExpr.eval s b := by
        intro b hb
        exact basicNames_eval_encodeAux (by
          intro x hx
          exact h x (by
            simp only [varDeclNames, List.mem_flatMap]
            exact ⟨b, hb, hx⟩))
      have hmap : es.mapM (BasicExpr.eval (encodeAuxStore s as)) =
          es.mapM (BasicExpr.eval s) := by
        rw [mapM_congr_set hall]
      have hn' : encodeAuxStore s as n = s n :=
        encodeAuxStore_not_mem s as n (by simpa [VarDeclItem.name] using hn)
      simp only [VarDeclItem.initializerHolds]
      rw [hmap, hn']

/-! ## Inversion of the shape pass -/

/-- The invariants of a successful set-shape pass.  The state is the
    accumulator reached by traversing the source constraints from the
    initial state; the result model is that state's declarations and
    emitted rows. -/
def ShapeExpansion.Inv (taken : List String) (m : Model)
    (sh : ShapeExpansion) : Prop :=
  sh.model.parameters = m.parameters ∧
    sh.model.predicates = m.predicates ∧
    sh.model.solve = m.solve ∧
    ∃ state : ShapeState,
      shapeExpandConstraints taken m m.constraints (ShapeState.initial taken) =
        some state ∧
      sh.model.variables = state.decls.reverse ++ m.variables ∧
      sh.model.constraints = state.cons.reverse ∧
      sh.aux = state.aux.reverse

/-- Inversion of a successful shape pass. -/
theorem shapeExpandModelWith_inv {taken : List String} {m : Model}
    {sh : ShapeExpansion} (h : shapeExpandModelWith taken m = some sh) :
    sh.Inv taken m := by
  unfold shapeExpandModelWith at h
  cases hc : shapeExpandConstraints taken m m.constraints
      { next := 0, aux := [], decls := [], cons := [],
        maxLen := maxStrLength taken } with
  | none => simp [hc] at h
  | some stF =>
      rw [hc] at h
      simp at h
      subst h
      exact ⟨rfl, rfl, rfl, stF, hc, rfl, rfl, rfl⟩

/-- The shape pass leaves parameters, predicates and the solve item
    untouched. -/
theorem shapeExpandModelWith_fields {taken : List String} {m : Model}
    {sh : ShapeExpansion} (h : shapeExpandModelWith taken m = some sh) :
    sh.model.parameters = m.parameters ∧
      sh.model.predicates = m.predicates ∧
      sh.model.solve = m.solve := by
  obtain ⟨hp, hpr, hs, _⟩ := shapeExpandModelWith_inv h
  exact ⟨hp, hpr, hs⟩

/-- The shape pass leaves parameters, predicates and the solve item
    untouched (unnamed variant). -/
theorem shapeExpandModel_fields {m : Model} {sh : ShapeExpansion}
    (h : shapeExpandModel m = some sh) :
    sh.model.parameters = m.parameters ∧
      sh.model.predicates = m.predicates ∧
      sh.model.solve = m.solve :=
  shapeExpandModelWith_fields h

/-- Every source declaration survives the shape pass. -/
theorem shapeExpandModel_variables_mem {m : Model} {sh : ShapeExpansion}
    (h : shapeExpandModel m = some sh) {d : VarDeclItem}
    (hd : d ∈ m.variables) : d ∈ sh.model.variables := by
  obtain ⟨_, _, _, stF, _, hvars, _, _⟩ := shapeExpandModelWith_inv h
  rw [hvars]
  exact List.mem_append_right _ hd

/-- The completeness store of a shape expansion: read the source store
    through the auxiliaries' functional definitions (allocation order). -/
def ShapeExpansion.encStore (sh : ShapeExpansion) (s : Store) : Store :=
  fun x => encodeAuxStore s sh.aux.reverse x

/-- The expansion store is the final state's interpreted store. -/
theorem ShapeExpansion.encStore_eq_of {sh : ShapeExpansion} {stF : ShapeState}
    {s : Store} (haux : sh.aux = stF.aux.reverse) :
    sh.encStore s = stF.encStore s := by
  funext x
  show encodeAuxStore s sh.aux.reverse x = encodeAuxStore s stF.aux x
  rw [haux, List.reverse_reverse]

/-- A taken source name reads the same in the expansion store. -/
theorem ShapeExpansion.encStore_at_taken {taken : List String} {m : Model}
    {stF : ShapeState} (hstwf : stF.WF taken m) {x : Ident}
    (hx : x.name ∈ taken) (s : Store) :
    stF.encStore s x = s x :=
  ShapeState.encStore_at_taken hstwf hx

/-! ## Model-level correctness of the shape pass -/

/-- **Soundness of the shape pass**: a store satisfying the expanded
    model satisfies the source model at the very same store, because
    every rewritten row forces its source constraint in that store. -/
theorem shapeExpand_sound {taken : List String} {m : Model}
    {sh : ShapeExpansion} {t : Store}
    (hwf : WellFormed fullSig m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : shapeExpandModelWith taken m = some sh)
    (hs : SatisfiesDyn fullInterp sh.model t) :
    SatisfiesDyn fullInterp m t := by
  obtain ⟨_, _, _, stF, hexp, hvars, hcons, haux⟩ :=
    shapeExpandModelWith_inv h
  obtain ⟨hconsSat, hdomSat, hinitSat⟩ := hs
  have hnd : (m.variables.map (fun d => d.name.name)).Nodup :=
    nodup_name_of_nodup_ident
      (List.nodup_append.mp hwf.valueNamesUnique).2.1
  have hstwf : stF.WF taken m :=
    shapeExpandConstraints_wf (ShapeState.initial_wf taken m) hwf hsup hexp
  have hmemsub : ∀ d ∈ m.variables, d ∈ sh.model.variables := by
    intro d hd
    rw [hvars]
    exact List.mem_append_right _ hd
  have hvdom : ShapeVarDomains m t := by
    intro d hd
    exact hdomSat d (hmemsub d hd)
  have hint : ShapeIntDomains m t := ShapeIntDomains.of_varDomains hnd hvdom
  have hset : ShapeSetDomains m t := ShapeSetDomains.of_varDomains hnd hvdom
  have hdefs : stF.DefHolds t := by
    intro a ha
    exact hconsSat _ (by
      rw [hcons]
      exact List.mem_reverse.mpr (hstwf.defs a ha))
  have hholds : stF.Holds t := by
    intro c hc
    exact hconsSat c (by
      rw [hcons]
      exact List.mem_reverse.mpr hc)
  refine ⟨?_, hvdom, ?_⟩
  · intro c hc
    exact shapeExpandConstraints_sound hexp hdefs hholds hint hset c hc
  · intro d hd
    exact hinitSat d (hmemsub d hd)

/-- **Completeness of the shape pass**: every source store extends to the
    expansion store, in which every auxiliary takes its functional value
    and every rewritten row holds. -/
theorem shapeExpand_complete {taken : List String} {m : Model}
    {sh : ShapeExpansion} {s : Store}
    (hwf : WellFormed fullSig m)
    (hsup : ∀ x ∈ setTaken m, x ∈ taken)
    (h : shapeExpandModelWith taken m = some sh)
    (hsat : SatisfiesDyn fullInterp m s) :
    SatisfiesDyn fullInterp sh.model (sh.encStore s) := by
  obtain ⟨_, _, _, stF, hexp, hvars, hcons, haux⟩ :=
    shapeExpandModelWith_inv h
  have hsat' := hsat
  obtain ⟨hconsSat, hdomSat, hinitSat⟩ := hsat
  have hnd : (m.variables.map (fun d => d.name.name)).Nodup :=
    nodup_name_of_nodup_ident
      (List.nodup_append.mp hwf.valueNamesUnique).2.1
  have hstwf : stF.WF taken m :=
    shapeExpandConstraints_wf (ShapeState.initial_wf taken m) hwf hsup hexp
  have henc : sh.encStore s = stF.encStore s :=
    ShapeExpansion.encStore_eq_of haux
  have hint : ShapeIntDomains m s := ShapeIntDomains.of_varDomains hnd
    (fun d hd => hdomSat d hd)
  have hset : ShapeSetDomains m s := ShapeSetDomains.of_varDomains hnd
    (fun d hd => hdomSat d hd)
  have hset' : ShapeSetDomains m (stF.encStore s) :=
    ShapeSetDomains.encStore hstwf hsup hset
  have hdefs : stF.DefHolds (stF.encStore s) :=
    fun a ha => ShapeState.aux_definition_holds hnd hsat' hstwf ha
  have hnew : (ShapeState.initial taken).NewHolds stF (stF.encStore s) :=
    shapeExpandConstraints_newHolds hexp hdefs hconsSat hint hset hset'
      (fun x hx => ShapeState.encStore_at_taken hstwf hx)
      (fun c hc x hx => hsup x (wf_constraint_names_taken hwf c hc x hx))
  have hholds0 : (ShapeState.initial taken).Holds (stF.encStore s) := by
    intro c hc
    simp [ShapeState.initial] at hc
  have hfinalHolds : stF.Holds (stF.encStore s) :=
    ShapeState.holds_of_new hholds0 hnew
  rw [henc]
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    rw [hcons] at hc
    exact hfinalHolds c (List.mem_reverse.mp hc)
  · intro d hd
    rw [hvars] at hd
    rcases List.mem_append.mp hd with hdAux | hdSrc
    · rw [hstwf.auxDecls] at hdAux
      obtain ⟨a, ha, had⟩ := List.mem_map.mp (List.mem_reverse.mp hdAux)
      subst had
      have hdef := ShapeState.encStore_aux_defined (s := s) hstwf ha
      have hval : a.value (stF.encStore s) ≠ none :=
        ShapeState.encStore_aux_total hnd hsat' hstwf ha
      cases hv : a.value (stF.encStore s) with
      | none => exact absurd hv hval
      | some v =>
          refine ⟨v, ?_, ?_⟩
          · unfold ShapeAux.defined at hdef
            simpa [VarDeclItem.name] using hdef.trans hv
          · exact ShapeAux.value_contains (hstwf.tyOk a ha) hv
    · cases d with
      | basic ty n anns init =>
          obtain ⟨v, hv, hcont⟩ := hdomSat (.basic ty n anns init) hdSrc
          have hname : n.name ∈ taken :=
            hsup _ (List.mem_append_right _
              (List.mem_map.mpr ⟨.basic ty n anns init, hdSrc, rfl⟩))
          refine ⟨v, ?_, hcont⟩
          rw [ShapeState.encStore_at_taken hstwf (x := n) hname]
          exact hv
      | array ty n anns es =>
          obtain ⟨vs, hv, hlen, hcont⟩ := hdomSat (.array ty n anns es) hdSrc
          have hname : n.name ∈ taken :=
            hsup _ (List.mem_append_right _
              (List.mem_map.mpr ⟨.array ty n anns es, hdSrc, rfl⟩))
          refine ⟨vs, ?_, hlen, hcont⟩
          rw [ShapeState.encStore_at_taken hstwf (x := n) hname]
          exact hv
  · intro d hd
    rw [hvars] at hd
    rcases List.mem_append.mp hd with hdAux | hdSrc
    · rw [hstwf.auxDecls] at hdAux
      obtain ⟨a, ha, had⟩ := List.mem_map.mp (List.mem_reverse.mp hdAux)
      subst had
      trivial
    · exact (initializerHolds_encodeAux_iff
        (s := s) (as := stF.aux)
        (by
          intro hmem
          obtain ⟨a, ha, han⟩ := List.mem_map.mp hmem
          exact hstwf.namesAvoid a ha (han ▸
            hsup d.name.name
              (List.mem_append_right _ (List.mem_map.mpr ⟨d, hdSrc, rfl⟩))))
        (by
          intro x hx hmem
          obtain ⟨a, ha, han⟩ := List.mem_map.mp hmem
          exact hstwf.namesAvoid a ha (han ▸
            hsup x (wf_init_names_taken hwf d hdSrc x hx)))
        (d := d)).mpr (hinitSat d hdSrc)

end LeanFzn.Compiler
