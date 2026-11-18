/-
Purpose: Explicit source admission for the reviewed FlatZinc fragment.
Dependencies: Globals supplies decoded shapes, values and the source shape store.
DAG: Semantics.Globals -> Admission -> checker front doors and compiler entry.
These gates establish representation/premise checks, not upstream equivalence.
-/
import LeanFzn.Semantics.Globals

namespace LeanFzn.Semantics.Admission
open LeanFzn LeanFzn.Semantics.Globals

/-- Parameter-only evaluation never invents a value for a decision variable. -/
def parameterStore (m : Model) : Store := fun x =>
  lookupIdent x (m.parameters.map (fun d => (d.name, d.value)))

/-- Any value obtained from the parameter-only store is fixed in every
parameter-honest candidate store. No static dummy value enters this argument. -/
theorem parameterStore_some {m : Model} {store : Store} (hp : ParamHonest m store)
    {x : Ident} {v : Value} (h : parameterStore m x = some v) : store x = some v := by
  obtain ⟨y, hy, hname⟩ := shapeLookup_inv_mem x
    (m.parameters.map (fun d : ParDeclItem => (d.name, d.value))) v h
  obtain ⟨d, hd, heq⟩ := List.mem_map.mp hy
  have hn : d.name = x := Ident.eq_of_name_eq
    ((congrArg (fun p : Ident × Value => p.1.name) heq).trans hname)
  have hv : d.value = v := by simpa using congrArg Prod.snd heq
  simpa [hn, hv] using hp d hd

theorem basic_parameter_eval {m : Model} {store : Store} (hp : ParamHonest m store)
    {e : BasicExpr} {v : Value} (h : e.eval (parameterStore m) = some v) :
    e.eval store = some v := by
  cases e with
  | lit l => exact h
  | ident x => exact parameterStore_some hp h

theorem array_parameter_eval {m : Model} {store : Store} (hp : ParamHonest m store)
    {es : List BasicExpr} {vs : List Value}
    (h : es.mapM (BasicExpr.eval (parameterStore m)) = some vs) :
    es.mapM (BasicExpr.eval store) = some vs := by
  induction es generalizing vs with
  | nil => simpa using h
  | cons e es ih =>
    cases he : e.eval (parameterStore m) with
    | none => simp [List.mapM_cons, he] at h
    | some v =>
      cases ht : es.mapM (BasicExpr.eval (parameterStore m)) with
      | none => simp [List.mapM_cons, he, ht] at h
      | some rest =>
        simp only [List.mapM_cons, he, ht] at h
        cases h
        simp [List.mapM_cons, basic_parameter_eval hp he, ih ht]

theorem parameter_eval {m : Model} {store : Store} (hp : ParamHonest m store)
    {e : Expr} {v : Value} (h : e.eval (parameterStore m) = some v) :
    e.eval store = some v := by
  cases e with
  | basic b => exact basic_parameter_eval hp h
  | array es =>
    cases he : es.mapM (BasicExpr.eval (parameterStore m)) with
    | none => simp [Expr.eval, he] at h
    | some vs =>
      simp only [Expr.eval, he, Option.map_some] at h
      cases h
      simp [Expr.eval, array_parameter_eval hp he]

/-- Array shape, independent of its decision-variable elements. -/
def arrayLength (m : Model) (e : Expr) : Option Nat :=
  match e.eval m.shapeStore with
  | some (.array vs) => some vs.length
  | _ => none

/-- A public nonnegative-constant premise is checked using parameters only. -/
def NonnegativeArray (m : Model) (e : Expr) : Prop :=
  match e.eval (parameterStore m) with
  | some (.array vs) => ∀ v ∈ vs, match v with
      | .int i => 0 ≤ i
      | _ => False
  | _ => False

instance (m : Model) (e : Expr) : Decidable (NonnegativeArray m e) := by
  unfold NonnegativeArray
  split
  · have : DecidablePred (fun v : Value => match v with
        | .int i => 0 ≤ i
        | _ => False) := fun v => by cases v <;> infer_instance
    infer_instance
  · infer_instance

theorem nonnegativeArray_values {m : Model} {store : Store}
    (hp : ParamHonest m store) {e : Expr} (h : NonnegativeArray m e) :
    ∃ vs, e.eval store = some (.array vs) ∧
      ∀ v ∈ vs, match v with | .int i => 0 ≤ i | _ => False := by
  unfold NonnegativeArray at h
  cases he : e.eval (parameterStore m) with
  | none => simp [he] at h
  | some v =>
    cases v with
    | array vs => exact ⟨vs, parameter_eval hp he, by simpa [he] using h⟩
    | bool _ | int _ | setOfInt _ => simp [he] at h

/-- Empty-cardinality wrapper assertions require every lower bound to
allow zero, separately from the aggregate sum. -/
def NonpositiveArray (m : Model) (e : Expr) : Prop :=
  match e.eval (parameterStore m) with
  | some (.array vs) => ∀ v ∈ vs, match v with
      | .int i => i ≤ 0
      | _ => False
  | _ => False

instance (m : Model) (e : Expr) : Decidable (NonpositiveArray m e) := by
  unfold NonpositiveArray
  split
  · have : DecidablePred (fun v : Value => match v with
        | .int i => i ≤ 0
        | _ => False) := fun v => by cases v <;> infer_instance
    infer_instance
  · infer_instance

/-- Machine-index reads must be valid even when the native implication masks
one of them. Constant machines avoid assuming a decision-variable range. -/
def BoundedMachineArray (m : Model) (e : Expr) (bound : Nat) : Prop :=
  match e.eval (parameterStore m) with
  | some (.array vs) => ∀ v ∈ vs, match v with
      | .int i => 1 ≤ i ∧ i ≤ (bound : Int)
      | _ => False
  | _ => False

instance (m : Model) (e : Expr) (bound : Nat) :
    Decidable (BoundedMachineArray m e bound) := by
  unfold BoundedMachineArray
  split
  · have : DecidablePred (fun v : Value => match v with
        | .int i => 1 ≤ i ∧ i ≤ (bound : Int)
        | _ => False) := fun v => by cases v <;> infer_instance
    infer_instance
  · infer_instance

/-- Checked premises of each admitted restricted family. Unresolved native
metadata/activation contracts are excluded altogether, including ground calls.
Other names retain the existing well-formedness and name-support obligations. -/
def ConstraintAdmitted (m : Model) (c : ConstraintItem) : Prop :=
  match c.name.name with
  | "fzn_geost" | "fzn_geost_bb" | "fzn_geost_smallest_bb" |
    "fzn_mdd_nondet" | "fzn_cost_mdd" => False
  | "fzn_bin_packing" =>
      match c.args with
      | [cap, bin, weight] =>
          (match cap.eval (parameterStore m) with
           | some (.int i) => 0 ≤ i
           | _ => False) ∧
          NonnegativeArray m weight ∧
          arrayLength m bin = arrayLength m weight ∧
          (arrayLength m bin).isSome = true
      | _ => False
  | "fzn_cumulative" =>
      match c.args with
      | [start, duration, resource, _] =>
          NonnegativeArray m duration ∧ NonnegativeArray m resource ∧
          arrayLength m start = arrayLength m duration ∧
          arrayLength m start = arrayLength m resource ∧
          (arrayLength m start).isSome = true
      | _ => False
  | "fzn_cumulatives" | "fzn_cumulatives_decomp" =>
      match c.args with
      | start :: duration :: resource :: machine :: bound :: _ =>
          (match arrayLength m start, arrayLength m duration,
              arrayLength m resource, arrayLength m machine, arrayLength m bound with
           | some s, some d, some r, some a, some b =>
               s ≤ d ∧ s ≤ r ∧ s ≤ a ∧ BoundedMachineArray m machine b
           | _, _, _, _, _ => False) ∧
          (if c.name.name = "fzn_cumulatives" then
            match (c.args[6]?).bind (fun e : Expr => e.eval (parameterStore m)) with
            | some (.int i) => i = 1
            | _ => False
           else True)
      | _ => False
  | "fzn_regular" | "fzn_regular_nfa" | "fzn_cost_regular" =>
      match c.args.mapM (Expr.eval m.shapeStore) with
      | some args => Regular.regularDecodes c.name.name args = true
      | none => False
  | "fzn_global_cardinality_low_up_closed" =>
      match c.args with
      | [xs, cover, low, up] =>
          match arrayLength m xs, arrayLength m cover, arrayLength m low, arrayLength m up with
          | some n, some c, some l, some u => c = l ∧ c = u ∧
              (n = 0 → NonpositiveArray m low ∧ NonnegativeArray m up)
          | _, _, _, _ => False
      | _ => False
  | _ => True

instance (m : Model) (c : ConstraintItem) : Decidable (ConstraintAdmitted m c) := by
  unfold ConstraintAdmitted
  split <;> (repeat first | infer_instance | split)

/-- Every restricted call meets the published admission contract. Array lower
indices are 1 by construction of Syntax.IndexSet; WellFormed checks lengths. -/
def Admitted (m : Model) : Prop := ∀ c ∈ m.constraints, ConstraintAdmitted m c

instance (m : Model) : Decidable (Admitted m) := by
  unfold Admitted
  infer_instance

def admittedB (m : Model) : Bool := decide (Admitted m)

theorem admittedB_iff (m : Model) : admittedB m = true ↔ Admitted m :=
  decide_eq_true_iff

/-- First failing call, with an unsupported result distinct from falsity. -/
def firstFailure (m : Model) : Option String :=
  (m.constraints.find? (fun c => !decide (ConstraintAdmitted m c))).map
    (fun c => c.name.name ++ ": outside the admitted FlatZinc fragment")

theorem firstFailure_none_iff (m : Model) : firstFailure m = none ↔ Admitted m := by
  simp [firstFailure, Admitted, List.find?_eq_none]

theorem admitted_constraint {m : Model} (h : Admitted m) {c : ConstraintItem}
    (hc : c ∈ m.constraints) : ConstraintAdmitted m c := h c hc

theorem admitted_cumulative {m : Model} {c : ConstraintItem}
    (h : ConstraintAdmitted m c) (hn : c.name.name = "fzn_cumulative")
    {s d r b : Expr} (ha : c.args = [s,d,r,b]) :
    NonnegativeArray m d ∧ NonnegativeArray m r ∧
      arrayLength m s = arrayLength m d ∧ arrayLength m s = arrayLength m r ∧
      (arrayLength m s).isSome = true := by
  simpa [ConstraintAdmitted, hn, ha] using h

end LeanFzn.Semantics.Admission
