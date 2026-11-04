/-
Purpose: Correctness and equivalence theorems for the solution checker.
Dependencies: Checker.Runtime.Solution and correctness of earlier checker layers.
DAG: Runtime.Solution -> Proofs.Solution -> public Checker.Solution import.
-/
import LeanFzn.Checker.Runtime.Solution

open LeanFzn.Semantics LeanFzn.Parser LeanFzn.Semantics.Evaluation

namespace LeanFzn.Checker.Solution

open LeanFzn LeanFzn.Checker.Solution

theorem completedStore_apply (m : Model) (es : List Entry) (x : Ident) :
    completedStore m es x = (completedMap m es)[x.name]? := rfl

/-- Folding insertions leaves a key that is never inserted unchanged. -/
theorem foldl_insert_getElem?_of_not_mem {β : Type} (key : β → String) (val : β → Value) :
    ∀ (xs : List β) (base : Std.HashMap String Value) (k : String),
      k ∉ xs.map key →
      (xs.foldl (fun acc x => acc.insert (key x) (val x)) base)[k]? = base[k]? := by
  intro xs
  induction xs with
  | nil => intro _ _ _; rfl
  | cons x xs ih =>
    intro base k hk
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    simp only [List.foldl_cons]
    rw [ih _ _ hk.2, Std.HashMap.getElem?_insert]
    have hne : (key x == k) = false := by
      simpa using fun h => hk.1 h.symm
    simp [hne]

/-- Folding insertions with pairwise distinct keys reads back every
    inserted value. -/
theorem foldl_insert_getElem?_of_mem {β : Type} (key : β → String) (val : β → Value) :
    ∀ (xs : List β) (base : Std.HashMap String Value) (x : β),
      (xs.map key).Nodup → x ∈ xs →
      (xs.foldl (fun acc x => acc.insert (key x) (val x)) base)[key x]? = some (val x) := by
  intro xs
  induction xs with
  | nil => intro _ _ _ h; cases h
  | cons y ys ih =>
    intro base x hnd hx
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.foldl_cons]
    rcases List.mem_cons.mp hx with rfl | hx'
    · rw [foldl_insert_getElem?_of_not_mem key val ys _ _ hnd.1,
        Std.HashMap.getElem?_insert_self]
    · exact ih _ x hnd.2 hx'

/-- A completion pass never changes a key that is already bound. -/
theorem completePass_getElem?_of_some (vars : List VarDeclItem) :
    ∀ (known : Std.HashMap String Value) (k : String) (v : Value),
      known[k]? = some v → (completePass vars known)[k]? = some v := by
  unfold completePass
  induction vars with
  | nil => intro known k v h; exact h
  | cons d ds ih =>
    intro known k v h
    simp only [List.foldl_cons]
    apply ih
    by_cases hc : known.contains d.name.name = true
    · simp only [hc, if_true]; exact h
    · rw [if_neg hc]
      split
      · rw [Std.HashMap.getElem?_insert]
        by_cases hk : d.name.name = k
        · subst hk
          rw [Std.HashMap.contains_eq_isSome_getElem?, h] at hc
          exact absurd rfl hc
        · simp [hk, h]
      · exact h

/-- Initializer completion never changes a key that is already bound. -/
theorem completeFix_getElem?_of_some (vars : List VarDeclItem) :
    ∀ (n : Nat) (known : Std.HashMap String Value) (k : String) (v : Value),
      known[k]? = some v → (completeFix vars n known)[k]? = some v := by
  intro n
  induction n with
  | zero => intro known k v h; exact h
  | succ n ih =>
    intro known k v h
    have hp := completePass_getElem?_of_some vars known k v h
    simp only [completeFix]
    split
    · exact hp
    · exact ih _ k v hp

/-- With distinct parameter names, the parameter map binds every
    parameter to its declared value. -/
theorem paramMap_getElem? (m : Model)
    (hnd : (m.parameters.map (fun d => d.name.name)).Nodup)
    {d : ParDeclItem} (hd : d ∈ m.parameters) :
    (paramMap m)[d.name.name]? = some d.value :=
  foldl_insert_getElem?_of_mem (fun d : ParDeclItem => d.name.name) ParDeclItem.value
    m.parameters {} d hnd hd

/-- **Entries are preserved.**  When the solution assigns each name at
    most once, the completed store maps every assigned name to exactly
    the value written in the solution string. -/
theorem completedStore_entry {m : Model} {es : List Entry} {e : Entry}
    (hnd : (es.map (·.name)).Nodup) (he : e ∈ es) :
    completedStore m es ⟨e.name⟩ = some e.value.toValue := by
  rw [completedStore_apply]
  exact completeFix_getElem?_of_some _ _ _ _ _
    (foldl_insert_getElem?_of_mem Entry.name (fun e => e.value.toValue) es (paramMap m) e
      hnd he)

/-- **Parameters keep their model values.**  When parameter names are
    distinct and no entry assigns a parameter name, the completed store
    is parameter-honest. -/
theorem completedStore_paramHonest {m : Model} {es : List Entry}
    (hpn : (m.parameters.map (fun d => d.name.name)).Nodup)
    (hdis : ∀ e ∈ es, ∀ d ∈ m.parameters, e.name ≠ d.name.name) :
    ParamHonest m (completedStore m es) := by
  intro d hd
  rw [completedStore_apply]
  apply completeFix_getElem?_of_some
  unfold entryMap
  rw [foldl_insert_getElem?_of_not_mem Entry.name (fun e => e.value.toValue) es _ _ (by
    intro hmem
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    exact hdis e he d hd heq)]
  exact paramMap_getElem? m hpn hd

/-- `constraintHoldsB` decides `Holds stdInterp` for standard
    predicates. -/
private theorem constraintHoldsB_iff {store : Store} {c : ConstraintItem}
    (hname : c.name.name ∈ stdNames ∨ c.name.name ∈ setNames) :
    constraintHoldsB store c = true ↔ c.Holds stdInterp store := by
  unfold constraintHoldsB ConstraintItem.Holds
  cases hargs : c.args.mapM (Expr.eval store) with
  | none =>
      constructor
      · intro hfalse
        exact absurd hfalse (by intro hc; cases hc)
      · rintro ⟨args, hnone, _⟩
        cases hnone
  | some args =>
      constructor
      · intro h
        refine ⟨args, rfl, ?_⟩
        have hred : interpB c.name args = true := h
        rcases hname with h | h
        · cases hc : c.name with
          | mk n' =>
              rw [hc] at hred h
              exact (interpB_std_iff (n := n') (show n' ∈ stdNames from h)).mp hred
        · exact (interpB_set_iff h).mp hred
      · rintro ⟨args', hargs', hinterp⟩
        have hargs_eq : args = args' := Option.some.inj hargs'
        subst hargs_eq
        -- goal: (match some args with | some args => interpB c.name args) = true
        show interpB c.name args = true
        rcases hname with h | h
        · cases hc : c.name with
          | mk n' =>
              rw [hc] at hinterp h
              exact (interpB_std_iff (n := n') (show n' ∈ stdNames from h)).mpr hinterp
        · exact (interpB_set_iff h).mpr hinterp

/-- `varTypeContainsB` decides `BasicVarType.contains`. -/
theorem varTypeContainsB_iff {ty : BasicVarType} {v : Value} :
    varTypeContainsB ty v = true ↔ ty.contains v := by
  cases ty with
  | par t =>
    cases t with
    | bool => cases v with
      | bool _ => simp [varTypeContainsB, BasicVarType.contains]
      | _ => simp [varTypeContainsB, BasicVarType.contains]
    | int => cases v with
      | int _ => simp [varTypeContainsB, BasicVarType.contains]
      | _ => simp [varTypeContainsB, BasicVarType.contains]
    | setOfInt => cases v with
      | setOfInt _ => simp [varTypeContainsB, BasicVarType.contains]
      | _ => simp [varTypeContainsB, BasicVarType.contains]
  | intRange lo hi =>
    cases v with
    | int x =>
        simp only [varTypeContainsB, BasicVarType.contains, decide_eq_true_eq]
    | _ => simp [varTypeContainsB, BasicVarType.contains]
  | intSet xs =>
    cases v with
    | int x =>
        simp only [varTypeContainsB, BasicVarType.contains, decide_eq_true_eq]
    | _ => simp [varTypeContainsB, BasicVarType.contains]
  | setOfIntRange lo hi =>
    cases v with
    | setOfInt sv =>
        simp only [varTypeContainsB, BasicVarType.contains, setSubB_iff]
        rfl
    | _ => simp [varTypeContainsB, BasicVarType.contains]
  | setOfIntSet allowed =>
    cases v with
    | setOfInt sv =>
        simp only [varTypeContainsB, BasicVarType.contains, setSubB_iff]
        rfl
    | _ => simp [varTypeContainsB, BasicVarType.contains]

theorem semEqB_iff {a b : Value} : semEqB a b = true ↔ a.SemEq b := by
  cases a <;> cases b <;> simp [semEqB, Value.SemEq, setEqB_iff]

theorem semEqListB_iff {as bs : List Value} :
    semEqListB as bs = true ↔ Forall2 Value.SemEq as bs := by
  induction as generalizing bs with
  | nil => cases bs <;> simp [semEqListB, Forall2]
  | cons a as ih =>
    cases bs with
    | nil => simp [semEqListB, Forall2]
    | cons b bs => simp only [semEqListB, Forall2, Bool.and_eq_true, semEqB_iff, ih]

/-- `initializerHoldsB` decides `VarDeclItem.initializerHolds`. -/
theorem initializerHoldsB_iff {store : Store} {d : VarDeclItem} :
    initializerHoldsB store d = true ↔ d.initializerHolds store := by
  cases d with
  | basic ty n anns opt =>
    cases opt with
    | none => simp [initializerHoldsB, VarDeclItem.initializerHolds]
    | some v =>
        simp only [initializerHoldsB, VarDeclItem.initializerHolds]
        cases v.eval store <;> cases store n <;> simp [semEqB_iff]
  | array ty n anns es =>
      simp only [initializerHoldsB, VarDeclItem.initializerHolds]
      cases es.mapM (fun e => e.eval store) with
      | none => simp
      | some vs =>
        cases hn : store n with
        | none => simp
        | some w =>
          cases w <;> simp [semEqListB_iff]

end LeanFzn.Checker.Solution
