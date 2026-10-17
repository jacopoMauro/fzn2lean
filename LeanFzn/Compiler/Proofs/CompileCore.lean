/-
File: LeanFzn/Compiler/Proofs/CompileCore.lean

Purpose:
  The exact semantic-correspondence theorems for the certified
  FlatZinc fragment compiler (`LeanFzn/Compiler/Compile.lean`).

Dependencies:
  - LeanFzn.Compiler.Compile: the executable compiler.
DAG:
  LeanFzn.Compiler.Compile -> LeanFzn.Compiler.Proofs.Compile
     -> LeanFzn.Compiler.Correctness
-/

import LeanFzn.Solver.Core
import LeanFzn.Compiler.Compile
open LeanFzn.Compiler.Domains

namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Core

/-! ## Lookup lemmas -/

/-- Name equality is identifier equality (Ident is a one-field
    structure). -/
theorem ident_eq_of_name {x y : Ident} (h : x.name = y.name) : x = y := by
  obtain ⟨n1⟩ := x
  obtain ⟨n2⟩ := y
  simp only [Ident.mk.injEq]
  exact h

/-- `lookupIdent` returns the head's value when queried at the head's
    exact identifier. -/
theorem lookupIdent_cons_eq {β : Type} {y : Ident} {v : β}
    {rest : List (Ident × β)} :
    lookupIdent y ((y, v) :: rest) = some v := by
  simp only [lookupIdent, reduceIte]

/-- `lookupIdent` skips a head whose name differs. -/
theorem lookupIdent_cons_ne {β : Type} {x y : Ident} {v : β}
    {rest : List (Ident × β)} (hne : x.name ≠ y.name) :
    lookupIdent x ((y, v) :: rest) = lookupIdent x rest := by
  simp only [lookupIdent, if_neg hne]

/-- `lookupIdent` finds the pair's value when queried at that exact
    identifier, in a name-unique list (first-match-wins then
    coincides with membership). -/
theorem lookupIdent_of_mem {β : Type} {x : Ident} {v : β}
    {l : List (Ident × β)} (hnu : (l.map Prod.fst).Nodup)
    (hmem : (x, v) ∈ l) :
    lookupIdent x l = some v := by
  induction l with
  | nil => cases hmem
  | cons ab rest ih =>
      rw [List.map_cons, List.nodup_cons] at hnu
      rcases List.mem_cons.mp hmem with heq | htl
      · have hxa : x = ab.1 := (Prod.mk.injEq .. ▸ heq).1
        have hva : v = ab.2 := (Prod.mk.injEq .. ▸ heq).2
        rw [hxa, hva]
        exact lookupIdent_cons_eq (y := ab.1) (v := ab.2) (rest := rest)
      · obtain ⟨y', v'⟩ := ab
        by_cases hname : x.name = y'.name
        · exfalso
          have hxy' : x = y' := ident_eq_of_name hname
          apply hnu.1
          rw [List.mem_map]
          refine ⟨(x, v), htl, ?_⟩
          simp only [hxy']
        · rw [lookupIdent_cons_ne hname]
          exact ih hnu.2 htl

/-- A parameter with a scalar literal value resolves in `parEnv` to
    exactly that value, in a model with unique value names. -/
theorem parEnv_of_decl {m : Model} {d : ParDeclItem}
    (hd : d ∈ m.parameters) {v : Value}
    (hv : parDeclValue d = some v)
    (hnu : ((m.parameters.filterMap
        (fun d2 => parDeclValue d2 |>.map (fun v2 => (ParDeclItem.name d2, v2)))).map
      Prod.fst).Nodup) :
    parEnv m (ParDeclItem.name d) = some v := by
  unfold parEnv
  have hmem : (ParDeclItem.name d, v) ∈
      (m.parameters.filterMap
        (fun d2 => parDeclValue d2 |>.map (fun v2 => (ParDeclItem.name d2, v2)))) := by
    rw [List.mem_filterMap]
    refine ⟨d, hd, ?_⟩
    rw [hv]
    simp
  have hlk := lookupIdent_of_mem hnu hmem
  rw [hlk]

/-! ## The compiler inversion -/

/-- The aux-slot expansion's slot equation: the model-level
    pre-pass's first component, against the same slot list
    `slotsChecked` extracted (the `toOption` projection agrees). -/
theorem modelAuxSlots_eq {m : Model}
    {slots0 : List (String × List Value)}
    (hslot : slotsChecked m = .ok slots0) :
    modelAuxSlots m = (expandPlan (auxTaken m slots0) [] m.constraints).1 := by
  have hget : (slotsChecked m).toOption.getD [] = slots0 := by
    rw [hslot]; rfl
  unfold modelAuxSlots modelSlots
  rw [hget]

/-- The aux-slot expansion's constraint equation. -/
theorem modelExpand_eq {m : Model}
    {slots0 : List (String × List Value)}
    (hslot : slotsChecked m = .ok slots0) :
    modelExpand m = (expandPlan (auxTaken m slots0) [] m.constraints).2 := by
  have hget : (slotsChecked m).toOption.getD [] = slots0 := by
    rw [hslot]; rfl
  unfold modelExpand modelSlots
  rw [hget]

/-- A successful compile passes every gate and yields the assembled
    problem. The gates: no predicate items, scalar-only parameters,
    initializer-free basic variables only, `solve satisfy`, a
    successful slot extraction, and a successful constraint
    compilation of the AUX-EXPANDED constraint list (the literal
    pinning shapes rewritten over the fresh aux slots, which are
    appended to the model's slot list). -/
theorem compileModel_ok_inv {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem) :
    problem.source = m ∧
    ∃ slots dcs,
      (∃ slots0, slotsChecked m = .ok slots0 ∧
        slots = slots0 ++ modelAuxSlots m) ∧
      compileConstraints (parEnv m) (slots.map Prod.fst)
        (modelExpand m) = .ok dcs ∧
      problem = assemble m slots dcs := by
  unfold compileModel at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc
    · split at hc
      · cases hc
      · split at hc
        · rcases hslots : slotsChecked m with _ | slots
          · rw [hslots] at hc; cases hc
          · rw [hslots] at hc
            have hauxs : modelAuxSlots m =
                (expandPlan (auxTaken m slots) [] m.constraints).1 :=
              modelAuxSlots_eq hslots
            have hexp : modelExpand m =
                (expandPlan (auxTaken m slots) [] m.constraints).2 :=
              modelExpand_eq hslots
            have hstep : (match (Except.ok slots :
                  Except String (List (String × List Value))) with
                | .error e => Except.error e
                | .ok s =>
                  have allSlots := s ++ modelAuxSlots m;
                  match compileConstraints (parEnv m)
                      (List.map Prod.fst allSlots) (modelExpand m) with
                  | .error e => Except.error e
                  | .ok dcs => Except.ok (assemble m allSlots dcs)) = .ok problem := hc
            have hstep2 : (match compileConstraints (parEnv m)
                  (List.map Prod.fst (slots ++ modelAuxSlots m))
                  (modelExpand m) with
                | .error e => Except.error e
                | .ok dcs => Except.ok (assemble m (slots ++ modelAuxSlots m) dcs))
                = .ok problem := hstep
            rcases hdcs : compileConstraints (parEnv m)
              (List.map Prod.fst (slots ++ modelAuxSlots m)) (modelExpand m) with _ | dcs
            · rw [hdcs] at hstep2; cases hstep2
            · rw [hdcs] at hstep2
              have hprog : problem = assemble m (slots ++ modelAuxSlots m) dcs :=
                (Except.ok.inj hstep2).symm
              subst hprog
              exact ⟨rfl, slots ++ modelAuxSlots m, dcs,
                ⟨slots, hslots.symm ▸ rfl, rfl⟩, hdcs, rfl⟩
        · cases hc

/-! ## nameIndex position finding -/

/-- `nameIndex` finds the list's own element when names are
    distinct. -/
theorem nameIndex_at_nodup : ∀ (names : List String) (i : Nat),
    names.Nodup → i < names.length → nameIndex names names[i]! = some i := by
  intro names i
  induction names generalizing i with
  | nil => intro _ hlt; cases hlt
  | cons n rest ih =>
      intro hnu hlt
      have hnd := (List.nodup_cons.mp hnu)
      by_cases hiz : i = 0
      · subst hiz
        simp only [nameIndex, List.getElem_cons_zero]
        rw [if_pos (by simp)]
      · have hpos : ∃ k, i = k + 1 := by
            rcases Nat.exists_eq_succ_of_ne_zero hiz with ⟨k', hk'⟩
            exact ⟨k', by omega⟩
        obtain ⟨k, hk⟩ := hpos
        subst hk
        have hklt : k < rest.length := by
          simp only [List.length_cons] at hlt
          omega
        show (if (n == (n :: rest)[k+1]!) = true then some 0
            else (nameIndex rest (n :: rest)[k+1]!).map (fun x => x + 1)) =
            some (k+1)
        have hread : (n :: rest)[k+1]! = rest[k]! := by
          rw [List.getElem!_cons_succ]
        rw [hread]
        have hne : (n == rest[k]!) = false := by
          cases hbeq : (n == rest[k]!) with
          | false => rfl
          | true =>
              have hcc : n = rest[k]! := by simpa using hbeq
              have hmem : rest[k]! ∈ rest := by
                rw [show rest[k]! = rest[k] from by
                  rw [List.getElem!_eq_getElem?_getD]
                  simp only [List.getElem?_eq_getElem hklt]
                  rfl]
                exact List.getElem_mem hklt
              exact absurd (hcc ▸ hmem) hnd.1
        rw [hne]
        rw [ih k hnd.2 hklt]
        simp

/-! ## The store bridge -/

/-- At an assembled problem, `toStore` reads the assignment (some) at
    every slot name, in bounds. -/
theorem toStore_slot {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {i : Nat}
    (hnu : (slots.map Prod.fst).Nodup)
    (hlt : i < slots.length) (ha : i < a.length) :
    (assemble m slots dcs).toStore a
        (Ident.mk (slots.map Prod.fst)[i]!) = some a[i]! := by
  show (match nameIndex (slots.map Prod.fst)
      (Ident.mk (slots.map Prod.fst)[i]!).name with
    | some j => a[j]?
    | none => parEnv m (Ident.mk (slots.map Prod.fst)[i]!)) = some a[i]!
  have hnamekey : (Ident.mk (slots.map Prod.fst)[i]!).name =
      (slots.map Prod.fst)[i]! := rfl
  rw [hnamekey]
  have hmaplen : (slots.map Prod.fst).length = slots.length := by
    simp
  have hidx : nameIndex (slots.map Prod.fst) (slots.map Prod.fst)[i]! =
      some i := by
    apply nameIndex_at_nodup (slots.map Prod.fst) i hnu
    rw [hmaplen]
    exact hlt
  rw [hidx]
  show (a[i]?) = some a[i]!
  have hget2 : a[i]! = a[i] := by
    rw [List.getElem!_eq_getElem?_getD]
    have hget : a[i]? = some a[i] := List.getElem?_eq_getElem (by omega)
    rw [hget]
    rfl
  rw [hget2, List.getElem?_eq_getElem (by omega)]

/-- At an assembled problem, `toStore` resolves a scalar parameter to
    its declared value, in a well-formed model whose slot names are
    distinct from the parameter names. -/
theorem toStore_par {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {d : ParDeclItem}
    (hd : d ∈ m.parameters) {v : Value} (hv : parDeclValue d = some v)
    (hdisj : ∀ i, i < slots.length →
      (slots.map Prod.fst)[i]! ≠ (ParDeclItem.name d).name)
    (hnu : ((m.parameters.filterMap
        (fun d2 => parDeclValue d2 |>.map
          (fun v2 => (ParDeclItem.name d2, v2)))).map
      Prod.fst).Nodup):
    (assemble m slots dcs).toStore a (ParDeclItem.name d) = some v := by
  show (match nameIndex (slots.map Prod.fst) (ParDeclItem.name d).name with
    | some j => a[j]?
    | none => parEnv m (ParDeclItem.name d)) = some v
  by_cases hfind : nameIndex (slots.map Prod.fst) (ParDeclItem.name d).name
      = none
  · rw [hfind]
    exact parEnv_of_decl hd hv hnu
  · exfalso
    obtain ⟨j, hj⟩ : ∃ j, nameIndex (slots.map Prod.fst)
        (ParDeclItem.name d).name = some j := by
      cases hfind' : nameIndex (slots.map Prod.fst)
          (ParDeclItem.name d).name with
      | none => exact absurd hfind' hfind
      | some j => exact ⟨j, rfl⟩
    obtain ⟨hjlt, hjget⟩ := nameIndex_some (slots.map Prod.fst)
      (ParDeclItem.name d).name j hj
    have hlen : (slots.map Prod.fst).length = slots.length := by simp
    have hjlt2 : j < slots.length := by omega
    have hnamej : (slots.map Prod.fst)[j]!
        = (ParDeclItem.name d).name := by
      rw [List.getElem!_eq_getElem?_getD, hjget]
      rfl
    exact absurd hnamej (hdisj j hjlt2)


/-! ## Constraint exactness -/

/-! ## The converse (assignment → store) -/
/-! ## The interpolation bridge for the converse direction -/

/-- The full interpretation delegates to the standard-library
    interpretation on every predicate name of the compiled fragment
    (none of them is a global-constraint name). -/
theorem fullInterp_eq_stdInterp_of_fragment (n : String)
    (hn : n = "int_eq" ∨ n = "int_ne" ∨ n = "int_le" ∨ n = "int_lt" ∨
      n = "int_ge" ∨ n = "int_gt" ∨ n = "int_plus" ∨ n = "int_times" ∨
      n = "int_min" ∨ n = "int_max" ∨ n = "int_abs" ∨ n = "bool_not" ∨
      n = "bool_and" ∨ n = "bool_or" ∨ n = "all_different" ∨
      n = "int_lin_eq" ∨ n = "int_lin_le") :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    simp only [fullInterp]
    rw [if_neg (by decide)]

/-- Transport of an interpretation along the constraint's name. -/
theorem interp_concrete {c : ConstraintItem} {n : String}
    {args : List Value} (hinterp : fullInterp c.name args)
    (hname : c.name.name = n) : fullInterp (Ident.mk n) args :=
  interp_of_hname hname hinterp

/-! ## dotProduct helpers for the literal-bound int_plus shape -/

/-- The two-element unit-coefficient dot product (the compiled form of
    `int_plus(x, y, k)` as `linEq [1, 1] [i, j] k`). -/
theorem dotProduct_two_one : ∀ (x y : Value),
    dotProduct [Value.int 1, Value.int 1] [x, y] =
      (match x, y with
      | .int p, .int q => some (p + q)
      | _, _ => none) := by
  intro x y
  cases x <;> cases y <;> simp [LeanFzn.Semantics.dotProduct]

/-- Inversion of the two-element unit-coefficient dot product. -/
theorem dotProduct_two_one_inv {x y : Value} {k : Int}
    (h : dotProduct [Value.int 1, Value.int 1] [x, y] = some k) :
    ∃ p q, x = .int p ∧ y = .int q ∧ p + q = k := by
  rw [dotProduct_two_one] at h
  cases x with
  | int p =>
      cases y with
      | int q =>
          have hk : p + q = k := (Option.some.inj h)
          exact ⟨p, q, rfl, rfl, hk⟩
      | bool w => exact absurd h (by simp)
      | setOfInt w => exact absurd h (by simp)
      | array w => exact absurd h (by simp)
  | bool w => exact absurd h (by simp)
  | setOfInt w => exact absurd h (by simp)
  | array w => exact absurd h (by simp)


/-- Evaluation of an identifier argument at the assembled store reads
    the assignment's value at the slot (the converse bridge). -/
theorem eval_ident_toStore {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x : Ident} {i : Nat}
    (hnu : (slots.map Prod.fst).Nodup)
    (hx : nameIndex (slots.map Prod.fst) x.name = some i)
    (halt : a.length = slots.length) :
    BasicExpr.eval ((assemble m slots dcs).toStore a) (.ident x)
      = some a[i]! := by
  unfold BasicExpr.eval
  show (assemble m slots dcs).toStore a x = some a[i]!
  obtain ⟨hilt, higet⟩ := nameIndex_some (slots.map Prod.fst) x.name i hx
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have hislt : i < slots.length := by omega
  have ha5 : i < a.length := by rw [halt]; exact hislt
  -- the store's key for x reads a[i]! via the slot bridge:
  have hstore : (assemble m slots dcs).toStore a
      (Ident.mk (slots.map Prod.fst)[i]!) = some a[i]! :=
    toStore_slot (m := m) (dcs := dcs) hnu hislt ha5
  -- the query identifier x IS the slot's identifier:
  have hname : (slots.map Prod.fst)[i]! = x.name := by
    rw [List.getElem!_eq_getElem?_getD, higet]
    rfl
  have hxid : Ident.mk (slots.map Prod.fst)[i]! = x := by
    apply ident_eq_of_name
    exact hname
  rw [hxid] at hstore
  exact hstore


/-- The read at the slot is `some` of the bang read (in bounds). -/
theorem getElem_as_some {a : List Value} {i : Nat} (hlt : i < a.length) :
    a[i]? = some a[i]! := by
  rw [List.getElem?_eq_getElem hlt]
  rw [List.getElem!_eq_getElem?_getD (i := i) (l := a), List.getElem?_eq_getElem hlt]
  rfl

/-- The assembled store reads the value at an identifier whose name
    resolves to a slot. -/
theorem toStore_read {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x : Ident} {i : Nat}
    (hnu : (slots.map Prod.fst).Nodup)
    (hx : nameIndex (slots.map Prod.fst) x.name = some i)
    (halt : a.length = slots.length) :
    (assemble m slots dcs).toStore a x = some a[i]! := by
  have hxA : i < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) x.name i hx).1
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have ha5 : i < a.length := by omega
  show (match nameIndex (slots.map Prod.fst) x.name with
    | some j => a[j]?
    | none => parEnv m x) = _
  rw [hx]
  show (a[i]?) = _
  rw [getElem_as_some ha5]

/-- The `Expr.eval` of a two-identifier argument list. -/
theorem eval_two_ident {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x y : Ident} {i j : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j) :
    ([Expr.basic (.ident x), Expr.basic (.ident y)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, a[j]!] := by
  have hxA : i < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have ha5 : i < a.length := by omega
  have hxA2 : j < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
  have ha6 : j < a.length := by omega
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← (assemble m slots dcs).toStore a y
      pure [v1, v2]) = _
  rw [toStore_read (m := m) hnu hxi halt]
  rw [toStore_read (m := m) hnu hyi halt]
  rfl

/-- The `Expr.eval` of a three-identifier argument list. -/
theorem eval_three_ident {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x y z : Ident}
    {i j k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k) :
    ([Expr.basic (.ident x), Expr.basic (.ident y),
       Expr.basic (.ident z)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, a[j]!, a[k]!] := by
  have hxA : i < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have ha5 : i < a.length := by omega
  have hxA2 : j < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
  have ha6 : j < a.length := by omega
  have hxA3 : k < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
  have ha7 : k < a.length := by omega
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← (assemble m slots dcs).toStore a y
      let v3 ← (assemble m slots dcs).toStore a z
      pure [v1, v2, v3]) = _
  rw [toStore_read (m := m) hnu hxi halt]
  rw [toStore_read (m := m) hnu hyi halt]
  rw [toStore_read (m := m) hnu hzi halt]
  rfl

/-- The `Expr.eval` of an identifier-and-int-literal list. -/
theorem eval_ident_int {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x : Ident} {i : Nat}
    {k : Int}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i) :
    ([Expr.basic (.ident x), Expr.basic (.lit (.int k))].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, .int k] := by
  have hxA : i < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have ha5 : i < a.length := by omega
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← pure (LeanFzn.Semantics.Value.int k)
      pure [v1, v2]) = _
  rw [toStore_read (m := m) hnu hxi halt]
  rfl

/-- The `Expr.eval` of an int-literal-and-identifier list. -/
theorem eval_int_ident {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {y : Ident} {j : Nat}
    {k : Int}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j) :
    ([Expr.basic (.lit (.int k)), Expr.basic (.ident y)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [.int k, a[j]!] := by
  have hxA : j < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have ha5 : j < a.length := by omega
  show (do
      let v1 ← pure (LeanFzn.Semantics.Value.int k)
      let v2 ← (assemble m slots dcs).toStore a y
      pure [v1, v2]) = _
  rw [toStore_read (m := m) hnu hyi halt]
  rfl




/-- A `?`-read that is `some w` makes the bang read `w`. -/
theorem bang_of_getElem? {a : List Value} {i : Nat} {w : Value}
    (h : a[i]? = some w) : a[i]! = w := by
  rw [List.getElem!_eq_getElem?_getD, h]
  rfl

/-- The full interpretation is the standard-library interpretation on
    every name outside the global-constraint set (all the compiled
    fragment's predicate names qualify, by `decide`). -/
theorem fullInterp_std {n : String}
    (hn : ¬ n ∈ globalsNames) :
    fullInterp (Ident.mk n) = stdInterp (Ident.mk n) := by
  simp only [fullInterp]
  rw [if_neg hn]

/-- The interpretation transport to a concrete name. -/
theorem holds_name_transport {c : ConstraintItem} {n : String}
    {args : List Value} (hinterp : fullInterp (Ident.mk n) args)
    (hname : c.name.name = n) : fullInterp c.name args := by
  rw [ident_eq_of_name hname]
  exact hinterp

/-! ## Generic argument-evaluation bridges for the converse direction -/

/-- Evaluation of two-identifiers-then-a-constant-valued argument list
    at the assembled store (the `int_plus(x, y, k)` bridge). -/
theorem eval_ident_ident_E {m : Model}
    {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value}
    {x y : Ident} {i j : Nat} {e3 : Expr} {k : Int}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (he3 : Expr.eval ((assemble m slots dcs).toStore a) e3 = some (.int k)) :
    ([Expr.basic (.ident x), Expr.basic (.ident y), e3].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, a[j]!, .int k] := by
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← (assemble m slots dcs).toStore a y
      let v3 ← Expr.eval ((assemble m slots dcs).toStore a) e3
      pure [v1, v2, v3]) = _
  rw [toStore_read (m := m) hnu hxi halt, toStore_read (m := m) hnu hyi halt,
    he3]
  rfl

/-- Every position produced by `allDiffIndices` is in bounds for
    the slot-name list it indexes (mirroring `linIndices_lt`). -/
theorem allDiffIndices_lt {names : List String} :
    ∀ (elems : ArrayLiteral) (is : List Nat),
    allDiffIndices names elems = some is →
    ∀ i, i ∈ is → i < names.length := by
  intro elems
  induction elems with
  | nil =>
      intro is hidx i hi
      have hnil : allDiffIndices names [] = some [] := rfl
      rw [hnil] at hidx
      have his : is = [] := (Option.some.inj hidx).symm
      rw [his] at hi
      exact absurd hi (by simp)
  | cons e es ih =>
      intro is hidx i hi
      cases he : e with
      | lit l =>
          rw [he] at hidx
          exact absurd hidx (by simp [allDiffIndices])
      | ident x =>
          rw [he] at hidx
          simp only [allDiffIndices] at hidx
          cases hn : nameIndex names x.name with
          | none => rw [hn] at hidx; exact absurd hidx (by simp)
          | some n =>
              rw [hn] at hidx
              cases hrest : allDiffIndices names es with
              | none => rw [hrest] at hidx; exact absurd hidx (by simp)
              | some rest =>
                  rw [hrest] at hidx
                  have his : is = n :: rest := by simpa using hidx.symm
                  rw [his] at hi
                  obtain ⟨hxlt, _⟩ := nameIndex_some names x.name n hn
                  cases hi with
                  | head => exact hxlt
                  | tail _ hitl => exact ih rest hrest i hitl

/-- The mapM-fold reading of an identifier array at the assembled
    store: the elements' values are exactly the assignment's reads at
    the extracted positions, in order (the all_different converse
    bridge). -/
theorem eval_allDiff_array {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length) :
    ∀ (elems : ArrayLiteral) (is : List Nat),
    allDiffIndices (slots.map Prod.fst) elems = some is →
    (∀ i, i ∈ is → i < a.length) →
    (elems.mapM (BasicExpr.eval ((assemble m slots dcs).toStore a)))
      = some (is.map (fun i => a[i]!)) := by
  intro elems
  induction elems with
  | nil =>
      intro is hidx _
      have hnil : allDiffIndices (slots.map Prod.fst) [] = some [] := rfl
      rw [hnil] at hidx
      have his : is = [] := (Option.some.inj hidx).symm
      subst his
      rfl
  | cons e es ih =>
      intro is hidx hin
      cases he : e with
      | lit l =>
          rw [he] at hidx
          exact absurd hidx (by simp [allDiffIndices])
      | ident x =>
          rw [he] at hidx
          simp only [allDiffIndices] at hidx
          cases hn : nameIndex (slots.map Prod.fst) x.name with
          | none => rw [hn] at hidx; exact absurd hidx (by simp)
          | some n =>
              rw [hn] at hidx
              cases hrest : allDiffIndices (slots.map Prod.fst) es with
              | none => rw [hrest] at hidx; exact absurd hidx (by simp)
              | some rest =>
                  rw [hrest] at hidx
                  have his : is = n :: rest := by simpa using hidx.symm
                  subst his
                  have hnlt : n < a.length := hin n (by simp)
                  have hread : ((assemble m slots dcs).toStore a) x =
                      some a[n]! :=
                    toStore_read (m := m) hnu hn halt
                  simp only [List.mapM_cons, List.map_cons, BasicExpr.eval]
                  rw [hread,
                    ih rest hrest (by
                      intro i hi
                      exact hin i (by simp [hi]))]
                  rfl

/-- Evaluation of an all_different argument at the assembled store:
    the array literal evaluates to the reads at the extracted
    positions. -/
theorem eval_allDiff_args {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {elems : ArrayLiteral} {is : List Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hidx : allDiffIndices (slots.map Prod.fst) elems = some is)
    (hin : ∀ i, i ∈ is → i < a.length) :
    ([Expr.array elems].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [.array (is.map (fun i => a[i]!))] := by
  have harr : (Expr.array elems).eval
      ((assemble m slots dcs).toStore a) =
      some (.array (is.map (fun i => a[i]!))) := by
    show ((elems.mapM
        (BasicExpr.eval ((assemble m slots dcs).toStore a))).map
      Value.array) = _
    rw [eval_allDiff_array hnu halt elems is hidx hin]
    rfl
  show (do
      let v1 ← (Expr.array elems).eval ((assemble m slots dcs).toStore a)
      pure [v1]) = _
  rw [harr]
  rfl

/-- The `Expr.eval` bridge for the linear shapes: the coefficient
    array evaluates to `intVals coeffs`, the variable array to the
    assignment's reads at `is`, and the literal to itself. -/
theorem eval_lin_args {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value}
    {ks elems : ArrayLiteral} {coeffs : List Int} {is : List Nat}
    {b : Int}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hcoeffs : linCoeffs ks = some coeffs)
    (hidx : linIndices (slots.map Prod.fst) elems = some is)
    (hin : ∀ i, i ∈ is → i < a.length) :
    ([Expr.array ks, Expr.array elems, Expr.basic (.lit (.int b))].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
        .int b] := by
  have hlength : (slots.map Prod.fst).length = slots.length := by simp
  have hvals : ∀ (i : Nat), i < (slots.map Prod.fst).length →
      ∀ (v : Value), a[i]? = some v →
      (assemble m slots dcs).toStore a (Ident.mk (slots.map Prod.fst)[i]!)
        = some v := by
    intro i hilt v hv
    have hislt : i < slots.length := by omega
    have ha5 : i < a.length := by rw [halt]; exact hislt
    have hread : (assemble m slots dcs).toStore a
        (Ident.mk (slots.map Prod.fst)[i]!) = some a[i]! :=
      toStore_slot (m := m) (dcs := dcs) hnu hislt ha5
    have hsome : a[i]? = some a[i]! := getElem_as_some ha5
    have hvv : v = a[i]! := by
      rw [hsome] at hv
      exact (Option.some.inj hv).symm
    rw [hvv]
    exact hread
  have h1 : (Expr.array ks).eval ((assemble m slots dcs).toStore a) =
      some (.array (intVals coeffs)) := by
    show ((ks.mapM
        (BasicExpr.eval ((assemble m slots dcs).toStore a))).map
      Value.array) = _
    rw [linCoeffs_eval ks coeffs hcoeffs]
    rfl
  have h2 : (Expr.array elems).eval ((assemble m slots dcs).toStore a) =
      some (.array (is.map (fun i => a[i]!))) := by
    show ((elems.mapM
        (BasicExpr.eval ((assemble m slots dcs).toStore a))).map
      Value.array) = _
    rw [linIndices_eval hvals elems is hidx hin]
    rfl
  show (do
      let v1 ← (Expr.array ks).eval ((assemble m slots dcs).toStore a)
      let v2 ← (Expr.array elems).eval ((assemble m slots dcs).toStore a)
      let v3 ← (Expr.basic (.lit (.int b))).eval
          ((assemble m slots dcs).toStore a)
      pure [v1, v2, v3]) = _
  rw [h1, h2]
  rfl

/-- The `Expr.eval` of one identifier-array argument at the assembled
    store: the evaluated array is the assignment's reads at the
    extracted positions (the array-argument bridge of `bool_clause`). -/
theorem eval_array_arg {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {elems : ArrayLiteral} {is : List Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hidx : linIndices (slots.map Prod.fst) elems = some is)
    (hin : ∀ i, i ∈ is → i < a.length) :
    (Expr.array elems).eval ((assemble m slots dcs).toStore a) =
      some (.array (is.map (fun i => a[i]!))) := by
  have hlength : (slots.map Prod.fst).length = slots.length := by simp
  have hvals : ∀ (i : Nat), i < (slots.map Prod.fst).length →
      ∀ (v : Value), a[i]? = some v →
      (assemble m slots dcs).toStore a (Ident.mk (slots.map Prod.fst)[i]!)
        = some v := by
    intro i hilt v hv
    have hislt : i < slots.length := by omega
    have ha5 : i < a.length := by rw [halt]; exact hislt
    have hread : (assemble m slots dcs).toStore a
        (Ident.mk (slots.map Prod.fst)[i]!) = some a[i]! :=
      toStore_slot (m := m) (dcs := dcs) hnu hislt ha5
    have hsome : a[i]? = some a[i]! := getElem_as_some ha5
    have hvv : v = a[i]! := by
      rw [hsome] at hv
      exact (Option.some.inj hv).symm
    rw [hvv]
    exact hread
  show ((elems.mapM
      (BasicExpr.eval ((assemble m slots dcs).toStore a))).map
    Value.array) = _
  rw [linIndices_eval hvals elems is hidx hin]
  rfl

/-- The `Expr.eval` of a two-slot-array argument list at the assembled
    store (the `bool_clause` converse bridge). -/
theorem eval_two_arrays {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {elems1 elems2 : ArrayLiteral} {is1 is2 : List Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hidx1 : linIndices (slots.map Prod.fst) elems1 = some is1)
    (hidx2 : linIndices (slots.map Prod.fst) elems2 = some is2)
    (hin1 : ∀ i, i ∈ is1 → i < a.length)
    (hin2 : ∀ i, i ∈ is2 → i < a.length) :
    ([Expr.array elems1, Expr.array elems2].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [.array (is1.map (fun i => a[i]!)),
        .array (is2.map (fun i => a[i]!))] := by
  have h1 := eval_array_arg (m := m) (dcs := dcs) hnu halt hidx1 hin1
  have h2 := eval_array_arg (m := m) (dcs := dcs) hnu halt hidx2 hin2
  show (do
      let v1 ← (Expr.array elems1).eval ((assemble m slots dcs).toStore a)
      let v2 ← (Expr.array elems2).eval ((assemble m slots dcs).toStore a)
      pure [v1, v2]) = _
  rw [h1, h2]
  rfl

/-- The `Expr.eval` of an array-then-identifier argument list. -/
theorem eval_arr_ident {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {elems : ArrayLiteral} {is : List Nat} {r : Ident} {k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (his : linIndices (slots.map Prod.fst) elems = some is)
    (hr : nameIndex (slots.map Prod.fst) r.name = some k)
    (hin : ∀ i, i ∈ is → i < a.length) :
    ([Expr.array elems, Expr.basic (.ident r)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [.array (is.map (fun i => a[i]!)), a[k]!] := by
  have hR : k < (slots.map Prod.fst).length :=
    (nameIndex_some (slots.map Prod.fst) r.name k hr).1
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have hak : k < a.length := by omega
  show (do
      let v1 ← (Expr.array elems).eval ((assemble m slots dcs).toStore a)
      let v2 ← (assemble m slots dcs).toStore a r
      pure [v1, v2]) = _
  rw [eval_array_arg (m := m) (dcs := dcs) hnu halt his hin]
  rw [toStore_read (m := m) hnu hr halt]
  rfl

/-- The `Expr.eval` of a constant integer array argument that produced
    `xs` via `intLits`. -/
theorem eval_intLits_arg {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {elems : ArrayLiteral} {xs : List Int}
    (hxs : intLits elems = some xs) :
    (Expr.array elems).eval ((assemble m slots dcs).toStore a) =
      some (.array (xs.map Value.int)) := by
  show ((elems.mapM
      (BasicExpr.eval ((assemble m slots dcs).toStore a))).map
    Value.array) = _
  rw [intLits_eval elems xs hxs]
  rfl

/-- The `Expr.eval` of an identifier-array-identifier argument list at
    the assembled store, with the array evaluated by `intLits` (the
    `array_int_element` converse bridge). -/
theorem eval_ident_arr_lits {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {x y : Ident} {elems : ArrayLiteral} {xs : List Int}
    {i k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyk : nameIndex (slots.map Prod.fst) y.name = some k)
    (hxs : intLits elems = some xs) :
    ([Expr.basic (.ident x), Expr.array elems, Expr.basic (.ident y)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, .array (xs.map Value.int), a[k]!] := by
  have hA : (Expr.array elems).eval ((assemble m slots dcs).toStore a) =
      some (.array (xs.map Value.int)) :=
    eval_intLits_arg (m := m) (dcs := dcs) hxs
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← (Expr.array elems).eval ((assemble m slots dcs).toStore a)
      let v3 ← (assemble m slots dcs).toStore a y
      pure [v1, v2, v3]) = _
  rw [toStore_read (m := m) hnu hxi halt]
  rw [hA]
  rw [toStore_read (m := m) hnu hyk halt]
  rfl

/-- The `Expr.eval` of an identifier-array-identifier argument list at
    the assembled store, with the array evaluated by `linIndices` (the
    `array_var_int_element`/`array_var_bool_element` converse
    bridge). -/
theorem eval_ident_arr_ident {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {x y : Ident} {elems : ArrayLiteral} {is : List Nat}
    {i k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyk : nameIndex (slots.map Prod.fst) y.name = some k)
    (his : linIndices (slots.map Prod.fst) elems = some is)
    (hin : ∀ j, j ∈ is → j < a.length) :
    ([Expr.basic (.ident x), Expr.array elems, Expr.basic (.ident y)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, .array (is.map (fun j => a[j]!)), a[k]!] := by
  have hA : (Expr.array elems).eval ((assemble m slots dcs).toStore a) =
      some (.array (is.map (fun j => a[j]!))) :=
    eval_array_arg (m := m) (dcs := dcs) hnu halt his hin
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← (Expr.array elems).eval ((assemble m slots dcs).toStore a)
      let v3 ← (assemble m slots dcs).toStore a y
      pure [v1, v2, v3]) = _
  rw [toStore_read (m := m) hnu hxi halt]
  rw [hA]
  rw [toStore_read (m := m) hnu hyk halt]
  rfl

/-- The `Expr.eval` of a linear argument list followed by a reification
    identifier (the `int_lin_*_reif` converse bridge). -/
theorem eval_lin_reif_args {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value}
    {ks elems : ArrayLiteral} {coeffs : List Int} {is : List Nat}
    {b : Int} {r : Ident} {k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hcoeffs : linCoeffs ks = some coeffs)
    (hidx : linIndices (slots.map Prod.fst) elems = some is)
    (hin : ∀ i, i ∈ is → i < a.length)
    (hrk : nameIndex (slots.map Prod.fst) r.name = some k) :
    ([Expr.array ks, Expr.array elems, Expr.basic (.lit (.int b)),
       Expr.basic (.ident r)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
        .int b, a[k]!] := by
  have hlength : (slots.map Prod.fst).length = slots.length := by simp
  have hvals : ∀ (i : Nat), i < (slots.map Prod.fst).length →
      ∀ (v : Value), a[i]? = some v →
      (assemble m slots dcs).toStore a (Ident.mk (slots.map Prod.fst)[i]!)
        = some v := by
    intro i hilt v hv
    have hislt : i < slots.length := by omega
    have ha5 : i < a.length := by rw [halt]; exact hislt
    have hread : (assemble m slots dcs).toStore a
        (Ident.mk (slots.map Prod.fst)[i]!) = some a[i]! :=
      toStore_slot (m := m) (dcs := dcs) hnu hislt ha5
    have hsome : a[i]? = some a[i]! := getElem_as_some ha5
    have hvv : v = a[i]! := by
      rw [hsome] at hv
      exact (Option.some.inj hv).symm
    rw [hvv]
    exact hread
  have h1 : (Expr.array ks).eval ((assemble m slots dcs).toStore a) =
      some (.array (intVals coeffs)) := by
    show ((ks.mapM
        (BasicExpr.eval ((assemble m slots dcs).toStore a))).map
      Value.array) = _
    rw [linCoeffs_eval ks coeffs hcoeffs]
    rfl
  have h2 : (Expr.array elems).eval ((assemble m slots dcs).toStore a) =
      some (.array (is.map (fun i => a[i]!))) := by
    show ((elems.mapM
        (BasicExpr.eval ((assemble m slots dcs).toStore a))).map
      Value.array) = _
    rw [linIndices_eval hvals elems is hidx hin]
    rfl
  show (do
      let v1 ← (Expr.array ks).eval ((assemble m slots dcs).toStore a)
      let v2 ← (Expr.array elems).eval ((assemble m slots dcs).toStore a)
      let v3 ← (Expr.basic (.lit (.int b))).eval
          ((assemble m slots dcs).toStore a)
      let v4 ← (assemble m slots dcs).toStore a r
      pure [v1, v2, v3, v4]) = _
  rw [h1, h2]
  rw [toStore_read (m := m) hnu hrk halt]
  rfl

/-- The `BasicExpr.eval` of one general integer operand (`intArgOf`
    resolved) at the assembled store: the store's value of the source
    expression IS the operand's read — an identifier reads the
    assignment's slot value, an integer literal denotes itself. -/
theorem eval_basic_arg {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {e : BasicExpr} {o : DomIntArg}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (ho : intArgOf (slots.map Prod.fst) e = some o) :
    BasicExpr.eval ((assemble m slots dcs).toStore a) e =
      some (DomIntArg.read a o) := by
  cases e with
  | lit l =>
      cases l with
      | int k =>
          have ho' : o = .lit k :=
            (Option.some.inj (by simpa [intArgOf] using ho)).symm
          subst ho'
          rfl
      | bool b => exact absurd ho (by simp [intArgOf])
      | set s => exact absurd ho (by simp [intArgOf])
  | ident x =>
      simp only [intArgOf] at ho
      cases hn : nameIndex (slots.map Prod.fst) x.name with
      | none => rw [hn] at ho; exact absurd ho (by simp)
      | some i =>
          rw [hn] at ho
          have ho' : o = .slot i := (Option.some.inj (by simpa using ho)).symm
          subst ho'
          exact toStore_read (m := m) hnu hn halt

/-- The `Expr.eval` of a three-general-basic-argument list at the
    assembled store: the evaluated arguments are the operands' reads. -/
theorem eval_three_basic {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {a₀ a₁ a₂ : BasicExpr}
    {o₀ o₁ o₂ : DomIntArg}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (ho₀ : intArgOf (slots.map Prod.fst) a₀ = some o₀)
    (ho₁ : intArgOf (slots.map Prod.fst) a₁ = some o₁)
    (ho₂ : intArgOf (slots.map Prod.fst) a₂ = some o₂) :
    ([Expr.basic a₀, Expr.basic a₁, Expr.basic a₂].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [DomIntArg.read a o₀, DomIntArg.read a o₁,
        DomIntArg.read a o₂] := by
  have h1 := eval_basic_arg (m := m) (dcs := dcs) hnu halt ho₀
  have h2 := eval_basic_arg (m := m) (dcs := dcs) hnu halt ho₁
  have h3 := eval_basic_arg (m := m) (dcs := dcs) hnu halt ho₂
  show (do
      let v1 ← BasicExpr.eval ((assemble m slots dcs).toStore a) a₀
      let v2 ← BasicExpr.eval ((assemble m slots dcs).toStore a) a₁
      let v3 ← BasicExpr.eval ((assemble m slots dcs).toStore a) a₂
      pure [v1, v2, v3]) = _
  rw [h1, h2, h3]
  rfl

/-- The `Expr.eval` of a result-slot-then-slot-array argument list at
    the assembled store (the `array_int_maximum(m, xs)` shape): the
    array evaluates to the assignment's reads at the extracted
    positions. -/
theorem eval_ident_slot_array {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {x : Ident} {elems : ArrayLiteral} {is : List Nat}
    {k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hk : nameIndex (slots.map Prod.fst) x.name = some k)
    (his : linIndices (slots.map Prod.fst) elems = some is) :
    ([Expr.basic (.ident x), Expr.array elems].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[k]!, .array (is.map (fun i => a[i]!))] := by
  have hin : ∀ i, i ∈ is → i < a.length := by
    intro i hi
    have hlt := linIndices_lt elems is his i hi
    have hlen : (slots.map Prod.fst).length = slots.length := by simp
    omega
  have harr := eval_array_arg (m := m) (dcs := dcs) hnu halt his hin
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← (Expr.array elems).eval ((assemble m slots dcs).toStore a)
      pure [v1, v2]) = _
  rw [toStore_read (m := m) hnu hk halt, harr]
  rfl

/-- int_ne(x, y) converse under int-valued reads: two INTEGER slot
    arguments reading DIFFERENT values make the source constraint hold
    at the assembled store. -/
theorem holds_int_ne_slot_toStore {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {i j : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_ne")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hwi : ∃ p, a[i]! = Value.int p) (hwj : ∃ q, a[j]! = Value.int q)
    (hdcsat : (DomConstraint.neSlot i j).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨w, z, hw, hz, hne⟩ := hdcsat
  have hib : a[i]! = w := bang_of_getElem? hw
  have hjb : a[j]! = z := bang_of_getElem? hz
  obtain ⟨p, hp⟩ := hwi
  obtain ⟨q, hq⟩ := hwj
  have hwp : w = Value.int p := by rw [← hib, hp]
  have hzq : z = Value.int q := by rw [← hjb, hq]
  refine ⟨[a[i]!, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_two_ident (m := m) hnu halt hxi hyi
  · rw [ident_eq_of_name hname]
    rw [fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!] with
      | [Value.int p, Value.int q] => p ≠ q
      | _ => False)
    rw [hib, hjb, hwp, hzq]
    intro heq
    exact hne (by rw [hwp, hzq, heq])


/-- int_eq(x, y) converse under int-valued reads: two INTEGER slot
    arguments reading equal values make the source constraint hold
    at the assembled store. -/
theorem holds_int_eq_slot_toStore {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {i j : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_eq")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hwi : ∃ p, a[i]! = Value.int p) (hwj : ∃ q, a[j]! = Value.int q)
    (hdcsat : (DomConstraint.eqSlot i j).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hp⟩ := hwi
  obtain ⟨q, hq⟩ := hwj
  obtain ⟨w, z, hw, hz, heq⟩ := hdcsat
  have hib : a[i]! = w := bang_of_getElem? hw
  have hjb : a[j]! = z := bang_of_getElem? hz
  -- w = .int p (from hib and hp)
  have hwp : w = Value.int p := by rw [← hib, hp]
  have hzq : z = Value.int q := by rw [← hjb, hq]
  refine ⟨[a[i]!, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_two_ident (m := m) hnu halt hxi hyi
  · have hcname : c.name = Ident.mk "int_eq" :=
      ident_eq_of_name hname
    rw [hcname]
    rw [show fullInterp (Ident.mk "int_eq") = LeanFzn.Semantics.stdInterp
        (Ident.mk "int_eq") from by
      simp only [fullInterp]
      rw [if_neg (by decide)]]
    show (match [a[i]!, a[j]!] with
      | [Value.int p, Value.int q] => p = q
      | _ => False)
    rw [hib, hjb, hwp, hzq]
    rw [hwp, hzq] at heq
    exact (Value.int.inj heq)


/-! ## The Fits/allAssigns bridges -/

/-- Membership in `allAssigns` implies the length equality
    (an easy induction once we generalize over the assignment). -/
theorem mem_allAssigns_length : ∀ (doms : List (List Value))
    (a : List Value), a ∈ allAssigns doms → a.length = doms.length := by
  intro doms
  induction doms with
  | nil =>
      intro a h
      simp only [allAssigns, List.mem_singleton] at h
      rw [h]
      rfl
  | cons d rest ih =>
      intro a h
      cases hd : d with
      | nil =>
          simp only [allAssigns, hd] at h
          cases h
      | cons v vs =>
          have hmemiff : a ∈ allAssigns ((v :: vs) :: rest) ↔
              ∃ w ∈ (v :: vs), ∃ a' ∈ allAssigns rest, a = w :: a' :=
            mem_allAssigns_singleton v vs rest a
          rw [hd] at h
          rw [hmemiff] at h
          obtain ⟨w, hw, a', ha', heq⟩ := h
          rw [heq, List.length_cons]
          have hlen := ih a' ha'
          rw [hlen]
          rfl

/-- Membership in `allAssigns` implies every read is in its slot's
    domain (via the singleton characterization). -/
theorem mem_allAssigns_fits : ∀ (doms : List (List Value))
    (a : List Value), a ∈ allAssigns doms →
    ∀ (i : Nat) (v : Value), a[i]? = some v → v ∈ doms.getD i [] := by
  intro doms
  induction doms with
  | nil =>
      intro a h i v hv
      simp only [allAssigns, List.mem_singleton] at h
      rw [h] at hv
      cases hv
  | cons d rest ih =>
      intro a h i v hv
      cases hd : d with
      | nil =>
          simp only [allAssigns, hd] at h
          cases h
      | cons v' vs =>
          have hmemiff : a ∈ allAssigns ((v' :: vs) :: rest) ↔
              ∃ w ∈ (v' :: vs), ∃ a' ∈ allAssigns rest, a = w :: a' :=
            mem_allAssigns_singleton v' vs rest a
          rw [hd] at h
          rw [hmemiff] at h
          obtain ⟨w, hw, a', ha', heq⟩ := h
          cases i with
          | zero =>
              rw [heq] at hv
              rw [List.getElem?_cons_zero] at hv
              have hvw : v = w := (Option.some.inj hv).symm
              rw [hvw]
              simp only [List.getD_cons_zero]
              exact hw
          | succ i2 =>
              rw [heq] at hv
              rw [List.getElem?_cons_succ] at hv
              rw [show ((v' :: vs) :: rest).getD (i2 + 1) [] =
                  rest.getD i2 [] from rfl]
              exact ih a' ha' i2 v hv


/-- **THE CONSTRAINT CORRESPONDENCE (assignment → store), recorded
    shapes**: if `extractConstraint` produced `dc` from `c` (the 21
    recorded shapes) and `dc` is satisfied by the assignment — with
    the int-valued reads of the two `eq/ne` slot shapes supplied —
    then the source constraint holds at the assembled store under
    `fullInterp`.  (The int-reads premise is NAME-CONDITIONED in the
    new linker design (Exact.lean's compile_sat_link_extracted)
    derives it from the constraint's name via the signature check,
    so callers pass no shape facts.) -/
theorem extractConstraint_holds_converse {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {dc : DomConstraint}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hdc : extractConstraint (slots.map Prod.fst) c = some dc)
    (hreads : ∀ (x : Ident) (i : Nat),
      Expr.basic (.ident x) ∈ c.args →
      nameIndex (slots.map Prod.fst) x.name = some i →
      (c.name.name = "int_eq" ∨ c.name.name = "int_ne") →
      ∃ p, a[i]! = Value.int p)
    (hsat : dc.SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  -- (the int-reads premise is NAME-CONDITIONED: only the eq/ne slot
  -- shapes consult it, for their OWN arguments; the linker derives
  -- it from the typing chain for eq/ne constraints)
  rcases extractConstraint_inv hdc with
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, k, i, hname, hargs, hxi, hdc'⟩ |
    ⟨k, y, i, hname, hargs, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, k, i, hname, hargs, hxi, hdc'⟩ |
    ⟨k, y, i, hname, hargs, hyi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨elems, is, hname, hargs, hidx, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, hname, hargs, hcoeffs, his, hlen, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, hname, hargs, hcoeffs, his, hlen, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, i, k, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, k, i, hname, hargs, hxi, hdc'⟩ |
    ⟨k, y, i, hname, hargs, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨x, y, z, i, j, k, hname, hargs, hxi, hyi, hzi, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, hname, hargs, hcoeffs, his, hlen, hdc'⟩ |
    ⟨elems1, elems2, ps, ns, hname, hargs, hidx1, hidx2, hdc'⟩ |
    ⟨elems, r, is, k, hname, hargs, his, hr, hdc'⟩ |
    ⟨x, y, i, k, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨x, y, i, j, hname, hargs, hxi, hyi, hdc'⟩ |
    ⟨elems, xs, x, y, i, k, hname, hargs, hxs, hxi, hyk, hdc'⟩ |
    ⟨elems, is, x, y, i, k, hname, hargs, his, hxi, hyk, hdc'⟩ |
    ⟨elems, is, x, y, i, k, hname, hargs, his, hxi, hyk, hdc'⟩ |
    ⟨x, y, r, i, j, k, hname, hargs, hxi, hyi, hrk, hdc'⟩ |
    ⟨x, y, r, i, j, k, hname, hargs, hxi, hyi, hrk, hdc'⟩ |
    ⟨x, y, r, i, j, k, hname, hargs, hxi, hyi, hrk, hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, r, k, hname, hargs, hcoeffs, his, hlen, hrk,
      hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, r, k, hname, hargs, hcoeffs, his, hlen, hrk,
      hdc'⟩ |
    ⟨ks, elems, coeffs, is, b, r, k, hname, hargs, hcoeffs, his, hlen, hrk,
      hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨a₀, a₁, a₂, o₀, o₁, o₂, hname, hargs, ho₀, ho₁, ho₂, hdc'⟩ |
    ⟨x, elems, is, k, hname, hargs, hk, his, hdc'⟩ |
    ⟨x, elems, is, k, hname, hargs, hk, his, hdc'⟩
  · -- int_eq(x, y): the dedicated reads lemma
    subst hdc'
    have hmemx : Expr.basic (.ident x) ∈ c.args := by
      rw [hargs]; exact List.mem_cons_self
    have hmemy : Expr.basic (.ident y) ∈ c.args := by
      rw [hargs]; exact List.mem_cons_of_mem _ List.mem_cons_self
    exact holds_int_eq_slot_toStore hnu halt hname hargs hxi hyi
      (hreads x i hmemx hxi (Or.inl hname))
      (hreads y j hmemy hyi (Or.inl hname)) hsat
  · -- int_eq(x, k)
    subst hdc'
    have hai : a[i]! = Value.int k :=
      bang_of_getElem? hsat
    refine ⟨[a[i]!, .int k], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_int (m := m) hnu halt hxi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, Value.int k] with
        | [Value.int p, Value.int q] => p = q
        | _ => False)
      rw [hai]
  · -- int_eq(k, y)
    subst hdc'
    have hai : a[i]! = Value.int k :=
      bang_of_getElem? hsat
    refine ⟨[.int k, a[i]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_int_ident (m := m) hnu halt hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [Value.int k, a[i]!] with
        | [Value.int p, Value.int q] => p = q
        | _ => False)
      rw [hai]
  · -- int_ne(x, y): the dedicated reads lemma
    subst hdc'
    have hmemx : Expr.basic (.ident x) ∈ c.args := by
      rw [hargs]; exact List.mem_cons_self
    have hmemy : Expr.basic (.ident y) ∈ c.args := by
      rw [hargs]; exact List.mem_cons_of_mem _ List.mem_cons_self
    exact holds_int_ne_slot_toStore hnu halt hname hargs hxi hyi
      (hreads x i hmemx hxi (Or.inr hname))
      (hreads y j hmemy hyi (Or.inr hname)) hsat
  · -- int_le(x, y)
    subst hdc'
    obtain ⟨p, q, hw, hz, hle⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    have hjb : a[j]! = Value.int q := bang_of_getElem? hz
    refine ⟨[a[i]!, a[j]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_two_ident (m := m) hnu halt hxi hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!] with
        | [Value.int p, Value.int q] => p ≤ q
        | _ => False)
      rw [hib, hjb]
      exact hle
  · -- int_le(x, k)
    subst hdc'
    obtain ⟨p, hw, hpc⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    refine ⟨[a[i]!, .int k], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_int (m := m) hnu halt hxi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, Value.int k] with
        | [Value.int p, Value.int q] => p ≤ q
        | _ => False)
      rw [hib]
      exact hpc
  · -- int_le(k, y)
    subst hdc'
    obtain ⟨p, hw, hcp⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    refine ⟨[.int k, a[i]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_int_ident (m := m) hnu halt hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [Value.int k, a[i]!] with
        | [Value.int p, Value.int q] => p ≤ q
        | _ => False)
      rw [hib]
      exact hcp
  · -- int_plus(x, y, z)
    subst hdc'
    obtain ⟨p, q, r, hw, hz, hw2, hpqr⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    have hjb : a[j]! = Value.int q := bang_of_getElem? hz
    have hkb : a[k]! = Value.int r := bang_of_getElem? hw2
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hzi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.int p, Value.int q, Value.int r] => p + q = r
        | _ => False)
      rw [hib, hjb, hkb]
      exact hpqr
  · -- all_different([elems])
    subst hdc'
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := allDiffIndices_lt elems is hidx i hi
      have hlen : (slots.map Prod.fst).length = slots.length := by simp
      have halt2 : a.length = (slots.map Prod.fst).length := by
        rw [halt]; exact hlen.symm
      omega
    refine ⟨[.array (is.map (fun i => a[i]!))], ?_, ?_⟩
    · rw [hargs]
      exact eval_allDiff_args (m := m) hnu halt hidx hin
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show valuesAllDifferent (is.map (fun i => a[i]!))
      rw [← (valuesAllDifferent_iff_nodup _).mpr hsat]
  · -- int_lin_eq
    subst hdc'
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      have hlen : (slots.map Prod.fst).length = slots.length := by simp
      have halt2 : a.length = (slots.map Prod.fst).length := by
        rw [halt]; exact hlen.symm
      omega
    refine ⟨[.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
      .int b], ?_, ?_⟩
    · rw [hargs]
      exact eval_lin_args (m := m) hnu halt hcoeffs his hin
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show LeanFzn.Semantics.dotProduct (intVals coeffs)
          (is.map (fun i => a[i]!)) = some b
      exact hsat
  · -- int_lin_le
    subst hdc'
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      have hlen : (slots.map Prod.fst).length = slots.length := by simp
      have halt2 : a.length = (slots.map Prod.fst).length := by
        rw [halt]; exact hlen.symm
      omega
    refine ⟨[.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
      .int b], ?_, ?_⟩
    · rw [hargs]
      exact eval_lin_args (m := m) hnu halt hcoeffs his hin
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show LeanFzn.Semantics.dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
      exact hsat
  · -- int_times(x, y, z)
    subst hdc'
    obtain ⟨p, q, r, hw, hz, hw2, hpqr⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    have hjb : a[j]! = Value.int q := bang_of_getElem? hz
    have hkb : a[k]! = Value.int r := bang_of_getElem? hw2
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hzi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.int p, Value.int q, Value.int r] => p * q = r
        | _ => False)
      rw [hib, hjb, hkb]
      exact hpqr
  · -- int_min(x, y, z)
    subst hdc'
    obtain ⟨p, q, r, hw, hz, hw2, hpqr⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    have hjb : a[j]! = Value.int q := bang_of_getElem? hz
    have hkb : a[k]! = Value.int r := bang_of_getElem? hw2
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hzi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.int p, Value.int q, Value.int r] => r = min p q
        | _ => False)
      rw [hib, hjb, hkb]
      exact hpqr.symm
  · -- int_max(x, y, z)
    subst hdc'
    obtain ⟨p, q, r, hw, hz, hw2, hpqr⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    have hjb : a[j]! = Value.int q := bang_of_getElem? hz
    have hkb : a[k]! = Value.int r := bang_of_getElem? hw2
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hzi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.int p, Value.int q, Value.int r] => r = max p q
        | _ => False)
      rw [hib, hjb, hkb]
      exact hpqr.symm
  · -- int_abs(x, y)
    subst hdc'
    obtain ⟨p, r, hw, hz, habs⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    have hjb : a[k]! = Value.int r := bang_of_getElem? hz
    refine ⟨[a[i]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_two_ident (m := m) hnu halt hxi hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[k]!] with
        | [Value.int p, Value.int q] => q = if p < 0 then -p else p
        | _ => False)
      rw [hib, hjb, ← habs]
      rfl
  · -- int_lt(x, y)
    subst hdc'
    obtain ⟨p, q, hw, hz, hpq⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    have hjb : a[j]! = Value.int q := bang_of_getElem? hz
    refine ⟨[a[i]!, a[j]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_two_ident (m := m) hnu halt hxi hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!] with
        | [Value.int p, Value.int q] => p < q
        | _ => False)
      rw [hib, hjb]
      exact hpq
  · -- int_lt(x, k)
    subst hdc'
    obtain ⟨p, hw, hpc⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    refine ⟨[a[i]!, .int k], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_int (m := m) hnu halt hxi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, Value.int k] with
        | [Value.int p, Value.int q] => p < q
        | _ => False)
      rw [hib]
      exact hpc
  · -- int_lt(k, y)
    subst hdc'
    obtain ⟨p, hw, hcp⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hw
    refine ⟨[.int k, a[i]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_int_ident (m := m) hnu halt hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [Value.int k, a[i]!] with
        | [Value.int p, Value.int q] => p < q
        | _ => False)
      rw [hib]
      exact hcp
  · -- bool_not(x, y)
    subst hdc'
    obtain ⟨w, z, hw, hz, hnot⟩ := hsat
    have hib : a[i]! = w := bang_of_getElem? hw
    have hjb : a[j]! = z := bang_of_getElem? hz
    -- the disjunction forces both reads Boolean
    rcases hnot with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨[a[i]!, a[j]!], ?_, ?_⟩
      · rw [hargs]
        exact eval_two_ident (m := m) hnu halt hxi hyi
      · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
        show (match [a[i]!, a[j]!] with
          | [Value.bool p, Value.bool q] => q = !p
          | _ => False)
        rw [hib, hjb, h1, h2]
        rfl
    · refine ⟨[a[i]!, a[j]!], ?_, ?_⟩
      · rw [hargs]
        exact eval_two_ident (m := m) hnu halt hxi hyi
      · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
        show (match [a[i]!, a[j]!] with
          | [Value.bool p, Value.bool q] => q = !p
          | _ => False)
        rw [hib, hjb, h1, h2]
        rfl
  · -- bool_and(x, y, z)
    subst hdc'
    obtain ⟨p, q, r, hw, hz, hw2, hpqr⟩ := hsat
    have hib : a[i]! = Value.bool p := bang_of_getElem? hw
    have hjb : a[j]! = Value.bool q := bang_of_getElem? hz
    have hkb : a[k]! = Value.bool r := bang_of_getElem? hw2
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hzi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
        | _ => False)
      rw [hib, hjb, hkb]
      exact hpqr.symm
  · -- bool_or(x, y, z)
    subst hdc'
    obtain ⟨p, q, r, hw, hz, hw2, hpqr⟩ := hsat
    have hib : a[i]! = Value.bool p := bang_of_getElem? hw
    have hjb : a[j]! = Value.bool q := bang_of_getElem? hz
    have hkb : a[k]! = Value.bool r := bang_of_getElem? hw2
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hzi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
        | _ => False)
      rw [hib, hjb, hkb]
      exact hpqr.symm
  · -- int_lin_ne
    subst hdc'
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      have hlen : (slots.map Prod.fst).length = slots.length := by simp
      have halt2 : a.length = (slots.map Prod.fst).length := by
        rw [halt]; exact hlen.symm
      omega
    refine ⟨[.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
      .int b], ?_, ?_⟩
    · rw [hargs]
      exact eval_lin_args (m := m) hnu halt hcoeffs his hin
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show LeanFzn.Semantics.dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b = true
      exact hsat
  · -- bool_clause
    subst hdc'
    have hlen : (slots.map Prod.fst).length = slots.length := by simp
    have hin1 : ∀ i, i ∈ ps → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems1 ps hidx1 i hi
      simp only [List.length_map] at hilt
      omega
    have hin2 : ∀ j, j ∈ ns → j < a.length := by
      intro j hj
      have hilt := linIndices_lt elems2 ns hidx2 j hj
      simp only [List.length_map] at hilt
      omega
    refine ⟨[.array (ps.map (fun i => a[i]!)),
      .array (ns.map (fun j => a[j]!))], ?_, ?_⟩
    · rw [hargs]
      exact eval_two_arrays (m := m) hnu halt hidx1 hidx2 hin1 hin2
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (((ps.map (fun i => a[i]!)).any (fun x => x.eqB (.bool true))) ||
        ((ns.map (fun j => a[j]!)).any (fun y => y.eqB (.bool false)))) = true
      rw [Bool.or_eq_true]
      rcases hsat with hsat | hsat
      · exact Or.inl ((bang_any_eqB_iff_slotIsBoolB hin1).mpr hsat)
      · exact Or.inr ((bang_any_eqB_iff_slotIsBoolB hin2).mpr hsat)
  · -- array_bool_and
    subst hdc'
    have hlen : (slots.map Prod.fst).length = slots.length := by simp
    have hin : ∀ i, i ∈ is → i < a.length := by
      intro i hi
      have hilt := linIndices_lt elems is his i hi
      simp only [List.length_map] at hilt
      omega
    have hkb : a[k]! = Value.bool (is.all (fun i => slotIsBoolB a i true)) :=
      bang_of_getElem? hsat
    refine ⟨[.array (is.map (fun i => a[i]!)), a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_arr_ident (m := m) hnu halt his hr hin
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [Value.array (is.map (fun i => a[i]!)), a[k]!] with
        | [Value.array xs, Value.bool r] =>
            r = (xs.all fun x => x.eqB (Value.bool true))
        | _ => False)
      rw [hkb]
      show (is.all fun i => slotIsBoolB a i true)
          = ((is.map fun i => a[i]!).all fun x => x.eqB (Value.bool true))
      rw [List.all_map]
      exact (Bool.eq_iff_iff.mpr
        (bang_all_eqB_iff_slotIsBoolB (b := true) hin)).symm
  · -- bool2int
    subst hdc'
    obtain ⟨p, hb, hka⟩ := hsat
    have hib : a[i]! = Value.bool p := bang_of_getElem? hb
    have hkb : a[k]! = Value.int (if p then 1 else 0) := bang_of_getElem? hka
    refine ⟨[a[i]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_two_ident (m := m) hnu halt hxi hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[k]!] with
        | [Value.bool b, Value.int j] => j = (if b then 1 else 0)
        | _ => False)
      rw [hib, hkb]
  · -- bool_eq
    subst hdc'
    obtain ⟨p, q, hb, hc, hpq⟩ := hsat
    have hib : a[i]! = Value.bool p := bang_of_getElem? hb
    have hjb : a[j]! = Value.bool q := bang_of_getElem? hc
    refine ⟨[a[i]!, a[j]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_two_ident (m := m) hnu halt hxi hyi
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!] with
        | [Value.bool p, Value.bool q] => p = q
        | _ => False)
      rw [hib, hjb]
      exact hpq
  · -- array_int_element on a constant integer array
    subst hdc'
    obtain ⟨idx, e, hi, hk, hget⟩ := hsat
    have hib : a[i]! = Value.int idx := bang_of_getElem? hi
    have hkb : a[k]! = Value.int e := bang_of_getElem? hk
    refine ⟨[a[i]!, .array (xs.map Value.int), a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_arr_lits (m := m) hnu halt hxi hyk hxs
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, Value.array (xs.map Value.int), a[k]!] with
        | [Value.int i, Value.array ys, Value.int e] =>
            valuesGet1 ys i = some (.int e)
        | _ => False)
      rw [hib, hkb]
      exact hget
  · -- array_var_int_element on an explicit slot array
    subst hdc'
    obtain ⟨idx, e, hi, hk, hall, hget⟩ := hsat
    have hib : a[i]! = Value.int idx := bang_of_getElem? hi
    have hkb : a[k]! = Value.int e := bang_of_getElem? hk
    have hin : ∀ j, j ∈ is → j < a.length := by
      intro j hj
      obtain ⟨v, hv⟩ := hall j hj
      exact (List.getElem?_eq_some_iff.mp hv).choose
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_arr_ident (m := m) hnu halt hxi hyk his hin
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, Value.array (is.map (fun j => a[j]!)), a[k]!] with
        | [Value.int i, Value.array ys, Value.int e] =>
            valuesGet1 ys i = some (.int e)
        | _ => False)
      rw [hib, hkb]
      exact hget
  · -- array_var_bool_element on an explicit slot array
    subst hdc'
    obtain ⟨idx, e, hi, hk, hall, hget⟩ := hsat
    have hib : a[i]! = Value.int idx := bang_of_getElem? hi
    have hkb : a[k]! = Value.bool e := bang_of_getElem? hk
    have hin : ∀ j, j ∈ is → j < a.length := by
      intro j hj
      obtain ⟨v, hv⟩ := hall j hj
      exact (List.getElem?_eq_some_iff.mp hv).choose
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_arr_ident (m := m) hnu halt hxi hyk his hin
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, Value.array (is.map (fun j => a[j]!)), a[k]!] with
        | [Value.int i, Value.array ys, Value.bool e] =>
            valuesGet1 ys i = some (.bool e)
        | _ => False)
      rw [hib, hkb]
      exact hget
  · -- int_eq_reif(x, y, r): the reification slot agrees with equality
    subst hdc'
    obtain ⟨p, q, rb, hi, hj, hr, hiff⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hi
    have hjb : a[j]! = Value.int q := bang_of_getElem? hj
    have hkb : a[k]! = Value.bool rb := bang_of_getElem? hr
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hrk
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.int a, Value.int b, Value.bool rb] =>
            (rb = true ∧ a = b) ∨ (rb = false ∧ a ≠ b)
        | _ => False)
      rw [hib, hjb, hkb]
      exact (reif_disj_iff (p = q) rb).mpr hiff
  · -- int_le_reif(x, y, r): the reification slot agrees with ≤
    subst hdc'
    obtain ⟨p, q, rb, hi, hj, hr, hiff⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hi
    have hjb : a[j]! = Value.int q := bang_of_getElem? hj
    have hkb : a[k]! = Value.bool rb := bang_of_getElem? hr
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hrk
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.int a, Value.int b, Value.bool rb] =>
            (rb = true ∧ a ≤ b) ∨ (rb = false ∧ a > b)
        | _ => False)
      rw [hib, hjb, hkb]
      rcases (reif_disj_iff (p ≤ q) rb).mpr hiff with
        ⟨hrb, hle⟩ | ⟨hrb, hnle⟩
      · exact Or.inl ⟨hrb, hle⟩
      · exact Or.inr ⟨hrb, by omega⟩
  · -- int_ne_reif(x, y, r): the reification slot agrees with ≠
    subst hdc'
    obtain ⟨p, q, rb, hi, hj, hr, hiff⟩ := hsat
    have hib : a[i]! = Value.int p := bang_of_getElem? hi
    have hjb : a[j]! = Value.int q := bang_of_getElem? hj
    have hkb : a[k]! = Value.bool rb := bang_of_getElem? hr
    refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_three_ident (m := m) hnu halt hxi hyi hrk
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[i]!, a[j]!, a[k]!] with
        | [Value.int a, Value.int b, Value.bool rb] =>
            (rb = true ∧ a ≠ b) ∨ (rb = false ∧ a = b)
        | _ => False)
      rw [hib, hjb, hkb]
      rcases (reif_disj_iff (p ≠ q) rb).mpr hiff with
        ⟨hrb, hne⟩ | ⟨hrb, hnne⟩
      · exact Or.inl ⟨hrb, hne⟩
      · exact Or.inr ⟨hrb,
          Decidable.byContradiction (fun hne => hnne hne)⟩
  · -- int_lin_eq_reif(coeffs, xs, b, r)
    subst hdc'
    obtain ⟨rb, hk, hiff⟩ := hsat
    have hkb : a[k]! = Value.bool rb := bang_of_getElem? hk
    refine ⟨[.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
      .int b, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_lin_reif_args (m := m) hnu halt hcoeffs his
        (by
          intro i hi
          have hilt := linIndices_lt elems is his i hi
          have hlen : (slots.map Prod.fst).length = slots.length := by simp
          have halt2 : a.length = (slots.map Prod.fst).length := by
            rw [halt]; exact hlen.symm
          omega) hrk
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [.array (intVals coeffs),
          .array (is.map (fun i => a[i]!)), .int b, a[k]!] with
        | [Value.array as_, Value.array xs, Value.int b', Value.bool rb'] =>
            (rb' = true ∧ dotProduct as_ xs = some b') ∨
              (rb' = false ∧ dotProduct as_ xs ≠ some b')
        | _ => False)
      rw [hkb]
      exact (reif_disj_iff (dotProduct (intVals coeffs)
        (is.map (fun i => a[i]!)) = some b) rb).mpr hiff
  · -- int_lin_le_reif(coeffs, xs, b, r)
    subst hdc'
    obtain ⟨rb, hk, hiff⟩ := hsat
    have hkb : a[k]! = Value.bool rb := bang_of_getElem? hk
    refine ⟨[.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
      .int b, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_lin_reif_args (m := m) hnu halt hcoeffs his
        (by
          intro i hi
          have hilt := linIndices_lt elems is his i hi
          have hlen : (slots.map Prod.fst).length = slots.length := by simp
          have halt2 : a.length = (slots.map Prod.fst).length := by
            rw [halt]; exact hlen.symm
          omega) hrk
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [.array (intVals coeffs),
          .array (is.map (fun i => a[i]!)), .int b, a[k]!] with
        | [Value.array as_, Value.array xs, Value.int b', Value.bool rb'] =>
            (rb' = true ∧ dotLe as_ xs b' = true) ∨
              (rb' = false ∧ dotLe as_ xs b' = false)
        | _ => False)
      rw [hkb]
      rcases (reif_disj_iff (dotLe (intVals coeffs)
        (is.map (fun i => a[i]!)) b = true) rb).mpr hiff with
        ⟨hrb, hle⟩ | ⟨hrb, hnle⟩
      · exact Or.inl ⟨hrb, hle⟩
      · refine Or.inr ⟨hrb, ?_⟩
        cases hd2 : dotLe (intVals coeffs) (is.map (fun i => a[i]!)) b with
        | false => rfl
        | true => exact absurd hd2 hnle
  · -- int_lin_ne_reif(coeffs, xs, b, r)
    subst hdc'
    obtain ⟨rb, hk, hiff⟩ := hsat
    have hkb : a[k]! = Value.bool rb := bang_of_getElem? hk
    refine ⟨[.array (intVals coeffs), .array (is.map (fun i => a[i]!)),
      .int b, a[k]!], ?_, ?_⟩
    · rw [hargs]
      exact eval_lin_reif_args (m := m) hnu halt hcoeffs his
        (by
          intro i hi
          have hilt := linIndices_lt elems is his i hi
          have hlen : (slots.map Prod.fst).length = slots.length := by simp
          have halt2 : a.length = (slots.map Prod.fst).length := by
            rw [halt]; exact hlen.symm
          omega) hrk
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [.array (intVals coeffs),
          .array (is.map (fun i => a[i]!)), .int b, a[k]!] with
        | [Value.array as_, Value.array xs, Value.int b', Value.bool rb'] =>
            (rb' = true ∧ dotNe as_ xs b' = true) ∨
              (rb' = false ∧ dotNe as_ xs b' = false)
        | _ => False)
      rw [hkb]
      rcases (reif_disj_iff (dotNe (intVals coeffs)
        (is.map (fun i => a[i]!)) b = true) rb).mpr hiff with
        ⟨hrb, hne⟩ | ⟨hrb, hnne⟩
      · exact Or.inl ⟨hrb, hne⟩
      · refine Or.inr ⟨hrb, ?_⟩
        cases hd2 : dotNe (intVals coeffs) (is.map (fun i => a[i]!)) b with
        | false => rfl
        | true => exact absurd hd2 hnne
  · -- int_min in the general two-operand shape
    subst hdc'
    obtain ⟨p, q, hp, hq, hr⟩ := hsat
    refine ⟨[DomIntArg.read a o₀, DomIntArg.read a o₁, DomIntArg.read a o₂],
      ?_, ?_⟩
    · rw [hargs]
      exact eval_three_basic (m := m) (dcs := dcs) hnu halt ho₀ ho₁ ho₂
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [DomIntArg.read a o₀, DomIntArg.read a o₁,
          DomIntArg.read a o₂] with
        | [Value.int p', Value.int q', Value.int w] => w = min p' q'
        | _ => False)
      rw [hp, hq, hr]
  · -- int_max in the general two-operand shape
    subst hdc'
    obtain ⟨p, q, hp, hq, hr⟩ := hsat
    refine ⟨[DomIntArg.read a o₀, DomIntArg.read a o₁, DomIntArg.read a o₂],
      ?_, ?_⟩
    · rw [hargs]
      exact eval_three_basic (m := m) (dcs := dcs) hnu halt ho₀ ho₁ ho₂
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [DomIntArg.read a o₀, DomIntArg.read a o₁,
          DomIntArg.read a o₂] with
        | [Value.int p', Value.int q', Value.int w] => w = max p' q'
        | _ => False)
      rw [hp, hq, hr]
  · -- int_div in the general shape
    subst hdc'
    obtain ⟨p, q, hp, hq, hq0, hr⟩ := hsat
    refine ⟨[DomIntArg.read a o₀, DomIntArg.read a o₁, DomIntArg.read a o₂],
      ?_, ?_⟩
    · rw [hargs]
      exact eval_three_basic (m := m) (dcs := dcs) hnu halt ho₀ ho₁ ho₂
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [DomIntArg.read a o₀, DomIntArg.read a o₁,
          DomIntArg.read a o₂] with
        | [Value.int p', Value.int q', Value.int w] => q' ≠ 0 ∧ w = Int.tdiv p' q'
        | _ => False)
      rw [hp, hq, hr]
      exact ⟨hq0, rfl⟩
  · -- int_mod in the general shape
    subst hdc'
    obtain ⟨p, q, hp, hq, hq0, hr⟩ := hsat
    refine ⟨[DomIntArg.read a o₀, DomIntArg.read a o₁, DomIntArg.read a o₂],
      ?_, ?_⟩
    · rw [hargs]
      exact eval_three_basic (m := m) (dcs := dcs) hnu halt ho₀ ho₁ ho₂
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [DomIntArg.read a o₀, DomIntArg.read a o₁,
          DomIntArg.read a o₂] with
        | [Value.int p', Value.int q', Value.int w] => q' ≠ 0 ∧ w = Int.tmod p' q'
        | _ => False)
      rw [hp, hq, hr]
      exact ⟨hq0, rfl⟩
  · -- array_int_maximum
    subst hdc'
    obtain ⟨mv, hm, hmax⟩ := hsat
    rw [DomIntArg.read_slot a k] at hm
    have hmax' : maxValue (is.map (fun i => a[i]!)) = some mv := by
      rw [← hmax, List.map_map]
      rfl
    refine ⟨[a[k]!, .array (is.map (fun i => a[i]!))], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_slot_array (m := m) (dcs := dcs) hnu halt hk his
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[k]!, .array (is.map (fun i => a[i]!))] with
        | [Value.int m', Value.array xs] => maxValue xs = some m'
        | _ => False)
      rw [hm]
      exact hmax'
  · -- array_int_minimum
    subst hdc'
    obtain ⟨mv, hm, hmin⟩ := hsat
    rw [DomIntArg.read_slot a k] at hm
    have hmin' : minValue (is.map (fun i => a[i]!)) = some mv := by
      rw [← hmin, List.map_map]
      rfl
    refine ⟨[a[k]!, .array (is.map (fun i => a[i]!))], ?_, ?_⟩
    · rw [hargs]
      exact eval_ident_slot_array (m := m) (dcs := dcs) hnu halt hk his
    · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
      show (match [a[k]!, .array (is.map (fun i => a[i]!))] with
        | [Value.int m', Value.array xs] => minValue xs = some m'
        | _ => False)
      rw [hm]
      exact hmin'


/-! ## The slot/typing chain (the int-reads premises) -/

/-- A successful lookup finds a same-named key. -/
theorem lookupIdent_inv_mem {β : Type} (x : Ident) (l : List (Ident × β))
    (v : β) (h : lookupIdent x l = some v) :
    ∃ y, (y, v) ∈ l ∧ y.name = x.name := by
  induction l with
  | nil => simp [lookupIdent] at h
  | cons ab rest ih =>
      simp only [lookupIdent] at h
      by_cases hab : x.name = ab.1.name
      · rw [if_pos hab] at h
        have hvv : ab.2 = v := (Option.some.inj h)
        subst hvv
        exact ⟨ab.1, List.mem_cons_self, hab.symm⟩
      · rw [if_neg hab] at h
        obtain ⟨y, hy, hname⟩ := ih h
        exact ⟨y, by simp [hy], hname⟩

/-- A slot list comes from the variable declarations: every slot pair
    was produced by `declSlot` of some variable.  Stated for every
    slot list (generalized induction, so the tail case can instantiate
    the hypothesis at the tail's slots). -/
theorem declSlots_mem : ∀ (vars : List VarDeclItem)
    (slots : List (String × List Value)),
    declSlots vars = .ok slots →
    ∀ p ∈ slots, ∃ d ∈ vars, declSlot d = .ok (some p) := by
  intro vars
  induction vars with
  | nil =>
      intro slots h
      simp only [declSlots] at h
      have hnil : slots = [] := (Except.ok.inj h).symm
      subst hnil
      intro p hp
      cases hp
  | cons d rest ih =>
      intro slots h
      unfold declSlots at h
      match hd : declSlot d with
      | .error e => rw [hd] at h; simp at h
      | .ok none =>
          rw [hd] at h
          intro p hp
          obtain ⟨d', hd', hdslot⟩ := ih slots h p hp
          refine ⟨d', ?_, hdslot⟩
          simp only [List.mem_cons]
          exact Or.inr hd'
      | .ok (some p0) =>
          rw [hd] at h
          match hrest : declSlots rest with
          | .error e =>
              rw [hrest] at h
              exact absurd h (by simp [Except.map])
          | .ok restslots =>
              rw [hrest] at h
              have hmapstep : (Except.ok restslots : Except String
                  (List (String × List Value))).map
                  (fun s => p0 :: s) = .ok slots := h
              have hmapred : (Except.ok restslots : Except String
                  (List (String × List Value))).map
                  (fun s => p0 :: s) = .ok (p0 :: restslots) := rfl
              rw [hmapred] at hmapstep
              have hmap : (p0 :: restslots) = slots := Except.ok.inj hmapstep
              rw [← hmap]
              intro p hp
              rcases List.mem_cons.mp hp with rfl | htl
              · refine ⟨d, ?_, hd⟩
                simp only [List.mem_cons]
                exact Or.inl trivial
              · obtain ⟨d', hd', hdslot⟩ :=
                  ih restslots hrest p htl
                refine ⟨d', ?_, hdslot⟩
                simp only [List.mem_cons]
                exact Or.inr hd'

/-- `declSlot` of an initializer-free basic variable has that variable's
    name and its extracted domain's values. -/
theorem declSlot_basic_inv {ty : BasicVarType} {n : Ident}
    {anns : List Annotation} {p : String × List Value}
    (h : declSlot (.basic ty n anns none) = .ok (some p)) :
    ∃ dom, varDomain ty = .ok dom ∧ p = (n.name, dom.values) := by
  simp only [declSlot] at h
  by_cases harr : n.name == "array1d"
  · rw [if_pos harr] at h
    exact absurd h (by simp)
  · rw [if_neg harr] at h
    match hdom : varDomain ty with
    | .error e => rw [hdom] at h; exact absurd h (by simp)
    | .ok dom =>
        rw [hdom] at h
        have hpair : (n.name, dom.values) = p := Option.some.inj (Except.ok.inj h)
        exact ⟨dom, rfl, hpair.symm⟩

/-- An integer-based variable type with a successful domain extraction
    yields an integer domain (unbounded `var int` is rejected). -/
theorem varDomain_int_of_base {ty : BasicVarType} {dom : VarDomain}
    (h : varDomain ty = .ok dom) (hbase : ty.base = .int) :
    ∃ xs, dom = .intDom xs := by
  cases ty with
  | par t =>
      cases t with
      | bool => rw [BasicVarType.base] at hbase; exact absurd hbase (by intro h2; cases h2)
      | int =>
          simp only [varDomain] at h
          simp at h
      | setOfInt => rw [BasicVarType.base] at hbase; exact absurd hbase (by intro h2; cases h2)
  | intRange lo hi =>
      exact ⟨_, by simpa using (Except.ok.inj h).symm⟩
  | intSet xs =>
      exact ⟨_, by simpa using (Except.ok.inj h).symm⟩
  | setOfIntRange lo hi => simp [BasicVarType.base] at hbase
  | setOfIntSet xs => simp [BasicVarType.base] at hbase

/-- Every value of an extracted integer domain is an integer. -/
theorem intDom_values_int {xs : List Int} :
    ∀ v ∈ (VarDomain.intDom xs).values, ∃ p, v = Value.int p := by
  intro v hv
  simp only [VarDomain.values, List.mem_map] at hv
  obtain ⟨p, _, rfl⟩ := hv
  exact ⟨p, rfl⟩

/-- The slot-list inversion of `slotsChecked`: a successful slot
    extraction comes from the declarations.  (With the leaves cap
    removed, `slotsChecked` is exactly `declSlots`.) -/
theorem declSlots_of_slotsChecked {m : Model}
    {slots : List (String × List Value)}
    (h : slotsChecked m = .ok slots) :
    declSlots m.variables = .ok slots := by
  exact h

/-- The second half of a distinct concatenation is itself
    distinct. -/
theorem nodup_of_append_right {α : Type} {l1 l2 : List α}
    (h : (l1 ++ l2).Nodup) : l2.Nodup := by
  induction l1 with
  | nil => simpa using h
  | cons a rest ih =>
      have hnucons : (a :: (rest ++ l2)).Nodup := h
      exact ih (List.nodup_cons.mp hnucons).2

/-- A value in both halves of a concatenation contradicts the
    concatenation's distinctness. -/
theorem nodup_append_mem_mem_false {α : Type} {l1 l2 : List α} {x : α}
    (h1 : x ∈ l1) (h2 : x ∈ l2) (hnu : (l1 ++ l2).Nodup) : False := by
  induction l1 with
  | nil => cases h1
  | cons a rest ih =>
      have hnucons : (a :: (rest ++ l2)).Nodup := hnu
      obtain ⟨hhead, htail⟩ := List.nodup_cons.mp hnucons
      rcases List.mem_cons.mp h1 with rfl | htl
      · exact hhead (List.mem_append.mpr (Or.inr h2))
      · exact ih htl htail

/-- The static environment resolves a slot position's name to its
    variable's declared type: parameters cannot shadow variable names
    in a well-formed model, and the variable names are distinct. -/
theorem staticEnv_of_slot {m : Model}
    {slots : List (String × List Value)} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hilt : i < slots.length) :
    ∃ d ∈ m.variables, declSlot d = .ok (some slots[i]!) ∧
      m.staticEnv (Ident.mk slots[i]!.1) = some (d.type, true) := by
  have hdecls := declSlots_of_slotsChecked hslot
  have hmemslot : slots[i]! ∈ slots := by
    rw [show slots[i]! = slots[i] from by
      rw [List.getElem!_eq_getElem?_getD,
        List.getElem?_eq_getElem hilt]
      rfl]
    exact List.getElem_mem hilt
  obtain ⟨d, hd, hdslot⟩ := declSlots_mem m.variables slots hdecls slots[i]!
    hmemslot
  refine ⟨d, hd, hdslot, ?_⟩
  -- d must be an initializer-free basic variable (declSlot shape)
  obtain ⟨ty, n, anns, hshape⟩ : ∃ ty n anns, d = .basic ty n anns none := by
    match hs : declSlot d with
    | .error e => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok none => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok (some p) =>
        cases d with
        | basic ty n anns opt2 =>
            cases opt2 with
            | none => exact ⟨ty, n, anns, rfl⟩
            | some e =>
                rw [hs] at *
                exact absurd hdslot (by simp [declSlot])
        | array ty n anns vs =>
            rw [hs] at *
            exact absurd hdslot (by simp [declSlot])
  subst hshape
  -- the slot name is the variable's name
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  have hname1 : slots[i]!.1 = n.name := by
    have hslotpair : slots[i]! = (n.name, dom.values) := by rw [← hpair]
    have : slots[i]!.1 = (n.name, dom.values).1 := by
      rw [hslotpair]
    exact this
  -- parameters cannot carry this name (well-formed value namespace)
  have hnu := hwf.valueNamesUnique
  have hparamnone : lookupIdent n
      (m.parameters.map (fun d => (d.name, (d.type, false)))) = none := by
    by_cases hlk : lookupIdent n
        (m.parameters.map (fun d => (d.name, (d.type, false)))) = none
    · exact hlk
    · exfalso
      -- the lookup succeeds for some info (Option dichotomy)
      obtain ⟨info, hinfo⟩ :
          ∃ info, lookupIdent n
            (m.parameters.map (fun d => (d.name, (d.type, false))))
              = some info := by
        cases hlk2 : lookupIdent n
            (m.parameters.map (fun d => (d.name, (d.type, false)))) with
        | none => exact absurd hlk2 hlk
        | some info => exact ⟨info, rfl⟩
      obtain ⟨y, hy, hyname⟩ :=
        lookupIdent_inv_mem n _ info hinfo
      obtain ⟨d2, hd2, hdy⟩ := List.mem_map.mp hy
      have hyd2 : y = d2.name := by
        injection hdy with h1
        exact h1.symm
      -- d2.name = n (same name), so d2.name is ALSO the variable d's
      -- name: both halves of the concatenated namespace contain it,
      -- contradicting Nodup
      have hd2n : d2.name = n := by
        apply ident_eq_of_name
        rw [← hyd2]
        exact hyname
      have hmempar : d2.name ∈ m.parameters.map (fun d => d.name) :=
        List.mem_map_of_mem hd2
      have hmemvar : d2.name ∈ m.variables.map (fun d => d.name) := by
        have hnmem : n ∈ m.variables.map (fun d => d.name) :=
          List.mem_map_of_mem hd
        rw [hd2n]
        exact hnmem
      -- the append-nodup duplicate contradiction
      exact nodup_append_mem_mem_false hmempar hmemvar hnu
  -- the static environment: the parameter lookup misses; the variable
  -- lookup finds the first same-named variable, which is d itself
  rw [show (Ident.mk slots[i]!.1) = n from ident_eq_of_name hname1]
  show (match lookupIdent n
      (m.parameters.map (fun d => (d.name, (d.type, false)))) with
    | some info => some info
    | none => lookupIdent n
        (m.variables.map (fun d => (d.name, (d.type, true)))))
      = some ((VarDeclItem.basic ty n anns none).type, true)
  rw [hparamnone]
  -- the variable lookup: the FIRST same-named entry is d's own, by
  -- `lookupIdent_of_mem` at d's own entry under the variables' name
  -- distinctness (the second half of the value namespace)
  have hpairmap : (m.variables.map (fun d => (d.name, (d.type, true)))).map
      Prod.fst = m.variables.map (fun d => d.name) := by
    induction m.variables with
    | nil => rfl
    | cons v rest ih =>
        rw [List.map_cons, List.map_cons, ih]
        rfl
  have hvarnu : ((m.variables.map
      (fun d => (d.name, (d.type, true)))).map Prod.fst).Nodup := by
    rw [hpairmap]
    exact nodup_of_append_right hnu
  have hdentry : (n, ((VarDeclItem.basic ty n anns none).type, true)) ∈
      m.variables.map (fun d => (d.name, (d.type, true))) :=
    List.mem_map_of_mem hd
  exact lookupIdent_of_mem (x := n)
    (v := ((VarDeclItem.basic ty n anns none).type, true))
    (l := m.variables.map (fun d => (d.name, (d.type, true)))) hvarnu hdentry

/-! ## The converse for the compile-only fallback shapes -/
/-! ## Coverage for the compile-only fallback shapes (store → assignment) -/

/-- Inversion of `int_gt` with an identifier and a literal: the store's
    value at the name is an integer strictly above the literal. -/
theorem holds_int_gt_const {store : Store} {c : ConstraintItem}
    {x : Ident} {k : Int}
    (hname : c.name.name = "int_gt")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ k < p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, hsx, hargsv⟩ := mapM_two_const hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_gt") [vx, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide : ¬ "int_gt" ∈ globalsNames)] at h1
  have hmatch : (match [vx, .int k] with
    | [.int a, .int b] => a > b
    | _ => False) := h1
  cases vx with
  | int p => exact ⟨p, hsx, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `int_gt` with a literal and an identifier. -/
theorem holds_int_gt_const' {store : Store} {c : ConstraintItem}
    {y : Ident} {k : Int}
    (hname : c.name.name = "int_gt")
    (hargs : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k > p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vy, hsy, hargsv⟩ := mapM_two_const' hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_gt") [.int k, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide : ¬ "int_gt" ∈ globalsNames)] at h1
  have hmatch : (match [.int k, vy] with
    | [.int a, .int b] => a > b
    | _ => False) := h1
  cases vy with
  | int q => exact ⟨q, hsy, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `int_ge` with an identifier and a literal. -/
theorem holds_int_ge_const {store : Store} {c : ConstraintItem}
    {x : Ident} {k : Int}
    (hname : c.name.name = "int_ge")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ k ≤ p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vx, hsx, hargsv⟩ := mapM_two_const hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_ge") [vx, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide : ¬ "int_ge" ∈ globalsNames)] at h1
  have hmatch : (match [vx, .int k] with
    | [.int a, .int b] => a ≥ b
    | _ => False) := h1
  cases vx with
  | int p => exact ⟨p, hsx, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-- Inversion of `int_ge` with a literal and an identifier. -/
theorem holds_int_ge_const' {store : Store} {c : ConstraintItem}
    {y : Ident} {k : Int}
    (hname : c.name.name = "int_ge")
    (hargs : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident y)])
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k ≥ p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  obtain ⟨vy, hsy, hargsv⟩ := mapM_two_const' hargs hmap
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_ge") [.int k, vy] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide : ¬ "int_ge" ∈ globalsNames)] at h1
  have hmatch : (match [.int k, vy] with
    | [.int a, .int b] => a ≥ b
    | _ => False) := h1
  cases vy with
  | int q => exact ⟨q, hsy, by simpa using hmatch⟩
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)


/-- A fitting assignment is in the candidate space (the bridge the
    UNSAT coverage direction needs). -/
theorem fits_mem_allAssigns : ∀ (doms : List (List Value))
    (a : List Value), Solver.Core.Assignment.Fits doms a →
    a ∈ allAssigns doms := by
  intro doms
  induction doms with
  | nil =>
      intro a h
      obtain ⟨hlen, _⟩ := h
      cases a with
      | nil => exact List.mem_singleton_self []
      | cons x xs =>
          have : (x :: xs).length = [].length := hlen
          simp at this
  | cons d rest ih =>
      intro a h
      obtain ⟨hlen, hmem⟩ := h
      cases ha : a with
      | nil =>
          rw [ha] at hlen
          simp at hlen
      | cons x xs =>
          have hxmem : x ∈ d := by
            have := hmem 0 x (by rw [ha]; rfl)
            exact this
          have hrest : Solver.Core.Assignment.Fits rest xs := by
            refine ⟨?_, ?_⟩
            · rw [ha] at hlen
              simp only [List.length_cons] at hlen
              omega
            · intro slot value hval
              have hread : a[slot + 1]? = some value := by
                rw [ha]
                exact hval
              have hval2 := hmem (slot + 1) value hread
              rw [show (d :: rest).getD (slot + 1) [] = rest.getD slot []
                from rfl] at hval2
              exact hval2
          have hrec : xs ∈ allAssigns rest := ih xs hrest
          cases hd : d with
          | nil =>
              rw [hd] at hxmem
              exact absurd hxmem (by simp)
          | cons v vs =>
              have heq : x ∈ (v :: vs) := by rw [← hd]; exact hxmem
              have hmemiff : (x :: xs) ∈ allAssigns ((v :: vs) :: rest) ↔
                  ∃ w ∈ (v :: vs), ∃ a' ∈ allAssigns rest, (x :: xs) = w :: a' :=
                mem_allAssigns_singleton v vs rest (x :: xs)
              rw [hmemiff]
              exact ⟨x, heq, xs, hrec, rfl⟩



/-! ## The compile linkers (per-constraint dispatch, both directions) -/

/-- Inversion of `declSlots`'s cons step: a mapped slot list is the
    head pair consed onto the tail's slots. -/
theorem declSlots_map_ok_inv {p : String × List Value}
    {rest : List VarDeclItem} {slots : List (String × List Value)}
    (h : (declSlots rest).map (fun s => p :: s) = .ok slots) :
    ∃ restslots, declSlots rest = .ok restslots ∧ slots = p :: restslots := by
  cases hrest : declSlots rest with
  | error e =>
      rw [hrest] at h
      have herr : (Except.error e).map (fun s => p :: s)
          = @Except.error String (List (String × List Value)) e := rfl
      rw [herr] at h
      exact absurd h (by simp)
  | ok restslots =>
      have hstep : (declSlots rest).map (fun s => p :: s)
          = @Except.ok String (List (String × List Value))
              (p :: restslots) := by
        rw [hrest]
        rfl
      rw [hstep] at h
      exact ⟨restslots, rfl, (Except.ok.inj h).symm⟩

/-- The slot names of a successful extraction are distinct: each slot
    carries a distinct variable's name (the variables' names are
    pairwise distinct in a well-formed model). -/
theorem slot_name_eq_var : ∀ (d : VarDeclItem) (p : String × List Value),
    declSlot d = .ok (some p) → p.1 = d.name.name := by
  intro d p h
  cases d with
  | basic ty n anns opt =>
      cases opt with
      | none =>
          simp only [declSlot] at h
          by_cases harr : n.name == "array1d"
          · rw [if_pos harr] at h; exact absurd h (by simp)
          · rw [if_neg harr] at h
            cases hdom : varDomain ty with
            | error e => rw [hdom] at h; exact absurd h (by simp)
            | ok dom =>
                rw [hdom] at h
                have hp : p = (n.name, dom.values) := by
                  injection h with h1
                  injection h1 with h2
                  exact h2.symm
                rw [hp]
                rfl
      | some e => simp only [declSlot] at h; simp at h
  | array ty n anns vs => simp only [declSlot] at h; simp at h

/-- The slot names of a successful extraction are distinct in a
    well-formed model (each slot carries a distinct variable's
    name). -/
theorem slotNames_nodup {m : Model}
    {slots : List (String × List Value)}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots) :
    (slots.map Prod.fst).Nodup := by
  -- the slot list comes from declSlots over the variables
  -- (with the leaves cap removed, slotsChecked IS declSlots)
  have hdecls : declSlots m.variables = .ok slots := hslot
  -- the variables' names are pairwise distinct: names are preserved
  -- pairwise-distinct under the injective name projection
  have hnu : (m.variables.map (fun d => d.name.name)).Nodup := by
    have hvars : (m.variables.map VarDeclItem.name).Nodup :=
      hwf.valueNamesUnique.sublist
        (List.IsSuffix.sublist (List.suffix_append
          (m.parameters.map ParDeclItem.name)
          (m.variables.map VarDeclItem.name)))
    have main : ∀ (l : List VarDeclItem),
        (l.map VarDeclItem.name).Nodup →
        (l.map (fun d => d.name.name)).Nodup := by
      intro l
      induction l with
      | nil => intro _; simp
      | cons d ds ih =>
          intro hnod
          rw [List.map_cons] at hnod
          rw [List.map_cons, List.nodup_cons]
          obtain ⟨hdnot, hdsnod⟩ := List.nodup_cons.mp hnod
          refine ⟨?_, ih hdsnod⟩
          intro hmem
          rw [List.mem_map] at hmem
          obtain ⟨d', hd'mem, hd'name⟩ := hmem
          apply hdnot
          rw [List.mem_map]
          refine ⟨d', hd'mem, ?_⟩
          simp only [VarDeclItem.name] at hd'name ⊢
          exact Ident.eq_of_name_eq hd'name
    exact main m.variables hvars
  -- induction over the variables threading the slot equation
  have main : ∀ (vars : List VarDeclItem)
      (slots2 : List (String × List Value)),
      declSlots vars = .ok slots2 →
      (vars.map (fun d => d.name.name)).Nodup →
      (slots2.map Prod.fst).Nodup := by
    intro vars
    induction vars with
    | nil =>
        intro slots2 h _
        rw [declSlots] at h
        have hnil : slots2 = [] := (Except.ok.inj h).symm
        subst hnil
        simp
    | cons d rest ih =>
        intro slots2 h hnuvars
        rw [declSlots] at h
        rw [List.map_cons, List.nodup_cons] at hnuvars
        obtain ⟨hdnot, hrestnu⟩ := hnuvars
        match hds : declSlot d with
        | .error e => rw [hds] at h; exact absurd h (by simp)
        | .ok none =>
            rw [hds] at h
            exact ih slots2 h hrestnu
        | .ok (some p) =>
            rw [hds] at h
            obtain ⟨restslots, hrest, hcons⟩ := declSlots_map_ok_inv h
            subst hcons
            rw [List.map_cons, List.nodup_cons]
            refine ⟨?_, ih restslots hrest hrestnu⟩
            -- p.1 is not among restslots' names: p.1 is d's name, and
            -- every restslot name is some rest variable's name
            intro hmem
            have hp1 : p.1 = d.name.name := slot_name_eq_var d p hds
            have hnamesof : d.name.name ∈ restslots.map Prod.fst := by
              rw [← hp1]; exact hmem
            have hex : ∃ p' ∈ restslots, p'.1 = d.name.name := by
              rw [List.mem_map] at hnamesof
              obtain ⟨p', hp'mem, hp'fst⟩ := hnamesof
              exact ⟨p', hp'mem, hp'fst⟩
            obtain ⟨p', hp'mem, hp'name⟩ := hex
            have hfrom := declSlots_mem rest restslots hrest
            obtain ⟨d', hd'mem, hdslot'⟩ := hfrom p' hp'mem
            have hd'name : p'.1 = d'.name.name :=
              slot_name_eq_var d' p' hdslot'
            apply hdnot
            rw [List.mem_map]
            refine ⟨d', hd'mem, ?_⟩
            exact hd'name.symm.trans hp'name
  exact main m.variables slots hdecls hnu


/-! ## The int-reads derivation (the typing chain's payoff) -/

/-- The bang read of a mapped list is the mapped bang read (the
    projection pairing used by the slot chain). -/
theorem getElem!_map_fst {slots : List (String × List Value)} (i : Nat) :
    (slots.map Prod.fst)[i]! = slots[i]!.1 := by
  induction slots generalizing i with
  | nil => cases i <;> rfl
  | cons s rest ih =>
      cases i with
      | zero => rfl
      | succ i2 => simp only [List.map_cons, List.getElem!_cons_succ, ih i2]

/-- The bang read equals the plain read in bounds. -/
theorem getElem!_eq_getElem {slots : List (String × List Value)} {i : Nat}
    (hlt : i < slots.length) : slots[i]! = slots[i] := by
  rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem hlt]
  rfl

/-- The `getD` read of the mapped domain list is the slot's own domain
    (the membership bridge between `allAssigns` and slot pairs). -/
theorem getD_map_snd {slots : List (String × List Value)} {i : Nat}
    (hlt : i < slots.length) :
    (slots.map Prod.snd).getD i [] = slots[i].snd := by
  induction slots generalizing i with
  | nil => exact absurd hlt (by simp)
  | cons s rest ih =>
      cases i with
      | zero => rfl
      | succ i2 =>
          have hl2 : i2 < rest.length := by
            simp only [List.length_cons] at hlt
            omega
          simp only [List.map_cons, List.getD_cons_succ]
          rw [ih hl2]
          rfl

/-- The signature `checkArg` premise for an int-typed predicate
    argument that is a slot identifier: the identifier's static type is
    a base `int`. -/
theorem staticEnv_int_of_checkArg {env : StaticEnv} {x : Ident}
    (h : (Expr.basic (.ident x)).checkArg env
        (.basic (.var (.par .int)))) :
    ∃ isVar, env x = some (.base .int, isVar) := by
  simp only [Expr.checkArg, BasicExpr.checkBase] at h
  cases hlk : env x with
  | none => rw [hlk] at h; simp at h
  | some p =>
      obtain ⟨ft, isVar⟩ := p
      rw [show env x = some (ft, isVar) from hlk] at h
      cases ft with
      | base t =>
          have hbase : (BasicVarType.par BasicParType.int).base = t := h.1
          exact ⟨isVar, by rw [← hbase]; rfl⟩
      | array n te => exact absurd h (by simp)

/-- The int-reads premise for the `int_eq`/`int_ne` slot shapes: a
    slot-position read of an assignment is an integer whenever the
    constraint's argument checks against the int-typed signature (the
    full typing chain). -/
theorem int_read_of_checkArg_slot {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType}
    {x : Ident} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hcheck :
      (Expr.basic (.ident x)).checkArg m.staticEnv (.basic (.var (.par .int))))
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns (slots.map Prod.snd)) :
    ∃ p, a[i]! = Value.int p := by
  -- the slot is in bounds
  obtain ⟨hxlt, hxget⟩ :=
    nameIndex_some (slots.map Prod.fst) x.name i hxi
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have hislt : i < slots.length := by omega
  -- the check supplies the int base type for x
  obtain ⟨isVar, henv⟩ := staticEnv_int_of_checkArg hcheck
  -- the slot's variable, with its staticEnv resolution
  obtain ⟨d, hd, hdslot, hstatic⟩ := staticEnv_of_slot hwf hslot hislt
  -- the checked identifier IS the slot's name (both are slots[i].1)
  have hnameilt : i < (slots.map Prod.fst).length := by
    rw [List.length_map]
    omega
  have hnamei : (slots.map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt hxget
  have hxslot : slots[i]!.1 = x.name := by
    rw [show slots[i]!.1 = (slots.map Prod.fst)[i]! from
      (getElem!_map_fst i).symm]
    exact hnamei
  have hstaticx : m.staticEnv x = some (d.type, true) := by
    have hxmk : x = Ident.mk slots[i]!.1 := by
      obtain ⟨s⟩ := x
      apply ident_eq_of_name
      rw [hxslot]
    rw [hxmk]
    exact hstatic
  -- both resolutions describe the same staticEnv value: the type is int
  obtain ⟨ty, n, anns, hdshape⟩ : ∃ ty n anns,
      d = .basic ty n anns none := by
    match hs : declSlot d with
    | .error e => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok none => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok (some p) =>
        cases d with
        | basic ty n anns opt2 =>
            cases opt2 with
            | none => exact ⟨ty, n, anns, rfl⟩
            | some e => rw [hs] at *; exact absurd hdslot (by simp [declSlot])
        | array ty n anns vs =>
            rw [hs] at *; exact absurd hdslot (by simp [declSlot])
  subst hdshape
  -- combine the two staticEnv values: the variable's type is base int
  have htyint : ty.base = BaseType.int := by
    have hboth : some (FznType.base ty.base, true)
        = some (FznType.base BaseType.int, isVar) :=
      hstaticx.symm.trans henv
    have h1 : (FznType.base ty.base, true)
        = (FznType.base BaseType.int, isVar) := Option.some.inj hboth
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, _⟩ := h1
    injection h2
  -- the slot's domain is an intDom
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  obtain ⟨xs, hxs⟩ := varDomain_int_of_base hdom htyint
  -- the assignment's read is in the slot's values — all int
  have halt : a.length = (slots.map Prod.snd).length :=
    mem_allAssigns_length _ _ hmem
  have hsndlen : (slots.map Prod.snd).length = slots.length := by simp
  have haia : i < a.length := by omega
  have hsome : a[i]? = some a[i]! := getElem_as_some haia
  have hmemv : a[i]! ∈ slots[i].snd := by
    have hfits := mem_allAssigns_fits (slots.map Prod.snd) a hmem i a[i]! hsome
    rw [getD_map_snd hislt] at hfits
    exact hfits
  -- the slot pair is (n.name, dom.values), so slots[i].snd = dom.values
  have hpairplain : slots[i] = (n.name, dom.values) := by
    have hslotpair : slots[i]! = (n.name, dom.values) := by rw [← hpair]
    have hplain : slots[i]! = slots[i] := getElem!_eq_getElem hislt
    rw [← hplain]
    exact hslotpair
  rw [hpairplain] at hmemv
  -- dom = .intDom xs, so every value is an integer
  rw [hxs] at hmemv
  obtain ⟨p, hp⟩ := intDom_values_int a[i]! hmemv
  exact ⟨p, hp⟩


/-! ## The typing-driven converse and the SAT linker -/

/-- The signature environment resolves `int_eq` to its two int-var
    parameter types in a model without predicate items. -/
theorem sigEnv_int_eq {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "int_eq") =
    some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  show (match m.declaredSigs (Ident.mk "int_eq") with
    | some params => some params
    | none => fullSig (Ident.mk "int_eq")) = _
  have hdecl : m.declaredSigs (Ident.mk "int_eq") = none := by
    show lookupIdent (Ident.mk "int_eq")
      (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
    rw [hpred]
    rfl
  rw [hdecl]
  rfl

/-- The signature environment resolves `int_ne` the same way. -/
theorem sigEnv_int_ne {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "int_ne") =
    some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  show (match m.declaredSigs (Ident.mk "int_ne") with
    | some params => some params
    | none => fullSig (Ident.mk "int_ne")) = _
  have hdecl : m.declaredSigs (Ident.mk "int_ne") = none := by
    show lookupIdent (Ident.mk "int_ne")
      (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
    rw [hpred]
    rfl
  rw [hdecl]
  rfl

/-- A `Forall2 (checkArg env)` on two arguments gives the SECOND
    argument's check (the step lemma, input order). -/
theorem forall2_checkArg_second {env : StaticEnv} {e1 e2 : Expr}
    {pt1 pt2 : PredParamType}
    (h : Forall2 (Expr.checkArg env) [e1, e2] [pt1, pt2]) :
    Expr.checkArg env e2 pt2 := by
  rw [Forall2] at h
  exact h.2.1

/-- A `Forall2 (checkArg env)` on two arguments gives the FIRST
    argument's check. -/
theorem forall2_checkArg_first {env : StaticEnv} {e1 e2 : Expr}
    {pt1 pt2 : PredParamType}
    (h : Forall2 (Expr.checkArg env) [e1, e2] [pt1, pt2]) :
    Expr.checkArg env e1 pt1 := by
  rw [Forall2] at h
  exact h.1

/-- Membership gives the position: a name in a slot-name list sits at
    some index whose bang-read returns it. -/
theorem nameIndex_mem : ∀ (names : List String) (s : String),
    s ∈ names → ∃ i, i < names.length ∧ names[i]! = s := by
  intro names
  induction names with
  | nil => intro s hmem; exact absurd hmem (by simp)
  | cons n rest ih =>
      intro s hmem
      rcases List.mem_cons.mp hmem with rfl | htl
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨i, hilt, higet⟩ := ih s htl
        exact ⟨i + 1, by
          simp only [List.length_cons]
          omega, by
          rw [List.getElem!_cons_succ]
          exact higet⟩

/-- `nameIndex` is injective on successful lookups: two names at the
    same position are equal. -/
theorem nameIndex_inj {names : List String} {s s' : String} {i : Nat}
    (h : nameIndex names s = some i) (h' : nameIndex names s' = some i) :
    s = s' := by
  obtain ⟨hlt, hget⟩ := nameIndex_some names s i h
  obtain ⟨hlt2, hget2⟩ := nameIndex_some names s' i h'
  rw [List.getElem?_eq_getElem hlt] at hget
  rw [List.getElem?_eq_getElem hlt2] at hget2
  exact Option.some.inj (hget.symm.trans hget2)

/-- A `Forall2` premise gives each member's counterpart. -/
theorem forall2_mem {α β : Type} (R : α → β → Prop) :
    ∀ (l1 : List α) (l2 : List β), Forall2 R l1 l2 →
    ∀ a ∈ l1, ∃ b ∈ l2, R a b := by
  intro l1
  induction l1 with
  | nil => intro l2 _ a ha; cases ha
  | cons x xs ih =>
      intro l2 h
      cases l2 with
      | nil => cases h
      | cons b bs =>
          intro a ha
          rcases List.mem_cons.mp ha with rfl | htl
          · exact ⟨b, List.mem_cons_self, h.1⟩
          · obtain ⟨b2, hb2mem, hb2⟩ := ih bs h.2 a htl
            exact ⟨b2, List.mem_cons_of_mem _ hb2mem, hb2⟩

/-- The int-reads premise for any `int_eq`/`int_ne` constraint of a
    well-formed model (the signature-driven typing chain, no shape
    premises — argument membership drives it). -/
theorem int_reads_of_mem_eq_ne {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem}
    (hwf : WellFormed Globals.fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hname : c.name.name = "int_eq" ∨ c.name.name = "int_ne")
    (hmem : a ∈ allAssigns (slots.map Prod.snd)) :
    ∀ (x : Ident) (i : Nat), Expr.basic (.ident x) ∈ c.args →
      nameIndex (slots.map Prod.fst) x.name = some i →
      ∃ p, a[i]! = Value.int p := by
  intro x i hxarg hxi
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] := by
    rcases hname with h1 | h1
    · rw [h1]; exact sigEnv_int_eq hpred
    · rw [h1]; exact sigEnv_int_ne hpred
  have hparameq : params =
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] := by
    have h1 : m.sigEnv Globals.fullSig c.name = some params := hsig
    rw [show m.sigEnv Globals.fullSig c.name
        = m.sigEnv Globals.fullSig (Ident.mk c.name.name) from rfl] at h1
    rw [hres] at h1
    exact (Option.some.inj h1).symm
  rw [hparameq] at hfor
  obtain ⟨pt, hptmem, hchk0⟩ :=
    forall2_mem (Expr.checkArg m.staticEnv) c.args
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] hfor
      (Expr.basic (.ident x)) hxarg
  have hpt : pt =
      PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)) := by
    rcases List.mem_cons.mp hptmem with rfl | htl
    · rfl
    · rcases List.mem_cons.mp htl with rfl | hnil
      · rfl
      · exact absurd hnil (by simp)
  subst hpt
  exact int_read_of_checkArg_slot hwf hslot hfor hchk0 hxi hmem

/-! ## The compile-list inversions (the whole-model assemblies' fuel) -/

/-- The cons inversion of a successful constraint-list compilation:
    the head constraint compiled, the tail list compiled, and the
    results were consed. -/
theorem compileConstraints_ok_cons {env : Store}
    {names : List String} {c : ConstraintItem}
    {rest : List ConstraintItem} {dcs : List DomConstraint}
    (h : compileConstraints env names (c :: rest) = .ok dcs) :
    ∃ dc' rest', compileConstraint env names c = .ok dc' ∧
      compileConstraints env names rest = .ok rest' ∧
      dcs = dc' :: rest' := by
  rw [compileConstraints] at h
  match hc : compileConstraint env names c with
  | .error e =>
      rw [hc] at h
      exfalso
      have herr : (do
          let dc <- (Except.error e : Except String DomConstraint)
          let dcs <- compileConstraints env names rest
          pure (dc :: dcs)) = .error e := rfl
      rw [herr] at h
      cases h
  | .ok dc' =>
      rw [hc] at h
      match hrest : compileConstraints env names rest with
      | .error e =>
          rw [hrest] at h
          exfalso
          have herr : (do
              let dc <- (Except.ok dc' : Except String DomConstraint)
              let dcs <- (Except.error e : Except String (List DomConstraint))
              pure (dc :: dcs)) = .error e := rfl
          rw [herr] at h
          cases h
      | .ok rest' =>
          have hboth : (do
              let dc <- (Except.ok dc' : Except String DomConstraint)
              let dcs <- (Except.ok rest' : Except String (List DomConstraint))
              pure (dc :: dcs)) = .ok (dc' :: rest') := rfl
          rw [hrest, hboth] at h
          have hfinal : dcs = dc' :: rest' := by
            injection h with h1
            exact h1.symm
          exact ⟨dc', rest', rfl, rfl, hfinal⟩

/-- **The compile-list membership inversion**: every compiled
    constraint of a successful compilation comes from some model
    constraint via its own successful compile. -/
theorem compileConstraints_mem_inv {env : Store}
    {names : List String} :
    ∀ (cs : List ConstraintItem) (dcs : List DomConstraint),
    compileConstraints env names cs = .ok dcs →
    ∀ dc ∈ dcs, ∃ c ∈ cs, compileConstraint env names c = .ok dc := by
  intro cs
  induction cs with
  | nil =>
      intro dcs h
      rw [compileConstraints] at h
      have hnil : dcs = [] := (Except.ok.inj h).symm
      subst hnil
      intro dc hdc
      exact absurd hdc (by simp)
  | cons c rest ih =>
      intro dcs h
      obtain ⟨dc', rest', hc, hrest, hcons⟩ :=
        compileConstraints_ok_cons h
      subst hcons
      intro dc hdc
      rcases List.mem_cons.mp hdc with rfl | htl
      · exact ⟨c, List.mem_cons_self, hc⟩
      · obtain ⟨c', hc'mem, hc'⟩ := ih rest' hrest dc htl
        exact ⟨c', List.mem_cons_of_mem _ hc'mem, hc'⟩


/-! ## The whole-model assembly's ingredients -/

/-- Membership in a slot list gives the position whose bang-read
    returns the member. -/
theorem slot_getElem!_of_mem : ∀ (l : List (String × List Value))
    (x : String × List Value), x ∈ l →
    ∃ i, i < l.length ∧ l[i]! = x := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons y ys ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | htl
      · exact ⟨0, by simp, by simp⟩
      · obtain ⟨i, hilt, higet⟩ := ih x htl
        exact ⟨i + 1, by
          simp only [List.length_cons]
          omega, by
          rw [List.getElem!_cons_succ]
          exact higet⟩

/-- A successful `declSlots` never swallowed an erroring member. -/
theorem declSlots_no_error : ∀ (vars : List VarDeclItem)
    (slots : List (String × List Value)),
    declSlots vars = .ok slots →
    ∀ (d : VarDeclItem), d ∈ vars → ∀ e, declSlot d ≠ .error e := by
  intro vars
  induction vars with
  | nil => intro _ _ _ hmem _; cases hmem
  | cons d rest ih =>
      intro slots h d' hd' e hde
      rw [declSlots] at h
      match hds : declSlot d with
      | .error e2 =>
          rw [hds] at h
          exact absurd h (by simp)
      | .ok none =>
          rw [hds] at h
          rcases List.mem_cons.mp hd' with rfl | htl
          · rw [hde] at hds; exact absurd hds (by simp)
          · exact ih slots h d' htl e hde
      | .ok (some p) =>
          rw [hds] at h
          obtain ⟨restslots, hrest, _⟩ := declSlots_map_ok_inv h
          rcases List.mem_cons.mp hd' with rfl | htl
          · rw [hde] at hds; exact absurd hds (by simp)
          · exact ih restslots hrest d' htl e hde

/-- Every successfully-extracted slot pair of a declared variable is
    IN the produced slot list (production, no uniqueness needed). -/
theorem declSlots_produce : ∀ (vars : List VarDeclItem)
    (slots : List (String × List Value)),
    declSlots vars = .ok slots →
    ∀ (d : VarDeclItem), d ∈ vars → ∀ p, declSlot d = .ok (some p) →
    p ∈ slots := by
  intro vars
  induction vars with
  | nil => intro _ _ _ hmem _ _; cases hmem
  | cons d rest ih =>
      intro slots h d' hd' p hds
      rw [declSlots] at h
      match hhead : declSlot d with
      | .error e =>
          rw [hhead] at h; exact absurd h (by simp)
      | .ok none =>
          rw [hhead] at h
          rcases List.mem_cons.mp hd' with rfl | htl
          · rw [hds] at hhead; exact absurd hhead (by simp)
          · exact ih slots h d' htl p hds
      | .ok (some p0) =>
          rw [hhead] at h
          match hrest : declSlots rest with
          | .error e =>
              rw [hrest] at h
              exact absurd h (by simp [Except.map])
          | .ok restslots =>
              rw [hrest] at h
              have hmapstep : (Except.ok restslots : Except String
                  (List (String × List Value))).map
                  (fun s => p0 :: s) = .ok slots := h
              have hmapred : (Except.ok restslots : Except String
                  (List (String × List Value))).map
                  (fun s => p0 :: s) = .ok (p0 :: restslots) := rfl
              rw [hmapred] at hmapstep
              have hcons : p0 :: restslots = slots := Except.ok.inj hmapstep
              rw [← hcons]
              rcases List.mem_cons.mp hd' with rfl | htl
              · rw [hds] at hhead
                injection hhead with h1
                injection h1 with h2
                rw [h2]
                exact List.mem_cons_self
              · exact List.mem_cons_of_mem _
                  (ih restslots (by rw [hrest]) d' htl p hds)

/-- `declSlot` of an initializer-free basic variable never yields
    `.ok none` (only array and initialized variables yield none). -/
theorem declSlot_basic_none {ty : BasicVarType} {n : Ident}
    {anns : List Annotation}
    (h : declSlot (.basic ty n anns none) = .ok none) : False := by
  simp only [declSlot] at h
  by_cases harr : n.name == "array1d"
  · rw [if_pos harr] at h; exact absurd h (by simp)
  · rw [if_neg harr] at h
    cases hdom : varDomain ty with
    | error e => rw [hdom] at h; exact absurd h (by simp)
    | ok dom => rw [hdom] at h; exact absurd h (by simp)

/-- Every successfully-extracted slot pair of a declared variable
    sits in the produced slot list at a position where the name-index
    resolves to it (production + location; no pair uniqueness). -/
theorem declSlot_position {m : Model}
    {slots : List (String × List Value)}
    (hwf : WellFormed Globals.fullSig m)
    (hslot : slotsChecked m = .ok slots)
    {d : VarDeclItem} (hd : d ∈ m.variables)
    {p : String × List Value} (hds : declSlot d = .ok (some p)) :
    ∃ i, i < slots.length ∧ slots[i]! = p ∧
      nameIndex (slots.map Prod.fst) p.1 = some i := by
  have hdecls : declSlots m.variables = .ok slots :=
    declSlots_of_slotsChecked hslot
  have hmem : p ∈ slots := declSlots_produce m.variables slots hdecls d hd p hds
  obtain ⟨j, hjlt, hjget⟩ := slot_getElem!_of_mem slots p hmem
  have hnames : (slots.map Prod.fst).Nodup := slotNames_nodup hwf hslot
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have hjlt2 : j < (slots.map Prod.fst).length := by omega
  have hnamej : (slots.map Prod.fst)[j]! = p.1 := by
    rw [getElem!_map_fst j, hjget]
  refine ⟨j, hjlt, hjget, ?_⟩
  rw [← hnamej]
  exact nameIndex_at_nodup (slots.map Prod.fst) j hnames hjlt2

/-- A successfully compiled model declares only initializer-free
    basic variables (the compiler's variable gate). -/
theorem compileModel_vars_basic {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem) :
    ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none := by
  intro d hd
  unfold compileModel at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc
    · split at hc
      · exfalso
        cases hc
      · next hvars =>
          match hd2 : d with
          | .basic ty n anns opt =>
              cases opt with
              | none => exact ⟨ty, n, anns, rfl⟩
              | some e =>
                  exfalso
                  have hmem : (.basic ty n anns (some e) : VarDeclItem)
                      ∈ ([] : List VarDeclItem) := by
                    rw [← hvars]
                    exact List.mem_filter.mpr ⟨hd, by rfl⟩
                  cases hmem
          | .array ty n anns vs =>
              exfalso
              have hmem : (.array ty n anns vs : VarDeclItem)
                  ∈ ([] : List VarDeclItem) := by
                rw [← hvars]
                exact List.mem_filter.mpr ⟨hd, by rfl⟩
              cases hmem

/-- A successfully compiled model has no predicate items. -/
theorem compileModel_predicates_nil {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem) :
    m.predicates = [] := by
  unfold compileModel at hc
  split at hc
  · cases hc
  · next hpred => exact Classical.byContradiction hpred

/-- A successfully compiled model's parameters are all scalar
    (the filter of non-scalar parameters is empty). -/
theorem compileModel_params_scalar {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem) :
    m.parameters.filter (fun d => parDeclValue d = none) = [] := by
  unfold compileModel at hc
  split at hc
  · cases hc
  · split at hc
    · next hpar => cases hc
    · next hpar => exact hpar

/-- A successfully compiled model satisfies `solve satisfy`. -/
theorem compileModel_solve_satisfy {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem) :
    ∃ anns, m.solve = .satisfy anns := by
  unfold compileModel at hc
  split at hc
  · cases hc
  · split at hc
    · cases hc
    · split at hc
      · cases hc
      · split at hc
        · next anns hsolve => exact ⟨anns, hsolve⟩
        · cases hc

/-- Every declared initializer-free basic variable reads its
    assignment value at its slot position, contained in its declared
    domain (the var-decls half of `Satisfies`). -/
theorem decl_var_basic_holds {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {ty : BasicVarType} {n : Ident} {anns : List Annotation}
    (hwf : WellFormed Globals.fullSig m)
    (hd : (.basic ty n anns none : VarDeclItem) ∈ m.variables)
    (hslot : slotsChecked m = .ok slots)
    (hmem : a ∈ allAssigns (slots.map Prod.snd)) :
    ∃ v, ((assemble m slots dcs).toStore a) n = some v ∧ ty.contains v := by
  have hdecls : declSlots m.variables = .ok slots :=
    declSlots_of_slotsChecked hslot
  match hds : declSlot (.basic ty n anns none : VarDeclItem) with
  | .error e =>
      exact absurd hds
        (declSlots_no_error m.variables slots hdecls _ hd e)
  | .ok none => exact (declSlot_basic_none hds).elim
  | .ok (some p0) =>
      obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hds
      obtain ⟨j, hjlt, hjget, hjidx⟩ := declSlot_position hwf hslot hd hds
      have hfixj : nameIndex (slots.map Prod.fst) n.name = some j := by
        rw [show n.name = (n.name, dom.values).1 from rfl]
        rw [show (n.name, dom.values).1 = p0.1 from by rw [← hpair]]
        exact hjidx
      have hnu : (slots.map Prod.fst).Nodup := slotNames_nodup hwf hslot
      have halt : a.length = slots.length := by
        have h1 := mem_allAssigns_length (slots.map Prod.snd) a hmem
        rw [List.length_map] at h1
        exact h1
      have hstoreread : ((assemble m slots dcs).toStore a) n = some a[j]! :=
        toStore_read (m := m) (dcs := dcs) hnu hfixj halt
      have haj : j < a.length := by omega
      have hsome : a[j]? = some a[j]! := getElem_as_some haj
      have hfits := mem_allAssigns_fits (slots.map Prod.snd) a hmem j a[j]!
        hsome
      rw [getD_map_snd hjlt] at hfits
      rw [getElem!_eq_getElem hjlt] at hjget
      have hpairj : slots[j] = (n.name, dom.values) := hjget.trans hpair
      rw [hpairj] at hfits
      have hcontains : ty.contains a[j]! := (varDomain_values_iff hdom).mp hfits
      exact ⟨a[j]!, hstoreread, hcontains⟩

/-- A true `accepts` gives every compiled constraint's declarative
    satisfaction. -/
theorem accepts_of_true {problem : CompiledProblem DomConstraint}
    {a : List Value} (h : accepts problem a = true)
    (dc : DomConstraint) (hdc : dc ∈ problem.constraints) :
    dc.SatisfiedBy a :=
  (DomConstraint.satisfiedB_iff dc a).mp (List.all_eq_true.mp h dc hdc)

/-- The assembled store resolves a non-slot name through the
    parameter environment (the fallback shapes' parameter args). -/
theorem toStore_param {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x : Ident} {v : Value}
    (hnone : nameIndex (slots.map Prod.fst) x.name = none)
    (henv : parEnv m x = some v) :
    (assemble m slots dcs).toStore a x = some v := by
  show (match nameIndex (slots.map Prod.fst) x.name with
    | some i => a[i]?
    | none => parEnv m x) = some v
  rw [hnone, henv]

/-- Evaluation of an identifier-then-arbitrary-valued argument list at
    the assembled store (the fallback bridges' general form). -/
theorem eval_ident_E_any {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x : Ident} {i : Nat}
    {e2 : Expr} {w2 : Value}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (he2 : Expr.eval ((assemble m slots dcs).toStore a) e2 = some w2) :
    ([Expr.basic (.ident x), e2].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, w2] := by
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← Expr.eval ((assemble m slots dcs).toStore a) e2
      pure [v1, v2]) = _
  rw [toStore_read (m := m) hnu hxi halt, he2]
  rfl

/-- Evaluation of an arbitrary-valued-then-identifier argument list
    at the assembled store (the mirrored general bridge). -/
theorem eval_E_any {m : Model} {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {y : Ident} {j : Nat}
    {e1 : Expr} {w1 : Value}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (he1 : Expr.eval ((assemble m slots dcs).toStore a) e1 = some w1) :
    ([e1, Expr.basic (.ident y)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [w1, a[j]!] := by
  show (do
      let v1 ← Expr.eval ((assemble m slots dcs).toStore a) e1
      let v2 ← (assemble m slots dcs).toStore a y
      pure [v1, v2]) = _
  rw [he1, toStore_read (m := m) hnu hyi halt]
  rfl

/-- A successful `compileArgVal` of an identifier goes through a slot
    position when the name resolves in the list. -/
theorem compileArgVal_ident_inv {env : Store} {names : List String}
    {x : Ident} {i : Nat} {av : ArgVal}
    (h : compileArgVal env names (.ident x) = .ok av)
    (hxi : nameIndex names x.name = some i) :
    av = .slotRef i := by
  simp only [compileArgVal] at h
  rw [hxi] at h
  exact (Except.ok.inj h).symm

/-- A successful `compileArgVal` of an identifier resolves through
    the parameter environment when the name is not a slot. -/
theorem compileArgVal_ident_par {env : Store} {names : List String}
    {x : Ident} {av : ArgVal}
    (h : compileArgVal env names (.ident x) = .ok av)
    (hnone : nameIndex names x.name = none) :
    ∃ v, env x = some v ∧ av = .litVal v := by
  simp only [compileArgVal] at h
  rw [hnone] at h
  cases hex : env x with
  | none => rw [hex] at h; exact absurd h (by simp)
  | some v =>
      rw [hex] at h
      exact ⟨v, rfl, (Except.ok.inj h).symm⟩

/-! ## The bool typing chain (the bool-literal fallback shapes) -/

/-- The signature `checkArg` premise for a bool-typed predicate
    argument that is a slot identifier: the identifier's static type is
    a base `bool`. -/
theorem staticEnv_bool_of_checkArg {env : StaticEnv} {x : Ident}
    (h : (Expr.basic (.ident x)).checkArg env
        (.basic (.var (.par .bool)))) :
    ∃ isVar, env x = some (.base .bool, isVar) := by
  simp only [Expr.checkArg, BasicExpr.checkBase] at h
  cases hlk : env x with
  | none => rw [hlk] at h; simp at h
  | some p =>
      obtain ⟨ft, isVar⟩ := p
      rw [show env x = some (ft, isVar) from hlk] at h
      cases ft with
      | base t =>
          have hbase : (BasicVarType.par BasicParType.bool).base = t := h.1
          exact ⟨isVar, by rw [← hbase]; rfl⟩
      | array n te => exact absurd h (by simp)

/-- A bool-based variable type with a successful domain extraction
    yields the Boolean domain. -/
theorem varDomain_bool_of_base {ty : BasicVarType} {dom : VarDomain}
    (h : varDomain ty = .ok dom) (hbase : ty.base = .bool) :
    dom = .boolDom := by
  cases ty with
  | par t =>
      cases t with
      | bool =>
          simp only [varDomain] at h
          exact (Except.ok.inj h).symm
      | int => rw [BasicVarType.base] at hbase; exact absurd hbase (by intro h2; cases h2)
      | setOfInt => rw [BasicVarType.base] at hbase; exact absurd hbase (by intro h2; cases h2)
  | intRange lo hi => simp [BasicVarType.base] at hbase
  | intSet xs => simp [BasicVarType.base] at hbase
  | setOfIntRange lo hi => simp [BasicVarType.base] at hbase
  | setOfIntSet xs => simp [BasicVarType.base] at hbase

/-- Every value of the Boolean domain is a Boolean. -/
theorem boolDom_values_bool {v : Value} (h : v ∈ VarDomain.boolDom.values) :
    ∃ p, v = Value.bool p := by
  simp only [VarDomain.values] at h
  rcases List.mem_cons.mp h with rfl | h
  · exact ⟨false, rfl⟩
  · rcases List.mem_cons.mp h with rfl | h
    · exact ⟨true, rfl⟩
    · cases h

/-- The bool-reads premise: a slot-position read of an assignment is
    a Boolean whenever the constraint's argument checks against the
    bool-typed signature (the bool twin of
    `int_read_of_checkArg_slot`). -/
theorem bool_read_of_checkArg_slot {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType}
    {x : Ident} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hcheck :
      (Expr.basic (.ident x)).checkArg m.staticEnv (.basic (.var (.par .bool))))
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns (slots.map Prod.snd)) :
    ∃ p, a[i]! = Value.bool p := by
  -- the slot is in bounds
  obtain ⟨hxlt, hxget⟩ :=
    nameIndex_some (slots.map Prod.fst) x.name i hxi
  have hlen : (slots.map Prod.fst).length = slots.length := by simp
  have hislt : i < slots.length := by omega
  -- the check supplies the bool base type for x
  obtain ⟨isVar, henv⟩ := staticEnv_bool_of_checkArg hcheck
  -- the slot's variable, with its staticEnv resolution
  obtain ⟨d, hd, hdslot, hstatic⟩ := staticEnv_of_slot hwf hslot hislt
  -- the checked identifier IS the slot's name (both are slots[i].1)
  have hnameilt : i < (slots.map Prod.fst).length := by
    rw [List.length_map]
    omega
  have hnamei : (slots.map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt hxget
  have hxslot : slots[i]!.1 = x.name := by
    rw [show slots[i]!.1 = (slots.map Prod.fst)[i]! from
      (getElem!_map_fst i).symm]
    exact hnamei
  have hstaticx : m.staticEnv x = some (d.type, true) := by
    have hxmk : x = Ident.mk slots[i]!.1 := by
      obtain ⟨s⟩ := x
      apply ident_eq_of_name
      rw [hxslot]
    rw [hxmk]
    exact hstatic
  -- both resolutions describe the same staticEnv value: the type is bool
  obtain ⟨ty, n, anns, hdshape⟩ : ∃ ty n anns,
      d = .basic ty n anns none := by
    match hs : declSlot d with
    | .error e => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok none => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok (some p) =>
        cases d with
        | basic ty n anns opt2 =>
            cases opt2 with
            | none => exact ⟨ty, n, anns, rfl⟩
            | some e => rw [hs] at *; exact absurd hdslot (by simp [declSlot])
        | array ty n anns vs =>
            rw [hs] at *; exact absurd hdslot (by simp [declSlot])
  subst hdshape
  -- combine the two staticEnv values: the variable's type is base bool
  have htybool : ty.base = BaseType.bool := by
    have hboth : some (FznType.base ty.base, true)
        = some (FznType.base BaseType.bool, isVar) :=
      hstaticx.symm.trans henv
    have h1 : (FznType.base ty.base, true)
        = (FznType.base BaseType.bool, isVar) := Option.some.inj hboth
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, _⟩ := h1
    injection h2
  -- the slot's domain is a boolDom
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  have hbooldom : dom = .boolDom := varDomain_bool_of_base hdom htybool
  -- the assignment's read is in the slot's values — all bool
  have halt : a.length = (slots.map Prod.snd).length :=
    mem_allAssigns_length _ _ hmem
  have hsndlen : (slots.map Prod.snd).length = slots.length := by simp
  have haia : i < a.length := by omega
  have hsome : a[i]? = some a[i]! := getElem_as_some haia
  have hmemv : a[i]! ∈ slots[i].snd := by
    have hfits := mem_allAssigns_fits (slots.map Prod.snd) a hmem i a[i]! hsome
    rw [getD_map_snd hislt] at hfits
    exact hfits
  -- the slot pair is (n.name, dom.values), so slots[i].snd = dom.values
  have hpairplain : slots[i] = (n.name, dom.values) := by
    have hslotpair : slots[i]! = (n.name, dom.values) := by rw [← hpair]
    have hplain : slots[i]! = slots[i] := getElem!_eq_getElem hislt
    rw [← hplain]
    exact hslotpair
  rw [hpairplain] at hmemv
  -- dom = .boolDom, so every value is a Boolean
  rw [hbooldom] at hmemv
  have hmemv' : a[i]! ∈ VarDomain.boolDom.values := hmemv
  obtain ⟨p, hp⟩ := boolDom_values_bool hmemv'
  exact ⟨p, hp⟩

/-- The signature environment resolves `bool_not` to its two
    bool-var parameter types (model without predicate items). -/
theorem sigEnv_bool_not {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "bool_not") =
    some [.basic (.var (.par .bool)), .basic (.var (.par .bool))] := by
  show (match m.declaredSigs (Ident.mk "bool_not") with
    | some params => some params
    | none => fullSig (Ident.mk "bool_not")) = _
  have hdecl : m.declaredSigs (Ident.mk "bool_not") = none := by
    show lookupIdent (Ident.mk "bool_not")
      (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
    rw [hpred]
    rfl
  rw [hdecl]
  rfl

/-- The signature environment resolves `bool_and` to its three
    bool-var parameter types. -/
theorem sigEnv_bool_and {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "bool_and") =
    some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
      .basic (.var (.par .bool))] := by
  show (match m.declaredSigs (Ident.mk "bool_and") with
    | some params => some params
    | none => fullSig (Ident.mk "bool_and")) = _
  have hdecl : m.declaredSigs (Ident.mk "bool_and") = none := by
    show lookupIdent (Ident.mk "bool_and")
      (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
    rw [hpred]
    rfl
  rw [hdecl]
  rfl

/-- The signature environment resolves `bool_or` to its three
    bool-var parameter types. -/
theorem sigEnv_bool_or {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "bool_or") =
    some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
      .basic (.var (.par .bool))] := by
  show (match m.declaredSigs (Ident.mk "bool_or") with
    | some params => some params
    | none => fullSig (Ident.mk "bool_or")) = _
  have hdecl : m.declaredSigs (Ident.mk "bool_or") = none := by
    show lookupIdent (Ident.mk "bool_or")
      (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
    rw [hpred]
    rfl
  rw [hdecl]
  rfl

/-- The bool-reads premise for the bool-literal fallback families: any
    `bool_not`/`bool_and`/`bool_or` constraint of a well-formed model
    reads Booleans at its slot arguments. -/
theorem bool_reads_of_mem_bool_family {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem}
    (hwf : WellFormed Globals.fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hname : c.name.name = "bool_not" ∨ c.name.name = "bool_and" ∨
      c.name.name = "bool_or")
    (hmem : a ∈ allAssigns (slots.map Prod.snd)) :
    ∀ (x : Ident) (i : Nat), Expr.basic (.ident x) ∈ c.args →
      nameIndex (slots.map Prod.fst) x.name = some i →
      ∃ p, a[i]! = Value.bool p := by
  intro x i hxarg hxi
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  -- the param list equals the family's signature
  have hparameq : params =
      [.basic (.var (.par .bool)), .basic (.var (.par .bool))] ∨
      params =
      [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
        .basic (.var (.par .bool))] := by
    have h1 : m.sigEnv Globals.fullSig c.name = some params := hsig
    rw [show m.sigEnv Globals.fullSig c.name
        = m.sigEnv Globals.fullSig (Ident.mk c.name.name) from rfl] at h1
    rcases hname with hn | hn | hn
    · rw [show c.name.name = "bool_not" from hn, sigEnv_bool_not hpred] at h1
      exact Or.inl (Option.some.inj h1).symm
    · rw [show c.name.name = "bool_and" from hn, sigEnv_bool_and hpred] at h1
      exact Or.inr (Option.some.inj h1).symm
    · rw [show c.name.name = "bool_or" from hn, sigEnv_bool_or hpred] at h1
      exact Or.inr (Option.some.inj h1).symm
  -- every entry of params is a bool-var parameter
  have hpsall : ∀ pt ∈ params, pt = .basic (.var (.par .bool)) := by
    intro pt hpt
    rcases hparameq with h | h
    · rw [h] at hpt
      rcases List.mem_cons.mp hpt with rfl | hpt
      · rfl
      · rcases List.mem_cons.mp hpt with rfl | hpt
        · rfl
        · exact absurd hpt (by simp)
    · rw [h] at hpt
      rcases List.mem_cons.mp hpt with rfl | hpt
      · rfl
      · rcases List.mem_cons.mp hpt with rfl | hpt
        · rfl
        · rcases List.mem_cons.mp hpt with rfl | hpt
          · rfl
          · exact absurd hpt (by simp)
  obtain ⟨pt, hptmem, hchk0⟩ :=
    forall2_mem (Expr.checkArg m.staticEnv) c.args params hfor
      (Expr.basic (.ident x)) hxarg
  have hpt : pt = .basic (.var (.par .bool)) := hpsall pt hptmem
  subst hpt
  exact bool_read_of_checkArg_slot hwf hslot hfor hchk0 hxi hmem


end LeanFzn.Compiler
