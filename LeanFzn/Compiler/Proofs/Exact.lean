/-
File: LeanFzn/Compiler/Proofs/Exact.lean

Purpose:
  The whole-model correspondence between `LeanFzn.Compiler.compileModel` and the
  source semantics (`Satisfies fullSig fullInterp`):

  * the E-generalized per-shape converses (the fallback shapes'
    premises) and the fallback gate inversions;
  * `compile_sat_link` — the per-constraint SAT linker (a compiled
    constraint satisfied by an accepted assignment makes the source
    constraint hold at the assembled store), covering both the
    extracted and the fallback shapes;
  * `compile_holds_link` — the per-constraint coverage linker (a
    source constraint holding at a parameter-honest store makes the
    compiled constraint satisfied by the store's slot reads);
  * `compile_exact` — an accepted assignment reconstructs a store
    satisfying declarations and every source constraint;
  * `compile_covers` — every satisfying, parameter-honest store maps
    into the compiled candidate space and passes the internal
    evaluator.

Dependencies:
  - LeanFzn.Compiler.Proofs.Compile: the per-shape correspondence,
    the slot machinery, the compile-list inversions, and the
    whole-model gate inversions.
  - LeanFzn.Compiler.Compile: the executable compiler.
  - LeanFzn.Semantics.Model: `Satisfies`.

DAG:
  LeanFzn.Compiler.Proofs.Compile -> LeanFzn.Compiler.Proofs.Exact
    -> LeanFzn.Compiler.Correctness
-/

import LeanFzn.Compiler.Proofs.Compile
import LeanFzn.Solver.Propagation.Operations
open LeanFzn.Compiler.Domains


namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Core

/-- The compiled domains (compact `Dom.ofList` carriers) have the same
assignment space as their source value lists. -/
theorem allAssigns_map_ofList (slots : List (String × List Value)) :
    allAssigns (slots.map (fun p => Dom.ofList p.2)) = allAssigns (slots.map Prod.snd) := by
  induction slots with
  | nil => rfl
  | cons p rest ih =>
      obtain ⟨n, vs⟩ := p
      simp only [List.map_cons, allAssigns, DomainElems.elems_list,
        domElems_eq_enum, Dom.enum_ofList, ih]

/-! ## The E-generalized converses (the fallback shapes' premises)

The fallback shapes of `compileConstraint` (literal-bound `int_plus`,
`int_le`, `int_lt`, `int_gt`, `int_ge` with a parameter-resolved
argument) do not come through `extractConstraint`, so their
assignment→store converses are stated with an arbitrary
integer-valued argument expression `E`; the master SAT linker
instantiates `E` with the source argument and derives `hE` from the
compiler's own gate evaluation. -/

/-- int_le(x, E) with E evaluating to `.int k`. -/
theorem holds_int_le_const_hi_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {i : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_le")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.leConstHi i k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hpc⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? hw
  refine ⟨[a[i]!, .int k], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_any hnu halt hxi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.int k] with
      | [Value.int p, Value.int q] => p ≤ q
      | _ => False)
    rw [hib]
    exact hpc

/-- int_le(E, y) with E evaluating to `.int k`. -/
theorem holds_int_le_const_lo_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y : Ident} {j : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_le")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.leConstLo j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hcp⟩ := hsat
  have hib : a[j]! = Value.int p := bang_of_getElem? hw
  refine ⟨[.int k, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_any hnu halt hyi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[j]!] with
      | [Value.int p, Value.int q] => p ≤ q
      | _ => False)
    rw [hib]
    exact hcp

/-- int_lt(x, E) with E evaluating to `.int k`. -/
theorem holds_int_lt_const_hi_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {i : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_lt")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.ltConstHi i k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hpc⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? hw
  refine ⟨[a[i]!, .int k], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_any hnu halt hxi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.int k] with
      | [Value.int p, Value.int q] => p < q
      | _ => False)
    rw [hib]
    exact hpc

/-- int_lt(E, y) with E evaluating to `.int k`. -/
theorem holds_int_lt_const_lo_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y : Ident} {j : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_lt")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.ltConstLo j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hcp⟩ := hsat
  have hib : a[j]! = Value.int p := bang_of_getElem? hw
  refine ⟨[.int k, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_any hnu halt hyi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[j]!] with
      | [Value.int p, Value.int q] => p < q
      | _ => False)
    rw [hib]
    exact hcp

/-- int_gt(x, E) with E evaluating to `.int k` (compiled `ltConstLo`). -/
theorem holds_int_gt_const_lo_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {i : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_gt")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.ltConstLo i k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hcp⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? hw
  refine ⟨[a[i]!, .int k], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_any hnu halt hxi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.int k] with
      | [Value.int p, Value.int q] => p > q
      | _ => False)
    rw [hib]
    exact hcp

/-- int_gt(E, y) with E evaluating to `.int k` (compiled `ltConstHi`). -/
theorem holds_int_gt_const_hi_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y : Ident} {j : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_gt")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.ltConstHi j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hpc⟩ := hsat
  have hib : a[j]! = Value.int p := bang_of_getElem? hw
  refine ⟨[.int k, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_any hnu halt hyi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[j]!] with
      | [Value.int p, Value.int q] => p > q
      | _ => False)
    rw [hib]
    exact hpc

/-- int_ge(x, E) with E evaluating to `.int k` (compiled `leConstLo`). -/
theorem holds_int_ge_const_lo_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {i : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_ge")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.leConstLo i k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hcp⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? hw
  refine ⟨[a[i]!, .int k], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_any hnu halt hxi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.int k] with
      | [Value.int p, Value.int q] => p ≥ q
      | _ => False)
    rw [hib]
    exact hcp

/-- int_ge(E, y) with E evaluating to `.int k` (compiled `leConstHi`). -/
theorem holds_int_ge_const_hi_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y : Ident} {j : Nat} {k : Int}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_ge")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.leConstHi j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hcp⟩ := hsat
  have hib : a[j]! = Value.int p := bang_of_getElem? hw
  refine ⟨[.int k, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_any hnu halt hyi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[j]!] with
      | [Value.int p, Value.int q] => p ≥ q
      | _ => False)
    rw [hib]
    exact hcp

/-- int_plus(x, y, E) with E evaluating to `.int k` (compiled
    `linEq [1, 1] [i, j] k`). -/
theorem holds_int_plus_lit_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {i j : Nat}
    {k : Int} {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "int_plus")
    (hargs : c.args =
      [Expr.basic (.ident x), Expr.basic (.ident y), E])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k))
    (hsat : (DomConstraint.linEq [1, 1] [i, j] k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hdot : LeanFzn.Semantics.dotProduct (intVals [1, 1]) [a[i]!, a[j]!]
      = some k := hsat
  have hintvals : intVals [1, 1] = [Value.int 1, Value.int 1] := rfl
  rw [hintvals] at hdot
  obtain ⟨p, q, hib, hjb, hpqk⟩ := dotProduct_two_one_inv hdot
  refine ⟨[a[i]!, a[j]!, .int k], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_ident_E (m := m) hnu halt hxi hyi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, .int k] with
      | [Value.int p, Value.int q, Value.int r] => p + q = r
      | _ => False)
    rw [hib, hjb]
    exact hpqk

/-! ## The fallback-shape source inversion (coverage direction) -/

/-- Generic three-argument evaluation inversion: the first two
    arguments are the given identifiers, the third arbitrary. -/
theorem eval_three_inv {store : Store}
    {x y : Ident} {e3 : Expr} {l : List Value}
    (h3 : [Expr.basic (.ident x), Expr.basic (.ident y), e3].mapM
        (Expr.eval store) = some l) :
    ∃ v1 v2 v3, store x = some v1 ∧ store y = some v2 ∧
      Expr.eval store e3 = some v3 ∧ l = [v1, v2, v3] := by
  -- normalize to the three-step bind chain
  have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
        (fun v2 => Option.bind (Expr.eval store e3)
          (fun v3 => some [v1, v2, v3]))) = some l := by
    simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using h3
  -- the ident evals are the store reads
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  rw [hred1, hred2] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some v1 =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      cases hsy : store y with
      | none => rw [hsy] at hchain; simp at hchain
      | some v2 =>
          rw [hsy] at hchain
          simp only [Option.bind_some] at hchain
          cases he3 : Expr.eval store e3 with
          | none => rw [he3] at hchain; simp at hchain
          | some v3 =>
              rw [he3] at hchain
              simp only [Option.bind_some] at hchain
              exact ⟨v1, v2, v3, rfl, rfl, rfl, by simpa using hchain.symm⟩

/-- The E-generalized source inversion: `int_plus(x, y, E)` holding
    at a store where E evaluates to `.int k` forces the first two
    reads to be integers summing to `k`. -/
theorem holds_int_plus_E_inv {store : Store} {c : ConstraintItem}
    {x y : Ident} {k : Int} {E : Expr}
    (hname : c.name.name = "int_plus")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.int p) ∧ store y = some (.int q) ∧
      p + q = k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  obtain ⟨v1, v2, v3, hsx, hsy, he3, hargsv⟩ := eval_three_inv hmap
  have hv3 : v3 = .int k := (Option.some.inj (he3.symm.trans hE))
  subst hv3
  subst hargsv
  have h1 : fullInterp (Ident.mk "int_plus") [v1, v2, .int k] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide :
    ¬ "int_plus" ∈ globalsNames)] at h1
  have hmatch : (match [v1, v2, .int k] with
    | [Value.int a, Value.int b, Value.int w] => a + b = w
    | _ => False) := h1
  cases v1 with
  | int p =>
      cases v2 with
      | int q =>
          have hk : p + q = k := by simpa using hmatch
          exact ⟨p, q, hsx, hsy, hk⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)
  | bool w => exact absurd hmatch (by simp)
  | setOfInt w => exact absurd hmatch (by simp)
  | array w => exact absurd hmatch (by simp)

/-! ## The fallback gate inversion -/

/-- A `slotRef` compile comes only from an identifier expression whose
    name resolves in the slot-name list. -/
theorem compileArgVal_slotRef_inv {env : Store} {names : List String}
    {b : BasicExpr} {i : Nat}
    (h : compileArgVal env names b = .ok (.slotRef i)) :
    ∃ x, b = .ident x ∧ nameIndex names x.name = some i := by
  cases b with
  | lit l =>
      cases l with
      | int v => simp only [compileArgVal] at h; cases h
      | bool v => simp only [compileArgVal] at h; cases h
      | set v => simp only [compileArgVal] at h; cases h
  | ident x =>
      simp only [compileArgVal] at h
      -- case the lookup result outside h first, via a match statement
      have hgo : ∀ (o : Option Nat), nameIndex names x.name = o →
          nameIndex names x.name = some i := by
        intro o ho
        match o with
        | none =>
            rw [ho] at h
            -- the inner match on env x: either arm contradicts
            cases hex : env x with
            | none =>
                rw [hex] at h
                exact absurd h (by intro hcon; cases hcon)
            | some v =>
                rw [hex] at h
                exact absurd h (by intro hcon; cases hcon)
        | some i2 =>
            rw [ho] at h
            injection h with h3
            injection h3 with h4
            exact ho.trans (by rw [h4])
      exact ⟨x, rfl, hgo (nameIndex names x.name) rfl⟩

/-- A `litVal (.int k)` compile comes only from an int-literal
    expression or an identifier resolving to it (through the name
    list or the parameter environment). -/
theorem compileArgVal_litVal_int_inv {env : Store} {names : List String}
    {b : BasicExpr} {k : Int}
    (h : compileArgVal env names b = .ok (.litVal (.int k))) :
    b = .lit (.int k) ∨
      (∃ x, b = .ident x ∧ nameIndex names x.name = none ∧
        env x = some (.int k)) := by
  cases b with
  | lit l =>
      cases l with
      | int v =>
          simp only [compileArgVal] at h
          have hvv : ArgVal.litVal (Value.int v)
              = ArgVal.litVal (Value.int k) := (Except.ok.inj h)
          injection hvv with h1
          injection h1 with hvk
          exact Or.inl (by rw [hvk])
      | bool v => simp only [compileArgVal] at h; cases h
      | set v => simp only [compileArgVal] at h; cases h
  | ident x =>
      simp only [compileArgVal] at h
      cases hn : nameIndex names x.name with
      | none =>
          simp only [hn] at h
          cases hex : env x with
          | none => rw [hex] at h; cases h
          | some v =>
              simp only [hex] at h
              have hvv : ArgVal.litVal v
                  = ArgVal.litVal (Value.int k) := (Except.ok.inj h)
              have h2 : v = Value.int k := by injection hvv
              exact Or.inr ⟨x, rfl, hn, by rw [← h2]; exact hex⟩
      | some i2 => rw [hn] at h; cases h

/-- A list of length 3 is determined by its three bang reads. -/
theorem three_of_bang {c : ConstraintItem}
    (hlen : c.args.length = 3)
    (h0 : c.args[0]! = Expr.basic b0)
    (h1 : c.args[1]! = Expr.basic b1)
    (h2 : c.args[2]! = Expr.basic b2) :
    c.args = [Expr.basic b0, Expr.basic b1, Expr.basic b2] := by
  match h : c.args with
  | e0 :: e1 :: e2 :: e3 :: rest =>
      exfalso
      rw [h] at hlen
      simp only [List.length_cons] at hlen
      omega
  | e0 :: e1 :: e2 :: [] =>
      rw [h] at h0 h1 h2
      simp only [List.getElem!_cons_zero, List.getElem!_cons_succ,
        List.getElem!_cons_zero] at h0 h1 h2
      rw [h0, h1, h2]
  | e0 :: e1 :: [] =>
      rw [h] at hlen; simp at hlen
  | [e0] => rw [h] at hlen; simp at hlen
  | [] => rw [h] at hlen; simp at hlen

/-- A list of length 2 is determined by its two bang reads. -/
theorem two_of_bang {c : ConstraintItem}
    (hlen : c.args.length = 2)
    (h0 : c.args[0]! = Expr.basic b0)
    (h1 : c.args[1]! = Expr.basic b1) :
    c.args = [Expr.basic b0, Expr.basic b1] := by
  match h : c.args with
  | e0 :: e1 :: e2 :: rest =>
      exfalso
      rw [h] at hlen
      simp only [List.length_cons] at hlen
      omega
  | e0 :: e1 :: [] =>
      rw [h] at h0 h1
      simp only [List.getElem!_cons_zero, List.getElem!_cons_succ,
        List.getElem!_cons_zero] at h0 h1
      rw [h0, h1]
  | [e0] => rw [h] at hlen; simp at hlen
  | [] => rw [h] at hlen; simp at hlen

/-! ## The `argOf` inversions (the new Except-valued accessor) -/

/-! ## The signature lemmas (int-binary and int_plus) -/

/-- The declared-signature lookup is none for any name in a model
    without predicate items. -/
theorem declaredSigs_none {m : Model} (hpred : m.predicates = [])
    (x : Ident) : m.declaredSigs x = none := by
  show lookupIdent x (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
  rw [hpred]
  rfl

/-- The signature environment resolves every int-binary name of the
    fragment to its two int-var parameter types (model without
    predicate items). -/
theorem sigEnv_int_binary {m : Model} (hpred : m.predicates = [])
    (n : String)
    (hn : n = "int_eq" ∨ n = "int_ne" ∨ n = "int_le" ∨ n = "int_lt" ∨
      n = "int_ge" ∨ n = "int_gt") :
    m.sigEnv fullSig (Ident.mk n) =
    some [.basic (.var (.par .int)), .basic (.var (.par .int))] := by
  rcases hn with h | h | h | h | h | h
  all_goals
    show (match m.declaredSigs (Ident.mk n) with
      | some params => some params
      | none => fullSig (Ident.mk n)) = _
    rw [declaredSigs_none hpred (Ident.mk n), h]
    rfl

/-- The signature environment resolves `int_plus` to its three
    int-var parameter types. -/
theorem sigEnv_int_plus' {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "int_plus") =
    some [.basic (.var (.par .int)), .basic (.var (.par .int)),
      .basic (.var (.par .int))] := by
  show (match m.declaredSigs (Ident.mk "int_plus") with
    | some params => some params
    | none => fullSig (Ident.mk "int_plus")) = _
  rw [declaredSigs_none hpred (Ident.mk "int_plus")]
  rfl

/-- The signature environment resolves the array-extreme names to their
    result-var-int / array-of-var-int parameter types (PLAN C9
    remainder: the two-element array shapes). -/
theorem sigEnv_array_int_extreme {m : Model} (hpred : m.predicates = [])
    (n : String)
    (hn : n = "array_int_minimum" ∨ n = "array_int_maximum") :
    m.sigEnv fullSig (Ident.mk n) =
    some [.basic (.var (.par .int)), .array .int (.var (.par .int))] := by
  rcases hn with h | h
  all_goals
    show (match m.declaredSigs (Ident.mk n) with
      | some params => some params
      | none => fullSig (Ident.mk n)) = _
    rw [declaredSigs_none hpred (Ident.mk n), h]
    rfl

/-! ## The name-conditioned int-reads (all int-binary names) -/

/-- The int-reads premise for the extracted/fallback shapes of the
    int-binary names: any `int_eq`/`int_ne`/`int_le`/`int_lt`/
    `int_ge`/`int_gt` constraint of a well-formed model reads ints at
    its slot arguments (the signature check of WellFormed drives the
    typing chain). -/
theorem int_reads_of_mem_int_binary {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem}
    (hwf : WellFormed Globals.fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hname : c.name.name = "int_eq" ∨ c.name.name = "int_ne" ∨
      c.name.name = "int_le" ∨ c.name.name = "int_lt" ∨
      c.name.name = "int_ge" ∨ c.name.name = "int_gt")
    (hmem : a ∈ allAssigns (slots.map Prod.snd)) :
    ∀ (x : Ident) (i : Nat), Expr.basic (.ident x) ∈ c.args →
      nameIndex (slots.map Prod.fst) x.name = some i →
      ∃ p, a[i]! = Value.int p := by
  intro x i hxarg hxi
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
      some [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] :=
    sigEnv_int_binary hpred c.name.name hname
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

/-- The int-reads premise for the `int_plus` shapes (three int-var
    params). -/
theorem int_reads_of_mem_int_plus {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem}
    (hwf : WellFormed Globals.fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hname : c.name.name = "int_plus")
    (hmem : a ∈ allAssigns (slots.map Prod.snd)) :
    ∀ (x : Ident) (i : Nat), Expr.basic (.ident x) ∈ c.args →
      nameIndex (slots.map Prod.fst) x.name = some i →
      ∃ p, a[i]! = Value.int p := by
  intro x i hxarg hxi
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
      some [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] := by
    rw [hname]
    exact sigEnv_int_plus' hpred
  have hparameq : params =
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
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
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] hfor
      (Expr.basic (.ident x)) hxarg
  have hpt : pt =
      PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)) := by
    rcases List.mem_cons.mp hptmem with rfl | htl
    · rfl
    · rcases List.mem_cons.mp htl with rfl | htl2
      · rfl
      · rcases List.mem_cons.mp htl2 with rfl | hnil
        · rfl
        · exact absurd hnil (by simp)
  subst hpt
  exact int_read_of_checkArg_slot hwf hslot hfor hchk0 hxi hmem



/-! ## The master SAT linker (per-constraint, both shape families) -/

/-- **THE MASTER SAT LINKER (extracted arm)**: a model constraint that
    compiled through `extractConstraint` into a `DomConstraint`
    satisfied by an accepted assignment makes the source constraint
    hold at the assembled store. -/
theorem compile_sat_link_extracted {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {dc : DomConstraint}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hmem : a ∈ allAssigns (slots.map Prod.snd))
    (hex : extractConstraint (slots.map Prod.fst) c = some dc)
    (hsat : dc.SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hnu : (slots.map Prod.fst).Nodup := slotNames_nodup hwf hslot
  have halt : a.length = slots.length := by
    have h1 := mem_allAssigns_length (slots.map Prod.snd) a hmem
    rw [List.length_map] at h1
    exact h1
  -- the int-reads premise, name-conditioned: the eq/ne slot arms
  -- consult it; the typing chain supplies it there
  have hreads : ∀ (x : Ident) (i : Nat),
      Expr.basic (.ident x) ∈ c.args →
      nameIndex (slots.map Prod.fst) x.name = some i →
      (c.name.name = "int_eq" ∨ c.name.name = "int_ne") →
      ∃ p, a[i]! = Value.int p := by
    intro x i hxarg hxi hname
    exact int_reads_of_mem_eq_ne hwf hslot hc hpred hname hmem x i hxarg hxi
  exact extractConstraint_holds_converse hnu halt hex hreads hsat





/-- A successful argOf read pins the argument expression. -/
theorem argOf_ok_inv {c : ConstraintItem} {k : Nat} {b : BasicExpr}
    (h : argOf c k = .ok b) :
    c.args[k]! = .basic b := by
  unfold argOf at h
  cases he : c.args[k]! with
  | basic b2 =>
      rw [he] at h
      have hok : (Except.ok b2 : Except String BasicExpr) = .ok b := h
      injection hok with hb
      subst hb
      rfl
  | array es =>
      exfalso
      rw [he] at h
      exact absurd h (by simp)

/-- A store satisfies the parameter-honesty condition when every
    scalar parameter reads its declared literal value. -/
def ParamHonest (m : Model) (store : Store) : Prop :=
  ∀ d ∈ m.parameters, ∀ v, parDeclValue d = some v →
    store (ParDeclItem.name d) = some v

/-! ## The fallback gate inversions (per family) -/



/-- The source-shape disjunction shared by the two-argument fallback
    families: the non-slot argument is an int literal or a parameter
    identifier (resolving to the literal through the environment,
    with the name NOT a slot name). -/
def IntValuedArg (env : Store) (names : List String)
    (E : Expr) (k : Int) : Prop :=
  E = Expr.basic (.lit (.int k)) ∨ ∃ z, E = Expr.basic (.ident z) ∧
    nameIndex names z.name = none ∧ env z = some (.int k)

/-- The generic two-argument fallback do-block's inversion: a
    successful compile pins the argval pattern and the compiled
    form. -/
theorem fallback2_do_inv {env : Store} {names : List String}
    {b0 b1 : BasicExpr} {dc : DomConstraint}
    {f : Nat → Int → DomConstraint} {g : Int → Nat → DomConstraint}
    {msg : String}
    (h : ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) => .ok (f i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) => .ok (g k j)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error msg :
        Except String DomConstraint)) = .ok dc) :
    (∃ i k, compileArgVal env names b0 = .ok (.slotRef i) ∧
        compileArgVal env names b1 = .ok (.litVal (.int k)) ∧
        dc = f i k) ∨
    (∃ j k, compileArgVal env names b0 = .ok (.litVal (.int k)) ∧
        compileArgVal env names b1 = .ok (.slotRef j) ∧
        dc = g k j) := by
  split at h
  next i k hc0 hc1 =>
      exact Or.inl ⟨i, k, hc0, hc1, by
        have := (Except.ok.inj h)
        exact this ▸ rfl⟩
  next k j hc0 hc1 =>
      exact Or.inr ⟨j, k, hc0, hc1, by
        have := (Except.ok.inj h)
        exact this ▸ rfl⟩
  all_goals exact absurd h (by intro hc; injection hc)

/-- The int_le fallback gate: the do-block after the gate chain. -/
theorem fallback2_gate_le {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_le")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.leConstHi i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
            .ok (DomConstraint.leConstLo j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_le argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  have hplus_ne : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h1 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  unfold compileConstraint at h
  simp only [hnone] at h
  rw [if_neg hplus_ne] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          exact ⟨b0, b1, rfl, rfl, h⟩

/-- The int_lt fallback gate: the do-block after the gate chain. -/
theorem fallback2_gate_lt {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_lt")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.ltConstHi i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
            .ok (DomConstraint.ltConstLo j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_lt argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have hint_plus_ne : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h1 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_plus_ne] at h
  have hint_le_ne : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h1 : c.name.name = "int_le" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_le_ne] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          exact ⟨b0, b1, rfl, rfl, h⟩

/-- The int_gt fallback gate: the do-block after the gate chain. -/
theorem fallback2_gate_gt {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_gt")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.ltConstLo i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
            .ok (DomConstraint.ltConstHi j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_gt argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have hint_plus_ne : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h1 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_plus_ne] at h
  have hint_le_ne : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h1 : c.name.name = "int_le" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_le_ne] at h
  have hint_lt_ne : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
    intro hcon
    have h1 : c.name.name = "int_lt" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_lt_ne] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          exact ⟨b0, b1, rfl, rfl, h⟩

/-- The int_ge fallback gate: the do-block after the gate chain. -/
theorem fallback2_gate_ge {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_ge")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.leConstLo i k)
        | .ok (.litVal (.int k)), .ok (.slotRef j) =>
            .ok (DomConstraint.leConstHi j k)
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported int_ge argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have hint_plus_ne : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h1 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_plus_ne] at h
  have hint_le_ne : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h1 : c.name.name = "int_le" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_le_ne] at h
  have hint_lt_ne : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
    intro hcon
    have h1 : c.name.name = "int_lt" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_lt_ne] at h
  have hint_gt_ne : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
    intro hcon
    have h1 : c.name.name = "int_gt" := hcon.1
    rw [hname] at h1
    exact absurd h1 (by simp)
  rw [if_neg hint_gt_ne] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          exact ⟨b0, b1, rfl, rfl, h⟩


/-- The int_plus fallback gate: the three-argument do-block. -/
theorem fallback3_gate_plus {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_plus")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1 b2, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      argOf c 2 = .ok b2 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        let a2 ← (Except.ok b2 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1,
            compileArgVal env names b2 with
        | .ok (.slotRef i), .ok (.slotRef j), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.linEq [1, 1] [i, j] k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported int_plus argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  unfold compileConstraint at h
  simp only [hnone] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          match h2 : argOf c 2 with
          | .error e =>
              rw [h2] at h
              exact absurd h (by intro hc; injection hc)
          | .ok b2 =>
              rw [h2] at h
              exact ⟨b0, b1, b2, rfl, rfl, rfl, h⟩

/-- The int_plus do-block's inversion. -/
theorem fallback3_do_inv {env : Store} {names : List String}
    {b0 b1 b2 : BasicExpr} {dc : DomConstraint}
    (h : ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        let a2 ← (Except.ok b2 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1,
            compileArgVal env names b2 with
        | .ok (.slotRef i), .ok (.slotRef j), .ok (.litVal (.int k)) =>
            .ok (DomConstraint.linEq [1, 1] [i, j] k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported int_plus argument shapes" :
        Except String DomConstraint)) = .ok dc) :
    ∃ i j k, compileArgVal env names b0 = .ok (.slotRef i) ∧
      compileArgVal env names b1 = .ok (.slotRef j) ∧
      compileArgVal env names b2 = .ok (.litVal (.int k)) ∧
      dc = .linEq [1, 1] [i, j] k := by
  split at h
  next i j k hc0 hc1 hc2 =>
      exact ⟨i, j, k, hc0, hc1, hc2, by
        have := (Except.ok.inj h)
        exact this ▸ rfl⟩
  all_goals exact absurd h (by intro hc; injection hc)


/-- The full int_le fallback inversion: shape + compiled form. -/
theorem compileConstraint_le_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_le")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    (∃ x E i k, c.args = [Expr.basic (.ident x), E] ∧
      nameIndex names x.name = some i ∧ IntValuedArg env names E k ∧
      dc = .leConstHi i k) ∨
    (∃ y E j k, c.args = [E, Expr.basic (.ident y)] ∧
      nameIndex names y.name = some j ∧ IntValuedArg env names E k ∧
      dc = .leConstLo j k) := by
  have hlen := hargs
  obtain ⟨b0, b1, h0, h1, hdo⟩ :=
    fallback2_gate_le h hname hargs hnone
  rcases fallback2_do_inv (f := DomConstraint.leConstHi)
      (g := fun k j => DomConstraint.leConstLo j k)
      (msg := "unsupported int_le argument shapes") hdo with
    ⟨i, k, hc0, hc1, hdc⟩ | ⟨j, k, hc0, hc1, hdc⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    rcases compileArgVal_litVal_int_inv hc1 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    rcases compileArgVal_litVal_int_inv hc0 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩

/-- The full int_lt fallback inversion: shape + compiled form. -/
theorem compileConstraint_lt_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_lt")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    (∃ x E i k, c.args = [Expr.basic (.ident x), E] ∧
      nameIndex names x.name = some i ∧ IntValuedArg env names E k ∧
      dc = .ltConstHi i k) ∨
    (∃ y E j k, c.args = [E, Expr.basic (.ident y)] ∧
      nameIndex names y.name = some j ∧ IntValuedArg env names E k ∧
      dc = .ltConstLo j k) := by
  have hlen := hargs
  obtain ⟨b0, b1, h0, h1, hdo⟩ :=
    fallback2_gate_lt h hname hargs hnone
  rcases fallback2_do_inv (f := DomConstraint.ltConstHi)
      (g := fun k j => DomConstraint.ltConstLo j k)
      (msg := "unsupported int_lt argument shapes") hdo with
    ⟨i, k, hc0, hc1, hdc⟩ | ⟨j, k, hc0, hc1, hdc⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    rcases compileArgVal_litVal_int_inv hc1 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    rcases compileArgVal_litVal_int_inv hc0 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩


/-- The full int_gt fallback inversion: shape + compiled form. -/
theorem compileConstraint_gt_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_gt")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    (∃ x E i k, c.args = [Expr.basic (.ident x), E] ∧
      nameIndex names x.name = some i ∧ IntValuedArg env names E k ∧
      dc = .ltConstLo i k) ∨
    (∃ y E j k, c.args = [E, Expr.basic (.ident y)] ∧
      nameIndex names y.name = some j ∧ IntValuedArg env names E k ∧
      dc = .ltConstHi j k) := by
  have hlen := hargs
  obtain ⟨b0, b1, h0, h1, hdo⟩ :=
    fallback2_gate_gt h hname hargs hnone
  rcases fallback2_do_inv (f := DomConstraint.ltConstLo)
      (g := fun k j => DomConstraint.ltConstHi j k)
      (msg := "unsupported int_gt argument shapes") hdo with
    ⟨i, k, hc0, hc1, hdc⟩ | ⟨j, k, hc0, hc1, hdc⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    rcases compileArgVal_litVal_int_inv hc1 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    rcases compileArgVal_litVal_int_inv hc0 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩


/-- The full int_ge fallback inversion: shape + compiled form. -/
theorem compileConstraint_ge_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_ge")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    (∃ x E i k, c.args = [Expr.basic (.ident x), E] ∧
      nameIndex names x.name = some i ∧ IntValuedArg env names E k ∧
      dc = .leConstLo i k) ∨
    (∃ y E j k, c.args = [E, Expr.basic (.ident y)] ∧
      nameIndex names y.name = some j ∧ IntValuedArg env names E k ∧
      dc = .leConstHi j k) := by
  have hlen := hargs
  obtain ⟨b0, b1, h0, h1, hdo⟩ :=
    fallback2_gate_ge h hname hargs hnone
  rcases fallback2_do_inv (f := DomConstraint.leConstLo)
      (g := fun k j => DomConstraint.leConstHi j k)
      (msg := "unsupported int_ge argument shapes") hdo with
    ⟨i, k, hc0, hc1, hdc⟩ | ⟨j, k, hc0, hc1, hdc⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    rcases compileArgVal_litVal_int_inv hc1 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inl ⟨x, Expr.basic b1, i, k, ?_, hxi, ?_, hdc⟩
      · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    rcases compileArgVal_litVal_int_inv hc0 with hE | ⟨z, hE, hn, hz⟩
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr ⟨y, Expr.basic b0, j, k, ?_, hyi, ?_, hdc⟩
      · exact two_of_bang hargs (argOf_ok_inv h0) harg1
      · exact Or.inr ⟨z, by rw [hE], hn, hz⟩



/-- The full int_plus fallback inversion: shape + compiled form. -/
theorem compileConstraint_plus_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "int_plus")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    ∃ x y E i j k, c.args =
      [Expr.basic (.ident x), Expr.basic (.ident y), E] ∧
      nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      IntValuedArg env names E k ∧
      dc = .linEq [1, 1] [i, j] k := by
  obtain ⟨b0, b1, b2, h0, h1, h2, hdo⟩ :=
    fallback3_gate_plus h hname hargs hnone
  obtain ⟨i, j, k, hc0, hc1, hc2, hdc⟩ := fallback3_do_inv hdo
  obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
  obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
  have harg0 : c.args[0]! = Expr.basic (.ident x) :=
    (argOf_ok_inv h0).trans (congrArg _ hx)
  have harg1 : c.args[1]! = Expr.basic (.ident y) :=
    (argOf_ok_inv h1).trans (congrArg _ hy)
  rcases compileArgVal_litVal_int_inv hc2 with hE | ⟨z, hE, hn, hz⟩
  · refine ⟨x, y, Expr.basic b2, i, j, k, ?_, hxi, hyi, ?_, hdc⟩
    · exact three_of_bang hargs harg0 harg1 (argOf_ok_inv h2)
    · exact Or.inl (congrArg Expr.basic hE)
  · refine ⟨x, y, Expr.basic b2, i, j, k, ?_, hxi, hyi, ?_, hdc⟩
    · exact three_of_bang hargs harg0 harg1 (argOf_ok_inv h2)
    · exact Or.inr ⟨z, by rw [hE], hn, hz⟩

/-- A successful fallback compile of `bool_not` pins the argument
    count: the gate condition fired, so `c.args.length = 2`. -/
theorem compileConstraint_bool_not_len {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hnone : extractConstraint names c = none)
    (hname : c.name.name = "bool_not") :
    c.args.length = 2 := by
  by_cases hlen : c.args.length = 2
  · exact hlen
  · exfalso
    have hfall : compileConstraint env names c =
        .error s!"unsupported predicate '{c.name.name}'" := by
      unfold compileConstraint
      rw [hnone]
      have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
        intro hcon
        have h2 : c.name.name = "int_plus" := hcon.1
        rw [hname] at h2
        exact absurd h2 (by simp)
      have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
        intro hcon
        have h3 : c.name.name = "int_le" := hcon.1
        rw [hname] at h3
        exact absurd h3 (by simp)
      have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
        intro hcon
        have h4 : c.name.name = "int_lt" := hcon.1
        rw [hname] at h4
        exact absurd h4 (by simp)
      have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
        intro hcon
        have h5 : c.name.name = "int_gt" := hcon.1
        rw [hname] at h5
        exact absurd h5 (by simp)
      have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
        intro hcon
        have h6 : c.name.name = "int_ge" := hcon.1
        rw [hname] at h6
        exact absurd h6 (by simp)
      have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
        intro hcon
        exact absurd hcon.2 hlen
      have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
        intro hcon
        have h8 : c.name.name = "bool_and" := hcon.1
        rw [hname] at h8
        exact absurd h8 (by simp)
      have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
        intro hcon
        have h9 : c.name.name = "bool_or" := hcon.1
        rw [hname] at h9
        exact absurd h9 (by simp)
      have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
        intro hcon
        have h10 : c.name.name = "set_in" := hcon.1
        rw [hname] at h10
        exact absurd h10 (by simp)
      have h10 : ¬(c.name.name = "set_in_reif" ∧ c.args.length = 3) := by
        intro hcon
        have h11 : c.name.name = "set_in_reif" := hcon.1
        rw [hname] at h11
        exact absurd h11 (by simp)
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]
    rw [hfall] at h
    exact absurd h (by simp)

/-- The bool_not fallback gate: the two-argument do-block. -/
theorem fallback2_gate_bool_not {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "bool_not")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1 with
        | .ok (.slotRef i), .ok (.litVal (.bool b)) =>
            .ok (DomConstraint.constEq i (.bool (!b)))
        | .ok (.litVal (.bool b)), .ok (.slotRef j) =>
            .ok (DomConstraint.constEq j (.bool (!b)))
        | .error e, _ => .error e
        | _, .error e => .error e
        | _, _ => .error "unsupported bool_not argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h2 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h2
    exact absurd h2 (by simp)
  have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h3 : c.name.name = "int_le" := hcon.1
    rw [hname] at h3
    exact absurd h3 (by simp)
  have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
    intro hcon
    have h4 : c.name.name = "int_lt" := hcon.1
    rw [hname] at h4
    exact absurd h4 (by simp)
  have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
    intro hcon
    have h5 : c.name.name = "int_gt" := hcon.1
    rw [hname] at h5
    exact absurd h5 (by simp)
  have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
    intro hcon
    have h6 : c.name.name = "int_ge" := hcon.1
    rw [hname] at h6
    exact absurd h6 (by simp)
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          exact ⟨b0, b1, rfl, rfl, h⟩

/-- The bool_and fallback gate: the three-argument do-block. -/
theorem fallback3_gate_bool_and {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "bool_and")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1 b2, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      argOf c 2 = .ok b2 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        let a2 ← (Except.ok b2 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1,
            compileArgVal env names b2 with
        | .ok (.slotRef i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.slotRef _i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .ok (.litVal (.bool true)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .ok (.litVal (.bool false)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported bool_and argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h2 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h2
    exact absurd h2 (by simp)
  have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h3 : c.name.name = "int_le" := hcon.1
    rw [hname] at h3
    exact absurd h3 (by simp)
  have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
    intro hcon
    have h4 : c.name.name = "int_lt" := hcon.1
    rw [hname] at h4
    exact absurd h4 (by simp)
  have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
    intro hcon
    have h5 : c.name.name = "int_gt" := hcon.1
    rw [hname] at h5
    exact absurd h5 (by simp)
  have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
    intro hcon
    have h6 : c.name.name = "int_ge" := hcon.1
    rw [hname] at h6
    exact absurd h6 (by simp)
  have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
    intro hcon
    have h7 : c.name.name = "bool_not" := hcon.1
    rw [hname] at h7
    exact absurd h7 (by simp)
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          match h2 : argOf c 2 with
          | .error e =>
              rw [h2] at h
              exact absurd h (by intro hc; injection hc)
          | .ok b2 =>
              rw [h2] at h
              exact ⟨b0, b1, b2, rfl, rfl, rfl, h⟩

/-- The bool_or fallback gate: the three-argument do-block. -/
theorem fallback3_gate_bool_or {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "bool_or")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1 b2, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      argOf c 2 = .ok b2 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        let a2 ← (Except.ok b2 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1,
            compileArgVal env names b2 with
        | .ok (.slotRef _i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.slotRef i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.litVal (.bool true)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.litVal (.bool false)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported bool_or argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  unfold compileConstraint at h
  simp only [hnone] at h
  have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h2 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h2
    exact absurd h2 (by simp)
  have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h3 : c.name.name = "int_le" := hcon.1
    rw [hname] at h3
    exact absurd h3 (by simp)
  have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
    intro hcon
    have h4 : c.name.name = "int_lt" := hcon.1
    rw [hname] at h4
    exact absurd h4 (by simp)
  have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
    intro hcon
    have h5 : c.name.name = "int_gt" := hcon.1
    rw [hname] at h5
    exact absurd h5 (by simp)
  have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
    intro hcon
    have h6 : c.name.name = "int_ge" := hcon.1
    rw [hname] at h6
    exact absurd h6 (by simp)
  have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
    intro hcon
    have h7 : c.name.name = "bool_not" := hcon.1
    rw [hname] at h7
    exact absurd h7 (by simp)
  have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
    intro hcon
    have h8 : c.name.name = "bool_and" := hcon.1
    rw [hname] at h8
    exact absurd h8 (by simp)
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5, if_neg h6,
    if_neg h7] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          match h2 : argOf c 2 with
          | .error e =>
              rw [h2] at h
              exact absurd h (by intro hc; injection hc)
          | .ok b2 =>
              rw [h2] at h
              exact ⟨b0, b1, b2, rfl, rfl, rfl, h⟩

/-- The bool_and fallback do-block's inversion. -/
theorem fallback3_do_inv_bool_and {env : Store} {names : List String}
    {b0 b1 b2 : BasicExpr} {dc : DomConstraint}
    (h : ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        let a2 ← (Except.ok b2 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1,
            compileArgVal env names b2 with
        | .ok (.slotRef i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.slotRef _i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .ok (.litVal (.bool true)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .ok (.litVal (.bool false)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported bool_and argument shapes" :
        Except String DomConstraint)) = .ok dc) :
    (∃ i k, compileArgVal env names b0 = .ok (.slotRef i) ∧
        compileArgVal env names b1 = .ok (.litVal (.bool true)) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .eqSlot i k) ∨
    (∃ i k, compileArgVal env names b0 = .ok (.slotRef i) ∧
        compileArgVal env names b1 = .ok (.litVal (.bool false)) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .constEq k (.bool false)) ∨
    (∃ j k, compileArgVal env names b0 = .ok (.litVal (.bool true)) ∧
        compileArgVal env names b1 = .ok (.slotRef j) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .eqSlot j k) ∨
    (∃ j k, compileArgVal env names b0 = .ok (.litVal (.bool false)) ∧
        compileArgVal env names b1 = .ok (.slotRef j) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .constEq k (.bool false)) := by
  split at h
  next i k hc0 hc1 hc2 =>
      refine Or.inl ⟨i, k, hc0, hc1, hc2, ?_⟩
      have := (Except.ok.inj h)
      exact this ▸ rfl
  next k hc0 hc1 hc2 =>
      refine Or.inr (Or.inl ⟨_, k, hc0, hc1, hc2, ?_⟩)
      have := (Except.ok.inj h)
      exact this ▸ rfl
  next j k hc0 hc1 hc2 =>
      refine Or.inr (Or.inr (Or.inl ⟨j, k, hc0, hc1, hc2, ?_⟩))
      have := (Except.ok.inj h)
      exact this ▸ rfl
  next k hc0 hc1 hc2 =>
      refine Or.inr (Or.inr (Or.inr ⟨_, k, hc0, hc1, hc2, ?_⟩))
      have := (Except.ok.inj h)
      exact this ▸ rfl
  all_goals exact absurd h (by intro hc; injection hc)

/-- The bool_or fallback do-block's inversion. -/
theorem fallback3_do_inv_bool_or {env : Store} {names : List String}
    {b0 b1 b2 : BasicExpr} {dc : DomConstraint}
    (h : ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        let a2 ← (Except.ok b2 : Except String BasicExpr)
        match compileArgVal env names b0, compileArgVal env names b1,
            compileArgVal env names b2 with
        | .ok (.slotRef _i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.slotRef i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.litVal (.bool true)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.litVal (.bool false)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ => .error "unsupported bool_or argument shapes" :
        Except String DomConstraint)) = .ok dc) :
    (∃ i k, compileArgVal env names b0 = .ok (.slotRef i) ∧
        compileArgVal env names b1 = .ok (.litVal (.bool true)) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .constEq k (.bool true)) ∨
    (∃ j k, compileArgVal env names b0 = .ok (.litVal (.bool true)) ∧
        compileArgVal env names b1 = .ok (.slotRef j) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .constEq k (.bool true)) ∨
    (∃ i k, compileArgVal env names b0 = .ok (.slotRef i) ∧
        compileArgVal env names b1 = .ok (.litVal (.bool false)) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .eqSlot i k) ∨
    (∃ j k, compileArgVal env names b0 = .ok (.litVal (.bool false)) ∧
        compileArgVal env names b1 = .ok (.slotRef j) ∧
        compileArgVal env names b2 = .ok (.slotRef k) ∧
        dc = .eqSlot j k) := by
  split at h
  next k hc0 hc1 hc2 =>
      refine Or.inl ⟨_, k, hc0, hc1, hc2, ?_⟩
      have := (Except.ok.inj h)
      exact this ▸ rfl
  next i k hc0 hc1 hc2 =>
      refine Or.inr (Or.inr (Or.inl ⟨i, k, hc0, hc1, hc2, ?_⟩))
      have := (Except.ok.inj h)
      exact this ▸ rfl
  next k hc0 hc1 hc2 =>
      refine Or.inr (Or.inl ⟨_, k, hc0, hc1, hc2, ?_⟩)
      have := (Except.ok.inj h)
      exact this ▸ rfl
  next j k hc0 hc1 hc2 =>
      refine Or.inr (Or.inr (Or.inr ⟨j, k, hc0, hc1, hc2, ?_⟩))
      have := (Except.ok.inj h)
      exact this ▸ rfl
  all_goals exact absurd h (by intro hc; injection hc)

/-- A `litVal (.bool b)` compile comes only from a bool-literal
    expression or an identifier resolving to it (through the name
    list or the parameter environment). -/
theorem compileArgVal_litVal_bool_inv {env : Store} {names : List String}
    {b : BasicExpr} {w : Bool}
    (h : compileArgVal env names b = .ok (.litVal (.bool w))) :
    b = .lit (.bool w) ∨
      (∃ x, b = .ident x ∧ nameIndex names x.name = none ∧
        env x = some (.bool w)) := by
  cases b with
  | lit l =>
      cases l with
      | int v => simp only [compileArgVal] at h; cases h
      | bool v =>
          simp only [compileArgVal] at h
          have hvv : ArgVal.litVal (Value.bool v)
              = ArgVal.litVal (Value.bool w) := (Except.ok.inj h)
          have h2 : v = w := by injection hvv with h3; injection h3
          exact Or.inl (by rw [h2])
      | set v => simp only [compileArgVal] at h; cases h
  | ident x =>
      simp only [compileArgVal] at h
      cases hn : nameIndex names x.name with
      | none =>
          simp only [hn] at h
          cases hex : env x with
          | none => rw [hex] at h; cases h
          | some v =>
              simp only [hex] at h
              have hvv : ArgVal.litVal v
                  = ArgVal.litVal (Value.bool w) := (Except.ok.inj h)
              have h2 : v = Value.bool w := by injection hvv
              exact Or.inr ⟨x, rfl, hn, by rw [← h2]; exact hex⟩
      | some i2 => rw [hn] at h; cases h

/-- The bool-valued-argument analogue of `IntValuedArg`: the literal
    expression or parameter identifier a `.bool w` argval came from. -/
def BoolValuedArg (env : Store) (names : List String)
    (E : Expr) (w : Bool) : Prop :=
  E = Expr.basic (.lit (.bool w)) ∨ ∃ z, E = Expr.basic (.ident z) ∧
    nameIndex names z.name = none ∧ env z = some (.bool w)

/-- The full bool_not fallback inversion: shape + compiled form. -/
theorem compileConstraint_bool_not_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "bool_not")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    (∃ x E i w, c.args = [Expr.basic (.ident x), E] ∧
      nameIndex names x.name = some i ∧ BoolValuedArg env names E w ∧
      dc = .constEq i (.bool (!w))) ∨
    (∃ y E j w, c.args = [E, Expr.basic (.ident y)] ∧
      nameIndex names y.name = some j ∧ BoolValuedArg env names E w ∧
      dc = .constEq j (.bool (!w))) := by
  obtain ⟨b0, b1, h0, h1, hdo⟩ :=
    fallback2_gate_bool_not h hname hargs hnone
  split at hdo
  next i b hc0 hc1 =>
      obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
      have harg0 : c.args[0]! = Expr.basic (.ident x) :=
        (argOf_ok_inv h0).trans (congrArg _ hx)
      rcases compileArgVal_litVal_bool_inv hc1 with hE | ⟨z, hE, hn, hz⟩
      · refine Or.inl ⟨x, Expr.basic b1, i, b, ?_, hxi, ?_, ?_⟩
        · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
        · exact Or.inl (congrArg Expr.basic hE)
        · have := (Except.ok.inj hdo)
          exact this ▸ rfl
      · refine Or.inl ⟨x, Expr.basic b1, i, b, ?_, hxi, ?_, ?_⟩
        · exact two_of_bang hargs harg0 (argOf_ok_inv h1)
        · exact Or.inr ⟨z, by rw [hE], hn, hz⟩
        · have := (Except.ok.inj hdo)
          exact this ▸ rfl
  next b j hc0 hc1 =>
      obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
      have harg1 : c.args[1]! = Expr.basic (.ident y) :=
        (argOf_ok_inv h1).trans (congrArg _ hy)
      rcases compileArgVal_litVal_bool_inv hc0 with hE | ⟨z, hE, hn, hz⟩
      · refine Or.inr ⟨y, Expr.basic b0, j, b, ?_, hyi, ?_, ?_⟩
        · exact two_of_bang hargs (argOf_ok_inv h0) harg1
        · exact Or.inl (congrArg Expr.basic hE)
        · have := (Except.ok.inj hdo)
          exact this ▸ rfl
      · refine Or.inr ⟨y, Expr.basic b0, j, b, ?_, hyi, ?_, ?_⟩
        · exact two_of_bang hargs (argOf_ok_inv h0) harg1
        · exact Or.inr ⟨z, by rw [hE], hn, hz⟩
        · have := (Except.ok.inj hdo)
          exact this ▸ rfl
  all_goals exact absurd hdo (by intro hc; injection hc)

/-- The full bool_and fallback inversion: shape + compiled form. -/
theorem compileConstraint_bool_and_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "bool_and")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    (∃ x z E i k, c.args =
        [Expr.basic (.ident x), E, Expr.basic (.ident z)] ∧
      nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E true ∧ dc = .eqSlot i k) ∨
    (∃ x z E i k, c.args =
        [Expr.basic (.ident x), E, Expr.basic (.ident z)] ∧
      nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E false ∧ dc = .constEq k (.bool false)) ∨
    (∃ y z E j k, c.args =
        [E, Expr.basic (.ident y), Expr.basic (.ident z)] ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E true ∧ dc = .eqSlot j k) ∨
    (∃ y z E j k, c.args =
        [E, Expr.basic (.ident y), Expr.basic (.ident z)] ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E false ∧ dc = .constEq k (.bool false)) := by
  obtain ⟨b0, b1, b2, h0, h1, h2, hdo⟩ :=
    fallback3_gate_bool_and h hname hargs hnone
  rcases fallback3_do_inv_bool_and hdo with
    ⟨i, k, hc0, hc1, hc2, hdc⟩ |
    ⟨i, k, hc0, hc1, hc2, hdc⟩ |
    ⟨j, k, hc0, hc1, hc2, hdc⟩ |
    ⟨j, k, hc0, hc1, hc2, hdc⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc1 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi, hzi, ?_, hdc⟩
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi, hzi, ?_, hdc⟩
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc1 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inr (Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi, hzi,
        ?_, hdc⟩)
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr (Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi, hzi,
        ?_, hdc⟩)
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc0 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inr (Or.inr (Or.inl ⟨y, z, Expr.basic b0, j, k, ?_, hyi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr (Or.inr (Or.inl ⟨y, z, Expr.basic b0, j, k, ?_, hyi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc0 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inr (Or.inr (Or.inr ⟨y, z, Expr.basic b0, j, k, ?_, hyi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr (Or.inr (Or.inr ⟨y, z, Expr.basic b0, j, k, ?_, hyi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩

/-- The full bool_or fallback inversion: shape + compiled form. -/
theorem compileConstraint_bool_or_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "bool_or")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    (∃ x z E i k, c.args =
        [Expr.basic (.ident x), E, Expr.basic (.ident z)] ∧
      nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E true ∧ dc = .constEq k (.bool true)) ∨
    (∃ y z E j k, c.args =
        [E, Expr.basic (.ident y), Expr.basic (.ident z)] ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E true ∧ dc = .constEq k (.bool true)) ∨
    (∃ x z E i k, c.args =
        [Expr.basic (.ident x), E, Expr.basic (.ident z)] ∧
      nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E false ∧ dc = .eqSlot i k) ∨
    (∃ y z E j k, c.args =
        [E, Expr.basic (.ident y), Expr.basic (.ident z)] ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      BoolValuedArg env names E false ∧ dc = .eqSlot j k) := by
  obtain ⟨b0, b1, b2, h0, h1, h2, hdo⟩ :=
    fallback3_gate_bool_or h hname hargs hnone
  rcases fallback3_do_inv_bool_or hdo with
    ⟨i, k, hc0, hc1, hc2, hdc⟩ |
    ⟨j, k, hc0, hc1, hc2, hdc⟩ |
    ⟨i, k, hc0, hc1, hc2, hdc⟩ |
    ⟨j, k, hc0, hc1, hc2, hdc⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc1 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi, hzi, ?_, hdc⟩
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi, hzi, ?_, hdc⟩
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc0 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inr (Or.inl ⟨y, z, Expr.basic b0, j, k, ?_, hyi, hzi,
        ?_, hdc⟩)
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr (Or.inl ⟨y, z, Expr.basic b0, j, k, ?_, hyi, hzi,
        ?_, hdc⟩)
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩
  · obtain ⟨x, hx, hxi⟩ := compileArgVal_slotRef_inv hc0
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg0 : c.args[0]! = Expr.basic (.ident x) :=
      (argOf_ok_inv h0).trans (congrArg _ hx)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc1 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inr (Or.inr (Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr (Or.inr (Or.inl ⟨x, z, Expr.basic b1, i, k, ?_, hxi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs harg0 (argOf_ok_inv h1) harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩
  · obtain ⟨y, hy, hyi⟩ := compileArgVal_slotRef_inv hc1
    obtain ⟨z, hz, hzi⟩ := compileArgVal_slotRef_inv hc2
    have harg1 : c.args[1]! = Expr.basic (.ident y) :=
      (argOf_ok_inv h1).trans (congrArg _ hy)
    have harg2 : c.args[2]! = Expr.basic (.ident z) :=
      (argOf_ok_inv h2).trans (congrArg _ hz)
    rcases compileArgVal_litVal_bool_inv hc0 with hE | ⟨w, hE, hn, hw⟩
    · refine Or.inr (Or.inr (Or.inr ⟨y, z, Expr.basic b0, j, k, ?_, hyi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inl (congrArg Expr.basic hE)
    · refine Or.inr (Or.inr (Or.inr ⟨y, z, Expr.basic b0, j, k, ?_, hyi,
        hzi, ?_, hdc⟩))
      · exact three_of_bang hargs (argOf_ok_inv h0) harg1 harg2
      · exact Or.inr ⟨w, by rw [hE], hn, hw⟩

/-- A successful fallback compile of a comparison family pins the
    argument count: the gate condition fired, so `c.args.length = 2`. -/
theorem compileConstraint_fallback2_len {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hnone : extractConstraint names c = none)
    (hname : c.name.name = "int_le" ∨ c.name.name = "int_lt" ∨
      c.name.name = "int_gt" ∨ c.name.name = "int_ge") :
    c.args.length = 2 := by
  by_cases hlen : c.args.length = 2
  · exact hlen
  · exfalso
    -- every comparison gate is false (the length fails), and the
    -- plus gate fails by the name; the chain falls to the error
    have hfall : compileConstraint env names c =
        .error s!"unsupported predicate '{c.name.name}'" := by
      unfold compileConstraint
      rw [hnone]
      have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn | hn <;>
          exact absurd hcon.1 (by rw [hn]; simp)
      have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.2 hlen
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.2 hlen
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.2 hlen
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.2 hlen
      have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h10 : ¬(c.name.name = "set_in_reif" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]
    rw [hfall] at h
    exact absurd h (by simp)

/-- A successful fallback compile of `int_plus` pins the argument
    count: the gate condition fired, so `c.args.length = 3`. -/
theorem compileConstraint_fallback3_len {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hnone : extractConstraint names c = none)
    (hname : c.name.name = "int_plus" ∨ c.name.name = "bool_and" ∨
      c.name.name = "bool_or") :
    c.args.length = 3 := by
  by_cases hlen : c.args.length = 3
  · exact hlen
  · exfalso
    have hfall : compileConstraint env names c =
        .error s!"unsupported predicate '{c.name.name}'" := by
      unfold compileConstraint
      rw [hnone]
      have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.2 hlen
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.2 hlen
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.2 hlen
      have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
      have h10 : ¬(c.name.name = "set_in_reif" ∧ c.args.length = 3) := by
        intro hcon
        rcases hname with hn | hn | hn
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.1 (by rw [hn]; simp)
        · exact absurd hcon.2 hlen
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]
    rw [hfall] at h
    exact absurd h (by simp)

/-- The E-evaluation premise for a fallback constraint's int-valued
    argument at the assembled store: a literal denotes itself; a
    parameter identifier reads its `parEnv` value (the name is not a
    slot, so `toStore` goes through the parameter environment). -/
theorem eval_intValuedArg {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {E : Expr} {k : Int}
    (halt : a.length = slots.length)
    (hE : IntValuedArg (parEnv m) (slots.map Prod.fst) E k) :
    Expr.eval ((assemble m slots dcs).toStore a) E = some (.int k) := by
  rcases hE with hE | ⟨z, hE, hn, hz⟩
  · rw [hE]
    show (Expr.basic (BasicExpr.lit (BasicLiteral.int k))).eval
        ((assemble m slots dcs).toStore a) = some (Value.int k)
    rfl
  · rw [hE]
    show (Expr.basic (BasicExpr.ident z)).eval
        ((assemble m slots dcs).toStore a) = some (Value.int k)
    show (assemble m slots dcs).toStore a z = some (Value.int k)
    rw [toStore_param hn hz]

/-- The bool-valued-argument analogue of `eval_intValuedArg`. -/
theorem eval_boolValuedArg {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {E : Expr} {w : Bool}
    (halt : a.length = slots.length)
    (hE : BoolValuedArg (parEnv m) (slots.map Prod.fst) E w) :
    Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool w) := by
  rcases hE with hE | ⟨z, hE, hn, hz⟩
  · rw [hE]
    show (Expr.basic (BasicExpr.lit (BasicLiteral.bool w))).eval
        ((assemble m slots dcs).toStore a) = some (Value.bool w)
    rfl
  · rw [hE]
    show (Expr.basic (BasicExpr.ident z)).eval
        ((assemble m slots dcs).toStore a) = some (Value.bool w)
    show (assemble m slots dcs).toStore a z = some (Value.bool w)
    rw [toStore_param hn hz]

/-- bool_not(x, E) with E evaluating to `.bool w` (compiled
    `constEq i (.bool !w)`). -/
theorem holds_bool_not_lit_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {i : Nat} {w : Bool}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_not")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool w))
    (hsat : (DomConstraint.constEq i (.bool (!w))).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hw : a[i]? = some (.bool (!w)) := hsat
  have hib : a[i]! = Value.bool (!w) := bang_of_getElem? hw
  refine ⟨[a[i]!, .bool w], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_any hnu halt hxi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.bool w] with
      | [Value.bool p, Value.bool q] => q = !p
      | _ => False)
    rw [hib]
    simp [Bool.not_not]

/-- bool_not(E, y) with E evaluating to `.bool w` (compiled
    `constEq j (.bool !w)`). -/
theorem holds_bool_not_lit_E' {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y : Ident} {j : Nat} {w : Bool}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_not")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool w))
    (hsat : (DomConstraint.constEq j (.bool (!w))).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hw : a[j]? = some (.bool (!w)) := hsat
  have hjb : a[j]! = Value.bool (!w) := bang_of_getElem? hw
  refine ⟨[.bool w, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_any hnu halt hyi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.bool w, a[j]!] with
      | [Value.bool p, Value.bool q] => q = !p
      | _ => False)
    rw [hjb]

/-- Evaluation of an identifier, an arbitrary-valued expression, and
    an identifier (the `bool_and(x, E, z)` shape's argument bridge). -/
theorem eval_ident_E_E_ident {m : Model}
    {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {x z : Ident}
    {i k : Nat} {e2 : Expr} {w2 : Value}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (he2 : Expr.eval ((assemble m slots dcs).toStore a) e2 = some w2) :
    ([Expr.basic (.ident x), e2, Expr.basic (.ident z)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [a[i]!, w2, a[k]!] := by
  show (do
      let v1 ← (assemble m slots dcs).toStore a x
      let v2 ← Expr.eval ((assemble m slots dcs).toStore a) e2
      let v3 ← (assemble m slots dcs).toStore a z
      pure [v1, v2, v3]) = _
  rw [toStore_read (m := m) hnu hxi halt, he2,
    toStore_read (m := m) hnu hzi halt]
  rfl

/-- Evaluation of an arbitrary-valued expression and two identifiers
    (the `bool_and(E, y, z)` shape's argument bridge). -/
theorem eval_E_ident_ident {m : Model}
    {slots : List (String × List Value)}
    {dcs : List DomConstraint} {a : List Value} {y z : Ident}
    {j k : Nat} {e1 : Expr} {w1 : Value}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (he1 : Expr.eval ((assemble m slots dcs).toStore a) e1 = some w1) :
    ([e1, Expr.basic (.ident y), Expr.basic (.ident z)].mapM
      (Expr.eval ((assemble m slots dcs).toStore a)))
      = some [w1, a[j]!, a[k]!] := by
  show (do
      let v1 ← Expr.eval ((assemble m slots dcs).toStore a) e1
      let v2 ← (assemble m slots dcs).toStore a y
      let v3 ← (assemble m slots dcs).toStore a z
      pure [v1, v2, v3]) = _
  rw [he1, toStore_read (m := m) hnu hyi halt,
    toStore_read (m := m) hnu hzi halt]
  rfl

/-- bool_and(x, E, z) with E evaluating to `.bool true` (compiled
    `eqSlot i k`); the first slot's read is Boolean (the typing
    chain supplies it). -/
theorem holds_bool_and_true_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x z : Ident} {i k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [Expr.basic (.ident x), E, Expr.basic (.ident z)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[i]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool true))
    (hsat : (DomConstraint.eqSlot i k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨w, w2, hw, hw2, heq⟩ := hsat
  have hib : a[i]! = w := bang_of_getElem? hw
  have hkb : a[k]! = w2 := bang_of_getElem? hw2
  obtain ⟨p, hp⟩ := hread
  have hw1 : w = Value.bool p := hib.symm.trans hp
  refine ⟨[a[i]!, .bool true, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_E_ident (m := m) hnu halt hxi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.bool true, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
      | _ => False)
    rw [hp, hkb, ← heq, hw1]
    simp only [Bool.and_true]

/-- bool_and(x, E, z) with E evaluating to `.bool false` (compiled
    `constEq k (.bool false)`); the first slot's read is Boolean. -/
theorem holds_bool_and_false_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x z : Ident} {i k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [Expr.basic (.ident x), E, Expr.basic (.ident z)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[i]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool false))
    (hsat : (DomConstraint.constEq k (.bool false)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hw : a[k]? = some (.bool false) := hsat
  have hkb : a[k]! = Value.bool false := bang_of_getElem? hw
  obtain ⟨p, hp⟩ := hread
  refine ⟨[a[i]!, .bool false, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_E_ident (m := m) hnu halt hxi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.bool false, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
      | _ => False)
    rw [hp, hkb]
    simp only [Bool.and_false]

/-- bool_and(E, y, z) with E evaluating to `.bool true` (compiled
    `eqSlot j k`); the second slot's read is Boolean. -/
theorem holds_bool_and_true_E' {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y z : Ident} {j k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [E, Expr.basic (.ident y), Expr.basic (.ident z)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[j]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool true))
    (hsat : (DomConstraint.eqSlot j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨w, w2, hw, hw2, heq⟩ := hsat
  have hjb : a[j]! = w := bang_of_getElem? hw
  have hkb : a[k]! = w2 := bang_of_getElem? hw2
  obtain ⟨p, hp⟩ := hread
  have hw1 : w = Value.bool p := hjb.symm.trans hp
  refine ⟨[.bool true, a[j]!, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_ident_ident (m := m) hnu halt hyi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.bool true, a[j]!, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
      | _ => False)
    rw [hp, hkb, ← heq, hw1]
    simp only [Bool.true_and]

/-- bool_and(E, y, z) with E evaluating to `.bool false` (compiled
    `constEq k (.bool false)`); the second slot's read is Boolean. -/
theorem holds_bool_and_false_E' {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y z : Ident} {j k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [E, Expr.basic (.ident y), Expr.basic (.ident z)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[j]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool false))
    (hsat : (DomConstraint.constEq k (.bool false)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hw : a[k]? = some (.bool false) := hsat
  have hkb : a[k]! = Value.bool false := bang_of_getElem? hw
  obtain ⟨p, hp⟩ := hread
  refine ⟨[.bool false, a[j]!, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_ident_ident (m := m) hnu halt hyi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.bool false, a[j]!, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
      | _ => False)
    rw [hp, hkb]
    simp only [Bool.false_and]

/-- bool_or(x, E, z) with E evaluating to `.bool true` (compiled
    `constEq k (.bool true)`); the first slot's read is Boolean. -/
theorem holds_bool_or_true_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x z : Ident} {i k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [Expr.basic (.ident x), E, Expr.basic (.ident z)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[i]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool true))
    (hsat : (DomConstraint.constEq k (.bool true)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hw : a[k]? = some (.bool true) := hsat
  have hkb : a[k]! = Value.bool true := bang_of_getElem? hw
  obtain ⟨p, hp⟩ := hread
  refine ⟨[a[i]!, .bool true, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_E_ident (m := m) hnu halt hxi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.bool true, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
      | _ => False)
    rw [hp, hkb]
    simp only [Bool.or_true]

/-- bool_or(x, E, z) with E evaluating to `.bool false` (compiled
    `eqSlot i k`); the first slot's read is Boolean. -/
theorem holds_bool_or_false_E {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x z : Ident} {i k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [Expr.basic (.ident x), E, Expr.basic (.ident z)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[i]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool false))
    (hsat : (DomConstraint.eqSlot i k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨w, w2, hw, hw2, heq⟩ := hsat
  have hib : a[i]! = w := bang_of_getElem? hw
  have hkb : a[k]! = w2 := bang_of_getElem? hw2
  obtain ⟨p, hp⟩ := hread
  have hw1 : w = Value.bool p := hib.symm.trans hp
  refine ⟨[a[i]!, .bool false, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_E_ident (m := m) hnu halt hxi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.bool false, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
      | _ => False)
    rw [hp, hkb, ← heq, hw1]
    simp only [Bool.or_false]

/-- bool_or(E, y, z) with E evaluating to `.bool true` (compiled
    `constEq k (.bool true)`); the second slot's read is Boolean. -/
theorem holds_bool_or_true_E' {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y z : Ident} {j k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [E, Expr.basic (.ident y), Expr.basic (.ident z)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[j]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool true))
    (hsat : (DomConstraint.constEq k (.bool true)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hw : a[k]? = some (.bool true) := hsat
  have hkb : a[k]! = Value.bool true := bang_of_getElem? hw
  obtain ⟨p, hp⟩ := hread
  refine ⟨[.bool true, a[j]!, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_ident_ident (m := m) hnu halt hyi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.bool true, a[j]!, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
      | _ => False)
    rw [hp, hkb]
    simp only [Bool.true_or]

/-- bool_or(E, y, z) with E evaluating to `.bool false` (compiled
    `eqSlot j k`); the second slot's read is Boolean. -/
theorem holds_bool_or_false_E' {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {y z : Ident} {j k : Nat}
    {E : Expr}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [E, Expr.basic (.ident y), Expr.basic (.ident z)])
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hread : ∃ p, a[j]! = Value.bool p)
    (hE : Expr.eval ((assemble m slots dcs).toStore a) E = some (.bool false))
    (hsat : (DomConstraint.eqSlot j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨w, w2, hw, hw2, heq⟩ := hsat
  have hjb : a[j]! = w := bang_of_getElem? hw
  have hkb : a[k]! = w2 := bang_of_getElem? hw2
  obtain ⟨p, hp⟩ := hread
  have hw1 : w = Value.bool p := hjb.symm.trans hp
  refine ⟨[.bool false, a[j]!, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_ident_ident (m := m) hnu halt hyi hzi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.bool false, a[j]!, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
      | _ => False)
    rw [hp, hkb, ← heq, hw1]
    simp only [Bool.false_or]

/-! ## The C0 set-membership fallback family -/

/-- The set_in fallback gate: the two-argument do-block (a slot
    identifier against a constant set: a set literal or a parameter
    resolved to one). -/
theorem fallback2_gate_set_in {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "set_in")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        match a0, a1 with
        | .ident xa, .lit (.set sa) =>
            match nameIndex names xa.name with
            | some i => .ok (DomConstraint.setInSlot i sa.denote)
            | none =>
                .error s!"unresolved name '{xa.name}' in set_in"
        | .ident xa, .ident pa =>
            match nameIndex names xa.name with
            | some i =>
                match nameIndex names pa.name with
                | none =>
                    match env pa with
                    | some (.setOfInt sv) => .ok (DomConstraint.setInSlot i sv)
                    | _ => .error "set_in over a non-set parameter"
                | some _ =>
                    .error "set_in over a slot-typed set argument"
            | none => .error s!"unresolved name '{xa.name}' in set_in"
        | _, _ => .error "unsupported set_in argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h2 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h2
    exact absurd h2 (by simp)
  have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h3 : c.name.name = "int_le" := hcon.1
    rw [hname] at h3
    exact absurd h3 (by simp)
  have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
    intro hcon
    have h4 : c.name.name = "int_lt" := hcon.1
    rw [hname] at h4
    exact absurd h4 (by simp)
  have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
    intro hcon
    have h5 : c.name.name = "int_gt" := hcon.1
    rw [hname] at h5
    exact absurd h5 (by simp)
  have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
    intro hcon
    have h6 : c.name.name = "int_ge" := hcon.1
    rw [hname] at h6
    exact absurd h6 (by simp)
  have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
    intro hcon
    have h7 : c.name.name = "bool_not" := hcon.1
    rw [hname] at h7
    exact absurd h7 (by simp)
  have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
    intro hcon
    have h8 : c.name.name = "bool_and" := hcon.1
    rw [hname] at h8
    exact absurd h8 (by simp)
  have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
    intro hcon
    have h9 : c.name.name = "bool_or" := hcon.1
    rw [hname] at h9
    exact absurd h9 (by simp)
  unfold compileConstraint at h
  simp only [hnone] at h
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
    if_neg h6, if_neg h7, if_neg h8] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          exact ⟨b0, b1, rfl, rfl, h⟩

/-- The set_in_reif fallback gate: the three-argument do-block. -/
theorem fallback3_gate_set_in_reif {env : Store} {names : List String}
    {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    ∃ b0 b1 b2, argOf c 0 = .ok b0 ∧ argOf c 1 = .ok b1 ∧
      argOf c 2 = .ok b2 ∧
      ((do
        let a0 ← (Except.ok b0 : Except String BasicExpr)
        let a1 ← (Except.ok b1 : Except String BasicExpr)
        let a2 ← (Except.ok b2 : Except String BasicExpr)
        match a0, a1, a2 with
        | .ident xa, .lit (.set sa), .ident ra =>
            match nameIndex names xa.name, nameIndex names ra.name with
            | some i, some k => .ok (DomConstraint.setInReifSlot i sa.denote k)
            | some _, none =>
                .error s!"unresolved name '{ra.name}' in set_in_reif"
            | none, _ =>
                .error s!"unresolved name '{xa.name}' in set_in_reif"
        | .ident xa, .lit (.set sa), .lit (.bool true) =>
            match nameIndex names xa.name with
            | some i => .ok (DomConstraint.setInSlot i sa.denote)
            | none =>
                .error s!"unresolved name '{xa.name}' in set_in_reif"
        | .ident xa, .lit (.set sa), .lit (.bool false) =>
            .error "set_in_reif with a false literal is outside the certified fragment (complement of a finite set)"
        | .ident xa, .ident pa, .ident ra =>
            match nameIndex names xa.name with
            | some i =>
                match nameIndex names ra.name with
                | some k =>
                    match nameIndex names pa.name, env pa with
                    | none, some (.setOfInt sv) =>
                        .ok (DomConstraint.setInReifSlot i sv k)
                    | some _, _ =>
                        .error "set_in_reif over a slot-typed set argument"
                    | none, _ =>
                        .error "set_in_reif over a non-set parameter"
                | none =>
                    .error s!"unresolved name '{ra.name}' in set_in_reif"
            | none =>
                .error s!"unresolved name '{xa.name}' in set_in_reif"
        | _, _, _ => .error "unsupported set_in_reif argument shapes" :
        Except String DomConstraint)) = .ok dc := by
  have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
    intro hcon
    have h2 : c.name.name = "int_plus" := hcon.1
    rw [hname] at h2
    exact absurd h2 (by simp)
  have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
    intro hcon
    have h3 : c.name.name = "int_le" := hcon.1
    rw [hname] at h3
    exact absurd h3 (by simp)
  have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
    intro hcon
    have h4 : c.name.name = "int_lt" := hcon.1
    rw [hname] at h4
    exact absurd h4 (by simp)
  have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
    intro hcon
    have h5 : c.name.name = "int_gt" := hcon.1
    rw [hname] at h5
    exact absurd h5 (by simp)
  have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
    intro hcon
    have h6 : c.name.name = "int_ge" := hcon.1
    rw [hname] at h6
    exact absurd h6 (by simp)
  have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
    intro hcon
    have h7 : c.name.name = "bool_not" := hcon.1
    rw [hname] at h7
    exact absurd h7 (by simp)
  have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
    intro hcon
    have h8 : c.name.name = "bool_and" := hcon.1
    rw [hname] at h8
    exact absurd h8 (by simp)
  have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
    intro hcon
    have h9 : c.name.name = "bool_or" := hcon.1
    rw [hname] at h9
    exact absurd h9 (by simp)
  have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
    intro hcon
    have h10 : c.name.name = "set_in" := hcon.1
    rw [hname] at h10
    exact absurd h10 (by simp)
  unfold compileConstraint at h
  simp only [hnone] at h
  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
    if_neg h6, if_neg h7, if_neg h8, if_neg h9] at h
  rw [if_pos ⟨hname, hargs⟩] at h
  match h0 : argOf c 0 with
  | .error e =>
      rw [h0] at h
      exact absurd h (by intro hc; injection hc)
  | .ok b0 =>
      rw [h0] at h
      match h1 : argOf c 1 with
      | .error e =>
          rw [h1] at h
          exact absurd h (by intro hc; injection hc)
      | .ok b1 =>
          rw [h1] at h
          match h2 : argOf c 2 with
          | .error e =>
              rw [h2] at h
              exact absurd h (by intro hc; injection hc)
          | .ok b2 =>
              rw [h2] at h
              exact ⟨b0, b1, b2, rfl, rfl, rfl, h⟩

/-- A successful fallback compile of `set_in` pins the argument
    count: the gate condition fired, so `c.args.length = 2`. -/
theorem compileConstraint_set_in_len {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hnone : extractConstraint names c = none)
    (hname : c.name.name = "set_in") :
    c.args.length = 2 := by
  by_cases hlen : c.args.length = 2
  · exact hlen
  · exfalso
    have hfall : compileConstraint env names c =
        .error s!"unsupported predicate '{c.name.name}'" := by
      unfold compileConstraint
      rw [hnone]
      have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
        intro hcon
        exact absurd hcon.2 hlen
      have h10 : ¬(c.name.name = "set_in_reif" ∧ c.args.length = 3) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]
    rw [hfall] at h
    exact absurd h (by simp)

/-- A successful fallback compile of `set_in_reif` pins the argument
    count: the gate condition fired, so `c.args.length = 3`. -/
theorem compileConstraint_set_in_reif_len {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hnone : extractConstraint names c = none)
    (hname : c.name.name = "set_in_reif") :
    c.args.length = 3 := by
  by_cases hlen : c.args.length = 3
  · exact hlen
  · exfalso
    have hfall : compileConstraint env names c =
        .error s!"unsupported predicate '{c.name.name}'" := by
      unfold compileConstraint
      rw [hnone]
      have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
        intro hcon
        rw [hname] at hcon
        exact absurd hcon.1 (by simp)
      have h10 : ¬(c.name.name = "set_in_reif" ∧ c.args.length = 3) := by
        intro hcon
        exact absurd hcon.2 hlen
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
        if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]
    rw [hfall] at h
    exact absurd h (by simp)

/-- The full set_in fallback inversion: shape + compiled form. -/
theorem compileConstraint_set_in_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "set_in")
    (hargs : c.args.length = 2)
    (hnone : extractConstraint names c = none) :
    (∃ x s i, c.args =
        [Expr.basic (.ident x), Expr.basic (.lit (.set s))] ∧
      nameIndex names x.name = some i ∧
      dc = .setInSlot i s.denote) ∨
    (∃ x p i sv, c.args =
        [Expr.basic (.ident x), Expr.basic (.ident p)] ∧
      nameIndex names x.name = some i ∧ nameIndex names p.name = none ∧
      env p = some (.setOfInt sv) ∧
      dc = .setInSlot i sv) := by
  obtain ⟨b0, b1, h0, h1, hdo⟩ := fallback2_gate_set_in h hname hargs hnone
  match hb0 : b0 with
  | .ident x =>
      have harg0 : c.args[0]! = Expr.basic (.ident x) :=
        (argOf_ok_inv h0).trans rfl
      match hb1 : b1 with
      | .lit (.set s) =>
          have harg1 : c.args[1]! = Expr.basic (.lit (.set s)) :=
            (argOf_ok_inv h1).trans rfl
          have hdo2 : (match nameIndex names x.name with
              | some i => Except.ok (.setInSlot i s.denote)
              | none =>
                  Except.error s!"unresolved name '{x.name}' in set_in")
              = Except.ok dc := hdo
          cases hx : nameIndex names x.name with
          | none =>
              simp only [hx] at hdo2
              exact absurd hdo2 (by simp)
          | some i =>
              simp only [hx] at hdo2
              have hok : Except.ok (.setInSlot i s.denote)
                  = Except.ok dc := hdo2
              exact Or.inl ⟨x, s, i, two_of_bang hargs harg0 harg1, hx,
                (Except.ok.inj hok).symm⟩
      | .ident p =>
          have harg1 : c.args[1]! = Expr.basic (.ident p) :=
            (argOf_ok_inv h1).trans rfl
          have hdo2 : (match nameIndex names x.name with
              | some i =>
                  (match nameIndex names p.name with
                    | none =>
                        (match env p with
                          | some (.setOfInt sv) =>
                              Except.ok (.setInSlot i sv)
                          | _ =>
                              Except.error "set_in over a non-set parameter")
                    | some _ =>
                        Except.error "set_in over a slot-typed set argument")
              | none =>
                  Except.error s!"unresolved name '{x.name}' in set_in")
              = Except.ok dc := hdo
          cases hx : nameIndex names x.name with
          | none =>
              simp only [hx] at hdo2
              exact absurd hdo2 (by simp)
          | some i =>
              simp only [hx] at hdo2
              cases hpn : nameIndex names p.name with
              | some _ =>
                  simp only [hpn] at hdo2
                  exact absurd hdo2 (by simp)
              | none =>
                  simp only [hpn] at hdo2
                  match hpv : env p with
                  | none =>
                      simp only [hpv] at hdo2
                      exact absurd hdo2 (by simp)
                  | some (.setOfInt sv) =>
                      simp only [hpv] at hdo2
                      have hok : Except.ok (.setInSlot i sv)
                          = Except.ok dc := hdo2
                      exact Or.inr ⟨x, p, i, sv,
                        two_of_bang hargs harg0 harg1, hx, hpn, hpv,
                        (Except.ok.inj hok).symm⟩
                  | some (.int k) =>
                      simp only [hpv] at hdo2
                      exact absurd hdo2 (by simp)
                  | some (.bool bb) =>
                      simp only [hpv] at hdo2
                      exact absurd hdo2 (by simp)
                  | some (.array ws) =>
                      simp only [hpv] at hdo2
                      exact absurd hdo2 (by simp)
      | .lit (.int k) =>
          exact absurd hdo (by
            intro hc
            have h2 : Except.error "unsupported set_in argument shapes"
                = Except.ok dc := hc
            simp at h2)
      | .lit (.bool true) =>
          exact absurd hdo (by
            intro hc
            have h2 : Except.error "unsupported set_in argument shapes"
                = Except.ok dc := hc
            simp at h2)
      | .lit (.bool false) =>
          exact absurd hdo (by
            intro hc
            have h2 : Except.error "unsupported set_in argument shapes"
                = Except.ok dc := hc
            simp at h2)
  | .lit (.int k) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in argument shapes"
            = Except.ok dc := hc
        simp at h2)
  | .lit (.bool true) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in argument shapes"
            = Except.ok dc := hc
        simp at h2)
  | .lit (.bool false) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in argument shapes"
            = Except.ok dc := hc
        simp at h2)
  | .lit (.set s2) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in argument shapes"
            = Except.ok dc := hc
        simp at h2)

/-- The full set_in_reif fallback inversion: shape + compiled form
    (the false-literal reif arm errors, so it never appears). -/
theorem compileConstraint_set_in_reif_fallback_inv {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args.length = 3)
    (hnone : extractConstraint names c = none) :
    (∃ x s r i k, c.args =
        [Expr.basic (.ident x), Expr.basic (.lit (.set s)),
          Expr.basic (.ident r)] ∧
      nameIndex names x.name = some i ∧
      nameIndex names r.name = some k ∧
      dc = .setInReifSlot i s.denote k) ∨
    (∃ x s i, c.args =
        [Expr.basic (.ident x), Expr.basic (.lit (.set s)),
          Expr.basic (.lit (.bool true))] ∧
      nameIndex names x.name = some i ∧
      dc = .setInSlot i s.denote) ∨
    (∃ x p r i sv k, c.args =
        [Expr.basic (.ident x), Expr.basic (.ident p),
          Expr.basic (.ident r)] ∧
      nameIndex names x.name = some i ∧ nameIndex names p.name = none ∧
      env p = some (.setOfInt sv) ∧
      nameIndex names r.name = some k ∧
      dc = .setInReifSlot i sv k) := by
  obtain ⟨b0, b1, b2, h0, h1, h2, hdo⟩ :=
    fallback3_gate_set_in_reif h hname hargs hnone
  match hb0 : b0 with
  | .ident x =>
      have harg0 : c.args[0]! = Expr.basic (.ident x) :=
        (argOf_ok_inv h0).trans rfl
      match hb1 : b1 with
      | .lit (.set s) =>
          have harg1 : c.args[1]! = Expr.basic (.lit (.set s)) :=
            (argOf_ok_inv h1).trans rfl
          match hb2 : b2 with
          | .ident r =>
              have harg2 : c.args[2]! = Expr.basic (.ident r) :=
                (argOf_ok_inv h2).trans rfl
              have hdo2 : (match nameIndex names x.name,
                    nameIndex names r.name with
                  | some i, some k =>
                      Except.ok (.setInReifSlot i s.denote k)
                  | some _, none =>
                      Except.error
                        s!"unresolved name '{r.name}' in set_in_reif"
                  | none, _ =>
                      Except.error
                        s!"unresolved name '{x.name}' in set_in_reif")
                  = Except.ok dc := hdo
              cases hx : nameIndex names x.name with
              | none =>
                  simp only [hx] at hdo2
                  exact absurd hdo2 (by simp)
              | some i =>
                  simp only [hx] at hdo2
                  cases hr : nameIndex names r.name with
                  | none =>
                      simp only [hr] at hdo2
                      exact absurd hdo2 (by simp)
                  | some k =>
                      simp only [hr] at hdo2
                      have hok : Except.ok (.setInReifSlot i s.denote k)
                          = Except.ok dc := hdo2
                      exact Or.inl ⟨x, s, r, i, k,
                        three_of_bang hargs harg0 harg1 harg2, hx, hr,
                        (Except.ok.inj hok).symm⟩
          | .lit (.bool true) =>
              have harg2 : c.args[2]! = Expr.basic (.lit (.bool true)) :=
                (argOf_ok_inv h2).trans rfl
              have hdo2 : (match nameIndex names x.name with
                  | some i => Except.ok (.setInSlot i s.denote)
                  | none =>
                      Except.error
                        s!"unresolved name '{x.name}' in set_in_reif")
                  = Except.ok dc := hdo
              cases hx : nameIndex names x.name with
              | none =>
                  simp only [hx] at hdo2
                  exact absurd hdo2 (by simp)
              | some i =>
                  simp only [hx] at hdo2
                  have hok : Except.ok (.setInSlot i s.denote)
                      = Except.ok dc := hdo2
                  exact Or.inr (Or.inl ⟨x, s, i,
                    three_of_bang hargs harg0 harg1 harg2, hx,
                    (Except.ok.inj hok).symm⟩)
          | .lit (.int k) =>
              exact absurd hdo (by
                intro hc
                have h2 : Except.error "unsupported set_in_reif argument shapes"
                    = Except.ok dc := hc
                simp at h2)
          | .lit (.bool false) =>
              exact absurd hdo (by
                intro hc
                have h2 : Except.error
                    "set_in_reif with a false literal is outside the certified fragment (complement of a finite set)"
                    = Except.ok dc := hc
                simp at h2)
          | .lit (.set s2) =>
              exact absurd hdo (by
                intro hc
                have h2 : Except.error "unsupported set_in_reif argument shapes"
                    = Except.ok dc := hc
                simp at h2)
      | .ident p =>
          have harg1 : c.args[1]! = Expr.basic (.ident p) :=
            (argOf_ok_inv h1).trans rfl
          match hb2 : b2 with
          | .ident r =>
              have harg2 : c.args[2]! = Expr.basic (.ident r) :=
                (argOf_ok_inv h2).trans rfl
              have hdo2 : (match nameIndex names x.name with
                  | some i =>
                      (match nameIndex names r.name with
                        | some k =>
                            (match nameIndex names p.name, env p with
                              | none, some (.setOfInt sv) =>
                                  Except.ok (.setInReifSlot i sv k)
                              | some _, _ =>
                                  Except.error
                                    "set_in_reif over a slot-typed set argument"
                              | none, _ =>
                                  Except.error
                                    "set_in_reif over a non-set parameter")
                        | none =>
                            Except.error
                              s!"unresolved name '{r.name}' in set_in_reif")
                  | none =>
                      Except.error
                        s!"unresolved name '{x.name}' in set_in_reif")
                  = Except.ok dc := hdo
              cases hx : nameIndex names x.name with
              | none =>
                  simp only [hx] at hdo2
                  exact absurd hdo2 (by simp)
              | some i =>
                  simp only [hx] at hdo2
                  cases hr : nameIndex names r.name with
                  | none =>
                      simp only [hr] at hdo2
                      exact absurd hdo2 (by simp)
                  | some k =>
                      simp only [hr] at hdo2
                      cases hpn : nameIndex names p.name with
                      | some _ =>
                          simp only [hpn] at hdo2
                          exact absurd hdo2 (by simp)
                      | none =>
                          simp only [hpn] at hdo2
                          match hpv : env p with
                          | none =>
                              simp only [hpv] at hdo2
                              exact absurd hdo2 (by simp)
                          | some (.setOfInt sv) =>
                              simp only [hpv] at hdo2
                              have hok : Except.ok (.setInReifSlot i sv k)
                                  = Except.ok dc := hdo2
                              exact Or.inr (Or.inr ⟨x, p, r, i, sv, k,
                                three_of_bang hargs harg0 harg1 harg2, hx,
                                hpn, hpv, hr, (Except.ok.inj hok).symm⟩)
                          | some (.int k2) =>
                              simp only [hpv] at hdo2
                              exact absurd hdo2 (by simp)
                          | some (.bool bb) =>
                              simp only [hpv] at hdo2
                              exact absurd hdo2 (by simp)
                          | some (.array ws) =>
                              simp only [hpv] at hdo2
                              exact absurd hdo2 (by simp)
          | .lit (.int k) =>
              exact absurd hdo (by
                intro hc
                have h2 : Except.error "unsupported set_in_reif argument shapes"
                    = Except.ok dc := hc
                simp at h2)
          | .lit (.bool true) =>
              exact absurd hdo (by
                intro hc
                have h2 : Except.error "unsupported set_in_reif argument shapes"
                    = Except.ok dc := hc
                simp at h2)
          | .lit (.bool false) =>
              exact absurd hdo (by
                intro hc
                have h2 : Except.error "unsupported set_in_reif argument shapes"
                    = Except.ok dc := hc
                simp at h2)
          | .lit (.set s2) =>
              exact absurd hdo (by
                intro hc
                have h2 : Except.error "unsupported set_in_reif argument shapes"
                    = Except.ok dc := hc
                simp at h2)
      | .lit (.int k) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in_reif argument shapes"
            = Except.ok dc := hc
        simp at h2)
  | .lit (.bool true) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in_reif argument shapes"
            = Except.ok dc := hc
        simp at h2)
  | .lit (.bool false) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in_reif argument shapes"
            = Except.ok dc := hc
        simp at h2)
  | .lit (.set s2) =>
      exact absurd hdo (by
        intro hc
        have h2 : Except.error "unsupported set_in_reif argument shapes"
            = Except.ok dc := hc
        simp at h2)

/-- set_in(x, S) with a literal set: the slot reads an integer the
    set contains. -/
theorem holds_set_in_slot_lit {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {i : Nat}
    {s : SetLiteral}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "set_in")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.set s))])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hsat : (DomConstraint.setInSlot i s.denote).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hpc⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? hw
  refine ⟨[a[i]!, Value.setOfInt s.denote], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_any hnu halt hxi (by rfl)
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.setOfInt s.denote] with
      | [Value.int a', Value.setOfInt sv] => sv.Contains a'
      | _ => False)
    rw [hib]
    exact hpc

/-- set_in_reif(x, S, true) with a literal set: the reification is
    the membership itself (the literal-true reif compiles to the
    unreified `setInSlot`). -/
theorem holds_set_in_reif_true_slot {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {i : Nat}
    {s : SetLiteral}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.set s)),
        Expr.basic (.lit (.bool true))])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hsat : (DomConstraint.setInSlot i s.denote).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, hw, hpc⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? hw
  refine ⟨[a[i]!, Value.setOfInt s.denote, Value.bool true], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m slots dcs).toStore a x
        let v2 ← pure (Value.setOfInt s.denote)
        let v3 ← pure (Value.bool true)
        pure [v1, v2, v3]) = _
    rw [toStore_read (m := m) hnu hxi halt]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.setOfInt s.denote, Value.bool true] with
      | [Value.int a', Value.setOfInt sv, Value.bool rb'] =>
          (rb' = true ∧ sv.Contains a') ∨
            (rb' = false ∧ ¬ sv.Contains a')
      | _ => False)
    rw [hib]
    exact Or.inl ⟨rfl, hpc⟩

/-- set_in(x, p) with a parameter set: the assembled store resolves
    the parameter to its declared value. -/
theorem holds_set_in_slot_param {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x p : Ident} {i : Nat}
    {sv : IntSetValue}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "set_in")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident p)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hpn : nameIndex (slots.map Prod.fst) p.name = none)
    (hp : parEnv m p = some (.setOfInt sv))
    (hsat : (DomConstraint.setInSlot i sv).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p', hw, hpc⟩ := hsat
  have hib : a[i]! = Value.int p' := bang_of_getElem? hw
  have hpe : Expr.eval ((assemble m slots dcs).toStore a)
      (Expr.basic (.ident p)) = some (.setOfInt sv) :=
    toStore_param hpn hp
  refine ⟨[a[i]!, .setOfInt sv], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_E_any hnu halt hxi hpe
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.setOfInt sv] with
      | [Value.int a', Value.setOfInt sv'] => sv'.Contains a'
      | _ => False)
    rw [hib]
    exact hpc

/-- set_in_reif(x, S, r) with a literal set: the reified
    truth-value agreement. -/
theorem holds_set_in_reif_slot_lit {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x r : Ident}
    {i k : Nat} {s : SetLiteral}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.set s)),
        Expr.basic (.ident r)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hrk : nameIndex (slots.map Prod.fst) r.name = some k)
    (hsat : (DomConstraint.setInReifSlot i s.denote k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, rb, hwi, hwr, hriff⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? hwi
  have hkb : a[k]! = Value.bool rb := bang_of_getElem? hwr
  refine ⟨[a[i]!, Value.setOfInt s.denote, a[k]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m slots dcs).toStore a x
        let v2 ← pure (Value.setOfInt s.denote)
        let v3 ← (assemble m slots dcs).toStore a r
        pure [v1, v2, v3]) = _
    rw [toStore_read (m := m) hnu hxi halt]
    rw [toStore_read (m := m) hnu hrk halt]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.setOfInt s.denote, a[k]!] with
      | [Value.int a', Value.setOfInt sv, Value.bool rb'] =>
          (rb' = true ∧ sv.Contains a') ∨
            (rb' = false ∧ ¬ sv.Contains a')
      | _ => False)
    rw [hib, hkb]
    exact (reif_disj_iff (s.denote.Contains p) rb).mpr hriff

/-- set_in_reif(x, S, r) with a parameter set. -/
theorem holds_set_in_reif_slot_param {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x p r : Ident}
    {i k : Nat} {sv : IntSetValue}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident p),
        Expr.basic (.ident r)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hpn : nameIndex (slots.map Prod.fst) p.name = none)
    (hp : parEnv m p = some (.setOfInt sv))
    (hrk : nameIndex (slots.map Prod.fst) r.name = some k)
    (hsat : (DomConstraint.setInReifSlot i sv k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨q, rb, hwi, hwr, hriff⟩ := hsat
  have hib : a[i]! = Value.int q := bang_of_getElem? hwi
  have hkb : a[k]! = Value.bool rb := bang_of_getElem? hwr
  have hpe : Expr.eval ((assemble m slots dcs).toStore a)
      (Expr.basic (.ident p)) = some (.setOfInt sv) :=
    toStore_param hpn hp
  refine ⟨[a[i]!, .setOfInt sv, a[k]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m slots dcs).toStore a x
        let v2 ← Expr.eval ((assemble m slots dcs).toStore a)
            (Expr.basic (.ident p))
        let v3 ← (assemble m slots dcs).toStore a r
        pure [v1, v2, v3]) = _
    rw [toStore_read (m := m) hnu hxi halt, hpe]
    rw [toStore_read (m := m) hnu hrk halt]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.setOfInt sv, a[k]!] with
      | [Value.int a', Value.setOfInt sv', Value.bool rb'] =>
          (rb' = true ∧ sv'.Contains a') ∨
            (rb' = false ∧ ¬ sv'.Contains a')
      | _ => False)
    rw [hib, hkb]
    exact (reif_disj_iff (sv.Contains q) rb).mpr hriff

/-- **THE MASTER FALLBACK SAT LINKER**: a model constraint that
    compiled through the fallback gate into a `DomConstraint`
    satisfied by an accepted assignment makes the source constraint
    hold at the assembled store. -/
theorem compile_sat_link_fallback {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {dc : DomConstraint}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hmem : a ∈ allAssigns (slots.map Prod.snd))
    (hcc : compileConstraint (parEnv m) (slots.map Prod.fst) c = .ok dc)
    (hnone : extractConstraint (slots.map Prod.fst) c = none)
    (hsat : dc.SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hnu : (slots.map Prod.fst).Nodup := slotNames_nodup hwf hslot
  have halt : a.length = slots.length := by
    have h1 := mem_allAssigns_length (slots.map Prod.snd) a hmem
    rw [List.length_map] at h1
    exact h1
  -- the bool-reads premise for the bool-literal families (the
  -- typing chain supplies Boolean slot reads)
  have hboolreads : (c.name.name = "bool_not" ∨ c.name.name = "bool_and" ∨
      c.name.name = "bool_or") →
      ∀ (x : Ident) (i : Nat), Expr.basic (.ident x) ∈ c.args →
        nameIndex (slots.map Prod.fst) x.name = some i →
        ∃ p, a[i]! = Value.bool p :=
    fun hname => bool_reads_of_mem_bool_family hwf hslot hc hpred hname hmem
  -- the name must be one of the five fallback families (the gate
  -- chain's else-arm rejects everything else with an error)
  by_cases hle : c.name.name = "int_le"
  · rcases compileConstraint_le_fallback_inv hcc hle
      (compileConstraint_fallback2_len hcc hnone (Or.inl hle)) hnone with
      ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ | ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
    · rw [hdc] at hsat
      exact holds_int_le_const_hi_E hnu halt hle hargs hxi
        (eval_intValuedArg halt hE) hsat
    · rw [hdc] at hsat
      exact holds_int_le_const_lo_E hnu halt hle hargs hyi
        (eval_intValuedArg halt hE) hsat
  · by_cases hlt : c.name.name = "int_lt"
    · rcases compileConstraint_lt_fallback_inv hcc hlt
        (compileConstraint_fallback2_len hcc hnone
          (Or.inr (Or.inl hlt))) hnone with
        ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ | ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
      · rw [hdc] at hsat
        exact holds_int_lt_const_hi_E hnu halt hlt hargs hxi
          (eval_intValuedArg halt hE) hsat
      · rw [hdc] at hsat
        exact holds_int_lt_const_lo_E hnu halt hlt hargs hyi
          (eval_intValuedArg halt hE) hsat
    · by_cases hgt : c.name.name = "int_gt"
      · rcases compileConstraint_gt_fallback_inv hcc hgt
          (compileConstraint_fallback2_len hcc hnone
            (Or.inr (Or.inr (Or.inl hgt)))) hnone with
          ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ |
          ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
        · rw [hdc] at hsat
          exact holds_int_gt_const_lo_E hnu halt hgt hargs hxi
            (eval_intValuedArg halt hE) hsat
        · rw [hdc] at hsat
          exact holds_int_gt_const_hi_E hnu halt hgt hargs hyi
            (eval_intValuedArg halt hE) hsat
      · by_cases hge : c.name.name = "int_ge"
        · rcases compileConstraint_ge_fallback_inv hcc hge
            (compileConstraint_fallback2_len hcc hnone
              (Or.inr (Or.inr (Or.inr hge)))) hnone with
            ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ |
            ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
          · rw [hdc] at hsat
            exact holds_int_ge_const_lo_E hnu halt hge hargs hxi
              (eval_intValuedArg halt hE) hsat
          · rw [hdc] at hsat
            exact holds_int_ge_const_hi_E hnu halt hge hargs hyi
              (eval_intValuedArg halt hE) hsat
        · by_cases hplus : c.name.name = "int_plus"
          · obtain ⟨x, y, E, i, j, k, hargs, hxi, hyi, hE, hdc⟩ :=
              compileConstraint_plus_fallback_inv hcc hplus
                (compileConstraint_fallback3_len hcc hnone (Or.inl hplus)) hnone
            rw [hdc] at hsat
            exact holds_int_plus_lit_E hnu halt hplus hargs hxi hyi
              (eval_intValuedArg halt hE) hsat
          · by_cases hnot : c.name.name = "bool_not"
            · rcases compileConstraint_bool_not_fallback_inv hcc hnot
                (compileConstraint_bool_not_len hcc hnone hnot) hnone with
              ⟨x, E, i, w, hargs, hxi, hE, hdc⟩ |
                ⟨y, E, j, w, hargs, hyi, hE, hdc⟩
              · rw [hdc] at hsat
                exact holds_bool_not_lit_E hnu halt hnot hargs hxi
                  (eval_boolValuedArg halt hE) hsat
              · rw [hdc] at hsat
                exact holds_bool_not_lit_E' hnu halt hnot hargs hyi
                  (eval_boolValuedArg halt hE) hsat
            · by_cases hand : c.name.name = "bool_and"
              · rcases compileConstraint_bool_and_fallback_inv hcc hand
                  (compileConstraint_fallback3_len hcc hnone (Or.inr (Or.inl hand))) hnone with
                ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                  ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                  ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩ |
                  ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩
                · rw [hdc] at hsat
                  have hxarg : Expr.basic (.ident x) ∈ c.args := by
                    rw [hargs]; exact List.mem_cons_self
                  exact holds_bool_and_true_E hnu halt hand hargs hxi hzi
                    (hboolreads (Or.inr (Or.inl hand)) x i hxarg hxi)
                    (eval_boolValuedArg halt hE) hsat
                · rw [hdc] at hsat
                  have hxarg : Expr.basic (.ident x) ∈ c.args := by
                    rw [hargs]; exact List.mem_cons_self
                  exact holds_bool_and_false_E hnu halt hand hargs hxi hzi
                    (hboolreads (Or.inr (Or.inl hand)) x i hxarg hxi)
                    (eval_boolValuedArg halt hE) hsat
                · rw [hdc] at hsat
                  have hyarg : Expr.basic (.ident y) ∈ c.args := by
                    rw [hargs]
                    exact List.mem_cons_of_mem _ List.mem_cons_self
                  exact holds_bool_and_true_E' hnu halt hand hargs hyi hzi
                    (hboolreads (Or.inr (Or.inl hand)) y j hyarg hyi)
                    (eval_boolValuedArg halt hE) hsat
                · rw [hdc] at hsat
                  have hyarg : Expr.basic (.ident y) ∈ c.args := by
                    rw [hargs]
                    exact List.mem_cons_of_mem _ List.mem_cons_self
                  exact holds_bool_and_false_E' hnu halt hand hargs hyi hzi
                    (hboolreads (Or.inr (Or.inl hand)) y j hyarg hyi)
                    (eval_boolValuedArg halt hE) hsat
              · by_cases hor : c.name.name = "bool_or"
                · rcases compileConstraint_bool_or_fallback_inv hcc hor
                    (compileConstraint_fallback3_len hcc hnone (Or.inr (Or.inr hor))) hnone with
                  ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                    ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩ |
                    ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                    ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩
                  · rw [hdc] at hsat
                    have hxarg : Expr.basic (.ident x) ∈ c.args := by
                      rw [hargs]; exact List.mem_cons_self
                    exact holds_bool_or_true_E hnu halt hor hargs hxi hzi
                      (hboolreads (Or.inr (Or.inr hor)) x i hxarg hxi)
                      (eval_boolValuedArg halt hE) hsat
                  · rw [hdc] at hsat
                    have hyarg : Expr.basic (.ident y) ∈ c.args := by
                      rw [hargs]
                      exact List.mem_cons_of_mem _ List.mem_cons_self
                    exact holds_bool_or_true_E' hnu halt hor hargs hyi hzi
                      (hboolreads (Or.inr (Or.inr hor)) y j hyarg hyi)
                      (eval_boolValuedArg halt hE) hsat
                  · rw [hdc] at hsat
                    have hxarg : Expr.basic (.ident x) ∈ c.args := by
                      rw [hargs]; exact List.mem_cons_self
                    exact holds_bool_or_false_E hnu halt hor hargs hxi hzi
                      (hboolreads (Or.inr (Or.inr hor)) x i hxarg hxi)
                      (eval_boolValuedArg halt hE) hsat
                  · rw [hdc] at hsat
                    have hyarg : Expr.basic (.ident y) ∈ c.args := by
                      rw [hargs]
                      exact List.mem_cons_of_mem _ List.mem_cons_self
                    exact holds_bool_or_false_E' hnu halt hor hargs hyi hzi
                      (hboolreads (Or.inr (Or.inr hor)) y j hyarg hyi)
                      (eval_boolValuedArg halt hE) hsat
                · by_cases hsetin : c.name.name = "set_in"
                  · rcases compileConstraint_set_in_fallback_inv hcc hsetin
                      (compileConstraint_set_in_len hcc hnone hsetin) hnone with
                    ⟨x, sv, i, hargs, hxi, hdc⟩ |
                      ⟨x, pv, i, sv, hargs, hxi, hpn, hp, hdc⟩
                    · rw [hdc] at hsat
                      exact holds_set_in_slot_lit hnu halt hsetin hargs hxi hsat
                    · rw [hdc] at hsat
                      exact holds_set_in_slot_param hnu halt hsetin hargs hxi hpn hp
                        hsat
                  · by_cases hsetreif : c.name.name = "set_in_reif"
                    · rcases compileConstraint_set_in_reif_fallback_inv hcc hsetreif
                        (compileConstraint_set_in_reif_len hcc hnone hsetreif) hnone with
                      ⟨x, sv, r, i, k, hargs, hxi, hrk, hdc⟩ |
                        ⟨x, sv, i, hargs, hxi, hdc⟩ |
                        ⟨x, pv, r, i, sv, k, hargs, hxi, hpn, hp, hrk, hdc⟩
                      · rw [hdc] at hsat
                        exact holds_set_in_reif_slot_lit hnu halt hsetreif hargs hxi
                          hrk hsat
                      · rw [hdc] at hsat
                        exact holds_set_in_reif_true_slot hnu halt hsetreif hargs hxi
                          hsat
                      · rw [hdc] at hsat
                        exact holds_set_in_reif_slot_param hnu halt hsetreif hargs hxi
                          hpn hp hrk hsat
                    · -- no family matched: the compile failed, contradicting hcc
                      exfalso
                      have hfall : compileConstraint (parEnv m) (slots.map Prod.fst) c
                          = .error s!"unsupported predicate '{c.name.name}'" := by
                        unfold compileConstraint
                        rw [hnone]
                        have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
                          intro hcon
                          exact absurd hcon.1 hplus
                        have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
                          intro hcon
                          exact absurd hcon.1 hle
                        have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
                          intro hcon
                          exact absurd hcon.1 hlt
                        have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
                          intro hcon
                          exact absurd hcon.1 hgt
                        have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
                          intro hcon
                          exact absurd hcon.1 hge
                        have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
                          intro hcon
                          exact absurd hcon.1 hnot
                        have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
                          intro hcon
                          exact absurd hcon.1 hand
                        have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
                          intro hcon
                          exact absurd hcon.1 hor
                        have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
                          intro hcon
                          exact absurd hcon.1 hsetin
                        have h10 : ¬(c.name.name = "set_in_reif" ∧ c.args.length = 3) := by
                          intro hcon
                          exact absurd hcon.1 hsetreif
                        rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
                          if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]
                      rw [hfall] at hcc
                      exact absurd hcc (by simp)



/-- `Holds` is store-extensional: pointwise-equal stores satisfy the
    same constraints. -/
theorem Holds_ext {store1 store2 : Store} {c : ConstraintItem}
    (h : ∀ x, store1 x = store2 x)
    (hh : c.Holds fullInterp store1) :
    c.Holds fullInterp store2 := by
  obtain ⟨args, hmap, hinterp⟩ := hh
  refine ⟨args, ?_, hinterp⟩
  -- (a) the base-expression extensionality
  have hbeval : ∀ (b : BasicExpr), BasicExpr.eval store1 b =
      BasicExpr.eval store2 b := by
    intro b
    cases b with
    | lit l => rfl
    | ident x =>
        show store1 x = store2 x
        exact h x
  -- (b) the list extensionality
  have hlist : ∀ (l : List BasicExpr),
      l.mapM (BasicExpr.eval store1) = l.mapM (BasicExpr.eval store2) := by
    intro l
    induction l with
    | nil => rfl
    | cons b rest ih =>
        rw [List.mapM_cons, List.mapM_cons, hbeval b, ih]
  -- (c) the expression extensionality
  have heval : ∀ (e : Expr), Expr.eval store1 e = Expr.eval store2 e := by
    intro e
    cases e with
    | basic b => exact hbeval b
    | array es =>
        show (es.mapM (BasicExpr.eval store1)).map Value.array =
          (es.mapM (BasicExpr.eval store2)).map Value.array
        rw [hlist es]
  -- (d) transport the mapM (the function is pointwise equal)
  have hfun : Expr.eval store1 = Expr.eval store2 := by
    funext e
    exact heval e
  rw [hfun] at hmap
  exact hmap

/-! ## The whole-model SAT linker and `compile_exact` -/

/-- **THE PER-CONSTRAINT SAT LINKER (both families)**: a model
    constraint that compiled (extraction or fallback) into a
    `DomConstraint` satisfied by an accepted assignment makes the
    source constraint hold at the assembled store. -/
theorem compile_sat_link {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {dc : DomConstraint}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hmem : a ∈ allAssigns (slots.map Prod.snd))
    (hcc : compileConstraint (parEnv m) (slots.map Prod.fst) c = .ok dc)
    (hsat : dc.SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  cases hex : extractConstraint (slots.map Prod.fst) c with
  | some dc' =>
      -- extraction produced a possibly different constraint; the
      -- compiler took the extraction arm, so dc = dc'
      have hcdc : dc = dc' := by
        unfold compileConstraint at hcc
        simp only [hex] at hcc
        exact (Except.ok.inj hcc).symm
      subst hcdc
      exact compile_sat_link_extracted hwf hslot hc hpred hmem hex hsat
  | none =>
      exact compile_sat_link_fallback hwf hslot hc hpred hmem hcc hex hsat

/-- **THE FORWARD COMPILE INVERSION**: every model constraint of a
    successfully compiled constraint list has its own compiled
    `DomConstraint` IN the compiled list. -/
theorem compileConstraints_fwd_inv {env : Store} {names : List String} :
    ∀ (cs : List ConstraintItem) (dcs : List DomConstraint),
      compileConstraints env names cs = .ok dcs →
      ∀ c ∈ cs, ∃ dc ∈ dcs, compileConstraint env names c = .ok dc := by
  intro cs
  induction cs with
  | nil =>
      intro dcs h _ hmem
      cases hmem
  | cons c rest ih =>
      intro dcs h hc hcmem
      obtain ⟨dc', rest', hcc, hrest, hcons⟩ :=
        compileConstraints_ok_cons h
      subst hcons
      rcases List.mem_cons.mp hcmem with rfl | htl
      · exact ⟨dc', List.mem_cons_self, hcc⟩
      · obtain ⟨dc, hdcmem, hc'⟩ := ih rest' hrest hc htl
        exact ⟨dc, List.mem_cons_of_mem _ hdcmem, hc'⟩

/-- **THE WHOLE-MODEL SAT LINKER**: every constraint of a
    successfully compiled model, satisfied by an accepted assignment,
    holds at the assembled store. -/
theorem compile_sat_link_all {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hpred : m.predicates = [])
    (hcomp : compileConstraints (parEnv m) (slots.map Prod.fst)
      m.constraints = .ok dcs)
    (hmem : a ∈ allAssigns (slots.map Prod.snd))
    (hacc : accepts (assemble m slots dcs) a = true) :
    ∀ c ∈ m.constraints, c.Holds fullInterp
      ((assemble m slots dcs).toStore a) := by
  intro c hc
  obtain ⟨dc, hdcmem, hcc⟩ :=
    compileConstraints_fwd_inv m.constraints dcs hcomp c hc
  exact compile_sat_link hwf hslot hc hpred hmem hcc
    (accepts_of_true hacc dc hdcmem)


/-- The extended assembled store reads a model name at the model
    position (the prefix agreement). -/
theorem toStore_read_model {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {x : Ident} {i : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hx : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i) :
    (assemble m (slots0 ++ auxs) dcs).toStore a x = some a[i]! :=
  toStore_read (m := m) (slots := slots0 ++ auxs) (dcs := dcs) hnu hx halt

/-- nameIndex over the extended names agrees with the model names for
    model names (found in the model prefix). -/
theorem nameIndex_ext_eq_model {slots0 auxs : List (String × List Value)}
    {x : Ident} {i : Nat}
    (hxi : nameIndex (slots0.map Prod.fst) x.name = some i) :
    nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i := by
  rw [List.map_append]
  exact nameIndex_append_left hxi

/-- An assignment in the extended candidate space reads the aux
    slot's singleton pin at the slot's extended position. -/
theorem auxPin_of_mem {slots0 auxs : List (String × List Value)}
    {a : List Value} {i : Nat} {v : Value} {taken : List String}
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hilt : i < auxs.length)
    (hslot : auxs[i]? = some (auxName taken i, [v])) :
    a[slots0.length + i]? = some v := by
  have halt : a.length = (slots0 ++ auxs).length := by
    have h1 := mem_allAssigns_length ((slots0 ++ auxs).map Prod.snd) a hmem
    rw [List.length_map] at h1
    exact h1
  have hlt : slots0.length + i < a.length := by
    rw [halt, List.length_append]
    omega
  have hsome : a[slots0.length + i]? = some a[slots0.length + i]! :=
    getElem_as_some hlt
  -- the domain at the extended position is the singleton [v]
  have hfits := mem_allAssigns_fits ((slots0 ++ auxs).map Prod.snd) a hmem
    (slots0.length + i) a[slots0.length + i]!
    (by rw [hsome])
  have hdom : (((slots0 ++ auxs).map Prod.snd).getD (slots0.length + i) [])
      = [v] := by
    have hpairread : (slots0 ++ auxs)[slots0.length + i]? = some auxs[i] := by
      rw [List.getElem?_append_right (Nat.le_add_right slots0.length i)]
      rw [show slots0.length + i - slots0.length = i from by omega]
      exact List.getElem?_eq_getElem hilt
    have hmapread : ((slots0 ++ auxs).map Prod.snd)[slots0.length + i]?
        = some auxs[i].snd := by
      rw [List.getElem?_map]
      rw [hpairread]
      rfl
    rw [List.getD_eq_getElem?_getD, hmapread]
    have hpair : auxs[i] = (auxName taken i, [v]) := by
      have hplain : auxs[i]? = some auxs[i] := List.getElem?_eq_getElem hilt
      rw [hslot] at hplain
      exact (Option.some.inj hplain).symm
    have hsnd : auxs[i].snd = [v] := by rw [hpair]
    rw [hsnd]
    simp
  rw [hdom] at hfits
  have hv : a[slots0.length + i]! = v := List.mem_singleton.mp hfits
  rw [hv] at hsome
  exact hsome



/-! ### The ext-SAT linker (passthrough constraints) -/
/-! ### The ext-reads masters -/

/-- The master int-reads lemma over the extended names: any int-signed
    argument of a well-formed constraint reads an integer. -/
theorem int_read_of_checkArg_master_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType} {x : Ident} {i : Nat}
    (hvars : ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none)
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (hauxfresh : ∀ (n2 : Nat) (p : String × List Value),
      auxs[n2]? = some p → p.1 ∉ auxTaken m slots0)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hptint : ∀ pt ∈ params, pt = .basic (.var (.par .int)))
    (hxarg : Expr.basic (.ident x) ∈ c.args)
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd)) :
    ∃ p, a[i]! = Value.int p := by
  -- x's model-position resolution
  have hxmodel : ∃ j, nameIndex (slots0.map Prod.fst) x.name = some j := by
    by_cases hx : ∃ j, nameIndex (slots0.map Prod.fst) x.name = some j
    · exact hx
    · exfalso
      -- x is not a model slot name; the extended lookup found x —
      -- at an aux name. But x is declared (well-formedness): a
      -- variable (with a slot: contradiction) or a parameter (whose
      -- name is never an aux name: contradiction with hauxfresh).
      have hxdecl : (∃ d ∈ m.variables, VarDeclItem.name d = x) ∨
          (∃ d ∈ m.parameters, ParDeclItem.name d = x) := by
        have hstatic : m.staticEnv x ≠ none := by
          intro hnone
          obtain ⟨pt, hptmem, hchk0⟩ :=
            forall2_mem (Expr.checkArg m.staticEnv) c.args params hchecked
              (Expr.basic (.ident x)) hxarg
          rw [hptint pt hptmem] at hchk0
          simp only [Expr.checkArg, BasicExpr.checkBase] at hchk0
          rw [hnone] at hchk0
          cases hchk0
        -- the staticEnv resolution: parameters first, then vars
        unfold Model.staticEnv at hstatic
        cases hparam : lookupIdent x
            (m.parameters.map (fun d => (d.name, (d.type, false)))) with
        | some p =>
            obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hparam
            obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
            refine Or.inr ⟨d, hd, ?_⟩
            have hyd : y = ParDeclItem.name d := (congrArg Prod.fst hdget).symm
            have hyn : (ParDeclItem.name d).name = x.name := hyd ▸ hyname
            exact ident_eq_of_name hyn
        | none =>
            cases hvar : lookupIdent x
                (m.variables.map (fun d => (d.name, (d.type, true)))) with
            | some p =>
                obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hvar
                obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
                refine Or.inl ⟨d, hd, ?_⟩
                have hyd : y = VarDeclItem.name d := (congrArg Prod.fst hdget).symm
                have hyn : (VarDeclItem.name d).name = x.name := hyd ▸ hyname
                exact ident_eq_of_name hyn
            | none =>
                exfalso
                apply hstatic
                rw [hparam, hvar]
      -- x's name is in the taken list — but the aux name at the
      -- extended position is never a taken name
      have hxi' : nameIndex (slots0.map Prod.fst ++ auxs.map Prod.fst) x.name
          = some i := by
        rw [show slots0.map Prod.fst ++ auxs.map Prod.fst
          = (slots0 ++ auxs).map Prod.fst from (List.map_append).symm]
        exact hxi
      rcases nameIndex_append_inv (l1 := slots0.map Prod.fst)
          (l2 := auxs.map Prod.fst) hxi' with
        hmodel | ⟨j, hj, hjeq⟩
      · exact hx ⟨i, hmodel⟩
      · -- x.name is an aux name (the aux-half hit at j)
        have hname : (auxs.map Prod.fst)[j]! = x.name := by
          have hp := nameIndex_some (auxs.map Prod.fst) x.name j hj
          exact getElem_of_getElem? hp.1 hp.2
        -- x's name is in the taken list (variable or parameter)
        have htaken : x.name ∈ auxTaken m slots0 := by
          rcases hxdecl with ⟨d, hd, hdx⟩ | ⟨d, hd, hdx⟩
          · -- the variable's slot name is a model slot name
            have hslotmem : (VarDeclItem.name d).name ∈ slots0.map Prod.fst := by
              obtain ⟨ty, n, anns, hshape⟩ := hvars d hd
              rw [hshape] at hd
              match hs : declSlot (.basic ty n anns none : VarDeclItem) with
              | .error e => exact absurd hs (declSlots_no_error m.variables slots0
                  (declSlots_of_slotsChecked hslot) _ hd e)
              | .ok none => exact (declSlot_basic_none hs).elim
              | .ok (some p0) =>
                  have hp0mem : p0 ∈ slots0 :=
                    declSlots_produce m.variables slots0
                      (declSlots_of_slotsChecked hslot) _ hd p0 hs
                  rw [List.mem_map]
                  refine ⟨p0, hp0mem, ?_⟩
                  have hp1 : p0.1 = n.name := slot_name_eq_var _ p0 hs
                  have hdxn : n = x := by
                    rw [hshape] at hdx
                    exact hdx
                  rw [hp1, hdxn]
                  have hdd : d.name = x := by
                    rw [hshape]
                    exact hdxn
                  exact (congrArg (fun i => i.name) hdd).symm
            rw [hdx] at hslotmem
            exact List.mem_append.mpr (Or.inl hslotmem)
          · -- the parameter's name is a parameter name
            refine List.mem_append.mpr (Or.inr ?_)
            refine List.mem_map.mpr ⟨d, hd, ?_⟩
            exact congrArg (fun i => i.name) hdx
        -- the aux name at position j is fresh from the taken list
        have hlen : (auxs.map Prod.fst).length = auxs.length := by
          rw [List.length_map]
        have hjlt : j < auxs.length := by
          have := (nameIndex_some (auxs.map Prod.fst) x.name j hj).1
          rw [hlen] at this
          omega
        have hnamej : (auxs.map Prod.fst)[j]! = (auxs[j]).1 := by
          rw [getElem!_map_fst (slots := auxs) j, getElem!_eq_getElem hjlt]
        rw [hnamej] at hname
        have hfresh := hauxfresh j auxs[j] (List.getElem?_eq_getElem hjlt)
        rw [hname] at hfresh
        exact hfresh htaken
  obtain ⟨j, hxj⟩ := hxmodel
  have hextj : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name
      = some j := nameIndex_ext_eq_model hxj
  have hij : i = j := by
    have hilt := (nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name i hxi).1
    have hjlt := (nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name j hextj).1
    have hi2 := nameIndex_at_nodup ((slots0 ++ auxs).map Prod.fst) i hnu hilt
    have hj2 := nameIndex_at_nodup ((slots0 ++ auxs).map Prod.fst) j hnu hjlt
    have hgetj : ((slots0 ++ auxs).map Prod.fst)[j]! = x.name := by
      rw [List.getElem!_eq_getElem?_getD]
      rw [(nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name j hextj).2]
      rfl
    have hgeti : ((slots0 ++ auxs).map Prod.fst)[i]! = x.name := by
      rw [List.getElem!_eq_getElem?_getD]
      rw [(nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name i hxi).2]
      rfl
    -- nameIndex(names, x.name) = some i and = some j (the reads)
    have hNi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i := by
      rw [← hgeti]
      exact hi2
    have hNj : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some j := by
      rw [← hgetj]
      exact hj2
    rw [hNj] at hNi
    exact (Option.some.inj hNi).symm
  subst hij
  -- the int-signed check for x
  obtain ⟨pt, hptmem, hchk0⟩ :=
    forall2_mem (Expr.checkArg m.staticEnv) c.args params hchecked
      (Expr.basic (.ident x)) hxarg
  rw [hptint pt hptmem] at hchk0
  exact int_read_of_checkArg_slot_ext hwf hslot hchecked hchk0 hxj hmem


/-- The bool-reads master over the extended names. -/
theorem bool_read_of_checkArg_master_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType} {x : Ident} {i : Nat}
    (hvars : ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none)
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (hauxfresh : ∀ (n2 : Nat) (p : String × List Value),
      auxs[n2]? = some p → p.1 ∉ auxTaken m slots0)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hptbool : ∀ pt ∈ params, pt = .basic (.var (.par .bool)))
    (hxarg : Expr.basic (.ident x) ∈ c.args)
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd)) :
    ∃ p, a[i]! = Value.bool p := by
  -- x's model-position resolution (the int master's argument)
  have hxmodel : ∃ j, nameIndex (slots0.map Prod.fst) x.name = some j := by
    by_cases hx : ∃ j, nameIndex (slots0.map Prod.fst) x.name = some j
    · exact hx
    · exfalso
      have hxdecl : (∃ d ∈ m.variables, VarDeclItem.name d = x) ∨
          (∃ d ∈ m.parameters, ParDeclItem.name d = x) := by
        have hstatic : m.staticEnv x ≠ none := by
          intro hnone
          obtain ⟨pt, hptmem, hchk0⟩ :=
            forall2_mem (Expr.checkArg m.staticEnv) c.args params hchecked
              (Expr.basic (.ident x)) hxarg
          rw [hptbool pt hptmem] at hchk0
          simp only [Expr.checkArg, BasicExpr.checkBase] at hchk0
          rw [hnone] at hchk0
          cases hchk0
        -- the staticEnv resolution: parameters first, then vars
        unfold Model.staticEnv at hstatic
        cases hparam : lookupIdent x
            (m.parameters.map (fun d => (d.name, (d.type, false)))) with
        | some p =>
            obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hparam
            obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
            refine Or.inr ⟨d, hd, ?_⟩
            have hyd : y = ParDeclItem.name d := (congrArg Prod.fst hdget).symm
            have hyn : (ParDeclItem.name d).name = x.name := hyd ▸ hyname
            exact ident_eq_of_name hyn
        | none =>
            cases hvar : lookupIdent x
                (m.variables.map (fun d => (d.name, (d.type, true)))) with
            | some p =>
                obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hvar
                obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
                refine Or.inl ⟨d, hd, ?_⟩
                have hyd : y = VarDeclItem.name d := (congrArg Prod.fst hdget).symm
                have hyn : (VarDeclItem.name d).name = x.name := hyd ▸ hyname
                exact ident_eq_of_name hyn
            | none =>
                exfalso
                apply hstatic
                rw [hparam, hvar]
      -- x's name is in the taken list — but the aux name at the
      -- extended position is never a taken name
      have hxi' : nameIndex (slots0.map Prod.fst ++ auxs.map Prod.fst) x.name
          = some i := by
        rw [show slots0.map Prod.fst ++ auxs.map Prod.fst
          = (slots0 ++ auxs).map Prod.fst from (List.map_append).symm]
        exact hxi
      rcases nameIndex_append_inv (l1 := slots0.map Prod.fst)
          (l2 := auxs.map Prod.fst) hxi' with
        hmodel | ⟨j, hj, hjeq⟩
      · exact hx ⟨i, hmodel⟩
      · -- x.name is an aux name (the aux-half hit at j)
        have hname : (auxs.map Prod.fst)[j]! = x.name := by
          have hp := nameIndex_some (auxs.map Prod.fst) x.name j hj
          exact getElem_of_getElem? hp.1 hp.2
        -- x's name is in the taken list (variable or parameter)
        have htaken : x.name ∈ auxTaken m slots0 := by
          rcases hxdecl with ⟨d, hd, hdx⟩ | ⟨d, hd, hdx⟩
          · -- the variable's slot name is a model slot name
            have hslotmem : (VarDeclItem.name d).name ∈ slots0.map Prod.fst := by
              obtain ⟨ty, n, anns, hshape⟩ := hvars d hd
              rw [hshape] at hd
              match hs : declSlot (.basic ty n anns none : VarDeclItem) with
              | .error e => exact absurd hs (declSlots_no_error m.variables slots0
                  (declSlots_of_slotsChecked hslot) _ hd e)
              | .ok none => exact (declSlot_basic_none hs).elim
              | .ok (some p0) =>
                  have hp0mem : p0 ∈ slots0 :=
                    declSlots_produce m.variables slots0
                      (declSlots_of_slotsChecked hslot) _ hd p0 hs
                  rw [List.mem_map]
                  refine ⟨p0, hp0mem, ?_⟩
                  have hp1 : p0.1 = n.name := slot_name_eq_var _ p0 hs
                  have hdxn : n = x := by
                    rw [hshape] at hdx
                    exact hdx
                  rw [hp1, hdxn]
                  have hdd : d.name = x := by
                    rw [hshape]
                    exact hdxn
                  exact (congrArg (fun i => i.name) hdd).symm
            rw [hdx] at hslotmem
            exact List.mem_append.mpr (Or.inl hslotmem)
          · -- the parameter's name is a parameter name
            refine List.mem_append.mpr (Or.inr ?_)
            refine List.mem_map.mpr ⟨d, hd, ?_⟩
            exact congrArg (fun i => i.name) hdx
        -- the aux name at position j is fresh from the taken list
        have hlen : (auxs.map Prod.fst).length = auxs.length := by
          rw [List.length_map]
        have hjlt : j < auxs.length := by
          have := (nameIndex_some (auxs.map Prod.fst) x.name j hj).1
          rw [hlen] at this
          omega
        have hnamej : (auxs.map Prod.fst)[j]! = (auxs[j]).1 := by
          rw [getElem!_map_fst (slots := auxs) j, getElem!_eq_getElem hjlt]
        rw [hnamej] at hname
        have hfresh := hauxfresh j auxs[j] (List.getElem?_eq_getElem hjlt)
        rw [hname] at hfresh
        exact hfresh htaken
  obtain ⟨j, hxj⟩ := hxmodel
  have hextj : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name
      = some j := nameIndex_ext_eq_model hxj
  have hij : i = j := by
    have hilt := (nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name i hxi).1
    have hjlt := (nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name j hextj).1
    have hi2 := nameIndex_at_nodup ((slots0 ++ auxs).map Prod.fst) i hnu hilt
    have hj2 := nameIndex_at_nodup ((slots0 ++ auxs).map Prod.fst) j hnu hjlt
    have hgetj : ((slots0 ++ auxs).map Prod.fst)[j]! = x.name := by
      rw [List.getElem!_eq_getElem?_getD]
      rw [(nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name j hextj).2]
      rfl
    have hgeti : ((slots0 ++ auxs).map Prod.fst)[i]! = x.name := by
      rw [List.getElem!_eq_getElem?_getD]
      rw [(nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name i hxi).2]
      rfl
    have hNi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i := by
      rw [← hgeti]
      exact hi2
    have hNj : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some j := by
      rw [← hgetj]
      exact hj2
    rw [hNj] at hNi
    exact (Option.some.inj hNi).symm
  subst hij
  obtain ⟨pt, hptmem, hchk0⟩ :=
    forall2_mem (Expr.checkArg m.staticEnv) c.args params hchecked
      (Expr.basic (.ident x)) hxarg
  rw [hptbool pt hptmem] at hchk0
  exact bool_read_of_checkArg_slot_ext hwf hslot hchecked hchk0 hxj hmem


/-- A name found in the extended names whose model-half lookup misses
    is an aux name — but every declared identifier's name is a taken
    name, so a constraint-argument identifier of a well-formed model
    is always found in the model half. -/
theorem argIdent_model_position {m : Model}
    {slots0 auxs : List (String × List Value)}
    (hvars : ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none)
    (hslot : slotsChecked m = .ok slots0)
    (hauxfresh : ∀ (n2 : Nat) (p : String × List Value),
      auxs[n2]? = some p → p.1 ∉ auxTaken m slots0)
    {c : ConstraintItem} {x : Ident}
    (hstatic : m.staticEnv x ≠ none)
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i) :
    ∃ j, nameIndex (slots0.map Prod.fst) x.name = some j := by
  by_cases hx : ∃ j, nameIndex (slots0.map Prod.fst) x.name = some j
  · exact hx
  · exfalso
    -- x's declaration (variable or parameter)
    have hxdecl : (∃ d ∈ m.variables, VarDeclItem.name d = x) ∨
        (∃ d ∈ m.parameters, ParDeclItem.name d = x) := by
      unfold Model.staticEnv at hstatic
      cases hparam : lookupIdent x
          (m.parameters.map (fun d => (d.name, (d.type, false)))) with
      | some p =>
          obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hparam
          obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
          refine Or.inr ⟨d, hd, ?_⟩
          have hyd : y = ParDeclItem.name d := (congrArg Prod.fst hdget).symm
          have hyn : (ParDeclItem.name d).name = x.name := hyd ▸ hyname
          exact ident_eq_of_name hyn
      | none =>
          cases hvar : lookupIdent x
              (m.variables.map (fun d => (d.name, (d.type, true)))) with
          | some p =>
              obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hvar
              obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
              refine Or.inl ⟨d, hd, ?_⟩
              have hyd : y = VarDeclItem.name d := (congrArg Prod.fst hdget).symm
              have hyn : (VarDeclItem.name d).name = x.name := hyd ▸ hyname
              exact ident_eq_of_name hyn
          | none =>
              exfalso
              apply hstatic
              rw [hparam, hvar]
    -- x's name is in the taken list
    have htaken : x.name ∈ auxTaken m slots0 := by
      rcases hxdecl with ⟨d, hd, hdx⟩ | ⟨d, hd, hdx⟩
      · have hslotmem : (VarDeclItem.name d).name ∈ slots0.map Prod.fst := by
          obtain ⟨ty, n, anns, hshape⟩ := hvars d hd
          rw [hshape] at hd
          match hs : declSlot (.basic ty n anns none : VarDeclItem) with
          | .error e => exact absurd hs (declSlots_no_error m.variables slots0
              (declSlots_of_slotsChecked hslot) _ hd e)
          | .ok none => exact (declSlot_basic_none hs).elim
          | .ok (some p0) =>
              have hp0mem : p0 ∈ slots0 :=
                declSlots_produce m.variables slots0
                  (declSlots_of_slotsChecked hslot) _ hd p0 hs
              rw [List.mem_map]
              refine ⟨p0, hp0mem, ?_⟩
              have hp1 : p0.1 = n.name := slot_name_eq_var _ p0 hs
              have hdxn : n = x := by
                rw [hshape] at hdx
                exact hdx
              rw [hp1, hdxn]
              have hdd : d.name = x := by
                rw [hshape]
                exact hdxn
              exact (congrArg (fun i => i.name) hdd).symm
        rw [hdx] at hslotmem
        exact List.mem_append.mpr (Or.inl hslotmem)
      · refine List.mem_append.mpr (Or.inr ?_)
        refine List.mem_map.mpr ⟨d, hd, ?_⟩
        exact congrArg (fun i => i.name) hdx
    -- the extended lookup found x — at an aux name (the model half misses)
    have hxi' : nameIndex (slots0.map Prod.fst ++ auxs.map Prod.fst) x.name
        = some i := by
      rw [show slots0.map Prod.fst ++ auxs.map Prod.fst
        = (slots0 ++ auxs).map Prod.fst from (List.map_append).symm]
      exact hxi
    rcases nameIndex_append_inv (l1 := slots0.map Prod.fst)
        (l2 := auxs.map Prod.fst) hxi' with
      hmodel | ⟨j, hj, hjeq⟩
    · exact hx ⟨i, hmodel⟩
    · -- x.name is the aux name at j — fresh from taken: contradiction
      have hname : (auxs.map Prod.fst)[j]! = x.name := by
        have hp := nameIndex_some (auxs.map Prod.fst) x.name j hj
        exact getElem_of_getElem? hp.1 hp.2
      have hlen : (auxs.map Prod.fst).length = auxs.length := by
        rw [List.length_map]
      have hjlt : j < auxs.length := by
        have := (nameIndex_some (auxs.map Prod.fst) x.name j hj).1
        rw [hlen] at this
        omega
      have hnamej : (auxs.map Prod.fst)[j]! = (auxs[j]).1 := by
        rw [getElem!_map_fst (slots := auxs) j, getElem!_eq_getElem hjlt]
      rw [hnamej] at hname
      have hfresh := hauxfresh j auxs[j] (List.getElem?_eq_getElem hjlt)
      rw [hname] at hfresh
      exact hfresh htaken

/-- An int-signed identifier of a well-formed constraint whose args
    have the int_times signature has a MODEL SLOT (the well-formedness
    + slot chain). -/
theorem int_arg_model_slot {m : Model}
    {slots0 auxs : List (String × List Value)}
    (hvars : ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none)
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    {c : ConstraintItem} {x : Ident}
    (hc : c ∈ m.constraints) (hpred : m.predicates = [])
    (hname : c.name.name = "int_times")
    (hparamexcl : ∀ d ∈ m.parameters, ParDeclItem.name d ≠ x)
    (hxarg : Expr.basic (.ident x) ∈ c.args) :
    ∃ i3, nameIndex (slots0.map Prod.fst) x.name = some i3 := by
  -- the signature chain
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] := by
    show (match m.declaredSigs (Ident.mk c.name.name) with
      | some params => some params
      | none => fullSig (Ident.mk c.name.name)) = _
    rw [declaredSigs_none hpred, hname]
    rfl
  have hparameq : params =
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
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
        BasicParType.int)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int))] hfor
      (Expr.basic (.ident x)) hxarg
  have hpt : pt =
      PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.int)) := by
    rcases List.mem_cons.mp hptmem with rfl | htl
    · rfl
    · rcases List.mem_cons.mp htl with rfl | htl2
      · rfl
      · rcases List.mem_cons.mp htl2 with rfl | hnil
        · rfl
        · exact absurd hnil (by simp)
  subst hpt
  -- the check makes x's staticEnv a variable (isVar = true):
  -- x is a declared variable, with a model slot
  have hxdecl : ∃ d ∈ m.variables, VarDeclItem.name d = x := by
    -- the staticEnv resolution: variables carry isVar = true
    obtain ⟨isVar, henv⟩ := staticEnv_int_of_checkArg hchk0
    -- the env value's isVar=true forces the VARIABLES half of the
    -- staticEnv lookup
    unfold Model.staticEnv at henv
    cases hparam : lookupIdent x
        (m.parameters.map (fun d => (d.name, (d.type, false)))) with
    | some p =>
        exfalso
        obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hparam
        obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
        have hyd2 : y = d.name := (congrArg Prod.fst hdget).symm
        exact hparamexcl d hd (hyd2.symm.trans (ident_eq_of_name hyname))
    | none =>
        cases hvar : lookupIdent x
            (m.variables.map (fun d => (d.name, (d.type, true)))) with
        | some p =>
            obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hvar
            obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
            refine ⟨d, hd, ?_⟩
            have hyd : y = VarDeclItem.name d := (congrArg Prod.fst hdget).symm
            have hyn : (VarDeclItem.name d).name = x.name := hyd ▸ hyname
            exact ident_eq_of_name hyn
        | none =>
            exfalso
            rw [hparam, hvar] at henv
            exact absurd henv (by simp)
  -- the declared variable has a model slot (the fragment's basic
  -- initializer-free variables)
  obtain ⟨d, hd, hdx⟩ := hxdecl
  obtain ⟨ty, n, anns, hshape2⟩ := hvars d hd
  rw [hshape2] at hd
  match hs : declSlot (.basic ty n anns none : VarDeclItem) with
  | .error e =>
      exact absurd hs (declSlots_no_error m.variables slots0
        (declSlots_of_slotsChecked hslot) _ hd e)
  | .ok none => exact (declSlot_basic_none hs).elim
  | .ok (some p0) =>
      have hp0mem : p0 ∈ slots0 :=
        declSlots_produce m.variables slots0
          (declSlots_of_slotsChecked hslot) _ hd p0 hs
      -- the slot's name is n.name = x.name
      have hnameeq : p0.1 = n.name := slot_name_eq_var _ p0 hs
      have hnx : n = x := by
        rw [hshape2] at hdx
        exact hdx
      -- the model slot position
      obtain ⟨j, hjlt, hjget⟩ := slot_getElem!_of_mem slots0 p0 hp0mem
      refine ⟨j, ?_⟩
      -- names[j]! = x.name (the slot's name IS the variable's name)
      have hnamesx : (slots0.map Prod.fst)[j]! = x.name := by
        rw [getElem!_map_fst j, hjget, hnameeq, ← hnx]
      rw [← hnamesx, nameIndex_at_nodup (slots0.map Prod.fst) j
        (slotNames_nodup hwf hslot) (by
          have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
          omega)]

/-- A bool-signed identifier of a well-formed constraint whose args
    have the bool_and/bool_or signature has a MODEL SLOT. -/
theorem bool_arg_model_slot {m : Model}
    {slots0 : List (String × List Value)}
    (hvars : ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none)
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    {c : ConstraintItem} {x : Ident}
    (hc : c ∈ m.constraints) (hpred : m.predicates = [])
    (hname : c.name.name = "bool_and" ∨ c.name.name = "bool_or")
    (hparamexcl : ∀ d ∈ m.parameters, ParDeclItem.name d ≠ x)
    (hxarg : Expr.basic (.ident x) ∈ c.args) :
    ∃ i3, nameIndex (slots0.map Prod.fst) x.name = some i3 := by
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool))] := by
    rcases hname with hn | hn
    · rw [show Ident.mk c.name.name = Ident.mk "bool_and" from by rw [hn]]
      exact sigEnv_bool_and hpred
    · rw [show Ident.mk c.name.name = Ident.mk "bool_or" from by rw [hn]]
      exact sigEnv_bool_or hpred
  have hparameq : params =
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool))] := by
    have h1 : m.sigEnv Globals.fullSig c.name = some params := hsig
    rw [show m.sigEnv Globals.fullSig c.name
        = m.sigEnv Globals.fullSig (Ident.mk c.name.name) from rfl] at h1
    rw [hres] at h1
    exact (Option.some.inj h1).symm
  rw [hparameq] at hfor
  obtain ⟨pt, hptmem, hchk0⟩ :=
    forall2_mem (Expr.checkArg m.staticEnv) c.args
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool)),
       PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool))] hfor
      (Expr.basic (.ident x)) hxarg
  have hpt : pt =
      PredParamType.basic (BasicPredParamType.var (BasicVarType.par
        BasicParType.bool)) := by
    rcases List.mem_cons.mp hptmem with rfl | htl
    · rfl
    · rcases List.mem_cons.mp htl with rfl | htl2
      · rfl
      · rcases List.mem_cons.mp htl2 with rfl | hnil
        · rfl
        · exact absurd hnil (by simp)
  subst hpt
  obtain ⟨isVar, henv⟩ := staticEnv_bool_of_checkArg hchk0
  have hxdecl : ∃ d ∈ m.variables, VarDeclItem.name d = x := by
    unfold Model.staticEnv at henv
    cases hparam : lookupIdent x
        (m.parameters.map (fun d => (d.name, (d.type, false)))) with
    | some p =>
        exfalso
        obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hparam
        obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
        have hyd3 : y = d.name := (congrArg Prod.fst hdget).symm
        exact hparamexcl d hd (hyd3.symm.trans (ident_eq_of_name hyname))
    | none =>
        cases hvar : lookupIdent x
            (m.variables.map (fun d => (d.name, (d.type, true)))) with
        | some p =>
            obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x _ p hvar
            obtain ⟨d, hd, hdget⟩ := List.mem_map.mp hmem
            refine ⟨d, hd, ?_⟩
            have hyd : y = VarDeclItem.name d := (congrArg Prod.fst hdget).symm
            have hyn : (VarDeclItem.name d).name = x.name := hyd ▸ hyname
            exact ident_eq_of_name hyn
        | none =>
            exfalso
            rw [hparam, hvar] at henv
            exact absurd henv (by simp)
  obtain ⟨d, hd, hdx⟩ := hxdecl
  obtain ⟨ty, n, anns, hshape2⟩ := hvars d hd
  rw [hshape2] at hd
  match hs : declSlot (.basic ty n anns none : VarDeclItem) with
  | .error e =>
      exact absurd hs (declSlots_no_error m.variables slots0
        (declSlots_of_slotsChecked hslot) _ hd e)
  | .ok none => exact (declSlot_basic_none hs).elim
  | .ok (some p0) =>
      have hp0mem : p0 ∈ slots0 :=
        declSlots_produce m.variables slots0
          (declSlots_of_slotsChecked hslot) _ hd p0 hs
      have hnameeq : p0.1 = n.name := slot_name_eq_var _ p0 hs
      have hnx : n = x := by
        rw [hshape2] at hdx
        exact hdx
      obtain ⟨j, hjlt, hjget⟩ := slot_getElem!_of_mem slots0 p0 hp0mem
      refine ⟨j, ?_⟩
      -- names[j]! = x.name (the slot's name IS the variable's name)
      have hnamesx : (slots0.map Prod.fst)[j]! = x.name := by
        rw [getElem!_map_fst j, hjget, hnameeq, ← hnx]
      rw [← hnamesx, nameIndex_at_nodup (slots0.map Prod.fst) j
        (slotNames_nodup hwf hslot) (by
          have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
          omega)]

/-- A declared initializer-free basic variable's name resolves in the
    slot list. -/
theorem nameIndex_of_basic_var {m : Model}
    {slots : List (String × List Value)}
    (hwf : WellFormed Globals.fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (ty : BasicVarType) (n : Ident) (anns : List Annotation)
    (hd : (.basic ty n anns none : VarDeclItem) ∈ m.variables) :
    ∃ i, nameIndex (slots.map Prod.fst) n.name = some i := by
  have hdecls : declSlots m.variables = .ok slots :=
    declSlots_of_slotsChecked hslot
  match hds : declSlot (.basic ty n anns none : VarDeclItem) with
  | .error e =>
      exact absurd hds
        (declSlots_no_error m.variables slots hdecls _ hd e)
  | .ok none => exact (declSlot_basic_none hds).elim
  | .ok (some p0) =>
      obtain ⟨j, _, _, hjidx⟩ := declSlot_position hwf hslot hd hds
      obtain ⟨dom, _, hpair⟩ := declSlot_basic_inv hds
      have hname : p0.1 = n.name := by rw [hpair]
      rw [hname] at hjidx
      exact ⟨j, hjidx⟩

/-- FilterMap-membership reflection: a member of a filterMap comes
    from a source member mapping to it. -/
theorem mem_filterMap_src {α β : Type} (F : α → Option β) :
    ∀ (l : List α) (x : β), x ∈ l.filterMap F →
      ∃ a, a ∈ l ∧ F a = some x := by
  intro l
  induction l with
  | nil =>
      intro x hx
      cases hx
  | cons a rest ih =>
      intro x hx
      obtain ⟨a', ha'mem, ha'val⟩ := List.mem_filterMap.mp hx
      exact ⟨a', ha'mem, ha'val⟩

/-- The left-half nodup of an append. -/
theorem nodup_of_append_left {α : Type} {l1 l2 : List α}
    (h : (l1 ++ l2).Nodup) : l1.Nodup := by
  induction l1 with
  | nil => simp
  | cons a rest ih =>
      have hnucons : (a :: (rest ++ l2)).Nodup := h
      have h2 := List.nodup_cons.mp hnucons
      refine List.nodup_cons.mpr ⟨?_, ih h2.2⟩
      intro hmem
      exact h2.1 (List.mem_append.mpr (Or.inl hmem))

/-! ## The coverage direction (`compile_covers`) -/
/-! ## The store-agreement transport (identifier-restricted) -/
/-- The parameter-name agreement: for a well-formed model whose
    compiled gate accepted, every parameter name reads its parEnv
    value in a parameter-honest store. -/
theorem parEnv_agrees {m : Model}
    {slots : List (String × List Value)}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    {store : Store}
    (hparam : ParamHonest m store)
    (d : ParDeclItem) (hd : d ∈ m.parameters)
    (hscalar : ∃ v, parDeclValue d = some v) :
    store (ParDeclItem.name d) = parEnv m (ParDeclItem.name d) := by
  obtain ⟨v, hv⟩ := hscalar
  have hstore : store (ParDeclItem.name d) = some v := hparam d hd v hv
  -- parEnv: the environment reads v (via parEnv_of_decl, needs nodup)
  have hfull : (m.parameters.map ParDeclItem.name ++ m.variables.map
      VarDeclItem.name).Nodup := hwf.valueNamesUnique
  -- the filterMap's names: distinct (a sublist-style induction on
  -- the distinct parameter names)
  have hparnames : (m.parameters.map ParDeclItem.name).Nodup :=
    nodup_of_append_left hwf.valueNamesUnique
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
            -- dropped from the filterMap: the tail's names only
            show ((d2 :: rest).filterMap
                (fun d2 => parDeclValue d2 |>.map (fun v2 =>
                  (ParDeclItem.name d2, v2)))).map Prod.fst |>.Nodup
            rw [List.filterMap_cons, hpv]
            exact ih h2.2
        | some v2 =>
            -- kept: the head's name is not among the tail's names
            show ((d2 :: rest).filterMap
                (fun d2 => parDeclValue d2 |>.map (fun v2 =>
                  (ParDeclItem.name d2, v2)))).map Prod.fst |>.Nodup
            rw [List.filterMap_cons, hpv]
            simp only [List.map_cons, Option.map_some, List.nodup_cons]
            refine ⟨?_, ih h2.2⟩
            intro hmem
            -- the tail's filterMap names are among the tail's names
            have hsub : ∀ x ∈ (rest.filterMap
                (fun d2 => parDeclValue d2 |>.map (fun v2 =>
                  (ParDeclItem.name d2, v2)))).map Prod.fst,
                x ∈ rest.map ParDeclItem.name := by
              intro x hx
              -- unfold to the source: a filterMap member comes from a
              -- list member whose projection yields the pair
              obtain ⟨p, hpmem, hpname⟩ := List.mem_map.mp hx
              obtain ⟨d4, hd4mem, hd4val⟩ :=
                mem_filterMap_src
                  (fun d2 => parDeclValue d2 |>.map (fun v2 =>
                    (ParDeclItem.name d2, v2))) rest p hpmem
              have hpfst : ParDeclItem.name d4 = p.1 := by
                -- parDeclValue d4 = some w (it produced the pair p)
                cases hpd : parDeclValue d4 with
                | none => rw [hpd] at hd4val; exact absurd hd4val (by simp)
                | some w =>
                    rw [hpd] at hd4val
                    have hsome : some (ParDeclItem.name d4, w) = some p := hd4val
                    have hp : (ParDeclItem.name d4, w) = p := (Option.some.inj hsome)
                    exact congrArg Prod.fst hp
              exact List.mem_map.mpr
                ⟨d4, hd4mem, hpname ▸ hpfst⟩
            apply h2.1
            exact hsub _ hmem
  have hnu : ((m.parameters.filterMap
      (fun d2 => parDeclValue d2 |>.map (fun v2 => (ParDeclItem.name d2, v2)))).map
    Prod.fst).Nodup := hmain m.parameters hparnames
  have hpar : parEnv m (ParDeclItem.name d) = some v := parEnv_of_decl hd hv hnu
  rw [hpar]
  exact hstore

/-- FlatMap-membership reflection: a member of a flatMap comes from a
    source member. -/
theorem mem_flatMap_src {α β : Type} (f : α → List β) :
    ∀ (l : List α) (x : β), x ∈ l.flatMap f → ∃ a, a ∈ l ∧ x ∈ f a := by
  intro l
  induction l with
  | nil => intro x hx; cases hx
  | cons a rest ih =>
      intro x hx
      rw [List.flatMap_cons, List.mem_append] at hx
      rcases hx with hx | hx
      · exact ⟨a, List.mem_cons_self, hx⟩
      · obtain ⟨a2, ha2mem, ha2mem2⟩ := ih x hx
        exact ⟨a2, List.mem_cons_of_mem _ ha2mem, ha2mem2⟩




/-- The ext-SAT linker: a model constraint (not a pinning shape)
    that compiled over the EXTENDED names into a `DomConstraint`
    satisfied by an accepted extended assignment makes the source
    constraint hold at the extended assembled store. -/
theorem compile_sat_link_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {dc : DomConstraint}
    (hvars : ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none)
    (hauxfresh : ∀ (n2 : Nat) (p : String × List Value),
      auxs[n2]? = some p → p.1 ∉ auxTaken m slots0)
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (hcc : compileConstraint (parEnv m) ((slots0 ++ auxs).map Prod.fst) c
      = .ok dc)
    (hsat : dc.SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have halt : a.length = (slots0 ++ auxs).length := by
    have h1 := mem_allAssigns_length ((slots0 ++ auxs).map Prod.snd) a hmem
    rw [List.length_map] at h1
    exact h1
  -- the name-conditioned int-reads (the eq/ne arms)
  have hreads : ∀ (x : Ident) (i : Nat),
      Expr.basic (.ident x) ∈ c.args →
      nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i →
      (c.name.name = "int_eq" ∨ c.name.name = "int_ne") →
      ∃ p, a[i]! = Value.int p := by
    intro x i hxarg hxi hname
    -- the signature chain (as int_reads_of_mem_eq_ne, with the
    -- master-ext read derivation)
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
    exact int_read_of_checkArg_master_ext hvars hwf hslot hnu hauxfresh hfor
      (by intro pt hpt
          rcases List.mem_cons.mp hpt with rfl | htl
          · rfl
          · rcases List.mem_cons.mp htl with rfl | hnil
            · rfl
            · exact absurd hnil (by simp))
      hxarg hxi hmem
  cases hnone : extractConstraint ((slots0 ++ auxs).map Prod.fst) c with
  | some dc' =>
      have hcdc : dc = dc' := by
        unfold compileConstraint at hcc
        simp only [hnone] at hcc
        exact (Except.ok.inj hcc).symm
      subst hcdc
      exact extractConstraint_holds_converse hnu halt hnone hreads hsat
  | none =>
      -- the fallback arm: the family linkers are generic over the
      -- slot list except the bool-reads chain (the ext derivation)
      have hboolreads : (c.name.name = "bool_not" ∨ c.name.name = "bool_and" ∨
          c.name.name = "bool_or") →
          ∀ (x : Ident) (i : Nat), Expr.basic (.ident x) ∈ c.args →
            nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i →
            ∃ p, a[i]! = Value.bool p := by
        intro hname x i hxarg hxi
        -- the bool-family signature chain + the bool ext derivation
        obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
        have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
            [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool)),
             PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool))] ∨
            m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
            [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool)),
             PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool)),
             PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool))] := by
          rcases hname with hn | hn | hn
          · rw [hn]; exact Or.inl (sigEnv_bool_not hpred)
          · rw [hn]; exact Or.inr (sigEnv_bool_and hpred)
          · rw [hn]; exact Or.inr (sigEnv_bool_or hpred)
        have hparameq : params =
            [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool)),
             PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool))] ∨
            params =
            [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool)),
             PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool)),
             PredParamType.basic (BasicPredParamType.var (BasicVarType.par
              BasicParType.bool))] := by
          have h1 : m.sigEnv Globals.fullSig c.name = some params := hsig
          rw [show m.sigEnv Globals.fullSig c.name
              = m.sigEnv Globals.fullSig (Ident.mk c.name.name) from rfl] at h1
          rcases hres with hres | hres
          · rw [hres] at h1
            exact Or.inl (Option.some.inj h1).symm
          · rw [hres] at h1
            exact Or.inr (Option.some.inj h1).symm
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
        exact bool_read_of_checkArg_master_ext hvars hwf hslot hnu hauxfresh
          hfor hpsall hxarg hxi hmem
      -- the name must be one of the five fallback families (the gate
      -- chain's else-arm rejects everything else with an error)
      by_cases hle : c.name.name = "int_le"
      · rcases compileConstraint_le_fallback_inv hcc hle
          (compileConstraint_fallback2_len hcc hnone (Or.inl hle)) hnone with
          ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ | ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
        · rw [hdc] at hsat
          exact holds_int_le_const_hi_E hnu halt hle hargs hxi
            (eval_intValuedArg halt hE) hsat
        · rw [hdc] at hsat
          exact holds_int_le_const_lo_E hnu halt hle hargs hyi
            (eval_intValuedArg halt hE) hsat
      · by_cases hlt : c.name.name = "int_lt"
        · rcases compileConstraint_lt_fallback_inv hcc hlt
            (compileConstraint_fallback2_len hcc hnone
              (Or.inr (Or.inl hlt))) hnone with
            ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ | ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
          · rw [hdc] at hsat
            exact holds_int_lt_const_hi_E hnu halt hlt hargs hxi
              (eval_intValuedArg halt hE) hsat
          · rw [hdc] at hsat
            exact holds_int_lt_const_lo_E hnu halt hlt hargs hyi
              (eval_intValuedArg halt hE) hsat
        · by_cases hgt : c.name.name = "int_gt"
          · rcases compileConstraint_gt_fallback_inv hcc hgt
              (compileConstraint_fallback2_len hcc hnone
                (Or.inr (Or.inr (Or.inl hgt)))) hnone with
              ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ |
              ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
            · rw [hdc] at hsat
              exact holds_int_gt_const_lo_E hnu halt hgt hargs hxi
                (eval_intValuedArg halt hE) hsat
            · rw [hdc] at hsat
              exact holds_int_gt_const_hi_E hnu halt hgt hargs hyi
                (eval_intValuedArg halt hE) hsat
          · by_cases hge : c.name.name = "int_ge"
            · rcases compileConstraint_ge_fallback_inv hcc hge
                (compileConstraint_fallback2_len hcc hnone
                  (Or.inr (Or.inr (Or.inr hge)))) hnone with
                ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ |
                ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
              · rw [hdc] at hsat
                exact holds_int_ge_const_lo_E hnu halt hge hargs hxi
                  (eval_intValuedArg halt hE) hsat
              · rw [hdc] at hsat
                exact holds_int_ge_const_hi_E hnu halt hge hargs hyi
                  (eval_intValuedArg halt hE) hsat
            · by_cases hplus : c.name.name = "int_plus"
              · obtain ⟨x, y, E, i, j, k, hargs, hxi, hyi, hE, hdc⟩ :=
                  compileConstraint_plus_fallback_inv hcc hplus
                    (compileConstraint_fallback3_len hcc hnone (Or.inl hplus)) hnone
                rw [hdc] at hsat
                exact holds_int_plus_lit_E hnu halt hplus hargs hxi hyi
                  (eval_intValuedArg halt hE) hsat
              · by_cases hnot : c.name.name = "bool_not"
                · rcases compileConstraint_bool_not_fallback_inv hcc hnot
                    (compileConstraint_bool_not_len hcc hnone hnot) hnone with
                  ⟨x, E, i, w, hargs, hxi, hE, hdc⟩ |
                    ⟨y, E, j, w, hargs, hyi, hE, hdc⟩
                  · rw [hdc] at hsat
                    exact holds_bool_not_lit_E hnu halt hnot hargs hxi
                      (eval_boolValuedArg halt hE) hsat
                  · rw [hdc] at hsat
                    exact holds_bool_not_lit_E' hnu halt hnot hargs hyi
                      (eval_boolValuedArg halt hE) hsat
                · by_cases hand : c.name.name = "bool_and"
                  · rcases compileConstraint_bool_and_fallback_inv hcc hand
                      (compileConstraint_fallback3_len hcc hnone (Or.inr (Or.inl hand))) hnone with
                    ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                      ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                      ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩ |
                      ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩
                    · rw [hdc] at hsat
                      have hxarg : Expr.basic (.ident x) ∈ c.args := by
                        rw [hargs]; exact List.mem_cons_self
                      exact holds_bool_and_true_E hnu halt hand hargs hxi hzi
                        (hboolreads (Or.inr (Or.inl hand)) x i hxarg hxi)
                        (eval_boolValuedArg halt hE) hsat
                    · rw [hdc] at hsat
                      have hxarg : Expr.basic (.ident x) ∈ c.args := by
                        rw [hargs]; exact List.mem_cons_self
                      exact holds_bool_and_false_E hnu halt hand hargs hxi hzi
                        (hboolreads (Or.inr (Or.inl hand)) x i hxarg hxi)
                        (eval_boolValuedArg halt hE) hsat
                    · rw [hdc] at hsat
                      have hyarg : Expr.basic (.ident y) ∈ c.args := by
                        rw [hargs]
                        exact List.mem_cons_of_mem _ List.mem_cons_self
                      exact holds_bool_and_true_E' hnu halt hand hargs hyi hzi
                        (hboolreads (Or.inr (Or.inl hand)) y j hyarg hyi)
                        (eval_boolValuedArg halt hE) hsat
                    · rw [hdc] at hsat
                      have hyarg : Expr.basic (.ident y) ∈ c.args := by
                        rw [hargs]
                        exact List.mem_cons_of_mem _ List.mem_cons_self
                      exact holds_bool_and_false_E' hnu halt hand hargs hyi hzi
                        (hboolreads (Or.inr (Or.inl hand)) y j hyarg hyi)
                        (eval_boolValuedArg halt hE) hsat
                  · by_cases hor : c.name.name = "bool_or"
                    · rcases compileConstraint_bool_or_fallback_inv hcc hor
                        (compileConstraint_fallback3_len hcc hnone (Or.inr (Or.inr hor))) hnone with
                      ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                        ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩ |
                        ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                        ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩
                      · rw [hdc] at hsat
                        have hxarg : Expr.basic (.ident x) ∈ c.args := by
                          rw [hargs]; exact List.mem_cons_self
                        exact holds_bool_or_true_E hnu halt hor hargs hxi hzi
                          (hboolreads (Or.inr (Or.inr hor)) x i hxarg hxi)
                          (eval_boolValuedArg halt hE) hsat
                      · rw [hdc] at hsat
                        have hyarg : Expr.basic (.ident y) ∈ c.args := by
                          rw [hargs]
                          exact List.mem_cons_of_mem _ List.mem_cons_self
                        exact holds_bool_or_true_E' hnu halt hor hargs hyi hzi
                          (hboolreads (Or.inr (Or.inr hor)) y j hyarg hyi)
                          (eval_boolValuedArg halt hE) hsat
                      · rw [hdc] at hsat
                        have hxarg : Expr.basic (.ident x) ∈ c.args := by
                          rw [hargs]; exact List.mem_cons_self
                        exact holds_bool_or_false_E hnu halt hor hargs hxi hzi
                          (hboolreads (Or.inr (Or.inr hor)) x i hxarg hxi)
                          (eval_boolValuedArg halt hE) hsat
                      · rw [hdc] at hsat
                        have hyarg : Expr.basic (.ident y) ∈ c.args := by
                          rw [hargs]
                          exact List.mem_cons_of_mem _ List.mem_cons_self
                        exact holds_bool_or_false_E' hnu halt hor hargs hyi hzi
                          (hboolreads (Or.inr (Or.inr hor)) y j hyarg hyi)
                          (eval_boolValuedArg halt hE) hsat
                    · by_cases hsetin : c.name.name = "set_in"
                      · rcases compileConstraint_set_in_fallback_inv hcc hsetin
                          (compileConstraint_set_in_len hcc hnone hsetin) hnone with
                        ⟨x, sv, i, hargs, hxi, hdc⟩ |
                          ⟨x, pv, i, sv, hargs, hxi, hpn, hp, hdc⟩
                        · rw [hdc] at hsat
                          exact holds_set_in_slot_lit (m := m)
                            (slots := slots0 ++ auxs) (dcs := dcs) hnu halt hsetin
                            hargs hxi hsat
                        · rw [hdc] at hsat
                          exact holds_set_in_slot_param (m := m)
                            (slots := slots0 ++ auxs) (dcs := dcs) hnu halt hsetin
                            hargs hxi hpn hp hsat
                      · by_cases hsetreif : c.name.name = "set_in_reif"
                        · rcases compileConstraint_set_in_reif_fallback_inv hcc hsetreif
                            (compileConstraint_set_in_reif_len hcc hnone hsetreif) hnone with
                          ⟨x, sv, r, i, k, hargs, hxi, hrk, hdc⟩ |
                            ⟨x, sv, i, hargs, hxi, hdc⟩ |
                            ⟨x, pv, r, i, sv, k, hargs, hxi, hpn, hp, hrk, hdc⟩
                          · rw [hdc] at hsat
                            exact holds_set_in_reif_slot_lit (m := m)
                              (slots := slots0 ++ auxs) (dcs := dcs) hnu halt hsetreif
                              hargs hxi hrk hsat
                          · rw [hdc] at hsat
                            exact holds_set_in_reif_true_slot (m := m)
                              (slots := slots0 ++ auxs) (dcs := dcs) hnu halt
                              hsetreif hargs hxi hsat
                          · rw [hdc] at hsat
                            exact holds_set_in_reif_slot_param (m := m)
                              (slots := slots0 ++ auxs) (dcs := dcs) hnu halt hsetreif
                              hargs hxi hpn hp hrk hsat
                        · -- no family matched: the compile failed, contradicting hcc
                          exfalso
                          have hfall : compileConstraint (parEnv m)
                              ((slots0 ++ auxs).map Prod.fst) c
                              = .error s!"unsupported predicate '{c.name.name}'" := by
                            unfold compileConstraint
                            rw [hnone]
                            have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hplus
                            have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hle
                            have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hlt
                            have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hgt
                            have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hge
                            have h6 : ¬(c.name.name = "bool_not" ∧ c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hnot
                            have h7 : ¬(c.name.name = "bool_and" ∧ c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hand
                            have h8 : ¬(c.name.name = "bool_or" ∧ c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hor
                            have h9 : ¬(c.name.name = "set_in" ∧ c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hsetin
                            have h10 : ¬(c.name.name = "set_in_reif" ∧ c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hsetreif
                            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5,
                              if_neg h6, if_neg h7, if_neg h8, if_neg h9, if_neg h10]
                          rw [hfall] at hcc
                          exact absurd hcc (by simp)






/-! ### The per-shape SAT bridges -/

/-- The SAT bridge for `int_times(x, y, k)`: the piece's
    `timesSlot i j AUX`, satisfied by an accepted assignment whose
    AUX position carries the pin `.int k`, makes the source
    constraint hold at the extended assembled store. -/
theorem sat_aux_timesRK {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {k : Int}
    {i j n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "int_times")
    (hargs : c.args = [.basic (.ident x), .basic (.ident y),
        .basic (.lit (.int k))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsat : (DomConstraint.timesSlot i j (slots0.length + n)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨p, q, r, hri, hrj, hrAUX, hpqr⟩ := hsat
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  rw [hpin] at hrAUX
  have hk : k = r := by
    have h1 : Value.int k = Value.int r := by injection hrAUX
    injection h1
  subst hk
  have hstorex : ((assemble m (slots0 ++ auxs) dcs).toStore a) x
      = some a[i]! := toStore_read_model hnu halt hxi
  have hstorey : ((assemble m (slots0 ++ auxs) dcs).toStore a) y
      = some a[j]! := toStore_read_model hnu halt hyi
  have hib : a[i]! = Value.int p := bang_of_getElem? hri
  have hjb : a[j]! = Value.int q := bang_of_getElem? hrj
  refine ⟨[a[i]!, a[j]!, .int k], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        let v3 ← pure (Value.int k)
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, Value.int k] with
      | [Value.int p, Value.int q, Value.int r] => p * q = r
      | _ => False)
    rw [hib, hjb]
    exact hpqr


/-- The SAT bridge for `int_times(x, k, y)` (timesKR). -/
theorem sat_aux_timesKR {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {k : Int}
    {i j n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "int_times")
    (hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
        .basic (.ident y)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsat : (DomConstraint.timesSlot i (slots0.length + n) j).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨p, q, r, hri, hrAUX, hrj, hpqr⟩ := hsat
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  rw [hpin] at hrAUX
  have hk : k = q := by
    have h1 : Value.int k = Value.int q := by injection hrAUX
    injection h1
  subst hk
  have hstorex : ((assemble m (slots0 ++ auxs) dcs).toStore a) x
      = some a[i]! := toStore_read_model hnu halt hxi
  have hstorey : ((assemble m (slots0 ++ auxs) dcs).toStore a) y
      = some a[j]! := toStore_read_model hnu halt hyi
  have hib : a[i]! = Value.int p := bang_of_getElem? hri
  have hjb : a[j]! = Value.int r := bang_of_getElem? hrj
  refine ⟨[a[i]!, .int k, a[j]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← pure (Value.int k)
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.int k, a[j]!] with
      | [Value.int p, Value.int q, Value.int r] => p * q = r
      | _ => False)
    rw [hib, hjb]
    exact hpqr

/-- The SAT bridge for `int_times(k, x, y)` (timesKR'). -/
theorem sat_aux_timesKR' {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {k : Int}
    {i j n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "int_times")
    (hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
        .basic (.ident y)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsat : (DomConstraint.timesSlot (slots0.length + n) i j).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨p, q, r, hrAUX, hri, hrj, hpqr⟩ := hsat
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  rw [hpin] at hrAUX
  have hk : k = p := by
    have h1 : Value.int k = Value.int p := by injection hrAUX
    injection h1
  subst hk
  have hstorex : ((assemble m (slots0 ++ auxs) dcs).toStore a) x
      = some a[i]! := toStore_read_model hnu halt hxi
  have hstorey : ((assemble m (slots0 ++ auxs) dcs).toStore a) y
      = some a[j]! := toStore_read_model hnu halt hyi
  have hib : a[i]! = Value.int q := bang_of_getElem? hri
  have hjb : a[j]! = Value.int r := bang_of_getElem? hrj
  refine ⟨[.int k, a[i]!, a[j]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← pure (Value.int k)
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[i]!, a[j]!] with
      | [Value.int p, Value.int q, Value.int r] => p * q = r
      | _ => False)
    rw [hib, hjb]
    exact hpqr

/-- The SAT bridge for `int_times(x, k, k')` (timesRKK): the piece's
    `timesSlot i AUX₁ AUX₂`, satisfied by an accepted assignment
    whose two aux positions carry the pins `.int k` and `.int k'`,
    makes the source constraint hold at the extended assembled
    store. -/
theorem sat_aux_timesRKK {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {k k' : Int}
    {i n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot1 : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt1 : n < auxs.length)
    (hslot2 : auxs[n + 1]? = some (auxName (auxTaken m slots0) (n + 1), [.int k']))
    (hnlt2 : n + 1 < auxs.length)
    (hname : c.name.name = "int_times")
    (hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
        .basic (.lit (.int k'))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hsat : (DomConstraint.timesSlot i (slots0.length + n)
        (slots0.length + (n + 1))).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨p, q, r, hri, hrAUX1, hrAUX2, hpqr⟩ := hsat
  have hpin1 : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt1 hslot1
  have hpin2 : a[slots0.length + (n + 1)]? = some (.int k') :=
    auxPin_of_mem hmem hnlt2 hslot2
  rw [hpin1] at hrAUX1
  rw [hpin2] at hrAUX2
  have hk : k = q := by
    have h1 : Value.int k = Value.int q := by injection hrAUX1
    injection h1
  subst hk
  have hk' : k' = r := by
    have h1 : Value.int k' = Value.int r := by injection hrAUX2
    injection h1
  subst hk'
  have hstorex : ((assemble m (slots0 ++ auxs) dcs).toStore a) x
      = some a[i]! := toStore_read_model hnu halt hxi
  have hib : a[i]! = Value.int p := bang_of_getElem? hri
  refine ⟨[a[i]!, .int k, .int k'], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← pure (Value.int k)
        let v3 ← pure (Value.int k')
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.int k, Value.int k'] with
      | [Value.int p, Value.int q, Value.int r] => p * q = r
      | _ => False)
    rw [hib]
    exact hpqr

/-- The SAT bridge for `int_times(k, x, k')` (timesKRR). -/
theorem sat_aux_timesKRR {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {k k' : Int}
    {i n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot1 : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt1 : n < auxs.length)
    (hslot2 : auxs[n + 1]? = some (auxName (auxTaken m slots0) (n + 1), [.int k']))
    (hnlt2 : n + 1 < auxs.length)
    (hname : c.name.name = "int_times")
    (hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
        .basic (.lit (.int k'))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hsat : (DomConstraint.timesSlot (slots0.length + n) i
        (slots0.length + (n + 1))).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨p, q, r, hrAUX1, hri, hrAUX2, hpqr⟩ := hsat
  have hpin1 : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt1 hslot1
  have hpin2 : a[slots0.length + (n + 1)]? = some (.int k') :=
    auxPin_of_mem hmem hnlt2 hslot2
  rw [hpin1] at hrAUX1
  rw [hpin2] at hrAUX2
  have hk : k = p := by
    have h1 : Value.int k = Value.int p := by injection hrAUX1
    injection h1
  subst hk
  have hk' : k' = r := by
    have h1 : Value.int k' = Value.int r := by injection hrAUX2
    injection h1
  subst hk'
  have hstorex : ((assemble m (slots0 ++ auxs) dcs).toStore a) x
      = some a[i]! := toStore_read_model hnu halt hxi
  have hib : a[i]! = Value.int q := bang_of_getElem? hri
  refine ⟨[.int k, a[i]!, .int k'], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← pure (Value.int k)
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v3 ← pure (Value.int k')
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[i]!, Value.int k'] with
      | [Value.int p, Value.int q, Value.int r] => p * q = r
      | _ => False)
    rw [hib]
    exact hpqr

/-- The SAT bridge for `int_times(k, k', x)` (timesKKR). -/
theorem sat_aux_timesKKR {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {k k' : Int}
    {i n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot1 : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt1 : n < auxs.length)
    (hslot2 : auxs[n + 1]? = some (auxName (auxTaken m slots0) (n + 1), [.int k']))
    (hnlt2 : n + 1 < auxs.length)
    (hname : c.name.name = "int_times")
    (hargs : c.args = [.basic (.lit (.int k)), .basic (.lit (.int k')),
        .basic (.ident x)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hsat : (DomConstraint.timesSlot (slots0.length + n)
        (slots0.length + (n + 1)) i).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨p, q, r, hrAUX1, hrAUX2, hri, hpqr⟩ := hsat
  have hpin1 : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt1 hslot1
  have hpin2 : a[slots0.length + (n + 1)]? = some (.int k') :=
    auxPin_of_mem hmem hnlt2 hslot2
  rw [hpin1] at hrAUX1
  rw [hpin2] at hrAUX2
  have hk : k = p := by
    have h1 : Value.int k = Value.int p := by injection hrAUX1
    injection h1
  subst hk
  have hk' : k' = q := by
    have h1 : Value.int k' = Value.int q := by injection hrAUX2
    injection h1
  subst hk'
  have hstorex : ((assemble m (slots0 ++ auxs) dcs).toStore a) x
      = some a[i]! := toStore_read_model hnu halt hxi
  have hib : a[i]! = Value.int r := bang_of_getElem? hri
  refine ⟨[.int k, .int k', a[i]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← pure (Value.int k)
        let v2 ← pure (Value.int k')
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, Value.int k', a[i]!] with
      | [Value.int p, Value.int q, Value.int r] => p * q = r
      | _ => False)
    rw [hib]
    exact hpqr

/-- The SAT bridge for `int_ne(x, k)` (neRK). -/
theorem sat_aux_neRK {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {k : Int}
    {i n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "int_ne")
    (hargs : c.args = [.basic (.ident x), .basic (.lit (.int k))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hread : ∃ p, a[i]! = Value.int p)
    (hsat : (DomConstraint.neSlot i (slots0.length + n)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨w, z, hw, hz, hne⟩ := hsat
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  rw [hpin] at hz
  have hzk : z = Value.int k := (Option.some.inj hz).symm
  rw [hzk] at hne
  obtain ⟨p, hp⟩ := hread
  have hib : a[i]! = w := bang_of_getElem? hw
  have hwp : w = Value.int p := by rw [← hib, hp]
  refine ⟨[a[i]!, .int k], ?_, ?_⟩
  · rw [hargs]
    exact eval_ident_int (m := m) (slots := slots0 ++ auxs) (dcs := dcs)
      hnu halt hxi
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, Value.int k] with
      | [Value.int p, Value.int q] => p ≠ q
      | _ => False)
    rw [hp]
    intro heq
    exact hne (by rw [hwp, heq])

/-- The SAT bridge for `int_ne(k, x)` (neKR). -/
theorem sat_aux_neKR {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x : Ident} {k : Int}
    {i n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "int_ne")
    (hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hread : ∃ p, a[i]! = Value.int p)
    (hsat : (DomConstraint.neSlot (slots0.length + n) i).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨w, z, hw, hz, hne⟩ := hsat
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  rw [hpin] at hw
  have hwk : w = Value.int k := (Option.some.inj hw).symm
  rw [hwk] at hne
  obtain ⟨p, hp⟩ := hread
  have hib : a[i]! = z := bang_of_getElem? hz
  have hzp : z = Value.int p := by rw [← hib, hp]
  refine ⟨[.int k, a[i]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_int_ident (m := m) (slots := slots0 ++ auxs) (dcs := dcs)
      hnu halt hxi
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[i]!] with
      | [Value.int p, Value.int q] => p ≠ q
      | _ => False)
    rw [hp]
    intro heq
    exact hne (by rw [hzp, heq])

/-- The generic SAT bridge for a reified comparison with the literal in
    the second operand (PLAN C5b): the piece's reif slot constraint over
    the aux slot, with the aux pinned to `k`, makes the source constraint
    hold. -/
theorem sat_aux_reifRK {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x r : Ident} {k : Int}
    {i ir n : Nat} (nm : String) (R : Int → Int → Prop)
    (hiff : ∀ p q rb, fullInterp (Ident.mk nm) [.int p, .int q, .bool rb] ↔
      (rb = true ↔ R p q))
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = nm)
    (hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident r)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hri : nameIndex ((slots0 ++ auxs).map Prod.fst) r.name = some ir)
    (hsat : ∃ (p : Int) (q : Int) (rb : Bool), a[i]? = some (.int p) ∧
      a[slots0.length + n]? = some (.int q) ∧ a[ir]? = some (.bool rb) ∧ (rb = true ↔ R p q)) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  obtain ⟨u, v, rb, h1, h2, h3, hR⟩ := hsat
  rw [hpin] at h2
  have hv : k = v := by
    have := Option.some.inj h2
    injection this
  subst hv
  have hxb : a[i]! = .int u := bang_of_getElem? h1
  have hrb : a[ir]! = .bool rb := bang_of_getElem? h3
  refine ⟨[a[i]!, .int k, a[ir]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← pure (Value.int k)
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a r
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hri]
    rfl
  · rw [ident_eq_of_name hname, hxb, hrb]
    exact (hiff u k rb).mpr hR

/-- The generic SAT bridge for a reified comparison with the literal in
    the first operand (PLAN C5b): the piece's reif slot constraint over
    the aux slot, with the aux pinned to `k`, makes the source constraint
    hold. -/
theorem sat_aux_reifKR {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x r : Ident} {k : Int}
    {i ir n : Nat} (nm : String) (R : Int → Int → Prop)
    (hiff : ∀ p q rb, fullInterp (Ident.mk nm) [.int p, .int q, .bool rb] ↔
      (rb = true ↔ R p q))
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = nm)
    (hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident r)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hri : nameIndex ((slots0 ++ auxs).map Prod.fst) r.name = some ir)
    (hsat : ∃ (q : Int) (p : Int) (rb : Bool), a[slots0.length + n]? = some (.int q) ∧
      a[i]? = some (.int p) ∧ a[ir]? = some (.bool rb) ∧ (rb = true ↔ R q p)) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  obtain ⟨u, v, rb, h1, h2, h3, hR⟩ := hsat
  rw [hpin] at h1
  have hu : k = u := by
    have := Option.some.inj h1
    injection this
  subst hu
  have hxb : a[i]! = .int v := bang_of_getElem? h2
  have hrb : a[ir]! = .bool rb := bang_of_getElem? h3
  refine ⟨[.int k, a[i]!, a[ir]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← pure (Value.int k)
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a r
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hri]
    rfl
  · rw [ident_eq_of_name hname, hxb, hrb]
    exact (hiff k v rb).mpr hR

/-- The generic SAT bridge for a ternary int operation (PLAN C9) with the literal in
    the second operand (PLAN C5b): the piece's reif slot constraint over
    the aux slot, with the aux pinned to `k`, makes the source constraint
    hold. -/
theorem sat_aux_ternRK {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x r : Ident} {k : Int}
    {i ir n : Nat} (nm : String) (F : Int → Int → Int)
    (hiff : ∀ p q w, fullInterp (Ident.mk nm) [.int p, .int q, .int w] ↔ w = F p q)
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = nm)
    (hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident r)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hri : nameIndex ((slots0 ++ auxs).map Prod.fst) r.name = some ir)
    (hsat : ∃ (p : Int) (q : Int) (w : Int), a[i]? = some (.int p) ∧
      a[slots0.length + n]? = some (.int q) ∧ a[ir]? = some (.int w) ∧ F p q = w) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  obtain ⟨u, v, w, h1, h2, h3, hR⟩ := hsat
  rw [hpin] at h2
  have hv : k = v := by
    have := Option.some.inj h2
    injection this
  subst hv
  have hxb : a[i]! = .int u := bang_of_getElem? h1
  have hrb : a[ir]! = .int w := bang_of_getElem? h3
  refine ⟨[a[i]!, .int k, a[ir]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← pure (Value.int k)
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a r
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hri]
    rfl
  · rw [ident_eq_of_name hname, hxb, hrb]
    exact (hiff u k w).mpr hR.symm

/-- The generic SAT bridge for a ternary int operation (PLAN C9) with the literal in
    the first operand (PLAN C5b): the piece's reif slot constraint over
    the aux slot, with the aux pinned to `k`, makes the source constraint
    hold. -/
theorem sat_aux_ternKR {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x r : Ident} {k : Int}
    {i ir n : Nat} (nm : String) (F : Int → Int → Int)
    (hiff : ∀ p q w, fullInterp (Ident.mk nm) [.int p, .int q, .int w] ↔ w = F p q)
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = nm)
    (hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident r)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hri : nameIndex ((slots0 ++ auxs).map Prod.fst) r.name = some ir)
    (hsat : ∃ (q : Int) (p : Int) (w : Int), a[slots0.length + n]? = some (.int q) ∧
      a[i]? = some (.int p) ∧ a[ir]? = some (.int w) ∧ F q p = w) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  obtain ⟨u, v, w, h1, h2, h3, hR⟩ := hsat
  rw [hpin] at h1
  have hu : k = u := by
    have := Option.some.inj h1
    injection this
  subst hu
  have hxb : a[i]! = .int v := bang_of_getElem? h2
  have hrb : a[ir]! = .int w := bang_of_getElem? h3
  refine ⟨[.int k, a[i]!, a[ir]!], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← pure (Value.int k)
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a r
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hri]
    rfl
  · rw [ident_eq_of_name hname, hxb, hrb]
    exact (hiff k v w).mpr hR.symm

/-- The generic SAT bridge for a binary int operation (PLAN C9 remainder) with the
    literal in the RESULT position: the piece's slot constraint over the aux slot,
    with the aux pinned to `k`, makes the source constraint hold. -/
theorem sat_aux_ternRRK {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {k : Int}
    {i j n : Nat} (nm : String) (F : Int → Int → Int)
    (hiff : ∀ p q w, fullInterp (Ident.mk nm) [.int p, .int q, .int w] ↔ w = F p q)
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = nm)
    (hargs : c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.int k))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsat : ∃ (p : Int) (q : Int) (w : Int), a[i]? = some (.int p) ∧
      a[j]? = some (.int q) ∧ a[slots0.length + n]? = some (.int w) ∧ F p q = w) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  obtain ⟨p, q, w, h1, h2, h3, hR⟩ := hsat
  rw [hpin] at h3
  have hw : k = w := by
    have := Option.some.inj h3
    injection this
  have hxb : a[i]! = .int p := bang_of_getElem? h1
  have hyb : a[j]! = .int q := bang_of_getElem? h2
  refine ⟨[a[i]!, a[j]!, .int k], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        let v3 ← pure (Value.int k)
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, hxb, hyb]
    exact (hiff p q k).mpr (hw.trans hR.symm)

/-- The converse bridge for the two-element `array_int_minimum` chain
    (PLAN C9 remainder): a satisfied `minSlot` over the two element
    slots and the result slot makes the source array constraint hold at
    the assembled store. -/
theorem holds_array_int_minimum_of_minSlot {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {e1 e2 r : Ident} {i j k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "array_int_minimum")
    (hargs : c.args = [Expr.basic (.ident r),
      Expr.array [BasicExpr.ident e1, BasicExpr.ident e2]])
    (hxi : nameIndex (slots.map Prod.fst) e1.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) e2.name = some j)
    (hri : nameIndex (slots.map Prod.fst) r.name = some k)
    (hsat : (DomConstraint.minSlot i j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, q, w, h1, h2, h3, hmin⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? h1
  have hjb : a[j]! = Value.int q := bang_of_getElem? h2
  have hkb : a[k]! = Value.int w := bang_of_getElem? h3
  refine ⟨[a[k]!, .array [a[i]!, a[j]!]], ?_, ?_⟩
  · rw [hargs]
    have his : linIndices (slots.map Prod.fst)
        [BasicExpr.ident e1, BasicExpr.ident e2] = some [i, j] := by
      simp [linIndices, hxi, hyi]
    exact eval_ident_slot_array (m := m) (dcs := dcs)
      (x := r) (elems := [BasicExpr.ident e1, BasicExpr.ident e2])
      (is := [i, j]) (k := k) hnu halt hri his
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[k]!, .array [a[i]!, a[j]!]] with
      | [Value.int m', Value.array xs] => minValue xs = some m'
      | _ => False)
    rw [hkb, hib, hjb]
    show minValue [Value.int p, Value.int q] = some w
    rw [minValue_int_int, hmin]

/-- The converse bridge for the two-element `array_int_maximum` chain
    (PLAN C9 remainder): a satisfied `maxSlot` over the two element
    slots and the result slot makes the source array constraint hold at
    the assembled store. -/
theorem holds_array_int_maximum_of_maxSlot {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {e1 e2 r : Ident} {i j k : Nat}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "array_int_maximum")
    (hargs : c.args = [Expr.basic (.ident r),
      Expr.array [BasicExpr.ident e1, BasicExpr.ident e2]])
    (hxi : nameIndex (slots.map Prod.fst) e1.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) e2.name = some j)
    (hri : nameIndex (slots.map Prod.fst) r.name = some k)
    (hsat : (DomConstraint.maxSlot i j k).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  obtain ⟨p, q, w, h1, h2, h3, hmax⟩ := hsat
  have hib : a[i]! = Value.int p := bang_of_getElem? h1
  have hjb : a[j]! = Value.int q := bang_of_getElem? h2
  have hkb : a[k]! = Value.int w := bang_of_getElem? h3
  refine ⟨[a[k]!, .array [a[i]!, a[j]!]], ?_, ?_⟩
  · rw [hargs]
    have his : linIndices (slots.map Prod.fst)
        [BasicExpr.ident e1, BasicExpr.ident e2] = some [i, j] := by
      simp [linIndices, hxi, hyi]
    exact eval_ident_slot_array (m := m) (dcs := dcs)
      (x := r) (elems := [BasicExpr.ident e1, BasicExpr.ident e2])
      (is := [i, j]) (k := k) hnu halt hri his
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[k]!, .array [a[i]!, a[j]!]] with
      | [Value.int m', Value.array xs] => maxValue xs = some m'
      | _ => False)
    rw [hkb, hib, hjb]
    show maxValue [Value.int p, Value.int q] = some w
    rw [maxValue_int_int, hmax]

/-- The SAT bridge for `bool_and(x, y, true)` (andTrue). -/
theorem sat_aux_andTrue {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {i j : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [.basic (.ident x), .basic (.ident y),
        .basic (.lit (.bool true))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsati : (DomConstraint.constEq i (.bool true)).SatisfiedBy a)
    (hsatj : (DomConstraint.constEq j (.bool true)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hib : a[i]! = Value.bool true := bang_of_getElem? hsati
  have hjb : a[j]! = Value.bool true := bang_of_getElem? hsatj
  refine ⟨[a[i]!, a[j]!, .bool true], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        let v3 ← pure (Value.bool true)
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, Value.bool true] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
      | _ => False)
    rw [hib, hjb]
    rfl

/-- The SAT bridge for `bool_and(x, y, false)` (andFalse). -/
theorem sat_aux_andFalse {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {i j n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.bool false]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [.basic (.ident x), .basic (.ident y),
        .basic (.lit (.bool false))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsat : (DomConstraint.boolAndSlot i j (slots0.length + n)).SatisfiedBy a)
    (hsatpin : (DomConstraint.constEq (slots0.length + n) (.bool false)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hpin : a[slots0.length + n]? = some (.bool false) :=
    auxPin_of_mem hmem hnlt hslot
  obtain ⟨p, q, r, hri, hrj, hrAUX, hpqr⟩ := hsat
  rw [hpin] at hrAUX
  have hr : r = false := by
    have hval : Value.bool false = Value.bool r := by injection hrAUX
    have hbool : false = r := by injection hval
    exact hbool.symm
  subst hr
  have hib : a[i]! = Value.bool p := bang_of_getElem? hri
  have hjb : a[j]! = Value.bool q := bang_of_getElem? hrj
  refine ⟨[a[i]!, a[j]!, .bool false], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        let v3 ← pure (Value.bool false)
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, Value.bool false] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
      | _ => False)
    rw [hib, hjb]
    exact hpqr.symm

/-- The SAT bridge for `bool_or(x, y, true)` (orTrue). -/
theorem sat_aux_orTrue {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {i j n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.bool true]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [.basic (.ident x), .basic (.ident y),
        .basic (.lit (.bool true))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsat : (DomConstraint.boolOrSlot i j (slots0.length + n)).SatisfiedBy a)
    (hsatpin : (DomConstraint.constEq (slots0.length + n) (.bool true)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hpin : a[slots0.length + n]? = some (.bool true) :=
    auxPin_of_mem hmem hnlt hslot
  obtain ⟨p, q, r, hri, hrj, hrAUX, hpqr⟩ := hsat
  rw [hpin] at hrAUX
  have hr : r = true := by
    have hval : Value.bool true = Value.bool r := by injection hrAUX
    have hbool : true = r := by injection hval
    exact hbool.symm
  subst hr
  have hib : a[i]! = Value.bool p := bang_of_getElem? hri
  have hjb : a[j]! = Value.bool q := bang_of_getElem? hrj
  refine ⟨[a[i]!, a[j]!, .bool true], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        let v3 ← pure (Value.bool true)
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, Value.bool true] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
      | _ => False)
    rw [hib, hjb]
    exact hpqr.symm

/-- The SAT bridge for `bool_or(x, y, false)` (orFalse). -/
theorem sat_aux_orFalse {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident} {i j : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [.basic (.ident x), .basic (.ident y),
        .basic (.lit (.bool false))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some j)
    (hsati : (DomConstraint.constEq i (.bool false)).SatisfiedBy a)
    (hsatj : (DomConstraint.constEq j (.bool false)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  have hib : a[i]! = Value.bool false := bang_of_getElem? hsati
  have hjb : a[j]! = Value.bool false := bang_of_getElem? hsatj
  refine ⟨[a[i]!, a[j]!, .bool false], ?_, ?_⟩
  · rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        let v3 ← pure (Value.bool false)
        pure [v1, v2, v3]) = _
    rw [toStore_read_model (m := m) hnu halt hxi,
      toStore_read_model (m := m) hnu halt hyi]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, Value.bool false] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
      | _ => False)
    rw [hib, hjb]
    rfl


/-- The SAT bridge for the value-literal `array_int_element` over an
    all-literal table (constElemValL, PLAN C0 element values): the
    piece's slot-table element constraint over the pinned aux slot
    makes the source constraint hold. -/
theorem sat_aux_constElemValL {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x aux : Ident}
    {xs : List Int} {k : Int} {i n : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "array_int_element")
    (hargs : c.args = [.basic (.ident x), .array (litTab xs),
        .basic (.lit (.int k))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (haux : nameIndex ((slots0 ++ auxs).map Prod.fst) aux.name
      = some (slots0.length + n))
    (hsat : (DomConstraint.arrayIntElementSlot xs i (slots0.length + n)).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨idx, e, hread, hauxread, hget⟩ := hsat
  have hpin : a[slots0.length + n]? = some (.int k) :=
    auxPin_of_mem hmem hnlt hslot
  rw [hpin] at hauxread
  have hke : k = e := by
    have h1 := Option.some.inj hauxread
    injection h1
  subst hke
  -- the piece's Holds over the slot-table shape
  have hp : ({ name := Ident.mk "array_int_element"
             , args := [Expr.basic (.ident x), Expr.array (litTab xs),
                 Expr.basic (.ident aux)]
             , anns := [] } : ConstraintItem).Holds fullInterp
      ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
    refine ⟨[a[i]!, .array (xs.map Value.int), .int k], ?_, ?_⟩
    · show (do
          let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
          let v2 ← Option.map Value.array ((litTab xs).mapM (BasicExpr.eval
            ((assemble m (slots0 ++ auxs) dcs).toStore a)))
          let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a aux
          pure [v1, v2, v3]) = _
      rw [toStore_read_model (m := m) hnu halt hxi,
        toStore_read_model (m := m) hnu halt haux]
      rw [bang_of_getElem? hread, mapM_eval_litTab, bang_of_getElem? hpin]
      rfl
    · change fullInterp (Ident.mk "array_int_element")
        [a[i]!, .array (xs.map Value.int), .int k]
      rw [fullInterp_of_extracted_elem "array_int_element" (Or.inl rfl)]
      show (match [a[i]!, .array (xs.map Value.int), .int k] with
        | [.int i, .array ys, .int e] => valuesGet1 ys i = some (.int e)
        | _ => False)
      rw [bang_of_getElem? hread]
      exact hget
  -- the source follows by the argument-evaluation congruence
  have hargsmap : c.args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = ({ name := Ident.mk "array_int_element"
         , args := [Expr.basic (.ident x), Expr.array (litTab xs),
             Expr.basic (.ident aux)]
         , anns := [] } : ConstraintItem).args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a)) := by
    rw [hargs]
    exact mapM_eval_constElemValL
      (store := (assemble m (slots0 ++ auxs) dcs).toStore a)
      (x := x) (aux := aux) (xs := xs) (k := k)
      (by
        rw [toStore_read_model (m := m) hnu halt haux,
          bang_of_getElem? hpin])
  exact holds_of_eval_args_eq (nm := Ident.mk "array_int_element")
    (ident_eq_of_name hname)
    (show ({ name := Ident.mk "array_int_element"
           , args := [Expr.basic (.ident x), Expr.array (litTab xs),
               Expr.basic (.ident aux)]
           , anns := [] } : ConstraintItem).name
        = Ident.mk "array_int_element" from rfl)
    hargsmap hp

/-- The SAT bridge for the one-literal mixed `array_var_int_element`
    table with a SLOT value operand (`varElemTabLit`, PLAN C0 element
    values): the piece's all-slot table over the pinned aux slot makes
    the source constraint hold. -/
theorem sat_aux_varElemTabLit {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y aux : Ident}
    {pre post : List Ident} {k : Int} {i kk n : Nat} {is : List Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hname : c.name.name = "array_var_int_element")
    (hargs : c.args = [.basic (.ident x), .array (litSplitTab pre k post),
        .basic (.ident y)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some kk)
    (haux : nameIndex ((slots0 ++ auxs).map Prod.fst) aux.name
      = some (slots0.length + n))
    (his : linIndices ((slots0 ++ auxs).map Prod.fst) (auxTab pre aux post)
      = some is)
    (hsat : (DomConstraint.arrayVarIntElementSlot is i kk).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨idx, e, hreadi, hreadk, _hallreads, hget⟩ := hsat
  -- the aux slot reads its pinned literal
  have hauxpin : ((assemble m (slots0 ++ auxs) dcs).toStore a) aux
      = some (.int k) := by
    rw [toStore_read_model (m := m) hnu halt haux,
      bang_of_getElem? (auxPin_of_mem hmem hnlt hslot)]
  -- the piece's table evaluates to the assignment's reads at `is`
  have hl : linIndices ((slots0 ++ auxs).map Prod.fst)
      ((pre ++ [aux] ++ post).map (fun x => BasicExpr.ident x)) = some is := by
    rw [← auxTab_eq]
    exact his
  have hnameidx : (pre ++ [aux] ++ post).mapM
      (fun x => nameIndex ((slots0 ++ auxs).map Prod.fst) x.name)
      = some is := by
    rw [← linIndices_idents]
    exact hl
  have hreadlist : (auxTab pre aux post).mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [auxTab_eq, mapM_eval_idents]
    refine mapM_store_of_linIndices hl (fun j hj => ?_)
    have hres := mapM_nameIndex_get hnameidx j hj
    exact toStore_read_model (m := m) hnu halt hres
  -- the piece's Holds at the assembled store
  have hp : ({ name := Ident.mk "array_var_int_element"
             , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
                 Expr.basic (.ident y)]
             , anns := [] } : ConstraintItem).Holds fullInterp
      ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!], ?_, ?_⟩
    · show (do
          let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
          let v2 ← Option.map Value.array ((auxTab pre aux post).mapM
            (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
          let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
          pure [v1, v2, v3]) = _
      rw [toStore_read_model (m := m) hnu halt hxi,
        toStore_read_model (m := m) hnu halt hyi, hreadlist]
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      rfl
    · change fullInterp (Ident.mk "array_var_int_element")
        [a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!]
      rw [fullInterp_of_extracted_elem "array_var_int_element"
        (Or.inr (Or.inl rfl))]
      show (match [a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!] with
        | [.int i', .array xs, .int e'] => valuesGet1 xs i' = some (.int e')
        | _ => False)
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      exact hget
  -- the source follows by the argument-evaluation congruence
  have hargsmap : c.args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = ({ name := Ident.mk "array_var_int_element"
         , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
             Expr.basic (.ident y)]
         , anns := [] } : ConstraintItem).args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a)) := by
    rw [hargs]
    exact mapM_eval_varElemTabLit
      (store := (assemble m (slots0 ++ auxs) dcs).toStore a)
      (x := x) (y := y) (aux := aux) (pre := pre) (post := post) (k := k)
      hauxpin
  exact holds_of_eval_args_eq (nm := Ident.mk "array_var_int_element")
    (ident_eq_of_name hname)
    (show ({ name := Ident.mk "array_var_int_element"
           , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
               Expr.basic (.ident y)]
           , anns := [] } : ConstraintItem).name
        = Ident.mk "array_var_int_element" from rfl)
    hargsmap hp

/-- The SAT bridge for the one-literal mixed `array_var_int_element`
    table with a LITERAL value operand (`varElemTabValLit`, PLAN C0
    element values): the piece's all-slot table over the first pinned
    aux slot and the value operand on the second pinned aux slot make
    the source constraint hold. -/
theorem sat_aux_varElemTabValLit {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x aux aux2 : Ident}
    {pre post : List Ident} {k k' : Int} {i kk n : Nat} {is : List Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (hslot : auxs[n]? = some (auxName (auxTaken m slots0) n, [.int k]))
    (hnlt : n < auxs.length)
    (hslot2 : auxs[n + 1]?
      = some (auxName (auxTaken m slots0) (n + 1), [.int k']))
    (hnlt2 : n + 1 < auxs.length)
    (hname : c.name.name = "array_var_int_element")
    (hargs : c.args = [.basic (.ident x), .array (litSplitTab pre k post),
        .basic (.lit (.int k'))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (haux : nameIndex ((slots0 ++ auxs).map Prod.fst) aux.name
      = some (slots0.length + n))
    (haux2 : nameIndex ((slots0 ++ auxs).map Prod.fst) aux2.name
      = some (slots0.length + (n + 1)))
    (hkk : kk = slots0.length + (n + 1))
    (his : linIndices ((slots0 ++ auxs).map Prod.fst) (auxTab pre aux post)
      = some is)
    (hsat : (DomConstraint.arrayVarIntElementSlot is i kk).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨idx, e, hreadi, hreadk, _hallreads, hget⟩ := hsat
  -- the two aux slots read their pinned literals
  have hauxpin : ((assemble m (slots0 ++ auxs) dcs).toStore a) aux
      = some (.int k) := by
    rw [toStore_read_model (m := m) hnu halt haux,
      bang_of_getElem? (auxPin_of_mem hmem hnlt hslot)]
  have haux2pin : ((assemble m (slots0 ++ auxs) dcs).toStore a) aux2
      = some (.int k') := by
    rw [toStore_read_model (m := m) hnu halt haux2,
      bang_of_getElem? (auxPin_of_mem hmem hnlt2 hslot2)]
  -- the second pin fixes the value read
  have hek : e = k' := by
    have h1 : a[slots0.length + (n + 1)]! = Value.int k' := by
      have h2 := haux2pin
      rw [toStore_read_model (m := m) hnu halt haux2] at h2
      exact Option.some.inj h2
    rw [hkk] at hreadk
    rw [bang_of_getElem? hreadk] at h1
    exact Value.int.inj h1
  rw [hek] at hget
  rw [hkk] at hreadk
  rw [hek] at hreadk
  -- the piece's table evaluates to the assignment's reads at `is`
  have hl : linIndices ((slots0 ++ auxs).map Prod.fst)
      ((pre ++ [aux] ++ post).map (fun x => BasicExpr.ident x)) = some is := by
    rw [← auxTab_eq]
    exact his
  have hnameidx : (pre ++ [aux] ++ post).mapM
      (fun x => nameIndex ((slots0 ++ auxs).map Prod.fst) x.name)
      = some is := by
    rw [← linIndices_idents]
    exact hl
  have hreadlist : (auxTab pre aux post).mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [auxTab_eq, mapM_eval_idents]
    refine mapM_store_of_linIndices hl (fun j hj => ?_)
    have hres := mapM_nameIndex_get hnameidx j hj
    exact toStore_read_model (m := m) hnu halt hres
  -- the piece's Holds at the assembled store
  have hp : ({ name := Ident.mk "array_var_int_element"
             , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
                 Expr.basic (.ident aux2)]
             , anns := [] } : ConstraintItem).Holds fullInterp
      ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), .int k'], ?_, ?_⟩
    · show (do
          let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
          let v2 ← Option.map Value.array ((auxTab pre aux post).mapM
            (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
          let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a aux2
          pure [v1, v2, v3]) = _
      rw [toStore_read_model (m := m) hnu halt hxi,
        toStore_read_model (m := m) hnu halt haux2, hreadlist]
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      rfl
    · change fullInterp (Ident.mk "array_var_int_element")
        [a[i]!, .array (is.map (fun j => a[j]!)), .int k']
      rw [fullInterp_of_extracted_elem "array_var_int_element"
        (Or.inr (Or.inl rfl))]
      show (match [a[i]!, .array (is.map (fun j => a[j]!)), .int k'] with
        | [.int i', .array xs, .int e'] => valuesGet1 xs i' = some (.int e')
        | _ => False)
      rw [bang_of_getElem? hreadi]
      exact hget
  -- the source follows by the argument-evaluation congruence
  have hargsmap : c.args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = ({ name := Ident.mk "array_var_int_element"
         , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
             Expr.basic (.ident aux2)]
         , anns := [] } : ConstraintItem).args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a)) := by
    rw [hargs]
    exact mapM_eval_varElemTabValLit
      (store := (assemble m (slots0 ++ auxs) dcs).toStore a)
      (x := x) (aux := aux) (aux2 := aux2) (pre := pre) (post := post)
      (k := k) (k' := k') hauxpin haux2pin
  exact holds_of_eval_args_eq (nm := Ident.mk "array_var_int_element")
    (ident_eq_of_name hname)
    (show ({ name := Ident.mk "array_var_int_element"
           , args := [Expr.basic (.ident x), Expr.array (auxTab pre aux post),
               Expr.basic (.ident aux2)]
           , anns := [] } : ConstraintItem).name
        = Ident.mk "array_var_int_element" from rfl)
    hargsmap hp

/-- The aux-chain reads of a successfully compiled aux extension
    (PLAN C0 element values, k-literal generalization): the j-th
    successor slot of the extended position `n` reads the j-th pinned
    value. -/
theorem auxChain_reads {m : Model}
    {slots0 : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {taken : List String} {vs : List Value}
    {n N : Nat}
    (hsub : ∀ s ∈ slots0.map Prod.fst, s ∈ taken)
    (hspec : ∀ j p, (modelAuxSlots m)[j]? = some p → p.1 = auxName taken j)
    (hnu : ((slots0 ++ modelAuxSlots m).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ modelAuxSlots m).length)
    (hmem : a ∈ allAssigns ((slots0 ++ modelAuxSlots m).map Prod.snd))
    (hslot : ∀ j, j < N →
      (modelAuxSlots m)[n + j]?
        = some (auxName taken (n + j), [vs[j]!])) :
    ∀ j, j < N →
      ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore a)
        (auxChain (Ident.mk (auxName taken n)) N)[j]! = some (vs[j]!) := by
  intro j hj
  have hchain : (auxChain (Ident.mk (auxName taken n)) N)[j]?
      = some (Ident.mk (auxName taken (n + j))) :=
    auxChain_getElem? (taken := taken) (n := n) (k := N) (j := j) hj
  have hget : (auxChain (Ident.mk (auxName taken n)) N)[j]!
      = Ident.mk (auxName taken (n + j)) := bang_of_getElem?_id hchain
  have hres : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
      (auxName taken (n + j)) = some (slots0.length + (n + j)) :=
    nameIndex_aux_slot (slots0 := slots0) (auxs := modelAuxSlots m)
      (taken := taken) (i := n + j) (vs := [vs[j]!])
      hsub hspec (hslot j hj)
  have hstore : ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore a)
      (Ident.mk (auxName taken (n + j))) = some a[slots0.length + (n + j)]! :=
    toStore_read_model (m := m) hnu halt hres
  have hpin : a[slots0.length + (n + j)]? = some (vs[j]!) :=
    auxPin_of_mem hmem (List.getElem?_eq_some_iff.mp (hslot j hj)).1 (hslot j hj)
  rw [hget, hstore, bang_of_getElem? hpin]

/-- The SAT bridge for the k-literal mixed `array_var_int_element`
    table with a slot value (`varElemTabKs`, PLAN C0 element values):
    the piece's all-slot table over the k pinned aux slots makes the
    source constraint hold. -/
theorem sat_aux_varElemTabKs {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident}
    {tab : ArrayLiteral} {auxes : List Ident} {i kk : Nat} {is : List Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hname : c.name.name = "array_var_int_element")
    (hargs : c.args = [.basic (.ident x), .array tab, .basic (.ident y)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some kk)
    (hlen : auxes.length = (tabLitVals tab).length)
    (hmix : mixedOk tab)
    (hauxread : ∀ j, j < auxes.length →
      ((assemble m (slots0 ++ auxs) dcs).toStore a) auxes[j]!
        = some (.int (tabLitVals tab)[j]!))
    (his : linIndices ((slots0 ++ auxs).map Prod.fst) (mixSubst tab auxes)
      = some is)
    (hsat : (DomConstraint.arrayVarIntElementSlot is i kk).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨idx, e, hreadi, hreadk, _hallreads, hget⟩ := hsat
  have hl : linIndices ((slots0 ++ auxs).map Prod.fst)
      ((mixIdents tab auxes).map (fun x => BasicExpr.ident x)) = some is := by
    rw [← mixSubst_eq_map_mixIdents tab auxes hmix hlen]
    exact his
  have hnameidx : (mixIdents tab auxes).mapM
      (fun x => nameIndex ((slots0 ++ auxs).map Prod.fst) x.name)
      = some is := by
    rw [← linIndices_idents]
    exact hl
  have hreadlist : (mixSubst tab auxes).mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [mixSubst_eq_map_mixIdents tab auxes hmix hlen, mapM_eval_idents]
    refine mapM_store_of_linIndices hl (fun j hj => ?_)
    have hres := mapM_nameIndex_get hnameidx j hj
    exact toStore_read_model (m := m) hnu halt hres
  have hvals : tab.mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [← mapM_eval_mixSubst hlen hauxread]
    exact hreadlist
  have hp : ({ name := Ident.mk "array_var_int_element"
             , args := [Expr.basic (.ident x), Expr.array (mixSubst tab auxes),
                 Expr.basic (.ident y)]
             , anns := [] } : ConstraintItem).Holds fullInterp
      ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!], ?_, ?_⟩
    · show (do
          let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
          let v2 ← Option.map Value.array ((mixSubst tab auxes).mapM
            (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
          let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
          pure [v1, v2, v3]) = _
      rw [toStore_read_model (m := m) hnu halt hxi,
        toStore_read_model (m := m) hnu halt hyi, hreadlist]
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      rfl
    · change fullInterp (Ident.mk "array_var_int_element")
        [a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!]
      rw [fullInterp_of_extracted_elem "array_var_int_element"
        (Or.inr (Or.inl rfl))]
      show (match [a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!] with
        | [.int i', .array xs, .int e'] => valuesGet1 xs i' = some (.int e')
        | _ => False)
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      exact hget
  have hargsmap : c.args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = ({ name := Ident.mk "array_var_int_element"
         , args := [Expr.basic (.ident x), Expr.array (mixSubst tab auxes),
             Expr.basic (.ident y)]
         , anns := [] } : ConstraintItem).args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a)) := by
    rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array (tab.mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        pure [v1, v2, v3]) = (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array ((mixSubst tab auxes).mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        pure [v1, v2, v3])
    rw [mapM_eval_mixSubst hlen hauxread]
  exact holds_of_eval_args_eq (nm := Ident.mk "array_var_int_element")
    (ident_eq_of_name hname)
    (show ({ name := Ident.mk "array_var_int_element"
           , args := [Expr.basic (.ident x), Expr.array (mixSubst tab auxes),
               Expr.basic (.ident y)]
           , anns := [] } : ConstraintItem).name
        = Ident.mk "array_var_int_element" from rfl)
    hargsmap hp

/-- The SAT bridge for the k-literal mixed `array_var_int_element`
    table with a LITERAL value (`varElemTabValKs`): the piece's
    all-slot table over the k pinned aux slots and the value on the
    successor value slot make the source constraint hold. -/
theorem sat_aux_varElemTabValKs {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x aux2 : Ident}
    {tab : ArrayLiteral} {auxes : List Ident} {k' : Int}
    {i kk vpos : Nat} {is : List Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hname : c.name.name = "array_var_int_element")
    (hargs : c.args = [.basic (.ident x), .array tab,
        .basic (.lit (.int k'))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hlen : auxes.length = (tabLitVals tab).length)
    (hmix : mixedOk tab)
    (hauxread : ∀ j, j < auxes.length →
      ((assemble m (slots0 ++ auxs) dcs).toStore a) auxes[j]!
        = some (.int (tabLitVals tab)[j]!))
    (haux2 : nameIndex ((slots0 ++ auxs).map Prod.fst) aux2.name
      = some vpos)
    (hkk : kk = vpos)
    (haux2read : ((assemble m (slots0 ++ auxs) dcs).toStore a) aux2
      = some (.int k'))
    (his : linIndices ((slots0 ++ auxs).map Prod.fst) (mixSubst tab auxes)
      = some is)
    (hsat : (DomConstraint.arrayVarIntElementSlot is i kk).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨idx, e, hreadi, hreadk, _hallreads, hget⟩ := hsat
  have hek : e = k' := by
    have h1 : a[kk]! = Value.int k' := by
      have h2 := haux2read
      rw [toStore_read_model (m := m) hnu halt haux2] at h2
      have h2' : a[kk]! = a[vpos]! := by rw [hkk]
      exact h2'.trans (Option.some.inj h2)
    rw [bang_of_getElem? hreadk] at h1
    exact Value.int.inj h1
  rw [hek] at hget
  rw [hkk] at hreadk
  rw [hek] at hreadk
  have hl : linIndices ((slots0 ++ auxs).map Prod.fst)
      ((mixIdents tab auxes).map (fun x => BasicExpr.ident x)) = some is := by
    rw [← mixSubst_eq_map_mixIdents tab auxes hmix hlen]
    exact his
  have hnameidx : (mixIdents tab auxes).mapM
      (fun x => nameIndex ((slots0 ++ auxs).map Prod.fst) x.name)
      = some is := by
    rw [← linIndices_idents]
    exact hl
  have hreadlist : (mixSubst tab auxes).mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [mixSubst_eq_map_mixIdents tab auxes hmix hlen, mapM_eval_idents]
    refine mapM_store_of_linIndices hl (fun j hj => ?_)
    have hres := mapM_nameIndex_get hnameidx j hj
    exact toStore_read_model (m := m) hnu halt hres
  have hvals : tab.mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [← mapM_eval_mixSubst hlen hauxread]
    exact hreadlist
  have hp : ({ name := Ident.mk "array_var_int_element"
             , args := [Expr.basic (.ident x), Expr.array (mixSubst tab auxes),
                 Expr.basic (.ident aux2)]
             , anns := [] } : ConstraintItem).Holds fullInterp
      ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), .int k'], ?_, ?_⟩
    · show (do
          let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
          let v2 ← Option.map Value.array ((mixSubst tab auxes).mapM
            (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
          let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a aux2
          pure [v1, v2, v3]) = _
      rw [toStore_read_model (m := m) hnu halt hxi,
        toStore_read_model (m := m) hnu halt haux2, hreadlist]
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      rfl
    · change fullInterp (Ident.mk "array_var_int_element")
        [a[i]!, .array (is.map (fun j => a[j]!)), .int k']
      rw [fullInterp_of_extracted_elem "array_var_int_element"
        (Or.inr (Or.inl rfl))]
      show (match [a[i]!, .array (is.map (fun j => a[j]!)), .int k'] with
        | [.int i', .array xs, .int e'] => valuesGet1 xs i' = some (.int e')
        | _ => False)
      rw [bang_of_getElem? hreadi]
      exact hget
  have hargsmap : c.args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = ({ name := Ident.mk "array_var_int_element"
         , args := [Expr.basic (.ident x), Expr.array (mixSubst tab auxes),
             Expr.basic (.ident aux2)]
         , anns := [] } : ConstraintItem).args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a)) := by
    rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array (tab.mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← pure (Value.int k')
        pure [v1, v2, v3]) = (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array ((mixSubst tab auxes).mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a aux2
        pure [v1, v2, v3])
    rw [mapM_eval_mixSubst hlen hauxread, haux2read]
    rfl
  exact holds_of_eval_args_eq (nm := Ident.mk "array_var_int_element")
    (ident_eq_of_name hname)
    (show ({ name := Ident.mk "array_var_int_element"
           , args := [Expr.basic (.ident x), Expr.array (mixSubst tab auxes),
               Expr.basic (.ident aux2)]
           , anns := [] } : ConstraintItem).name
        = Ident.mk "array_var_int_element" from rfl)
    hargsmap hp

/-- The SAT bridge for the mixed bool `array_var_bool_element` table
    with a slot value (`varBoolTabLits`, PLAN C0 element values, bool
    tables): the piece's all-slot table over the pinned aux slots makes
    the source constraint hold. -/
theorem sat_aux_varBoolTabLits {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y : Ident}
    {tab : ArrayLiteral} {auxes : List Ident} {i kk : Nat} {is : List Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hname : c.name.name = "array_var_bool_element")
    (hargs : c.args = [.basic (.ident x), .array tab, .basic (.ident y)])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hyi : nameIndex ((slots0 ++ auxs).map Prod.fst) y.name = some kk)
    (hlen : auxes.length = (tabBoolVals tab).length)
    (hmix : mixedOkB tab)
    (hauxread : ∀ j, j < auxes.length →
      ((assemble m (slots0 ++ auxs) dcs).toStore a) auxes[j]!
        = some (.bool (tabBoolVals tab)[j]!))
    (his : linIndices ((slots0 ++ auxs).map Prod.fst) (mixSubstB tab auxes)
      = some is)
    (hsat : (DomConstraint.arrayVarBoolElementSlot is i kk).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨idx, e, hreadi, hreadk, _hallreads, hget⟩ := hsat
  have hl : linIndices ((slots0 ++ auxs).map Prod.fst)
      ((mixIdentsB tab auxes).map (fun x => BasicExpr.ident x)) = some is := by
    rw [← mixSubstB_eq_map_mixIdentsB tab auxes hmix hlen]
    exact his
  have hnameidx : (mixIdentsB tab auxes).mapM
      (fun x => nameIndex ((slots0 ++ auxs).map Prod.fst) x.name)
      = some is := by
    rw [← linIndices_idents]
    exact hl
  have hreadlist : (mixSubstB tab auxes).mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [mixSubstB_eq_map_mixIdentsB tab auxes hmix hlen, mapM_eval_idents]
    refine mapM_store_of_linIndices hl (fun j hj => ?_)
    have hres := mapM_nameIndex_get hnameidx j hj
    exact toStore_read_model (m := m) hnu halt hres
  have hvals : tab.mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [← mapM_eval_mixSubstB hlen hauxread]
    exact hreadlist
  have hp : ({ name := Ident.mk "array_var_bool_element"
             , args := [Expr.basic (.ident x), Expr.array (mixSubstB tab auxes),
                 Expr.basic (.ident y)]
             , anns := [] } : ConstraintItem).Holds fullInterp
      ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!], ?_, ?_⟩
    · show (do
          let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
          let v2 ← Option.map Value.array ((mixSubstB tab auxes).mapM
            (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
          let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
          pure [v1, v2, v3]) = _
      rw [toStore_read_model (m := m) hnu halt hxi,
        toStore_read_model (m := m) hnu halt hyi, hreadlist]
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      rfl
    · change fullInterp (Ident.mk "array_var_bool_element")
        [a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!]
      rw [fullInterp_of_extracted_elem "array_var_bool_element"
        (Or.inr (Or.inr rfl))]
      show (match [a[i]!, .array (is.map (fun j => a[j]!)), a[kk]!] with
        | [.int i', .array xs, .bool e'] => valuesGet1 xs i' = some (.bool e')
        | _ => False)
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      exact hget
  have hargsmap : c.args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = ({ name := Ident.mk "array_var_bool_element"
         , args := [Expr.basic (.ident x), Expr.array (mixSubstB tab auxes),
             Expr.basic (.ident y)]
         , anns := [] } : ConstraintItem).args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a)) := by
    rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array (tab.mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        pure [v1, v2, v3]) = (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array ((mixSubstB tab auxes).mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a y
        pure [v1, v2, v3])
    rw [mapM_eval_mixSubstB hlen hauxread]
  exact holds_of_eval_args_eq (nm := Ident.mk "array_var_bool_element")
    (ident_eq_of_name hname)
    (show ({ name := Ident.mk "array_var_bool_element"
           , args := [Expr.basic (.ident x), Expr.array (mixSubstB tab auxes),
               Expr.basic (.ident y)]
           , anns := [] } : ConstraintItem).name
        = Ident.mk "array_var_bool_element" from rfl)
    hargsmap hp

/-- The SAT bridge for the mixed bool `array_var_bool_element` table
    with a LITERAL value (`varBoolTabValLit`): the piece's all-slot
    table over the pinned aux slots and the value on the successor
    value slot make the source constraint hold. -/
theorem sat_aux_varBoolTabValLit {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x aux2 : Ident}
    {tab : ArrayLiteral} {auxes : List Ident} {b' : Bool}
    {i kk vpos : Nat} {is : List Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hname : c.name.name = "array_var_bool_element")
    (hargs : c.args = [.basic (.ident x), .array tab,
        .basic (.lit (.bool b'))])
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hlen : auxes.length = (tabBoolVals tab).length)
    (hmix : mixedOkB tab)
    (hauxread : ∀ j, j < auxes.length →
      ((assemble m (slots0 ++ auxs) dcs).toStore a) auxes[j]!
        = some (.bool (tabBoolVals tab)[j]!))
    (haux2 : nameIndex ((slots0 ++ auxs).map Prod.fst) aux2.name
      = some vpos)
    (hkk : kk = vpos)
    (haux2read : ((assemble m (slots0 ++ auxs) dcs).toStore a) aux2
      = some (.bool b'))
    (his : linIndices ((slots0 ++ auxs).map Prod.fst) (mixSubstB tab auxes)
      = some is)
    (hsat : (DomConstraint.arrayVarBoolElementSlot is i kk).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
  obtain ⟨idx, e, hreadi, hreadk, _hallreads, hget⟩ := hsat
  have hek : e = b' := by
    have h1 : a[kk]! = Value.bool b' := by
      have h2 := haux2read
      rw [toStore_read_model (m := m) hnu halt haux2] at h2
      have h2' : a[kk]! = a[vpos]! := by rw [hkk]
      exact h2'.trans (Option.some.inj h2)
    rw [bang_of_getElem? hreadk] at h1
    exact Value.bool.inj h1
  rw [hek] at hget
  rw [hkk] at hreadk
  rw [hek] at hreadk
  have hl : linIndices ((slots0 ++ auxs).map Prod.fst)
      ((mixIdentsB tab auxes).map (fun x => BasicExpr.ident x)) = some is := by
    rw [← mixSubstB_eq_map_mixIdentsB tab auxes hmix hlen]
    exact his
  have hnameidx : (mixIdentsB tab auxes).mapM
      (fun x => nameIndex ((slots0 ++ auxs).map Prod.fst) x.name)
      = some is := by
    rw [← linIndices_idents]
    exact hl
  have hreadlist : (mixSubstB tab auxes).mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [mixSubstB_eq_map_mixIdentsB tab auxes hmix hlen, mapM_eval_idents]
    refine mapM_store_of_linIndices hl (fun j hj => ?_)
    have hres := mapM_nameIndex_get hnameidx j hj
    exact toStore_read_model (m := m) hnu halt hres
  have hvals : tab.mapM
      (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = some (is.map (fun j => a[j]!)) := by
    rw [← mapM_eval_mixSubstB hlen hauxread]
    exact hreadlist
  have hp : ({ name := Ident.mk "array_var_bool_element"
             , args := [Expr.basic (.ident x), Expr.array (mixSubstB tab auxes),
                 Expr.basic (.ident aux2)]
             , anns := [] } : ConstraintItem).Holds fullInterp
      ((assemble m (slots0 ++ auxs) dcs).toStore a) := by
    refine ⟨[a[i]!, .array (is.map (fun j => a[j]!)), .bool b'], ?_, ?_⟩
    · show (do
          let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
          let v2 ← Option.map Value.array ((mixSubstB tab auxes).mapM
            (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
          let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a aux2
          pure [v1, v2, v3]) = _
      rw [toStore_read_model (m := m) hnu halt hxi,
        toStore_read_model (m := m) hnu halt haux2, hreadlist]
      rw [bang_of_getElem? hreadi, bang_of_getElem? hreadk]
      rfl
    · change fullInterp (Ident.mk "array_var_bool_element")
        [a[i]!, .array (is.map (fun j => a[j]!)), .bool b']
      rw [fullInterp_of_extracted_elem "array_var_bool_element"
        (Or.inr (Or.inr rfl))]
      show (match [a[i]!, .array (is.map (fun j => a[j]!)), .bool b'] with
        | [.int i', .array xs, .bool e'] => valuesGet1 xs i' = some (.bool e')
        | _ => False)
      rw [bang_of_getElem? hreadi]
      exact hget
  have hargsmap : c.args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a))
      = ({ name := Ident.mk "array_var_bool_element"
         , args := [Expr.basic (.ident x), Expr.array (mixSubstB tab auxes),
             Expr.basic (.ident aux2)]
         , anns := [] } : ConstraintItem).args.mapM (Expr.eval
        ((assemble m (slots0 ++ auxs) dcs).toStore a)) := by
    rw [hargs]
    show (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array (tab.mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← pure (Value.bool b')
        pure [v1, v2, v3]) = (do
        let v1 ← (assemble m (slots0 ++ auxs) dcs).toStore a x
        let v2 ← Option.map Value.array ((mixSubstB tab auxes).mapM
          (BasicExpr.eval ((assemble m (slots0 ++ auxs) dcs).toStore a)))
        let v3 ← (assemble m (slots0 ++ auxs) dcs).toStore a aux2
        pure [v1, v2, v3])
    rw [mapM_eval_mixSubstB hlen hauxread, haux2read]
    rfl
  exact holds_of_eval_args_eq (nm := Ident.mk "array_var_bool_element")
    (ident_eq_of_name hname)
    (show ({ name := Ident.mk "array_var_bool_element"
           , args := [Expr.basic (.ident x), Expr.array (mixSubstB tab auxes),
               Expr.basic (.ident aux2)]
           , anns := [] } : ConstraintItem).name
        = Ident.mk "array_var_bool_element" from rfl)
    hargsmap hp

/-- **WHOLE-MODEL EXACTNESS (`compile_exact`)**: an assignment accepted
    by the compiled problem reconstructs a store satisfying every
    dynamic condition of `Satisfies fullSig fullInterp` — every source
    constraint holds, every declared variable reads a value in its
    declared domain, and (no initializers in the fragment) the
    initializer conditions are trivial. -/
theorem compile_exact {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem)
    (hwf : WellFormed fullSig m)
    {a : List Value}
    (hmem : a ∈ allAssigns problem.domains)
    (hacc : accepts problem a = true) :
    (∀ c ∈ m.constraints, c.Holds fullInterp (problem.toStore a)) ∧
    (∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, (problem.toStore a) n = some v ∧
          ty.contains v
      | .array _ _ _ _ => False) := by
  -- invert the compile into the assembled problem (slots = model
  -- slots ++ aux slots; dcs from the EXPANDED constraint list)
  obtain ⟨_, slots, dcs, ⟨slots0, hslots0, hslots⟩, hcomp, hasm⟩ :=
    compileModel_ok_inv hc
  -- the assembled problem's fields
  have hdoms : problem.domains = slots.map (fun p => Dom.ofList p.2) := by
    show problem.domains = slots.map (fun p => Dom.ofList p.2)
    rw [hasm]
    rfl
  have hstore : ∀ x, problem.toStore a x =
      (assemble m slots dcs).toStore a x := by
    intro x
    show problem.toStore a x = (assemble m slots dcs).toStore a x
    rw [hasm]
  rw [hdoms, allAssigns_map_ofList] at hmem
  -- the combined names are distinct (model slots + fresh aux names)
  have hnu : (slots.map Prod.fst).Nodup := by
    rw [hslots]
    exact extendedSlotNames_nodup hwf hslots0 rfl
  have halt : a.length = slots.length := by
    have h1 := mem_allAssigns_length (slots.map Prod.snd) a hmem
    rw [List.length_map] at h1
    exact h1
  -- the expanded-list plan equation
  have hplan : expandPlan (auxTaken m slots0) [] m.constraints
      = (modelAuxSlots m, modelExpand m) := by
    have h1 := modelAuxSlots_eq hslots0
    have h2 := modelExpand_eq hslots0
    rw [h1, h2]
  have hpred : m.predicates = [] := compileModel_predicates_nil hc
  have hacc' : accepts (assemble m slots dcs) a = true := by
    rw [← hasm]
    exact hacc
  -- the constraints half: every ORIGINAL constraint holds
  have hcons : ∀ c ∈ m.constraints, c.Holds fullInterp
      ((assemble m slots dcs).toStore a) := by
    intro c hc'
    cases hshape : auxShapeOf c with
    | none =>
        -- a passthrough original: its compiled dc is IN the compiled
        -- list; the ext-SAT linker applies over the extended slots
        have hcmem : c ∈ modelExpand m :=
          expandPlan_keep m.constraints [] (modelAuxSlots m) (modelExpand m)
            hplan c hc' hshape
        obtain ⟨dc, hdcmem, hcc⟩ :=
          compileConstraints_fwd_inv (modelExpand m) dcs hcomp c hcmem
        rw [hslots]
        exact compile_sat_link_ext (auxs := modelAuxSlots m)
          (dcs := dcs) (compileModel_vars_basic hc)
          (fun n2 p hp => by
            -- aux names are fresh from the taken list
            have hspec := (modelAuxSlots_spec hslots0).1 n2 p hp
            rw [hspec]
            exact auxName_not_mem)
          hwf hslots0 hc' hpred (by rw [← hslots]; exact hmem)
          (by rw [← hslots]; exact hnu)
          (by rw [← hslots]; exact hcc)
          (accepts_of_true hacc' dc hdcmem)
    | some sh =>
        -- a pinning shape: its pieces are in the expanded list, their
        -- compiled constraints are satisfied, and the per-shape SAT
        -- bridges conclude c.Holds
        have hpieces := expandPlan_pieces_mem
          (taken := auxTaken m slots0) m.constraints [] (modelAuxSlots m)
          (modelExpand m) hplan c hc' sh hshape
        obtain ⟨i2, hpieces⟩ := hpieces
        -- the aux name of this constraint's slot (the pieces-mem
        -- package carries the pin2 disjunct too; project it away)
        have haux : ∀ c' ∈ sh.expand (Ident.mk (auxName (auxTaken m slots0) i2)),
            c' ∈ modelExpand m ∧ (sh.pin = none ∨
              ∃ v, sh.pin = some v ∧ (modelAuxSlots m)[i2]?
                = some (auxName (auxTaken m slots0) i2, [v])) ∧
              (sh.pin2 = none ∨
                ∃ v2, sh.pin2 = some v2 ∧ (modelAuxSlots m)[i2 + 1]?
                  = some (auxName (auxTaken m slots0) (i2 + 1), [v2])) ∧
              (∀ j, j < sh.pinsK.length → (modelAuxSlots m)[i2 + j]?
                = some (auxName (auxTaken m slots0) (i2 + j), [sh.pinsK[j]!])) :=
          fun c' hc'mem => hpieces c' hc'mem
        -- each piece's compiled dc is in dcs and satisfied
        have hpieceSat : ∀ c' ∈ sh.expand (Ident.mk (auxName (auxTaken m slots0) i2)), ∃ dc ∈ dcs,
            compileConstraint (parEnv m) (slots.map Prod.fst) c' = .ok dc ∧
              dc.SatisfiedBy a := by
          intro c' hc'mem
          obtain ⟨dc, hdcmem, hcc⟩ :=
            compileConstraints_fwd_inv (modelExpand m) dcs hcomp c' (haux c' hc'mem).1
          exact ⟨dc, hdcmem, hcc, accepts_of_true hacc' dc hdcmem⟩
        -- the per-shape SAT bridges: case on the nine shapes
        cases sh with
        | timesRK x y k =>
            -- the args inversion: c's args are [x, y, lit k]
            have hargsc : c.args = [.basic (.ident x), .basic (.ident y),
                .basic (.lit (.int k))] := auxShapeOf_timesRK_args hshape
            -- the pieces' pin info: the aux slot at i2 carries [.int k]
            rcases (haux ((AuxShape.expand (.timesRK x y k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.timesRK x y k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              -- the dc IS timesSlot over the model positions and the
              -- aux position (the piece's compile inversion); the
              -- sat_aux_timesRK bridge then concludes c.Holds
              obtain ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ :=
                compileConstraint_int_times3_inv hcc
              -- the aux position is the extended slots0.length + i2
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                -- the aux slot's name resolves at slots0.length + i2
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                -- the piece's AUX identifier name reduces to the
                -- slot's name string
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                -- both resolve the same name at a unique position
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              -- the store reads via the extended slots
              rw [hslots] at hnu halt hmem hxi hyi ⊢
              exact sat_aux_timesRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (y := y) (k := k)
                (i := i) (j := j) (n := i2)
                hnu halt hmem hslotget hnlt
                (by
                  rw [show c.name.name = "int_times" from by
                    rw [← auxShapeOf_timesRK_args hshape] at hargsc
                    exact auxShapeOf_timesRK_name hshape])
                hargsc hxi hyi hsatdc
        | timesKR x y k =>
            -- the args inversion: c's args are [x, lit k, y]
            have hargsc : c.args = [.basic (.ident x), .basic (.lit (.int k)),
                .basic (.ident y)] := auxShapeOf_timesKR_args hshape
            -- the pieces' pin info: the aux slot at i2 carries [.int k]
            rcases (haux ((AuxShape.expand (.timesKR x y k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.timesKR x y k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              -- the dc IS timesSlot i AUX j (the piece's compile
              -- inversion); the sat_aux_timesKR bridge concludes
              obtain ⟨i, iAUX, j, hxi, hAUXi, hyi, hdcform⟩ :=
                compileConstraint_int_times3_inv hcc
              -- the aux position is the extended slots0.length + i2
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              -- the store reads via the extended slots
              rw [hslots] at hnu halt hmem hxi hyi ⊢
              exact sat_aux_timesKR (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (y := y) (k := k)
                (i := i) (j := j) (n := i2)
                hnu halt hmem hslotget hnlt
                (by
                  rw [show c.name.name = "int_times" from by
                    rw [← auxShapeOf_timesKR_args hshape] at hargsc
                    exact auxShapeOf_timesKR_name hshape])
                hargsc hxi hyi hsatdc
        | timesKR' x y k =>
            -- the args inversion: c's args are [lit k, x, y]
            have hargsc : c.args = [.basic (.lit (.int k)), .basic (.ident x),
                .basic (.ident y)] := auxShapeOf_timesKR'_args hshape
            -- the pieces' pin info: the aux slot at i2 carries [.int k]
            rcases (haux ((AuxShape.expand (.timesKR' x y k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.timesKR' x y k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              -- the dc IS timesSlot AUX i j (the piece's compile
              -- inversion); the sat_aux_timesKR' bridge concludes
              obtain ⟨iAUX, i, j, hAUXi, hxi, hyi, hdcform⟩ :=
                compileConstraint_int_times3_inv hcc
              -- the aux position is the extended slots0.length + i2
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              -- the store reads via the extended slots
              rw [hslots] at hnu halt hmem hxi hyi ⊢
              exact sat_aux_timesKR' (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (y := y) (k := k)
                (i := i) (j := j) (n := i2)
                hnu halt hmem hslotget hnlt
                (by
                  rw [show c.name.name = "int_times" from by
                    rw [← auxShapeOf_timesKR'_args hshape] at hargsc
                    exact auxShapeOf_timesKR'_name hshape])
                hargsc hxi hyi hsatdc
        | timesRKK x k k' =>
            -- the args inversion: c's args are [x, lit k, lit k']
            have hargsc : c.args = [.basic (.ident x), .basic (.lit (.int k)),
                .basic (.lit (.int k'))] := auxShapeOf_timesRKK_args hshape
            -- the pieces' pin info: the aux slots at i2 and i2+1
            -- carry [.int k] and [.int k']
            have hslots2 : (modelAuxSlots m)[i2]?
                = some (auxName (auxTaken m slots0) i2, [Value.int k]) ∧
                (modelAuxSlots m)[i2 + 1]?
                  = some (auxName (auxTaken m slots0) (i2 + 1), [Value.int k']) := by
              rcases (haux ((AuxShape.expand (.timesRKK x k k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                (List.mem_cons_self)).2.1 with
                hpinnone | ⟨v, hpin, hslotget⟩
              · exact absurd hpinnone (by simp [AuxShape.pin])
              · rcases (haux ((AuxShape.expand (.timesRKK x k k')
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                  (List.mem_cons_self)).2.2.1 with
                  hpin2none | ⟨v2, hpin2, hslot2get⟩
                · exact absurd hpin2none (by simp [AuxShape.pin2])
                · have hvk : v = Value.int k := by
                    have h2 := hpin
                    rw [AuxShape.pin] at h2
                    exact (Option.some.inj h2).symm
                  have hvk' : v2 = Value.int k' := by
                    have h2 := hpin2
                    rw [AuxShape.pin2] at h2
                    exact (Option.some.inj h2).symm
                  subst hvk
                  subst hvk'
                  exact ⟨hslotget, hslot2get⟩
            obtain ⟨hslotget, hslot2get⟩ := hslots2
            have hnlt : i2 < (modelAuxSlots m).length :=
              (List.getElem?_eq_some_iff.mp hslotget).1
            have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
              (List.getElem?_eq_some_iff.mp hslot2get).1
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.timesRKK x k k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
            -- the dc IS timesSlot i AUX1 AUX2 (the piece's compile
            -- inversion); the sat_aux_timesRKK bridge then
            -- concludes c.Holds
            obtain ⟨i, iAUX1, iAUX2, hxi, hAUX1i, hAUX2i, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the first aux position is the extended
            -- slots0.length + i2
            have hAUX1pos : iAUX1 = slots0.length + i2 := by
              have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                  = slots.map Prod.fst := by rw [hslots]
              have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                  p.1 = auxName (auxTaken m slots0) j2 :=
                (modelAuxSlots_spec hslots0).1
              have hres := nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0) (i := i2)
                (vs := [Value.int k])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                hspec hslotget
              rw [hnames] at hres
              -- the piece's AUX identifier name reduces to the
              -- slot's name string
              have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                  = auxName (auxTaken m slots0) i2 := rfl
              rw [hAUXname] at hAUX1i
              -- both resolve the same name at a unique position
              have hsame : iAUX1 = slots0.length + i2 := by
                have h1 : nameIndex (List.map Prod.fst slots)
                    (auxName (auxTaken m slots0) i2) = some iAUX1 := hAUX1i
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              exact hsame
            -- the second aux position is the successor slot's
            -- extended position slots0.length + (i2 + 1)
            have hAUX2pos : iAUX2 = slots0.length + (i2 + 1) := by
              have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                  = slots.map Prod.fst := by rw [hslots]
              have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                  p.1 = auxName (auxTaken m slots0) j2 :=
                (modelAuxSlots_spec hslots0).1
              have hres := nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0) (i := i2 + 1)
                (vs := [Value.int k'])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                hspec hslot2get
              rw [hnames] at hres
              -- the piece's second AUX identifier name reduces to
              -- the successor slot's name string
              have hAUX2name : (nextAuxIdent
                  (Ident.mk (auxName (auxTaken m slots0) i2))).name
                  = auxName (auxTaken m slots0) (i2 + 1) :=
                nextAuxIdent_name (auxTaken m slots0) i2
              rw [hAUX2name] at hAUX2i
              -- both resolve the same name at a unique position
              have hsame : iAUX2 = slots0.length + (i2 + 1) := by
                have h1 : nameIndex (List.map Prod.fst slots)
                    (auxName (auxTaken m slots0) (i2 + 1)) = some iAUX2 := hAUX2i
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              exact hsame
            rw [hdcform, hAUX1pos, hAUX2pos] at hsatdc
            -- the store reads via the extended slots
            rw [hslots] at hnu halt hmem hxi ⊢
            exact sat_aux_timesRKK (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (k := k) (k' := k')
              (i := i) (n := i2)
              hnu halt hmem hslotget hnlt hslot2get hnlt2
              (by
                rw [show c.name.name = "int_times" from by
                  rw [← auxShapeOf_timesRKK_args hshape] at hargsc
                  exact auxShapeOf_timesRKK_name hshape])
              hargsc hxi hsatdc
        | timesKRR x k k' =>
            -- the args inversion: c's args are [lit k, x, lit k']
            have hargsc : c.args = [.basic (.lit (.int k)), .basic (.ident x),
                .basic (.lit (.int k'))] := auxShapeOf_timesKRR_args hshape
            -- the pieces' pin info: the aux slots at i2 and i2+1
            -- carry [.int k] and [.int k']
            have hslots2 : (modelAuxSlots m)[i2]?
                = some (auxName (auxTaken m slots0) i2, [Value.int k]) ∧
                (modelAuxSlots m)[i2 + 1]?
                  = some (auxName (auxTaken m slots0) (i2 + 1), [Value.int k']) := by
              rcases (haux ((AuxShape.expand (.timesKRR x k k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                (List.mem_cons_self)).2.1 with
                hpinnone | ⟨v, hpin, hslotget⟩
              · exact absurd hpinnone (by simp [AuxShape.pin])
              · rcases (haux ((AuxShape.expand (.timesKRR x k k')
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                  (List.mem_cons_self)).2.2.1 with
                  hpin2none | ⟨v2, hpin2, hslot2get⟩
                · exact absurd hpin2none (by simp [AuxShape.pin2])
                · have hvk : v = Value.int k := by
                    have h2 := hpin
                    rw [AuxShape.pin] at h2
                    exact (Option.some.inj h2).symm
                  have hvk' : v2 = Value.int k' := by
                    have h2 := hpin2
                    rw [AuxShape.pin2] at h2
                    exact (Option.some.inj h2).symm
                  subst hvk
                  subst hvk'
                  exact ⟨hslotget, hslot2get⟩
            obtain ⟨hslotget, hslot2get⟩ := hslots2
            have hnlt : i2 < (modelAuxSlots m).length :=
              (List.getElem?_eq_some_iff.mp hslotget).1
            have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
              (List.getElem?_eq_some_iff.mp hslot2get).1
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.timesKRR x k k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
            -- the dc IS timesSlot AUX1 i AUX2 (the piece's compile
            -- inversion); the sat_aux_timesKRR bridge concludes
            obtain ⟨iAUX1, i, iAUX2, hAUX1i, hxi, hAUX2i, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the first aux position is the extended
            -- slots0.length + i2
            have hAUX1pos : iAUX1 = slots0.length + i2 := by
              have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                  = slots.map Prod.fst := by rw [hslots]
              have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                  p.1 = auxName (auxTaken m slots0) j2 :=
                (modelAuxSlots_spec hslots0).1
              have hres := nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0) (i := i2)
                (vs := [Value.int k])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                hspec hslotget
              rw [hnames] at hres
              have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                  = auxName (auxTaken m slots0) i2 := rfl
              rw [hAUXname] at hAUX1i
              have hsame : iAUX1 = slots0.length + i2 := by
                have h1 : nameIndex (List.map Prod.fst slots)
                    (auxName (auxTaken m slots0) i2) = some iAUX1 := hAUX1i
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              exact hsame
            -- the second aux position is the successor slot's
            -- extended position slots0.length + (i2 + 1)
            have hAUX2pos : iAUX2 = slots0.length + (i2 + 1) := by
              have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                  = slots.map Prod.fst := by rw [hslots]
              have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                  p.1 = auxName (auxTaken m slots0) j2 :=
                (modelAuxSlots_spec hslots0).1
              have hres := nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0) (i := i2 + 1)
                (vs := [Value.int k'])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                hspec hslot2get
              rw [hnames] at hres
              have hAUX2name : (nextAuxIdent
                  (Ident.mk (auxName (auxTaken m slots0) i2))).name
                  = auxName (auxTaken m slots0) (i2 + 1) :=
                nextAuxIdent_name (auxTaken m slots0) i2
              rw [hAUX2name] at hAUX2i
              have hsame : iAUX2 = slots0.length + (i2 + 1) := by
                have h1 : nameIndex (List.map Prod.fst slots)
                    (auxName (auxTaken m slots0) (i2 + 1)) = some iAUX2 := hAUX2i
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              exact hsame
            rw [hdcform, hAUX1pos, hAUX2pos] at hsatdc
            -- the store reads via the extended slots
            rw [hslots] at hnu halt hmem hxi ⊢
            exact sat_aux_timesKRR (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (k := k) (k' := k')
              (i := i) (n := i2)
              hnu halt hmem hslotget hnlt hslot2get hnlt2
              (by
                rw [show c.name.name = "int_times" from by
                  rw [← auxShapeOf_timesKRR_args hshape] at hargsc
                  exact auxShapeOf_timesKRR_name hshape])
              hargsc hxi hsatdc
        | timesKKR x k k' =>
            -- the args inversion: c's args are [lit k, lit k', x]
            have hargsc : c.args = [.basic (.lit (.int k)), .basic (.lit (.int k')),
                .basic (.ident x)] := auxShapeOf_timesKKR_args hshape
            -- the pieces' pin info: the aux slots at i2 and i2+1
            -- carry [.int k] and [.int k']
            have hslots2 : (modelAuxSlots m)[i2]?
                = some (auxName (auxTaken m slots0) i2, [Value.int k]) ∧
                (modelAuxSlots m)[i2 + 1]?
                  = some (auxName (auxTaken m slots0) (i2 + 1), [Value.int k']) := by
              rcases (haux ((AuxShape.expand (.timesKKR x k k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                (List.mem_cons_self)).2.1 with
                hpinnone | ⟨v, hpin, hslotget⟩
              · exact absurd hpinnone (by simp [AuxShape.pin])
              · rcases (haux ((AuxShape.expand (.timesKKR x k k')
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                  (List.mem_cons_self)).2.2.1 with
                  hpin2none | ⟨v2, hpin2, hslot2get⟩
                · exact absurd hpin2none (by simp [AuxShape.pin2])
                · have hvk : v = Value.int k := by
                    have h2 := hpin
                    rw [AuxShape.pin] at h2
                    exact (Option.some.inj h2).symm
                  have hvk' : v2 = Value.int k' := by
                    have h2 := hpin2
                    rw [AuxShape.pin2] at h2
                    exact (Option.some.inj h2).symm
                  subst hvk
                  subst hvk'
                  exact ⟨hslotget, hslot2get⟩
            obtain ⟨hslotget, hslot2get⟩ := hslots2
            have hnlt : i2 < (modelAuxSlots m).length :=
              (List.getElem?_eq_some_iff.mp hslotget).1
            have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
              (List.getElem?_eq_some_iff.mp hslot2get).1
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.timesKKR x k k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
            -- the dc IS timesSlot AUX1 AUX2 i (the piece's compile
            -- inversion); the sat_aux_timesKKR bridge concludes
            obtain ⟨iAUX1, iAUX2, i, hAUX1i, hAUX2i, hxi, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the first aux position is the extended
            -- slots0.length + i2
            have hAUX1pos : iAUX1 = slots0.length + i2 := by
              have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                  = slots.map Prod.fst := by rw [hslots]
              have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                  p.1 = auxName (auxTaken m slots0) j2 :=
                (modelAuxSlots_spec hslots0).1
              have hres := nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0) (i := i2)
                (vs := [Value.int k])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                hspec hslotget
              rw [hnames] at hres
              have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                  = auxName (auxTaken m slots0) i2 := rfl
              rw [hAUXname] at hAUX1i
              have hsame : iAUX1 = slots0.length + i2 := by
                have h1 : nameIndex (List.map Prod.fst slots)
                    (auxName (auxTaken m slots0) i2) = some iAUX1 := hAUX1i
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              exact hsame
            -- the second aux position is the successor slot's
            -- extended position slots0.length + (i2 + 1)
            have hAUX2pos : iAUX2 = slots0.length + (i2 + 1) := by
              have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                  = slots.map Prod.fst := by rw [hslots]
              have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                  p.1 = auxName (auxTaken m slots0) j2 :=
                (modelAuxSlots_spec hslots0).1
              have hres := nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0) (i := i2 + 1)
                (vs := [Value.int k'])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                hspec hslot2get
              rw [hnames] at hres
              have hAUX2name : (nextAuxIdent
                  (Ident.mk (auxName (auxTaken m slots0) i2))).name
                  = auxName (auxTaken m slots0) (i2 + 1) :=
                nextAuxIdent_name (auxTaken m slots0) i2
              rw [hAUX2name] at hAUX2i
              have hsame : iAUX2 = slots0.length + (i2 + 1) := by
                have h1 : nameIndex (List.map Prod.fst slots)
                    (auxName (auxTaken m slots0) (i2 + 1)) = some iAUX2 := hAUX2i
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              exact hsame
            rw [hdcform, hAUX1pos, hAUX2pos] at hsatdc
            -- the store reads via the extended slots
            rw [hslots] at hnu halt hmem hxi ⊢
            exact sat_aux_timesKKR (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (k := k) (k' := k')
              (i := i) (n := i2)
              hnu halt hmem hslotget hnlt hslot2get hnlt2
              (by
                rw [show c.name.name = "int_times" from by
                  rw [← auxShapeOf_timesKKR_args hshape] at hargsc
                  exact auxShapeOf_timesKKR_name hshape])
              hargsc hxi hsatdc
        | neRK x k =>
            -- the args + name inversion: c is int_ne(x, lit k)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neRK_inv hshape
            -- the pieces' pin info: the aux slot at i2 carries [.int k]
            rcases (haux ((AuxShape.expand (.neRK x k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.neRK x k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              -- the dc IS neSlot i AUX (the piece's compile
              -- inversion); the sat_aux_neRK bridge concludes
              obtain ⟨i, iAUX, hxi, hAUXi, hdcform⟩ :=
                compileConstraint_int_ne2_inv hcc
              -- the aux position is the extended slots0.length + i2
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              -- the store reads via the extended slots
              rw [hslots] at hnu halt hmem hxi ⊢
              -- the int-read premise: x's slot value is an integer
              -- (the master ext-reads lemma over the well-formed
              -- constraint's int signature)
              have hread : ∃ p, a[i]! = Value.int p := by
                obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc'
                have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
                    [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                      BasicParType.int)),
                     PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                      BasicParType.int))] := by
                  rw [show Ident.mk c.name.name = Ident.mk "int_ne" from by
                    rw [hnamec]]
                  exact sigEnv_int_ne hpred
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
                exact int_read_of_checkArg_master_ext
                  (compileModel_vars_basic hc) hwf hslots0 hnu
                  (fun n2 p hp => by
                    -- aux names are fresh from the taken list
                    have hspec := (modelAuxSlots_spec hslots0).1 n2 p hp
                    rw [hspec]
                    exact auxName_not_mem)
                  hfor
                  (by
                    intro pt hpt
                    rcases List.mem_cons.mp hpt with rfl | htl
                    · rfl
                    · rcases List.mem_cons.mp htl with rfl | hnil
                      · rfl
                      · exact absurd hnil (by simp))
                  (by
                    rw [hargsc]
                    exact List.mem_cons_self)
                  hxi hmem
              exact sat_aux_neRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (k := k)
                (i := i) (n := i2)
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hread hsatdc
        | neKR x k =>
            -- the args + name inversion: c is int_ne(lit k, x)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neKR_inv hshape
            -- the pieces' pin info: the aux slot at i2 carries [.int k]
            rcases (haux ((AuxShape.expand (.neKR x k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.neKR x k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              -- the dc IS neSlot AUX i (the piece's compile
              -- inversion); the sat_aux_neKR bridge concludes
              obtain ⟨iAUX, i, hAUXi, hxi, hdcform⟩ :=
                compileConstraint_int_ne2_inv hcc
              -- the aux position is the extended slots0.length + i2
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              -- the store reads via the extended slots
              rw [hslots] at hnu halt hmem hxi ⊢
              -- the int-read premise: x's slot value is an integer
              -- (the master ext-reads lemma over the well-formed
              -- constraint's int signature)
              have hread : ∃ p, a[i]! = Value.int p := by
                obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc'
                have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
                    [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                      BasicParType.int)),
                     PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                      BasicParType.int))] := by
                  rw [show Ident.mk c.name.name = Ident.mk "int_ne" from by
                    rw [hnamec]]
                  exact sigEnv_int_ne hpred
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
                exact int_read_of_checkArg_master_ext
                  (compileModel_vars_basic hc) hwf hslots0 hnu
                  (fun n2 p hp => by
                    -- aux names are fresh from the taken list
                    have hspec := (modelAuxSlots_spec hslots0).1 n2 p hp
                    rw [hspec]
                    exact auxName_not_mem)
                  hfor
                  (by
                    intro pt hpt
                    rcases List.mem_cons.mp hpt with rfl | htl
                    · rfl
                    · rcases List.mem_cons.mp htl with rfl | hnil
                      · rfl
                      · exact absurd hnil (by simp))
                  (by
                    rw [hargsc]
                    exact List.mem_cons_of_mem _ List.mem_cons_self)
                  hxi hmem
              exact sat_aux_neKR (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (k := k)
                (i := i) (n := i2)
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hread hsatdc
        | eqReifRK x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_eqReifRK_inv hshape
            rcases (haux ((AuxShape.expand (.eqReifRK x r k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.eqReifRK x r k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
                compileConstraint_int_eq_reif_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_reifRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := r) (k := k)
                (i := i) (ir := ir) (n := i2) "int_eq_reif" (fun p q => p = q)
                fullInterp_int_eq_reif_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | eqReifKR x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_eqReifKR_inv hshape
            rcases (haux ((AuxShape.expand (.eqReifKR x r k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.eqReifKR x r k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
                compileConstraint_int_eq_reif_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_reifKR (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := r) (k := k)
                (i := i) (ir := ir) (n := i2) "int_eq_reif" (fun p q => p = q)
                fullInterp_int_eq_reif_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | leReifRK x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_leReifRK_inv hshape
            rcases (haux ((AuxShape.expand (.leReifRK x r k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.leReifRK x r k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
                compileConstraint_int_le_reif_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_reifRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := r) (k := k)
                (i := i) (ir := ir) (n := i2) "int_le_reif" (fun p q => p ≤ q)
                fullInterp_int_le_reif_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | leReifKR x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_leReifKR_inv hshape
            rcases (haux ((AuxShape.expand (.leReifKR x r k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.leReifKR x r k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
                compileConstraint_int_le_reif_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_reifKR (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := r) (k := k)
                (i := i) (ir := ir) (n := i2) "int_le_reif" (fun p q => p ≤ q)
                fullInterp_int_le_reif_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | neReifRK x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neReifRK_inv hshape
            rcases (haux ((AuxShape.expand (.neReifRK x r k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.neReifRK x r k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
                compileConstraint_int_ne_reif_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_reifRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := r) (k := k)
                (i := i) (ir := ir) (n := i2) "int_ne_reif" (fun p q => p ≠ q)
                fullInterp_int_ne_reif_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | neReifKR x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neReifKR_inv hshape
            rcases (haux ((AuxShape.expand (.neReifKR x r k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.neReifKR x r k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
                compileConstraint_int_ne_reif_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_reifKR (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := r) (k := k)
                (i := i) (ir := ir) (n := i2) "int_ne_reif" (fun p q => p ≠ q)
                fullInterp_int_ne_reif_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | minRK x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minRK_inv hshape
            rcases (haux ((AuxShape.expand (.minRK x z k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.minRK x z k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
                compileConstraint_int_min_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_ternRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := z) (k := k)
                (i := i) (ir := ir) (n := i2) "int_min" (fun p q => min p q)
                fullInterp_int_min_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | minKR x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minKR_inv hshape
            rcases (haux ((AuxShape.expand (.minKR x z k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.minKR x z k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
                compileConstraint_int_min_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_ternKR (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := z) (k := k)
                (i := i) (ir := ir) (n := i2) "int_min" (fun p q => min p q)
                fullInterp_int_min_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | maxRK x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxRK_inv hshape
            rcases (haux ((AuxShape.expand (.maxRK x z k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.maxRK x z k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
                compileConstraint_int_max_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_ternRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := z) (k := k)
                (i := i) (ir := ir) (n := i2) "int_max" (fun p q => max p q)
                fullInterp_int_max_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | maxKR x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxKR_inv hshape
            rcases (haux ((AuxShape.expand (.maxKR x z k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.maxKR x z k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
                compileConstraint_int_max_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hri ⊢
              exact sat_aux_ternKR (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (r := z) (k := k)
                (i := i) (ir := ir) (n := i2) "int_max" (fun p q => max p q)
                fullInterp_int_max_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hri hsatdc
        | minRRK x y k =>
            -- PLAN C9 remainder: the literal is the RESULT operand
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minRRK_inv hshape
            rcases (haux ((AuxShape.expand (.minRRK x y k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.minRRK x y k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ :=
                compileConstraint_int_min_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hyi ⊢
              exact sat_aux_ternRRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (y := y) (k := k)
                (i := i) (j := j) (n := i2) "int_min" (fun p q => min p q)
                fullInterp_int_min_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hyi hsatdc
        | maxRRK x y k =>
            -- PLAN C9 remainder: the literal is the RESULT operand
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxRRK_inv hshape
            rcases (haux ((AuxShape.expand (.maxRRK x y k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.maxRRK x y k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!) List.mem_cons_self
              obtain ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ :=
                compileConstraint_int_max_inv hcc
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                have hsame : iAUX = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX := hAUXi
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform, hAUXpos] at hsatdc
              rw [hslots] at hnu halt hmem hxi hyi ⊢
              exact sat_aux_ternRRK (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (y := y) (k := k)
                (i := i) (j := j) (n := i2) "int_max" (fun p q => max p q)
                fullInterp_int_max_iff
                hnu halt hmem hslotget hnlt
                (by rw [hnamec])
                hargsc hxi hyi hsatdc
        | minGen2 e1 e2 r =>
            -- PLAN C9 remainder: the two-element array minimum chains
            -- over the element slots themselves (no aux slot)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minGen2_inv hshape
            -- the piece: int_min(e₁, e₂, r) → minSlot i j k
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.minGen2 e1 e2 r)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            obtain ⟨i, j, k, hxi, hyi, hki, hdcform⟩ :=
              compileConstraint_int_min_inv hcc
            rw [hdcform] at hsatdc
            rw [hslots] at hnu halt hmem hxi hyi hki ⊢
            exact holds_array_int_minimum_of_minSlot (m := m)
              (slots := slots0 ++ modelAuxSlots m) (dcs := dcs)
              hnu halt hnamec hargsc hxi hyi hki hsatdc
        | maxGen2 e1 e2 r =>
            -- PLAN C9 remainder: the two-element array maximum chains
            -- over the element slots themselves (no aux slot)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxGen2_inv hshape
            -- the piece: int_max(e₁, e₂, r) → maxSlot i j k
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.maxGen2 e1 e2 r)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            obtain ⟨i, j, k, hxi, hyi, hki, hdcform⟩ :=
              compileConstraint_int_max_inv hcc
            rw [hdcform] at hsatdc
            rw [hslots] at hnu halt hmem hxi hyi hki ⊢
            exact holds_array_int_maximum_of_maxSlot (m := m)
              (slots := slots0 ++ modelAuxSlots m) (dcs := dcs)
              hnu halt hnamec hargsc hxi hyi hki hsatdc
        | xorSlots x y z =>
            -- PLAN C0: the Boolean XOR channel over its four clauses
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_xorSlots_inv hshape
            rw [hslots] at hnu halt hmem ⊢
            -- the position inversions of the clause arrays
            have singlepos : ∀ (w : Ident) (is : List Nat),
                linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    [BasicExpr.ident w] = some is →
                ∃ iw, nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    w.name = some iw ∧ is = [iw] := by
              intro w is h
              cases hw : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  w.name with
              | none => simp only [linIndices, hw] at h; exact absurd h (by simp)
              | some iw =>
                  refine ⟨iw, rfl, ?_⟩
                  simp only [linIndices, hw] at h
                  simpa using h.symm
            have pairpos : ∀ (w1 w2 : Ident) (is : List Nat),
                linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    [BasicExpr.ident w1, BasicExpr.ident w2] = some is →
                ∃ i1 i2, nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    w1.name = some i1 ∧
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    w2.name = some i2 ∧ is = [i1, i2] := by
              intro w1 w2 is h
              cases h1 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  w1.name with
              | none => simp only [linIndices, h1] at h; exact absurd h (by simp)
              | some i1 =>
                  cases h2 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      w2.name with
                  | none => simp only [linIndices, h1, h2] at h; exact absurd h (by simp)
                  | some i2 =>
                      refine ⟨i1, i2, rfl, rfl, ?_⟩
                      simp only [linIndices, h1, h2] at h
                      simpa using h.symm
            -- the four pieces' compiled bool_clause constraints
            obtain ⟨dc1, hdcmem1, hcc1, hsatdc1⟩ :=
              hpieceSat ((AuxShape.expand (.xorSlots x y z)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            obtain ⟨dc2, hdcmem2, hcc2, hsatdc2⟩ :=
              hpieceSat ((AuxShape.expand (.xorSlots x y z)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[1]!)
                (List.mem_cons_of_mem _ List.mem_cons_self)
            obtain ⟨dc3, hdcmem3, hcc3, hsatdc3⟩ :=
              hpieceSat ((AuxShape.expand (.xorSlots x y z)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[2]!)
                (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self))
            obtain ⟨dc4, hdcmem4, hcc4, hsatdc4⟩ :=
              hpieceSat ((AuxShape.expand (.xorSlots x y z)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[3]!)
                (List.mem_cons_of_mem _
                  (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)))
            rw [hslots] at hcc1 hcc2 hcc3 hcc4
            -- the clause positions (the shared argument positions come
            -- from the first clause)
            obtain ⟨ps1, ns1, hps1, hns1, hdcform1⟩ :=
              compileConstraint_bool_clause_inv hcc1
            obtain ⟨i, j, hxi, hyi, hps1'⟩ := pairpos x y ps1 hps1
            obtain ⟨k, hzi, hns1'⟩ := singlepos z ns1 hns1
            rw [hdcform1, hps1', hns1'] at hsatdc1
            obtain ⟨ps2, ns2, hps2, hns2, hdcform2⟩ :=
              compileConstraint_bool_clause_inv hcc2
            have hps2' : ps2 = [] :=
              Option.some.inj (hps2.symm.trans (by simp [linIndices]))
            have hlin2 : linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                [BasicExpr.ident x, BasicExpr.ident y, BasicExpr.ident z]
                = some [i, j, k] := by
              simp only [linIndices, hxi, hyi, hzi]
              rfl
            have hns2' : ns2 = [i, j, k] := Option.some.inj (hns2.symm.trans hlin2)
            rw [hdcform2, hps2', hns2'] at hsatdc2
            obtain ⟨ps3, ns3, hps3, hns3, hdcform3⟩ :=
              compileConstraint_bool_clause_inv hcc3
            have hlin3 : linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                [BasicExpr.ident y, BasicExpr.ident z] = some [j, k] := by
              simp only [linIndices, hyi, hzi]
              rfl
            have hps3' : ps3 = [j, k] := Option.some.inj (hps3.symm.trans hlin3)
            have hlin3b : linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                [BasicExpr.ident x] = some [i] := by
              simp only [linIndices, hxi]
              rfl
            have hns3' : ns3 = [i] := Option.some.inj (hns3.symm.trans hlin3b)
            rw [hdcform3, hps3', hns3'] at hsatdc3
            obtain ⟨ps4, ns4, hps4, hns4, hdcform4⟩ :=
              compileConstraint_bool_clause_inv hcc4
            have hlin4 : linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                [BasicExpr.ident x, BasicExpr.ident z] = some [i, k] := by
              simp only [linIndices, hxi, hzi]
              rfl
            have hps4' : ps4 = [i, k] := Option.some.inj (hps4.symm.trans hlin4)
            have hlin4b : linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                [BasicExpr.ident y] = some [j] := by
              simp only [linIndices, hyi]
              rfl
            have hns4' : ns4 = [j] := Option.some.inj (hns4.symm.trans hlin4b)
            rw [hdcform4, hps4', hns4'] at hsatdc4
            -- the well-formed constraint's bool signature
            obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc'
            have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
                some [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                  BasicParType.bool)),
                 PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                  BasicParType.bool)),
                 PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                  BasicParType.bool))] := by
              rw [show Ident.mk c.name.name = Ident.mk "bool_xor" from by
                rw [hnamec]]
              exact sigEnv_bool_xor hpred
            have hparameq : params =
                [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                  BasicParType.bool)),
                 PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                  BasicParType.bool)),
                 PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                  BasicParType.bool))] := by
              have h1 : m.sigEnv Globals.fullSig c.name = some params := hsig
              rw [show m.sigEnv Globals.fullSig c.name
                  = m.sigEnv Globals.fullSig (Ident.mk c.name.name) from rfl] at h1
              rw [hres] at h1
              exact (Option.some.inj h1).symm
            rw [hparameq] at hfor
            -- the bool-reads master (the three arguments)
            have hboolread : ∀ (w : Ident) (iw : Nat),
                nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst) w.name
                  = some iw → Expr.basic (.ident w) ∈ c.args →
                ∃ q, a[iw]! = Value.bool q := by
              intro w iw hwi hwarg
              exact bool_read_of_checkArg_master_ext
                (compileModel_vars_basic hc) hwf hslots0 hnu
                (fun n2 p hp => by
                  have hspec := (modelAuxSlots_spec hslots0).1 n2 p hp
                  rw [hspec]
                  exact auxName_not_mem)
                hfor
                (by
                  intro pt hpt
                  rcases List.mem_cons.mp hpt with rfl | htl
                  · rfl
                  · rcases List.mem_cons.mp htl with rfl | htl2
                    · rfl
                    · rcases List.mem_cons.mp htl2 with rfl | hnil
                      · rfl
                      · exact absurd hnil (by simp))
                hwarg hwi hmem
            obtain ⟨p, hp⟩ := hboolread x i hxi (by
              rw [hargsc]; exact List.mem_cons_self)
            obtain ⟨q, hq⟩ := hboolread y j hyi (by
              rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self)
            obtain ⟨rb, hr⟩ := hboolread z k hzi (by
              rw [hargsc]
              exact List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ List.mem_cons_self))
            exact sat_aux_xor (m := m) (slots := slots0 ++ modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (y := y) (z := z)
              (i := i) (j := j) (k := k) (p := p) (q := q) (r := rb)
              hnu halt hnamec hargsc hxi hyi hzi hp hq hr
              hsatdc1 hsatdc2 hsatdc3 hsatdc4
        | constElemValL x xs k =>
            -- PLAN C0 element values: the value-literal array_int_element
            -- over an all-literal table; the piece is the same table
            -- over the pinned aux slot
            have hinv := auxShapeOf_constElemValL_inv hshape
            have hnamec : c.name.name = "array_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array (litTab xs),
                Expr.basic (.lit (.int k))] := hinv.2
            -- the pieces' pin info: the aux slot at i2 carries [.int k]
            rcases (haux ((AuxShape.expand (.constElemValL x xs k)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.constElemValL x xs k)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                  List.mem_cons_self
              -- the piece's compile inversion: dc = arrayIntElementSlot
              -- xs i AUXPOS with the two name resolutions
              obtain ⟨i, iAUX, hxi, hAUXi, hdcform⟩ :=
                compileConstraint_constElemValL_inv hcc
              -- the aux position is the extended slots0.length + i2
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos] at hsatdc
              rw [hAUXpos] at hAUXi
              rw [hslots] at hnu halt hmem hxi hAUXi ⊢
              exact sat_aux_constElemValL (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x)
                (aux := Ident.mk (auxName (auxTaken m slots0) i2))
                (xs := xs) (k := k) (i := i) (n := i2)
                hnu halt hmem hslotget hnlt hnamec hargsc hxi hAUXi hsatdc
        | varElemTabLit x y pre k post =>
            -- PLAN C0 element values: the one-literal mixed
            -- array_var_int_element table with a slot value; the
            -- piece is the all-slot table over the pinned aux slot
            have hinv := auxShapeOf_varElemTabLit_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x),
                Expr.array (litSplitTab pre k post),
                Expr.basic (.ident y)] := hinv.2
            -- the pieces' pin info: the aux slot at i2 carries [.int k]
            rcases (haux ((AuxShape.expand (.varElemTabLit x y pre k post)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                hpieceSat ((AuxShape.expand (.varElemTabLit x y pre k post)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                  List.mem_cons_self
              -- the piece's compile inversion
              obtain ⟨is, i, kk, his, hxi, hyi, hdcform⟩ :=
                compileConstraint_varElem_inv hcc
              -- the aux identifier resolves at the extended position
              have hauxres : nameIndex
                  ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  (Ident.mk (auxName (auxTaken m slots0) i2)).name
                  = some (slots0.length + i2) := by
                show nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  (auxName (auxTaken m slots0) i2)
                  = some (slots0.length + i2)
                exact nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  (modelAuxSlots_spec hslots0).1 hslotget
              rw [hdcform] at hsatdc
              rw [hslots] at hxi hyi his
              rw [hslots] at hnu halt hmem ⊢
              exact sat_aux_varElemTabLit (m := m) (slots0 := slots0)
                (auxs := modelAuxSlots m)
                (dcs := dcs) (c := c) (x := x) (y := y)
                (aux := Ident.mk (auxName (auxTaken m slots0) i2))
                (pre := pre) (post := post) (k := k) (i := i) (kk := kk)
                (n := i2) (is := is)
                hnu halt hmem hslotget hnlt hnamec hargsc hxi hyi hauxres
                his hsatdc
        | varElemTabValLit x pre k post k' =>
            -- PLAN C0 element values: the one-literal mixed table with
            -- a literal value; the piece is the all-slot table over
            -- the first pinned aux slot and the value on the second
            have hinv := auxShapeOf_varElemTabValLit_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x),
                Expr.array (litSplitTab pre k post),
                Expr.basic (.lit (.int k'))] := hinv.2
            -- the two pins
            rcases (haux ((AuxShape.expand (.varElemTabValLit x pre k post k')
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.int k := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              rcases (haux ((AuxShape.expand
                (.varElemTabValLit x pre k post k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                (List.mem_cons_self)).2.2.1 with
                hpin2none | ⟨v2, hpin2, hslot2get⟩
              · exact absurd hpin2none (by simp [AuxShape.pin2])
              · have hvk' : v2 = Value.int k' := by
                  have h2 := hpin2
                  rw [AuxShape.pin2] at h2
                  exact (Option.some.inj h2).symm
                subst hvk'
                have hnlt : i2 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslotget).1
                have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslot2get).1
                obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
                  hpieceSat ((AuxShape.expand
                    (.varElemTabValLit x pre k post k')
                    (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                    List.mem_cons_self
                -- the piece's compile inversion
                obtain ⟨is, i, kk, his, hxi, hki, hdcform⟩ :=
                  compileConstraint_varElem_inv hcc
                -- the first aux identifier resolves at i2's position
                have hauxres : nameIndex
                    ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = some (slots0.length + i2) := by
                  show nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    (auxName (auxTaken m slots0) i2)
                    = some (slots0.length + i2)
                  exact nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2)
                    (vs := [Value.int k])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    (modelAuxSlots_spec hslots0).1 hslotget
                -- the second (value) aux identifier resolves at i2+1
                have haux2res : nameIndex
                    ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    (nextAuxIdent (Ident.mk
                      (auxName (auxTaken m slots0) i2))).name
                    = some (slots0.length + (i2 + 1)) := by
                  have hres := nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2 + 1)
                    (vs := [Value.int k'])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    (modelAuxSlots_spec hslots0).1 hslot2get
                  have hname2 : (nextAuxIdent (Ident.mk
                      (auxName (auxTaken m slots0) i2))).name
                      = auxName (auxTaken m slots0) (i2 + 1) :=
                    nextAuxIdent_name (auxTaken m slots0) i2
                  rw [hname2]
                  exact hres
                -- the value's compiled position IS the second aux slot
                have hkk : kk = slots0.length + (i2 + 1) := by
                  rw [hslots] at hki
                  exact Option.some.inj (hki.symm.trans haux2res)
                rw [hdcform] at hsatdc
                rw [hslots] at hxi his
                rw [hslots] at hnu halt hmem ⊢
                exact sat_aux_varElemTabValLit (m := m) (slots0 := slots0)
                  (auxs := modelAuxSlots m)
                  (dcs := dcs) (c := c) (x := x)
                  (aux := Ident.mk (auxName (auxTaken m slots0) i2))
                  (aux2 := nextAuxIdent (Ident.mk
                    (auxName (auxTaken m slots0) i2)))
                  (pre := pre) (post := post) (k := k) (k' := k')
                  (i := i) (kk := kk) (n := i2) (is := is)
                  hnu halt hmem hslotget hnlt hslot2get hnlt2 hnamec hargsc
                  hxi hauxres haux2res hkk his hsatdc
        | varElemTabKs x y tab =>
            -- PLAN C0 element values: the k-literal mixed table with a
            -- slot value; the piece is the all-slot table over the k
            -- pinned aux slots
            have hinv := auxShapeOf_varElemTabKs_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.ident y)] := hinv.2.1
            have hmix : mixedOk tab := mixedOk_of_mixTabOkB hinv.2.2
            -- the pieces' pins: one aux slot per table literal at
            -- i2, i2 + 1, ...
            have hpins := (haux ((AuxShape.expand (.varElemTabKs x y tab)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.2.2
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.varElemTabKs x y tab)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hyi, hdcform⟩ :=
              compileConstraint_varElemTab_inv hcc
            rw [hslots] at hnu halt hmem
            -- the pinned reads of the aux chain
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore a)
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabLitVals tab).length)[j]!
                  = some (.int (tabLitVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads (m := m) (slots0 := slots0)
                (dcs := dcs) (taken := auxTaken m slots0) (n := i2)
                (N := (tabLitVals tab).length)
                (vs := (tabLitVals tab).map Value.int)
                (by intro s hs; exact List.mem_append.mpr (Or.inl hs))
                (fun j p hp => (modelAuxSlots_spec hslots0).1 j p hp)
                hnu halt hmem (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varElemTabKs]
                    exact hi2')
                  rw [pinsK_varElemTabKs] at h2
                  exact h2)
                j hj
              rw [getElem!_map_eq (tabLitVals tab) Value.int hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length = (tabLitVals tab).length :=
              auxChain_length _ _
            rw [hdcform] at hsatdc
            rw [hslots] at hxi hyi his ⊢
            exact sat_aux_varElemTabKs (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (y := y)
              (tab := tab)
              (auxes := auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length)
              (i := i) (kk := kk) (is := is)
              hnu halt hnamec hargsc hxi hyi hlen hmix hauxread his hsatdc
        | varElemTabValKs x tab k' =>
            -- PLAN C0 element values: the k-literal mixed table with a
            -- literal value; the value rides the successor slot
            have hinv := auxShapeOf_varElemTabValKs_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.lit (.int k'))] := hinv.2.1
            have hmix : mixedOk tab := by
              rcases Bool.or_eq_true_iff.mp hinv.2.2 with h | h
              · exact mixedOk_of_mixTabOkB h
              · cases hall : allIdents tab with
                | none => simp [hall] at h
                | some l => exact mixedOk_of_allIdents hall
            have hpins := (haux ((AuxShape.expand (.varElemTabValKs x tab k')
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.2.2
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.varElemTabValKs x tab k')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hki, hdcform⟩ :=
              compileConstraint_varElemTab_inv hcc
            rw [hslots] at hnu halt hmem
            -- the pinned reads of the aux chain (table literals only)
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore a)
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabLitVals tab).length)[j]!
                  = some (.int (tabLitVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads (m := m) (slots0 := slots0)
                (dcs := dcs) (taken := auxTaken m slots0) (n := i2)
                (N := (tabLitVals tab).length)
                (vs := (tabLitVals tab).map Value.int)
                (by intro s hs; exact List.mem_append.mpr (Or.inl hs))
                (fun j p hp => (modelAuxSlots_spec hslots0).1 j p hp)
                hnu halt hmem (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varElemTabValKs]
                    omega)
                  rw [pinsK_varElemTabValKs] at h2
                  rwa [getElem!_append_left (by rw [List.length_map]; exact hi2')] at h2)
                j hj
              rw [getElem!_map_eq (tabLitVals tab) Value.int hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length = (tabLitVals tab).length :=
              auxChain_length _ _
            -- the value slot's resolution and pinned read
            have haux2 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                  (tabLitVals tab).length).name
                = some (slots0.length + (i2 + (tabLitVals tab).length)) := by
              have hname2 : (auxChainLast (Ident.mk
                  (auxName (auxTaken m slots0) i2))
                  (tabLitVals tab).length).name
                  = auxName (auxTaken m slots0)
                      (i2 + (tabLitVals tab).length) := by
                rw [auxChainLast_eq]
              rw [hname2]
              exact nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0)
                (i := i2 + (tabLitVals tab).length)
                (vs := [Value.int k'])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                (modelAuxSlots_spec hslots0).1
                (by
                  have h2 := hpins (tabLitVals tab).length (by
                    rw [pinsK_length_varElemTabValKs]
                    omega)
                  rw [pinsK_varElemTabValKs] at h2
                  rw [getElem!_append_right
                    (by rw [List.length_map]; omega)] at h2
                  have hsub2 : (tabLitVals tab).length
                      - (List.map Value.int (tabLitVals tab)).length = 0 := by
                    rw [List.length_map, Nat.sub_self]
                  rw [hsub2] at h2
                  simpa using h2)
            have haux2read : ((assemble m (slots0 ++ modelAuxSlots m)
                dcs).toStore a)
                (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                  (tabLitVals tab).length) = some (.int k') := by
              rw [toStore_read_model (m := m) hnu halt haux2]
              have hp : (modelAuxSlots m)[i2 + (tabLitVals tab).length]?
                  = some (auxName (auxTaken m slots0)
                      (i2 + (tabLitVals tab).length), [Value.int k']) := by
                have h2 := hpins (tabLitVals tab).length (by
                  rw [pinsK_length_varElemTabValKs]
                  omega)
                rw [pinsK_varElemTabValKs] at h2
                rw [getElem!_append_right
                  (by rw [List.length_map]; omega)] at h2
                have hsub2 : (tabLitVals tab).length
                    - (List.map Value.int (tabLitVals tab)).length = 0 := by
                  rw [List.length_map, Nat.sub_self]
                rw [hsub2] at h2
                simpa using h2
              have hpin : a[slots0.length + (i2 + (tabLitVals tab).length)]?
                  = some (Value.int k') :=
                auxPin_of_mem hmem
                  (List.getElem?_eq_some_iff.mp hp).1 hp
              rw [bang_of_getElem? hpin]
            have hkk : kk = slots0.length + (i2 + (tabLitVals tab).length) := by
              rw [hslots] at hki
              exact Option.some.inj (hki.symm.trans haux2)
            rw [hdcform] at hsatdc
            rw [hslots] at hxi his ⊢
            exact sat_aux_varElemTabValKs (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x)
              (aux2 := auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length)
              (tab := tab)
              (auxes := auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length)
              (k' := k') (i := i) (kk := kk)
              (vpos := slots0.length + (i2 + (tabLitVals tab).length)) (is := is)
              hnu halt hnamec hargsc hxi hlen hmix hauxread haux2 hkk haux2read his
              hsatdc
        | varBoolTabLits x y tab =>
            -- PLAN C0 element values, bool tables: the mixed bool table
            -- with a slot value; the piece is the all-slot table over
            -- the pinned aux slots
            have hinv := auxShapeOf_varBoolTabLits_inv hshape
            have hnamec : c.name.name = "array_var_bool_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.ident y)] := hinv.2.1
            have hmix : mixedOkB tab := mixedOkB_of_boolLitTabOkB hinv.2.2
            have hpins := (haux ((AuxShape.expand (.varBoolTabLits x y tab)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.2.2
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.varBoolTabLits x y tab)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hyi, hdcform⟩ :=
              compileConstraint_varBoolTab_inv hcc
            rw [hslots] at hnu halt hmem
            -- the pinned reads of the aux chain
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore a)
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabBoolVals tab).length)[j]!
                  = some (.bool (tabBoolVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads (m := m) (slots0 := slots0)
                (dcs := dcs) (taken := auxTaken m slots0) (n := i2)
                (N := (tabBoolVals tab).length)
                (vs := (tabBoolVals tab).map Value.bool)
                (by intro w hw; exact List.mem_append.mpr (Or.inl hw))
                (fun j2 p hp => (modelAuxSlots_spec hslots0).1 j2 p hp)
                hnu halt hmem (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varBoolTabLits]
                    exact hi2')
                  rw [pinsK_varBoolTabLits] at h2
                  exact h2)
                j hj
              rw [getElem!_map_eq (tabBoolVals tab) Value.bool hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length = (tabBoolVals tab).length :=
              auxChain_length _ _
            rw [hdcform] at hsatdc
            rw [hslots] at hxi hyi his ⊢
            exact sat_aux_varBoolTabLits (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (y := y)
              (tab := tab)
              (auxes := auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length)
              (i := i) (kk := kk) (is := is)
              hnu halt hnamec hargsc hxi hyi hlen hmix hauxread his hsatdc
        | varBoolTabValLit x tab b' =>
            -- PLAN C0 element values, bool tables: the mixed bool table
            -- with a literal value; the value rides the successor slot
            have hinv := auxShapeOf_varBoolTabValLit_inv hshape
            have hnamec : c.name.name = "array_var_bool_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.lit (.bool b'))] := hinv.2.1
            have hmix : mixedOkB tab := mixedOkB_of_boolTabOkB hinv.2.2
            have hpins := (haux ((AuxShape.expand (.varBoolTabValLit x tab b')
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.2.2
            obtain ⟨dc, hdcmem, hcc, hsatdc⟩ :=
              hpieceSat ((AuxShape.expand (.varBoolTabValLit x tab b')
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hki, hdcform⟩ :=
              compileConstraint_varBoolTab_inv hcc
            rw [hslots] at hnu halt hmem
            -- the pinned reads of the aux chain (table literals only)
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore a)
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabBoolVals tab).length)[j]!
                  = some (.bool (tabBoolVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads (m := m) (slots0 := slots0)
                (dcs := dcs) (taken := auxTaken m slots0) (n := i2)
                (N := (tabBoolVals tab).length)
                (vs := (tabBoolVals tab).map Value.bool)
                (by intro w hw; exact List.mem_append.mpr (Or.inl hw))
                (fun j2 p hp => (modelAuxSlots_spec hslots0).1 j2 p hp)
                hnu halt hmem (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varBoolTabValLit]
                    omega)
                  rw [pinsK_varBoolTabValLit] at h2
                  rwa [getElem!_append_left
                    (by rw [List.length_map]; exact hi2')] at h2)
                j hj
              rw [getElem!_map_eq (tabBoolVals tab) Value.bool hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length = (tabBoolVals tab).length :=
              auxChain_length _ _
            -- the value slot's resolution and pinned read
            have haux2 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                  (tabBoolVals tab).length).name
                = some (slots0.length + (i2 + (tabBoolVals tab).length)) := by
              have hname2 : (auxChainLast (Ident.mk
                  (auxName (auxTaken m slots0) i2))
                  (tabBoolVals tab).length).name
                  = auxName (auxTaken m slots0)
                      (i2 + (tabBoolVals tab).length) := by
                rw [auxChainLast_eq]
              rw [hname2]
              exact nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0)
                (i := i2 + (tabBoolVals tab).length)
                (vs := [Value.bool b'])
                (hsub := by
                  intro w hw
                  exact List.mem_append.mpr (Or.inl hw))
                (modelAuxSlots_spec hslots0).1
                (by
                  have h2 := hpins (tabBoolVals tab).length (by
                    rw [pinsK_length_varBoolTabValLit]
                    omega)
                  rw [pinsK_varBoolTabValLit] at h2
                  rw [getElem!_append_right
                    (by rw [List.length_map]; omega)] at h2
                  have hsub2 : (tabBoolVals tab).length
                      - (List.map Value.bool (tabBoolVals tab)).length = 0 := by
                    rw [List.length_map, Nat.sub_self]
                  rw [hsub2] at h2
                  simpa using h2)
            have haux2read : ((assemble m (slots0 ++ modelAuxSlots m)
                dcs).toStore a)
                (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                  (tabBoolVals tab).length) = some (.bool b') := by
              rw [toStore_read_model (m := m) hnu halt haux2]
              have hp : (modelAuxSlots m)[i2 + (tabBoolVals tab).length]?
                  = some (auxName (auxTaken m slots0)
                      (i2 + (tabBoolVals tab).length), [Value.bool b']) := by
                have h2 := hpins (tabBoolVals tab).length (by
                  rw [pinsK_length_varBoolTabValLit]
                  omega)
                rw [pinsK_varBoolTabValLit] at h2
                rw [getElem!_append_right
                  (by rw [List.length_map]; omega)] at h2
                have hsub2 : (tabBoolVals tab).length
                    - (List.map Value.bool (tabBoolVals tab)).length = 0 := by
                  rw [List.length_map, Nat.sub_self]
                rw [hsub2] at h2
                simpa using h2
              have hpin : a[slots0.length + (i2 + (tabBoolVals tab).length)]?
                  = some (Value.bool b') :=
                auxPin_of_mem hmem
                  (List.getElem?_eq_some_iff.mp hp).1 hp
              rw [bang_of_getElem? hpin]
            have hkk : kk = slots0.length + (i2 + (tabBoolVals tab).length) := by
              rw [hslots] at hki
              exact Option.some.inj (hki.symm.trans haux2)
            rw [hdcform] at hsatdc
            rw [hslots] at hxi his ⊢
            exact sat_aux_varBoolTabValLit (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x)
              (aux2 := auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length)
              (tab := tab)
              (auxes := auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length)
              (b' := b') (i := i) (kk := kk)
              (vpos := slots0.length + (i2 + (tabBoolVals tab).length)) (is := is)
              hnu halt hnamec hargsc hxi hlen hmix hauxread haux2 hkk haux2read his
              hsatdc
        | andTrue x y =>
            -- the args + name inversion: c is bool_and(x, y, true)
            have hargsc : c.args = [.basic (.ident x), .basic (.ident y),
                .basic (.lit (.bool true))] := auxShapeOf_andTrue_args hshape
            have hnamec : c.name.name = "bool_and" :=
              auxShapeOf_andTrue_name hshape
            -- the two pieces' dcs: bool_not(x, false) and
            -- bool_not(y, false), each compiled to constEq (.bool true)
            obtain ⟨dc1, hdcmem1, hcc1, hsatdc1⟩ :=
              hpieceSat ((AuxShape.expand (.andTrue x y)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            obtain ⟨i1, hxi1, hdcform1⟩ :=
              compileConstraint_bool_not_lit_inv hcc1
            obtain ⟨dc2, hdcmem2, hcc2, hsatdc2⟩ :=
              hpieceSat ((AuxShape.expand (.andTrue x y)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[1]!)
                (List.mem_cons_of_mem _ List.mem_cons_self)
            obtain ⟨i2', hyi1, hdcform2⟩ :=
              compileConstraint_bool_not_lit_inv hcc2
            -- the compiled forms: constEq i1 (.bool !false) = constEq
            -- i1 (.bool true), likewise for y
            rw [show (Bool.not false) = true from rfl] at hdcform1 hdcform2
            rw [hdcform1] at hsatdc1
            rw [hdcform2] at hsatdc2
            -- the store reads via the extended slots
            rw [hslots] at hnu halt hmem hxi1 hyi1 ⊢
            exact sat_aux_andTrue (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (y := y)
              (i := i1) (j := i2')
              hnu halt hnamec hargsc hxi1 hyi1 hsatdc1 hsatdc2
        | andFalse x y =>
            -- the args + name inversion: c is bool_and(x, y, false)
            have hargsc : c.args = [.basic (.ident x), .basic (.ident y),
                .basic (.lit (.bool false))] := auxShapeOf_andFalse_args hshape
            have hnamec : c.name.name = "bool_and" :=
              auxShapeOf_andFalse_name hshape
            -- the pieces' pin info: the aux slot at i2 carries
            -- [.bool false]
            rcases (haux ((AuxShape.expand (.andFalse x y)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.bool false := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              -- piece 2: bool_not(AUX, true) → constEq AUXpos false
              obtain ⟨dc2, hdcmem2, hcc2, hsatdc2⟩ :=
                hpieceSat ((AuxShape.expand (.andFalse x y)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[1]!)
                  (List.mem_cons_of_mem _ List.mem_cons_self)
              obtain ⟨iAUX2, hAUXi2, hdcform2⟩ :=
                compileConstraint_bool_not_lit_inv hcc2
              rw [show (Bool.not true) = false from rfl] at hdcform2
              -- the aux position: iAUX2 = slots0.length + i2
              have hAUXpos2 : iAUX2 = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.bool false])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi2
                have hsame : iAUX2 = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX2 := hAUXi2
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform2, hAUXpos2] at hsatdc2
              -- the pin: a[slots0.length + i2]? = some (.bool false)
              have hpinread : a[slots0.length + i2]? = some (Value.bool false) :=
                hsatdc2
              -- piece 1: bool_and(x, y, AUX) — the honest 5-way
              -- inversion of its compile
              obtain ⟨dc1, hdcmem1, hcc1, hsatdc1⟩ :=
                hpieceSat ((AuxShape.expand (.andFalse x y)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                  List.mem_cons_self
              -- the store reads via the extended slots (the outer
              -- goal, the shared premises, and the aux position's
              -- resolution hypothesis)
              rw [hslots] at hnu halt hmem hAUXi2 ⊢
              -- the well-formed constraint's bool signature (the
              -- bool-reads master's premise)
              obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc'
              have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
                  [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool))] := by
                rw [show Ident.mk c.name.name = Ident.mk "bool_and" from by
                  rw [hnamec]]
                exact sigEnv_bool_and hpred
              have hparameq : params =
                  [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool))] := by
                have h1 : m.sigEnv Globals.fullSig c.name = some params := hsig
                rw [show m.sigEnv Globals.fullSig c.name
                    = m.sigEnv Globals.fullSig (Ident.mk c.name.name) from rfl] at h1
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              rw [hparameq] at hfor
              -- the bool-reads master (for the resolved-variable cases)
              have hboolread : ∀ (z : Ident) (iz : Nat),
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst) z.name
                    = some iz → Expr.basic (.ident z) ∈ c.args →
                    ∃ q, a[iz]! = Value.bool q := by
                intro z iz hzi hzarg
                exact bool_read_of_checkArg_master_ext
                  (compileModel_vars_basic hc) hwf hslots0 hnu
                  (fun n2 p hp => by
                    have hspec := (modelAuxSlots_spec hslots0).1 n2 p hp
                    rw [hspec]
                    exact auxName_not_mem)
                  hfor
                  (by
                    intro pt hpt
                    rcases List.mem_cons.mp hpt with rfl | htl
                    · rfl
                    · rcases List.mem_cons.mp htl with rfl | htl2
                      · rfl
                      · rcases List.mem_cons.mp htl2 with rfl | hnil
                        · rfl
                        · exact absurd hnil (by simp))
                  hzarg hzi hmem
              rcases compileConstraint_bool_and3_inv hcc1 with
                ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ |
                ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩ |
                ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩
              · -- the main case: boolAndSlot i j AUX over the
                -- resolved positions and the pinned aux position
                rw [hslots] at hxi hyi hAUXi
                have hAUXpos : iAUX = slots0.length + i2 := by
                  have hsame : iAUX = iAUX2 :=
                    (Option.some.inj (hAUXi.symm.trans hAUXi2))
                  rw [hsame, hAUXpos2]
                rw [hdcform, hAUXpos] at hsatdc1
                exact sat_aux_andFalse (m := m) (slots0 := slots0)
                  (auxs := modelAuxSlots m)
                  (dcs := dcs) (c := c) (x := x) (y := y)
                  (i := i) (j := j) (n := i2)
                  hnu halt hmem hslotget hnlt
                  hnamec hargsc hxi hyi hsatdc1 hsatdc2
              · -- the parameter case: y is a par-bool parameter with
                -- value true; the piece compiled to eqSlot i AUXpos —
                -- x's read is false (the eqSlot + the pin)
                rw [hslots] at hxi hki hynone
                have hkpos : k = slots0.length + i2 := by
                  have hsame : k = iAUX2 :=
                    (Option.some.inj (hki.symm.trans hAUXi2))
                  rw [hsame, hAUXpos2]
                rw [hdcform] at hsatdc1
                obtain ⟨w, z, hw, hz, hne⟩ := hsatdc1
                rw [hkpos, hpinread] at hz
                -- st x = a[i]! = the false pin
                have hxread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) x = some (Value.bool false) := by
                  rw [toStore_read_model hnu halt hxi,
                    bang_of_getElem? hw]
                  exact congrArg some (hne.trans (Option.some.inj hz).symm)
                -- st y = the parameter's declared value (true)
                have hyread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) y = some (Value.bool true) :=
                  toStore_param hynone henvy
                -- the witness values and the interpretation
                refine ⟨[Value.bool false, Value.bool true, Value.bool false],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool false)
                      pure [v1, v2, v3]) = _
                  rw [hxread, hyread]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  rfl
              · -- the parameter case: y is a par-bool parameter with
                -- value false; the piece compiled to constEq AUXpos
                -- false — c holds outright (false = (x && false))
                rw [hslots] at hxi hynone
                have hyread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) y = some (Value.bool false) :=
                  toStore_param hynone henvy
                -- x's bool read (a declared bool variable with a slot)
                obtain ⟨i3, hi3⟩ :=
                  hboolread x i hxi (by
                    rw [hargsc]
                    exact List.mem_cons_self)
                refine ⟨[a[i]!, Value.bool false, Value.bool false],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool false)
                      pure [v1, v2, v3]) = _
                  rw [toStore_read_model hnu halt hxi, hyread]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  show (match [a[i]!, Value.bool false, Value.bool false] with
                    | [Value.bool p, Value.bool q, Value.bool r] =>
                        r = (p && q)
                    | _ => False)
                  rw [hi3]
                  simp [Bool.false_and]
              · -- the parameter case: x is a par-bool parameter with
                -- value true; the piece compiled to eqSlot j AUXpos —
                -- y's read is false (the eqSlot + the pin)
                rw [hslots] at hyi hki hxnone
                have hkpos : k = slots0.length + i2 := by
                  have hsame : k = iAUX2 :=
                    (Option.some.inj (hki.symm.trans hAUXi2))
                  rw [hsame, hAUXpos2]
                rw [hdcform] at hsatdc1
                obtain ⟨w, z, hw, hz, hne⟩ := hsatdc1
                rw [hkpos, hpinread] at hz
                have hyread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) y = some (Value.bool false) := by
                  rw [toStore_read_model hnu halt hyi,
                    bang_of_getElem? hw]
                  exact congrArg some (hne.trans (Option.some.inj hz).symm)
                have hxread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) x = some (Value.bool true) :=
                  toStore_param hxnone henvx
                refine ⟨[Value.bool true, Value.bool false, Value.bool false],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool false)
                      pure [v1, v2, v3]) = _
                  rw [hxread, hyread]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  rfl
              · -- the parameter case: x is a par-bool parameter with
                -- value false; the piece compiled to constEq AUXpos
                -- false — c holds outright (false = (false && y))
                rw [hslots] at hyi hxnone
                have hxread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) x = some (Value.bool false) :=
                  toStore_param hxnone henvx
                obtain ⟨j3, hj3⟩ :=
                  hboolread y j hyi (by
                    rw [hargsc]
                    exact List.mem_cons_of_mem _ List.mem_cons_self)
                refine ⟨[Value.bool false, a[j]!, Value.bool false],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool false)
                      pure [v1, v2, v3]) = _
                  rw [hxread, toStore_read_model hnu halt hyi]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  show (match [Value.bool false, a[j]!, Value.bool false] with
                    | [Value.bool p, Value.bool q, Value.bool r] =>
                        r = (p && q)
                    | _ => False)
                  rw [hj3]
                  simp [Bool.false_and]
        | orTrue x y =>
            -- the args + name inversion: c is bool_or(x, y, true)
            have hargsc : c.args = [.basic (.ident x), .basic (.ident y),
                .basic (.lit (.bool true))] := auxShapeOf_orTrue_args hshape
            have hnamec : c.name.name = "bool_or" :=
              auxShapeOf_orTrue_name hshape
            -- the pieces' pin info: the aux slot at i2 carries
            -- [.bool true]
            rcases (haux ((AuxShape.expand (.orTrue x y)
              (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
              (List.mem_cons_self)).2.1 with
              hpinnone | ⟨v, hpin, hslotget⟩
            · exact absurd hpinnone (by simp [AuxShape.pin])
            · have hvk : v = Value.bool true := by
                have h2 := hpin
                rw [AuxShape.pin] at h2
                exact (Option.some.inj h2).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              -- piece 2: bool_not(AUX, false) → constEq AUXpos true
              obtain ⟨dc2, hdcmem2, hcc2, hsatdc2⟩ :=
                hpieceSat ((AuxShape.expand (.orTrue x y)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[1]!)
                  (List.mem_cons_of_mem _ List.mem_cons_self)
              obtain ⟨iAUX2, hAUXi2, hdcform2⟩ :=
                compileConstraint_bool_not_lit_inv hcc2
              rw [show (Bool.not false) = true from rfl] at hdcform2
              -- the aux position: iAUX2 = slots0.length + i2
              have hAUXpos2 : iAUX2 = slots0.length + i2 := by
                have hnames : (slots0 ++ modelAuxSlots m).map Prod.fst
                    = slots.map Prod.fst := by rw [hslots]
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.bool true])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                rw [hnames] at hres
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi2
                have hsame : iAUX2 = slots0.length + i2 := by
                  have h1 : nameIndex (List.map Prod.fst slots)
                      (auxName (auxTaken m slots0) i2) = some iAUX2 := hAUXi2
                  rw [hres] at h1
                  exact (Option.some.inj h1).symm
                exact hsame
              rw [hdcform2, hAUXpos2] at hsatdc2
              -- the pin: a[slots0.length + i2]? = some (.bool true)
              have hpinread : a[slots0.length + i2]? = some (Value.bool true) :=
                hsatdc2
              -- piece 1: bool_or(x, y, AUX) — the honest 5-way
              -- inversion of its compile
              obtain ⟨dc1, hdcmem1, hcc1, hsatdc1⟩ :=
                hpieceSat ((AuxShape.expand (.orTrue x y)
                  (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                  List.mem_cons_self
              -- the store reads via the extended slots (the outer
              -- goal, the shared premises, and the aux position's
              -- resolution hypothesis)
              rw [hslots] at hnu halt hmem hAUXi2 ⊢
              -- the well-formed constraint's bool signature (the
              -- bool-reads master's premise)
              obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc'
              have hres : m.sigEnv Globals.fullSig (Ident.mk c.name.name) =
                  [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool))] := by
                rw [show Ident.mk c.name.name = Ident.mk "bool_or" from by
                  rw [hnamec]]
                exact sigEnv_bool_or hpred
              have hparameq : params =
                  [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool)),
                   PredParamType.basic (BasicPredParamType.var (BasicVarType.par
                    BasicParType.bool))] := by
                have h1 : m.sigEnv Globals.fullSig c.name = some params := hsig
                rw [show m.sigEnv Globals.fullSig c.name
                    = m.sigEnv Globals.fullSig (Ident.mk c.name.name) from rfl] at h1
                rw [hres] at h1
                exact (Option.some.inj h1).symm
              rw [hparameq] at hfor
              -- the bool-reads master (for the resolved-variable cases)
              have hboolread : ∀ (z : Ident) (iz : Nat),
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst) z.name
                    = some iz → Expr.basic (.ident z) ∈ c.args →
                    ∃ q, a[iz]! = Value.bool q := by
                intro z iz hzi hzarg
                exact bool_read_of_checkArg_master_ext
                  (compileModel_vars_basic hc) hwf hslots0 hnu
                  (fun n2 p hp => by
                    have hspec := (modelAuxSlots_spec hslots0).1 n2 p hp
                    rw [hspec]
                    exact auxName_not_mem)
                  hfor
                  (by
                    intro pt hpt
                    rcases List.mem_cons.mp hpt with rfl | htl
                    · rfl
                    · rcases List.mem_cons.mp htl with rfl | htl2
                      · rfl
                      · rcases List.mem_cons.mp htl2 with rfl | hnil
                        · rfl
                        · exact absurd hnil (by simp))
                  hzarg hzi hmem
              rcases compileConstraint_bool_or3_inv hcc1 with
                ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ |
                ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩ |
                ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩
              · -- the main case: boolOrSlot i j AUX over the
                -- resolved positions and the pinned aux position
                rw [hslots] at hxi hyi hAUXi
                have hAUXpos : iAUX = slots0.length + i2 := by
                  have hsame : iAUX = iAUX2 :=
                    (Option.some.inj (hAUXi.symm.trans hAUXi2))
                  rw [hsame, hAUXpos2]
                rw [hdcform, hAUXpos] at hsatdc1
                exact sat_aux_orTrue (m := m) (slots0 := slots0)
                  (auxs := modelAuxSlots m)
                  (dcs := dcs) (c := c) (x := x) (y := y)
                  (i := i) (j := j) (n := i2)
                  hnu halt hmem hslotget hnlt
                  hnamec hargsc hxi hyi hsatdc1 hsatdc2
              · -- the parameter case: y is a par-bool parameter with
                -- value true; the piece compiled to constEq AUXpos
                -- true — c holds outright (true = (x || true))
                rw [hslots] at hxi hynone
                have hyread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) y = some (Value.bool true) :=
                  toStore_param hynone henvy
                obtain ⟨i3, hi3⟩ :=
                  hboolread x i hxi (by
                    rw [hargsc]
                    exact List.mem_cons_self)
                refine ⟨[a[i]!, Value.bool true, Value.bool true],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool true)
                      pure [v1, v2, v3]) = _
                  rw [toStore_read_model hnu halt hxi, hyread]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  show (match [a[i]!, Value.bool true, Value.bool true] with
                    | [Value.bool p, Value.bool q, Value.bool r] =>
                        r = (p || q)
                    | _ => False)
                  rw [hi3]
                  simp [Bool.true_or]
              · -- the parameter case: y is a par-bool parameter with
                -- value false; the piece compiled to eqSlot i AUXpos —
                -- x's read is true (the eqSlot + the pin)
                rw [hslots] at hxi hki hynone
                have hkpos : k = slots0.length + i2 := by
                  have hsame : k = iAUX2 :=
                    (Option.some.inj (hki.symm.trans hAUXi2))
                  rw [hsame, hAUXpos2]
                rw [hdcform] at hsatdc1
                obtain ⟨w, z, hw, hz, hne⟩ := hsatdc1
                rw [hkpos, hpinread] at hz
                have hxread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) x = some (Value.bool true) := by
                  rw [toStore_read_model hnu halt hxi,
                    bang_of_getElem? hw]
                  exact congrArg some (hne.trans (Option.some.inj hz).symm)
                have hyread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) y = some (Value.bool false) :=
                  toStore_param hynone henvy
                refine ⟨[Value.bool true, Value.bool false, Value.bool true],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool true)
                      pure [v1, v2, v3]) = _
                  rw [hxread, hyread]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  rfl
              · -- the parameter case: x is a par-bool parameter with
                -- value true; the piece compiled to constEq AUXpos
                -- true — c holds outright (true = (true || y))
                rw [hslots] at hyi hxnone
                have hxread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) x = some (Value.bool true) :=
                  toStore_param hxnone henvx
                obtain ⟨j3, hj3⟩ :=
                  hboolread y j hyi (by
                    rw [hargsc]
                    exact List.mem_cons_of_mem _ List.mem_cons_self)
                refine ⟨[Value.bool true, a[j]!, Value.bool true],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool true)
                      pure [v1, v2, v3]) = _
                  rw [hxread, toStore_read_model hnu halt hyi]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  show (match [Value.bool true, a[j]!, Value.bool true] with
                    | [Value.bool p, Value.bool q, Value.bool r] =>
                        r = (p || q)
                    | _ => False)
                  rw [hj3]
                  simp [Bool.true_or]
              · -- the parameter case: x is a par-bool parameter with
                -- value false; the piece compiled to eqSlot j AUXpos —
                -- y's read is true (the eqSlot + the pin)
                rw [hslots] at hyi hki hxnone
                have hkpos : k = slots0.length + i2 := by
                  have hsame : k = iAUX2 :=
                    (Option.some.inj (hki.symm.trans hAUXi2))
                  rw [hsame, hAUXpos2]
                rw [hdcform] at hsatdc1
                obtain ⟨w, z, hw, hz, hne⟩ := hsatdc1
                rw [hkpos, hpinread] at hz
                have hyread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) y = some (Value.bool true) := by
                  rw [toStore_read_model hnu halt hyi,
                    bang_of_getElem? hw]
                  exact congrArg some (hne.trans (Option.some.inj hz).symm)
                have hxread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore a) x = some (Value.bool false) :=
                  toStore_param hxnone henvx
                refine ⟨[Value.bool false, Value.bool true, Value.bool true],
                  ?_, ?_⟩
                · rw [hargsc]
                  show (do
                      let v1 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a x
                      let v2 ← (assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore a y
                      let v3 ← pure (Value.bool true)
                      pure [v1, v2, v3]) = _
                  rw [hxread, hyread]
                  rfl
                · rw [ident_eq_of_name hnamec, fullInterp_std (by decide)]
                  rfl
        | orFalse x y =>
            -- the args + name inversion: c is bool_or(x, y, false)
            have hargsc : c.args = [.basic (.ident x), .basic (.ident y),
                .basic (.lit (.bool false))] := auxShapeOf_orFalse_args hshape
            have hnamec : c.name.name = "bool_or" :=
              auxShapeOf_orFalse_name hshape
            -- the two pieces' dcs: bool_not(x, true) and
            -- bool_not(y, true), each compiled to constEq (.bool false)
            obtain ⟨dc1, hdcmem1, hcc1, hsatdc1⟩ :=
              hpieceSat ((AuxShape.expand (.orFalse x y)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[0]!)
                List.mem_cons_self
            obtain ⟨i1, hxi1, hdcform1⟩ :=
              compileConstraint_bool_not_lit_inv hcc1
            obtain ⟨dc2, hdcmem2, hcc2, hsatdc2⟩ :=
              hpieceSat ((AuxShape.expand (.orFalse x y)
                (Ident.mk (auxName (auxTaken m slots0) i2)))[1]!)
                (List.mem_cons_of_mem _ List.mem_cons_self)
            obtain ⟨i2', hyi1, hdcform2⟩ :=
              compileConstraint_bool_not_lit_inv hcc2
            -- the compiled forms: constEq i1 (.bool !true) = constEq
            -- i1 (.bool false), likewise for y
            rw [show (Bool.not true) = false from rfl] at hdcform1 hdcform2
            rw [hdcform1] at hsatdc1
            rw [hdcform2] at hsatdc2
            -- the store reads via the extended slots
            rw [hslots] at hnu halt hmem hxi1 hyi1 ⊢
            exact sat_aux_orFalse (m := m) (slots0 := slots0)
              (auxs := modelAuxSlots m)
              (dcs := dcs) (c := c) (x := x) (y := y)
              (i := i1) (j := i2')
              hnu halt hnamec hargsc hxi1 hyi1 hsatdc1 hsatdc2
  -- the variables half: the model slots' reads (the aux slots are
  -- appended beyond the model variables, which read through the
  -- model positions — the original argument transfers)
  have hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, ((assemble m slots dcs).toStore a) n =
          some v ∧ ty.contains v
      | .array _ _ _ _ => False := by
    intro d hd
    obtain ⟨ty, n, anns, hshape⟩ :=
      compileModel_vars_basic hc d hd
    subst hshape
    -- the model-slot read bridge: the extended assembled store reads
    -- n at its model position (the prefix agreement with the
    -- model-only assembly, where decl_var_basic_holds applies)
    have hvarhold : ∃ v, ((assemble m slots dcs).toStore
        a) n = some v ∧ ty.contains v := by
      -- n's model slot position
      obtain ⟨i4, hi4⟩ := nameIndex_of_basic_var hwf hslots0 ty n anns hd
      -- the extended read: toStore_read via the extended position
      have hilt : i4 < slots.length := by
        have hlt4 : i4 < (slots0.map Prod.fst).length :=
          (nameIndex_some (slots0.map Prod.fst) n.name i4 hi4).1
        rw [hslots]
        have hlen4 : ((slots0 ++ modelAuxSlots m).map Prod.fst).length
            = slots0.length + (modelAuxSlots m).length := by
          have hmap : (slots0 ++ modelAuxSlots m).map Prod.fst
              = slots0.map Prod.fst ++ (modelAuxSlots m).map Prod.fst :=
            List.map_append
          rw [hmap, List.length_append, List.length_map, List.length_map]
        have hlen5 : (slots0.map Prod.fst).length = slots0.length := by
          rw [List.length_map]
        have hlen6 : (slots0 ++ modelAuxSlots m).length
            = slots0.length + (modelAuxSlots m).length :=
          (List.length_append ..)
        omega
      have hstore : ((assemble m slots dcs).toStore a) n
          = some a[i4]! := by
        show (match nameIndex (slots.map Prod.fst) n.name with
          | some i => a[i]?
          | none => parEnv m n) = _
        have hext : nameIndex (slots.map Prod.fst) n.name = some i4 := by
          rw [hslots]
          exact nameIndex_ext_eq_model hi4
        rw [hext]
        show (a[i4]?) = _
        rw [getElem_as_some (by rw [halt]; exact hilt)]
      -- the model-only assembly's read-and-containment (decl_var_
      -- basic_holds over the PREFIX assignment a.take slots0.length —
      -- whose reads agree with a's at model positions)
      have hmodelhold : ∃ v, ((assemble m slots0 dcs).toStore
          a) n = some v ∧ ty.contains v := by
        -- the take's membership in the MODEL domains' candidate space
        -- (the prefix restriction of the extended membership)
        have hlen0 : slots.length = slots0.length
            + (modelAuxSlots m).length := by
          rw [hslots, List.length_append]
        have halt0 : a.length = slots0.length
            + (modelAuxSlots m).length := by
          rw [halt, hlen0]
        have htake : a.take slots0.length ∈ allAssigns
            (slots0.map Prod.snd) := by
          apply fits_mem_allAssigns
          refine ⟨?_, ?_⟩
          · -- the length: a.take slots0.length has slots0.length
            -- entries (the extended length dominates)
            rw [List.length_take, List.length_map]
            omega
          · -- the reads: a.take's read = a's read at model
            -- positions; the domain is the model slot's own
            intro slot value hval
            by_cases hslt : slot < slots0.length
            · -- a model position: the take's read is a's read
              have hread : (a.take slots0.length)[slot]? = a[slot]? := by
                rw [show (a.take slots0.length)[slot]?
                  = if slot < slots0.length then a[slot]? else none from
                  List.getElem?_take]
                rw [if_pos hslt]
              rw [hread] at hval
              -- the extended membership: value is in the EXTENDED
              -- domain at slot
              have hfit := mem_allAssigns_fits (slots.map Prod.snd) a
                hmem slot value hval
              -- the extended domain at a model position is the
              -- model slot's own domain (the append's first half)
              rw [hslots] at hfit
              rw [getD_map_snd_append_first hslt] at hfit
              simp only [DomainLike.empty_list]
              rw [getD_map_snd hslt]
              exact hfit
            · -- beyond the take's length: the read is none
              have hnone : (a.take slots0.length)[slot]? = none := by
                rw [show (a.take slots0.length)[slot]?
                  = if slot < slots0.length then a[slot]? else none from
                  List.getElem?_take]
                rw [if_neg hslt]
              rw [hnone] at hval
              cases hval
        obtain ⟨v, hvread, hvcont⟩ :=
          decl_var_basic_holds (a := a.take slots0.length)
            (slots := slots0) (dcs := dcs) hwf hd hslots0 htake
        -- the take-based store's read at n equals the full a's read
        -- (n's model position i4 < slots0.length; the take's read
        -- is a's read there)
        have hreadtake : ((assemble m slots0 dcs).toStore
            (a.take slots0.length)) n = ((assemble m slots0 dcs).toStore
            a) n := by
          show (match nameIndex (slots0.map Prod.fst) n.name with
            | some i => (a.take slots0.length)[i]?
            | none => parEnv m n) =
            (match nameIndex (slots0.map Prod.fst) n.name with
            | some i => a[i]?
            | none => parEnv m n)
          rw [hi4]
          show ((a.take slots0.length)[i4]?) = (a[i4]?)
          rw [show (a.take slots0.length)[i4]?
            = if i4 < slots0.length then a[i4]? else none from
            List.getElem?_take]
          rw [if_pos (by
            have hlt4 : i4 < (slots0.map Prod.fst).length :=
              (nameIndex_some (slots0.map Prod.fst) n.name i4 hi4).1
            rw [List.length_map] at hlt4
            exact hlt4)]
        rw [← hreadtake]
        exact ⟨v, hvread, hvcont⟩
      obtain ⟨v, hvread, hvcont⟩ := hmodelhold
      -- the two stores agree at n (the prefix agreement)
      have hagree : ((assemble m slots0 dcs).toStore a) n
          = ((assemble m slots dcs).toStore a) n := by
        have hext : nameIndex (slots.map Prod.fst) n.name = some i4 := by
          rw [hslots]
          exact nameIndex_ext_eq_model hi4
        show (match nameIndex (slots0.map Prod.fst) n.name with
          | some i => a[i]?
          | none => parEnv m n) = _
        have hmodel : nameIndex (slots0.map Prod.fst) n.name = some i4 := hi4
        rw [hmodel]
        show (match some i4 with
          | some i => a[i]?
          | none => parEnv m n) =
          (match nameIndex (slots.map Prod.fst) n.name with
          | some i => a[i]?
          | none => parEnv m n)
        rw [hext]
      rw [← hagree]
      exact ⟨v, hvread, hvcont⟩
    obtain ⟨v, hvread, hvcont⟩ := hvarhold
    exact ⟨v, hvread, hvcont⟩
  -- transport both halves to problem.toStore
  have hst : ∀ x, ((assemble m slots dcs).toStore a) x =
      (problem.toStore a) x := fun x => (hstore x).symm
  refine ⟨fun c hc' => Holds_ext hst (hcons c hc'), ?_⟩
  intro d hd
  revert hd
  cases d with
  | basic ty n anns opt =>
      intro hd
      obtain ⟨v, hv, hc'⟩ := hvars (.basic ty n anns opt) hd
      exact ⟨v, hst n ▸ hv, hc'⟩
  | array ty n anns elems =>
      intro hd
      exact absurd hd (by
        intro hmem2
        obtain ⟨_, _, _, hshape⟩ :=
          compileModel_vars_basic hc _ hmem2
        cases hshape)

/-- The E-generalized `int_le(x, E)` inversion. -/
theorem holds_int_le_hi_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_le")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ p ≤ k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  rw [hred1, hE] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [vx, .int k] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_le") [vx, .int k] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_le" ∈ globalsNames)] at h1
      have hmatch : (match [vx, .int k] with
        | [Value.int a, Value.int b] => a ≤ b
        | _ => False) := h1
      cases vx with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

/-- The E-generalized `int_le(E, y)` inversion. -/
theorem holds_int_le_lo_E_inv {store : Store} {c : ConstraintItem}
    {y : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_le")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k ≤ p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store E)
      (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  rw [hred2] at hchain
  cases hsy : store y with
  | none => rw [hsy] at hchain; simp at hchain
  | some vy =>
      rw [hsy] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [.int k, vy] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_le") [.int k, vy] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_le" ∈ globalsNames)] at h1
      have hmatch : (match [.int k, vy] with
        | [Value.int a, Value.int b] => a ≤ b
        | _ => False) := h1
      cases vy with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

/-- The E-generalized `int_lt(x, E)` inversion. -/
theorem holds_int_lt_hi_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_lt")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ p < k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  rw [hred1, hE] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [vx, .int k] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_lt") [vx, .int k] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_lt" ∈ globalsNames)] at h1
      have hmatch : (match [vx, .int k] with
        | [Value.int a, Value.int b] => a < b
        | _ => False) := h1
      cases vx with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

/-- The E-generalized `int_lt(E, y)` inversion. -/
theorem holds_int_lt_lo_E_inv {store : Store} {c : ConstraintItem}
    {y : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_lt")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k < p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store E)
      (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  rw [hred2] at hchain
  cases hsy : store y with
  | none => rw [hsy] at hchain; simp at hchain
  | some vy =>
      rw [hsy] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [.int k, vy] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_lt") [.int k, vy] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_lt" ∈ globalsNames)] at h1
      have hmatch : (match [.int k, vy] with
        | [Value.int a, Value.int b] => a < b
        | _ => False) := h1
      cases vy with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

/-- The E-generalized `int_gt(x, E)` inversion. -/
theorem holds_int_gt_hi_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_gt")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ p > k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  rw [hred1, hE] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [vx, .int k] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_gt") [vx, .int k] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_gt" ∈ globalsNames)] at h1
      have hmatch : (match [vx, .int k] with
        | [Value.int a, Value.int b] => a > b
        | _ => False) := h1
      cases vx with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

/-- The E-generalized `int_gt(E, y)` inversion. -/
theorem holds_int_gt_lo_E_inv {store : Store} {c : ConstraintItem}
    {y : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_gt")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k > p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store E)
      (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  rw [hred2] at hchain
  cases hsy : store y with
  | none => rw [hsy] at hchain; simp at hchain
  | some vy =>
      rw [hsy] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [.int k, vy] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_gt") [.int k, vy] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_gt" ∈ globalsNames)] at h1
      have hmatch : (match [.int k, vy] with
        | [Value.int a, Value.int b] => a > b
        | _ => False) := h1
      cases vy with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

/-- The E-generalized `int_ge(x, E)` inversion. -/
theorem holds_int_ge_hi_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_ge")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ p ≥ k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  rw [hred1, hE] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [vx, .int k] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_ge") [vx, .int k] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_ge" ∈ globalsNames)] at h1
      have hmatch : (match [vx, .int k] with
        | [Value.int a, Value.int b] => a ≥ b
        | _ => False) := h1
      cases vx with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)

/-- The E-generalized `int_ge(E, y)` inversion. -/
theorem holds_int_ge_lo_E_inv {store : Store} {c : ConstraintItem}
    {y : Ident} {E : Expr} {k : Int}
    (hname : c.name.name = "int_ge")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hE : Expr.eval store E = some (.int k))
    (h : c.Holds fullInterp store) :
    ∃ p, store y = some (.int p) ∧ k ≥ p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hchain : Option.bind (Expr.eval store E)
      (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  rw [hred2] at hchain
  cases hsy : store y with
  | none => rw [hsy] at hchain; simp at hchain
  | some vy =>
      rw [hsy] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [.int k, vy] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "int_ge") [.int k, vy] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "int_ge" ∈ globalsNames)] at h1
      have hmatch : (match [.int k, vy] with
        | [Value.int a, Value.int b] => a ≥ b
        | _ => False) := h1
      cases vy with
      | int p => exact ⟨p, rfl, by simpa using hmatch⟩
      | bool w => exact absurd hmatch (by simp)
      | setOfInt w => exact absurd hmatch (by simp)
      | array w => exact absurd hmatch (by simp)


/-- A bang read equal to `.int p` from a `some (.int p)` read. -/
theorem int_of_some_read {a : List Value} {i : Nat} {p : Int}
    (h : some a[i]! = some (Value.int p)) : a[i]! = Value.int p := by
  cases hai : a[i]! with
  | int v =>
      rw [hai] at h
      have hiv : some (Value.int v) = some (Value.int p) := h
      have hvv : Value.int v = Value.int p := (Option.some.inj hiv)
      have hvp : v = p := by injection hvv
      subst hvp
      rfl
  | bool w =>
      rw [hai] at h
      exact absurd h (by simp)
  | setOfInt w =>
      rw [hai] at h
      exact absurd h (by simp)
  | array w =>
      rw [hai] at h
      exact absurd h (by simp)

/-- The `?`-read of an int-valued bang read (in bounds). -/
theorem getElem_int_of_bang {a : List Value} {i : Nat} {p : Int}
    (hlt : i < a.length) (h : a[i]! = Value.int p) :
    a[i]? = some (Value.int p) := by
  rw [← h]
  exact getElem_as_some hlt



/-- The identifiers appearing in a basic expression. -/
def BasicExpr.idents : BasicExpr → List Ident
  | .ident x => [x]
  | _ => []

/-- The identifiers appearing in an expression. -/
def Expr.idents : Expr → List Ident
  | .basic b => BasicExpr.idents b
  | .array es => es.flatMap BasicExpr.idents

/-- flatMap membership, head form. -/
theorem flatMap_cons_mem {b : BasicExpr} {rest : List BasicExpr}
    {x : Ident} (hx : x ∈ BasicExpr.idents b) :
    x ∈ (b :: rest).flatMap BasicExpr.idents := by
  rw [List.flatMap_cons]
  exact List.mem_append_left _ hx

/-- flatMap membership, tail form. -/
theorem flatMap_cons_mem' {b : BasicExpr} {rest : List BasicExpr}
    {x : Ident} (hx : x ∈ rest.flatMap BasicExpr.idents) :
    x ∈ (b :: rest).flatMap BasicExpr.idents := by
  rw [List.flatMap_cons]
  exact List.mem_append_right _ hx

/-- An identifier entry of an array table is among the table's idents. -/
theorem mem_flatMap_idents_of_mem {tab : ArrayLiteral} {x : Ident}
    (h : (.ident x : BasicExpr) ∈ tab) : x ∈ tab.flatMap BasicExpr.idents :=
  List.mem_flatMap.mpr ⟨BasicExpr.ident x, h, List.mem_cons_self⟩

/-- The identifier-image list's flatMap of `idents` is the list itself. -/
theorem flatMap_idents_map (l : List Ident) :
    (l.map (fun x => BasicExpr.ident x)).flatMap BasicExpr.idents = l := by
  induction l with
  | nil => rfl
  | cons x rest ih =>
      simp only [List.map_cons, List.flatMap_cons, ih, BasicExpr.idents,
        List.singleton_append]

/-- A mixed table's idents are exactly its slot names (PLAN C0 element
    values: the coverage direction's membership bridge). -/
theorem flatMap_idents_litSplitTab (pre post : List Ident) (k : Int) :
    (litSplitTab pre k post).flatMap BasicExpr.idents = pre ++ post := by
  rw [litSplitTab, List.flatMap_append, List.flatMap_append,
    flatMap_idents_map, flatMap_idents_map]
  rw [show List.flatMap BasicExpr.idents
      [BasicExpr.lit (BasicLiteral.int k)] = [] from rfl]
  rw [List.append_nil]

/-- `Holds` transfers between stores agreeing on the identifiers
    appearing in the constraint's arguments. -/
theorem Holds_ext_args {store1 store2 : Store} {c : ConstraintItem}
    (h : ∀ x, x ∈ (c.args.flatMap Expr.idents) → store1 x = store2 x)
    (hh : c.Holds fullInterp store1) :
    c.Holds fullInterp store2 := by
  obtain ⟨args, hmap, hinterp⟩ := hh
  refine ⟨args, ?_, hinterp⟩
  -- per-element agreement, by induction over basic-expression lists
  have hbelist : ∀ (es : List BasicExpr),
      (∀ x, x ∈ es.flatMap BasicExpr.idents → store1 x = store2 x) →
      es.mapM (BasicExpr.eval store1) = es.mapM (BasicExpr.eval store2) := by
    intro es
    induction es with
    | nil => intro _; rfl
    | cons b rest ih =>
        intro hall
        have hb : BasicExpr.eval store1 b = BasicExpr.eval store2 b := by
          cases b with
          | lit l => rfl
          | ident x =>
              show store1 x = store2 x
              exact hall x (flatMap_cons_mem (b := .ident x) (rest := rest)
                List.mem_cons_self)
        rw [List.mapM_cons, List.mapM_cons, hb,
          ih (fun x hx => hall x (flatMap_cons_mem' (b := b) (rest := rest) hx))]
  -- per-expression agreement
  have haeval : ∀ (e : Expr), (∀ x, x ∈ Expr.idents e →
      store1 x = store2 x) →
      Expr.eval store1 e = Expr.eval store2 e := by
    intro e hid
    cases e with
    | basic b =>
        cases b with
        | lit l => rfl
        | ident x =>
            show store1 x = store2 x
            exact hid x (by
              show x ∈ BasicExpr.idents (.ident x)
              exact List.mem_cons_self)
    | array es =>
        show (es.mapM (BasicExpr.eval store1)).map Value.array =
          (es.mapM (BasicExpr.eval store2)).map Value.array
        rw [hbelist es (fun x hx => hid x hx)]
  -- the args' mapM agreement, by induction over the args
  have hmain : ∀ (l : List Expr) (hl : ∀ x,
      x ∈ l.flatMap Expr.idents → store1 x = store2 x),
      l.mapM (Expr.eval store1) = l.mapM (Expr.eval store2) := by
    intro l
    induction l with
    | nil => intro _; rfl
    | cons e rest ih =>
        intro hl
        rw [List.mapM_cons, List.mapM_cons]
        rw [haeval e (fun x hx => hl x (by
          rw [List.flatMap_cons]
          exact List.mem_append_left _ hx))]
        rw [ih (fun x hx => hl x (by
          rw [List.flatMap_cons]
          exact List.mem_append_right _ hx))]
  rw [hmain c.args h] at hmap
  exact hmap



/-- Coverage inversion: `bool_not(x, E)` holding with E evaluating to
    `.bool w` forces the store's read at x to be the negation. -/
theorem holds_bool_not_hi_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {E : Expr} {w : Bool}
    (hname : c.name.name = "bool_not")
    (hargs : c.args = [Expr.basic (.ident x), E])
    (hE : Expr.eval store E = some (.bool w))
    (h : c.Holds fullInterp store) :
    store x = some (.bool (!w)) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  rw [hred1] at hmap
  have hchain : Option.bind (store x)
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [vx, .bool w] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "bool_not") [vx, .bool w] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "bool_not" ∈ globalsNames)] at h1
      have hmatch : (match [vx, .bool w] with
        | [Value.bool a, Value.bool b] => b = !a
        | _ => False) := h1
      cases vx with
      | bool p =>
          have hnp : Value.bool w = Value.bool (!p) := by simpa using hmatch
          have hpw : w = !p := by injection hnp
          rw [show Value.bool p = Value.bool (!w) from by
            rw [hpw]; simp [Bool.not_not]]
      | int v => exact absurd hmatch (by simp)
      | setOfInt v => exact absurd hmatch (by simp)
      | array v => exact absurd hmatch (by simp)

/-- Coverage inversion: `bool_not(E, y)` holding with E evaluating to
    `.bool w` forces the store's read at y to be the negation. -/
theorem holds_bool_not_lo_E_inv {store : Store} {c : ConstraintItem}
    {y : Ident} {E : Expr} {w : Bool}
    (hname : c.name.name = "bool_not")
    (hargs : c.args = [E, Expr.basic (.ident y)])
    (hE : Expr.eval store E = some (.bool w))
    (h : c.Holds fullInterp store) :
    store y = some (.bool (!w)) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  rw [hred2] at hmap
  have hchain : Option.bind (Expr.eval store E)
      (fun v1 => Option.bind (store y)
        (fun v2 => some [v1, v2])) = some args := by
    simpa [Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  cases hsy : store y with
  | none => rw [hsy] at hchain; simp at hchain
  | some vy =>
      rw [hsy] at hchain
      simp only [Option.bind_some] at hchain
      have hargsv : args = [.bool w, vy] := by simpa using hchain.symm
      subst hargsv
      have h1 : fullInterp (Ident.mk "bool_not") [.bool w, vy] :=
        interp_of_hname hname hinterp
      rw [fullInterp_std (by decide : ¬ "bool_not" ∈ globalsNames)] at h1
      have hmatch : (match [.bool w, vy] with
        | [Value.bool a, Value.bool b] => b = !a
        | _ => False) := h1
      cases vy with
      | bool q =>
          have hnq : Value.bool q = Value.bool (!w) := by simpa using hmatch
          rw [hnq]
      | int v => exact absurd hmatch (by simp)
      | setOfInt v => exact absurd hmatch (by simp)
      | array v => exact absurd hmatch (by simp)

/-- Coverage inversion: `bool_and(x, E, z)` holding with E evaluating
    to `.bool b` forces the reads at x and z to be Booleans with
    `r = (p && b)`. -/
theorem holds_bool_and_hi_E_inv {store : Store} {c : ConstraintItem}
    {x z : Ident} {E : Expr} {b : Bool}
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [Expr.basic (.ident x), E, Expr.basic (.ident z)])
    (hE : Expr.eval store E = some (.bool b))
    (h : c.Holds fullInterp store) :
    ∃ p r, store x = some (.bool p) ∧ store z = some (.bool r) ∧
      r = (p && b) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  have hred3 : Expr.eval store (Expr.basic (.ident z)) = store z := rfl
  rw [hred1, hred3] at hmap
  have hchain : Option.bind (store x)
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => Option.bind (store z)
          (fun v3 => some [v1, v2, v3]))) = some args := by
    simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      cases hsz : store z with
      | none => rw [hsz] at hchain; simp at hchain
      | some vz =>
          rw [hsz] at hchain
          simp only [Option.bind_some] at hchain
          have hargsv : args = [vx, .bool b, vz] := by
            simpa using hchain.symm
          subst hargsv
          have h1 : fullInterp (Ident.mk "bool_and") [vx, .bool b, vz] :=
            interp_of_hname hname hinterp
          rw [fullInterp_std (by decide : ¬ "bool_and" ∈ globalsNames)] at h1
          have hmatch : (match [vx, .bool b, vz] with
            | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
            | _ => False) := h1
          cases vx with
          | bool p =>
              cases vz with
              | bool r =>
                  have hpr : r = (p && b) := by simpa using hmatch
                  exact ⟨p, r, rfl, rfl, hpr⟩
              | int v => exact absurd hmatch (by simp)
              | setOfInt v => exact absurd hmatch (by simp)
              | array v => exact absurd hmatch (by simp)
          | int v => exact absurd hmatch (by simp)
          | setOfInt v => exact absurd hmatch (by simp)
          | array v => exact absurd hmatch (by simp)

/-- Coverage inversion: `bool_and(E, y, z)` holding with E evaluating
    to `.bool b` forces the reads at y and z to be Booleans with
    `r = (b && q)`. -/
theorem holds_bool_and_lo_E_inv {store : Store} {c : ConstraintItem}
    {y z : Ident} {E : Expr} {b : Bool}
    (hname : c.name.name = "bool_and")
    (hargs : c.args = [E, Expr.basic (.ident y), Expr.basic (.ident z)])
    (hE : Expr.eval store E = some (.bool b))
    (h : c.Holds fullInterp store) :
    ∃ q r, store y = some (.bool q) ∧ store z = some (.bool r) ∧
      r = (b && q) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  have hred3 : Expr.eval store (Expr.basic (.ident z)) = store z := rfl
  rw [hred2, hred3] at hmap
  have hchain : Option.bind (Expr.eval store E)
      (fun v1 => Option.bind (store y)
        (fun v2 => Option.bind (store z)
          (fun v3 => some [v1, v2, v3]))) = some args := by
    simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  cases hsy : store y with
  | none => rw [hsy] at hchain; simp at hchain
  | some vy =>
      rw [hsy] at hchain
      simp only [Option.bind_some] at hchain
      cases hsz : store z with
      | none => rw [hsz] at hchain; simp at hchain
      | some vz =>
          rw [hsz] at hchain
          simp only [Option.bind_some] at hchain
          have hargsv : args = [.bool b, vy, vz] := by
            simpa using hchain.symm
          subst hargsv
          have h1 : fullInterp (Ident.mk "bool_and") [.bool b, vy, vz] :=
            interp_of_hname hname hinterp
          rw [fullInterp_std (by decide : ¬ "bool_and" ∈ globalsNames)] at h1
          have hmatch : (match [.bool b, vy, vz] with
            | [Value.bool p, Value.bool q, Value.bool r] => r = (p && q)
            | _ => False) := h1
          cases vy with
          | bool q =>
              cases vz with
              | bool r =>
                  have hqr : r = (b && q) := by simpa using hmatch
                  exact ⟨q, r, rfl, rfl, hqr⟩
              | int v => exact absurd hmatch (by simp)
              | setOfInt v => exact absurd hmatch (by simp)
              | array v => exact absurd hmatch (by simp)
          | int v => exact absurd hmatch (by simp)
          | setOfInt v => exact absurd hmatch (by simp)
          | array v => exact absurd hmatch (by simp)

/-- Coverage inversion: `bool_or(x, E, z)` holding with E evaluating
    to `.bool b` forces the reads at x and z to be Booleans with
    `r = (p || b)`. -/
theorem holds_bool_or_hi_E_inv {store : Store} {c : ConstraintItem}
    {x z : Ident} {E : Expr} {b : Bool}
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [Expr.basic (.ident x), E, Expr.basic (.ident z)])
    (hE : Expr.eval store E = some (.bool b))
    (h : c.Holds fullInterp store) :
    ∃ p r, store x = some (.bool p) ∧ store z = some (.bool r) ∧
      r = (p || b) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hred1 : Expr.eval store (Expr.basic (.ident x)) = store x := rfl
  have hred3 : Expr.eval store (Expr.basic (.ident z)) = store z := rfl
  rw [hred1, hred3] at hmap
  have hchain : Option.bind (store x)
      (fun v1 => Option.bind (Expr.eval store E)
        (fun v2 => Option.bind (store z)
          (fun v3 => some [v1, v2, v3]))) = some args := by
    simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  cases hsx : store x with
  | none => rw [hsx] at hchain; simp at hchain
  | some vx =>
      rw [hsx] at hchain
      simp only [Option.bind_some] at hchain
      cases hsz : store z with
      | none => rw [hsz] at hchain; simp at hchain
      | some vz =>
          rw [hsz] at hchain
          simp only [Option.bind_some] at hchain
          have hargsv : args = [vx, .bool b, vz] := by
            simpa using hchain.symm
          subst hargsv
          have h1 : fullInterp (Ident.mk "bool_or") [vx, .bool b, vz] :=
            interp_of_hname hname hinterp
          rw [fullInterp_std (by decide : ¬ "bool_or" ∈ globalsNames)] at h1
          have hmatch : (match [vx, .bool b, vz] with
            | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
            | _ => False) := h1
          cases vx with
          | bool p =>
              cases vz with
              | bool r =>
                  have hpr : r = (p || b) := by simpa using hmatch
                  exact ⟨p, r, rfl, rfl, hpr⟩
              | int v => exact absurd hmatch (by simp)
              | setOfInt v => exact absurd hmatch (by simp)
              | array v => exact absurd hmatch (by simp)
          | int v => exact absurd hmatch (by simp)
          | setOfInt v => exact absurd hmatch (by simp)
          | array v => exact absurd hmatch (by simp)

/-- Coverage inversion: `bool_or(E, y, z)` holding with E evaluating
    to `.bool b` forces the reads at y and z to be Booleans with
    `r = (b || q)`. -/
theorem holds_bool_or_lo_E_inv {store : Store} {c : ConstraintItem}
    {y z : Ident} {E : Expr} {b : Bool}
    (hname : c.name.name = "bool_or")
    (hargs : c.args = [E, Expr.basic (.ident y), Expr.basic (.ident z)])
    (hE : Expr.eval store E = some (.bool b))
    (h : c.Holds fullInterp store) :
    ∃ q r, store y = some (.bool q) ∧ store z = some (.bool r) ∧
      r = (b || q) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil] at hmap
  have hred2 : Expr.eval store (Expr.basic (.ident y)) = store y := rfl
  have hred3 : Expr.eval store (Expr.basic (.ident z)) = store z := rfl
  rw [hred2, hred3] at hmap
  have hchain : Option.bind (Expr.eval store E)
      (fun v1 => Option.bind (store y)
        (fun v2 => Option.bind (store z)
          (fun v3 => some [v1, v2, v3]))) = some args := by
    simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
  rw [hE] at hchain
  simp only [Option.bind_some] at hchain
  cases hsy : store y with
  | none => rw [hsy] at hchain; simp at hchain
  | some vy =>
      rw [hsy] at hchain
      simp only [Option.bind_some] at hchain
      cases hsz : store z with
      | none => rw [hsz] at hchain; simp at hchain
      | some vz =>
          rw [hsz] at hchain
          simp only [Option.bind_some] at hchain
          have hargsv : args = [.bool b, vy, vz] := by
            simpa using hchain.symm
          subst hargsv
          have h1 : fullInterp (Ident.mk "bool_or") [.bool b, vy, vz] :=
            interp_of_hname hname hinterp
          rw [fullInterp_std (by decide : ¬ "bool_or" ∈ globalsNames)] at h1
          have hmatch : (match [.bool b, vy, vz] with
            | [Value.bool p, Value.bool q, Value.bool r] => r = (p || q)
            | _ => False) := h1
          cases vy with
          | bool q =>
              cases vz with
              | bool r =>
                  have hqr : r = (b || q) := by simpa using hmatch
                  exact ⟨q, r, rfl, rfl, hqr⟩
              | int v => exact absurd hmatch (by simp)
              | setOfInt v => exact absurd hmatch (by simp)
              | array v => exact absurd hmatch (by simp)
          | int v => exact absurd hmatch (by simp)
          | setOfInt v => exact absurd hmatch (by simp)
          | array v => exact absurd hmatch (by simp)

/-- Inversion of `Holds` for `set_in(x, S)` at an arbitrary store:
    the slot name reads an integer the set contains. -/
theorem holds_set_in_lit_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {s : SetLiteral}
    (hname : c.name.name = "set_in")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.set s))])
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ s.denote.Contains p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hxy : ∃ vx, store x = some vx ∧
      args = [vx, (BasicLiteral.set s).denote] := by
    rw [hargs] at hmap
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
    cases hsx : store x with
    | none => rw [hsx] at hmap; simp at hmap
    | some vx =>
        rw [hsx] at hmap
        exact ⟨vx, rfl, by simpa using hmap.symm⟩
  obtain ⟨vx, hsx, hargsv⟩ := hxy
  subst hargsv
  have h1 : fullInterp (Ident.mk "set_in") [vx, (BasicLiteral.set s).denote] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide)] at h1
  cases vx with
  | int p => exact ⟨p, hsx, h1⟩
  | bool w => exact absurd h1 (by simp [stdInterp])
  | setOfInt w => exact absurd h1 (by simp [stdInterp])
  | array w => exact absurd h1 (by simp [stdInterp])

/-- Inversion of `Holds` for `set_in(x, p)` with a parameter set. -/
theorem holds_set_in_param_E_inv {store : Store} {c : ConstraintItem}
    {x p : Ident} {sv : IntSetValue}
    (hname : c.name.name = "set_in")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident p)])
    (hp : store p = some (.setOfInt sv))
    (h : c.Holds fullInterp store) :
    ∃ q, store x = some (.int q) ∧ sv.Contains q := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hxy : ∃ vx, store x = some vx ∧
      args = [vx, Value.setOfInt sv] := by
    rw [hargs] at hmap
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
    cases hsx : store x with
    | none => rw [hsx] at hmap; simp at hmap
    | some vx =>
        rw [hsx] at hmap
        rw [hp] at hmap
        exact ⟨vx, rfl, by simpa using hmap.symm⟩
  obtain ⟨vx, hsx, hargsv⟩ := hxy
  subst hargsv
  have h1 : fullInterp (Ident.mk "set_in") [vx, Value.setOfInt sv] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide)] at h1
  cases vx with
  | int q => exact ⟨q, hsx, h1⟩
  | bool w => exact absurd h1 (by simp [stdInterp])
  | setOfInt w => exact absurd h1 (by simp [stdInterp])
  | array w => exact absurd h1 (by simp [stdInterp])

/-- Inversion of `Holds` for `set_in_reif(x, S, r)` with a literal
    set: the reified truth-value agreement. -/
theorem holds_set_in_reif_lit_E_inv {store : Store} {c : ConstraintItem}
    {x r : Ident} {s : SetLiteral}
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.set s)),
        Expr.basic (.ident r)])
    (h : c.Holds fullInterp store) :
    ∃ (p : Int) (rb : Bool), store x = some (.int p) ∧
      store r = some (.bool rb) ∧ (rb = true ↔ s.denote.Contains p) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hxy : ∃ vx vr, store x = some vx ∧ store r = some vr ∧
      args = [vx, (BasicLiteral.set s).denote, vr] := by
    rw [hargs] at hmap
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
    cases hsx : store x with
    | none => rw [hsx] at hmap; simp at hmap
    | some vx =>
        rw [hsx] at hmap
        cases hsr : store r with
        | none => rw [hsr] at hmap; simp at hmap
        | some vr =>
            rw [hsr] at hmap
            exact ⟨vx, vr, rfl, rfl, by simpa using hmap.symm⟩
  obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := hxy
  subst hargsv
  have h1 : fullInterp (Ident.mk "set_in_reif")
      [vx, (BasicLiteral.set s).denote, vr] := interp_of_hname hname hinterp
  rw [fullInterp_std (by decide)] at h1
  cases vx with
  | int p =>
      cases vr with
      | bool rb =>
          exact ⟨p, rb, hsx, hsr,
            (reif_disj_iff (s.denote.Contains p) rb).mp h1⟩
      | int w => exact absurd h1 (by simp [stdInterp])
      | setOfInt w => exact absurd h1 (by simp [stdInterp])
      | array w => exact absurd h1 (by simp [stdInterp])
  | bool w => exact absurd h1 (by simp [stdInterp])
  | setOfInt w => exact absurd h1 (by simp [stdInterp])
  | array w => exact absurd h1 (by simp [stdInterp])

/-- Inversion of `Holds` for `set_in_reif(x, p, r)` with a
    parameter set. -/
theorem holds_set_in_reif_param_E_inv {store : Store} {c : ConstraintItem}
    {x p r : Ident} {sv : IntSetValue}
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident p),
        Expr.basic (.ident r)])
    (hp : store p = some (.setOfInt sv))
    (h : c.Holds fullInterp store) :
    ∃ (q : Int) (rb : Bool), store x = some (.int q) ∧
      store r = some (.bool rb) ∧ (rb = true ↔ sv.Contains q) := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hxy : ∃ vx vr, store x = some vx ∧ store r = some vr ∧
      args = [vx, Value.setOfInt sv, vr] := by
    rw [hargs] at hmap
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
    cases hsx : store x with
    | none => rw [hsx] at hmap; simp at hmap
    | some vx =>
        rw [hsx] at hmap
        cases hsr : store r with
        | none => rw [hsr] at hmap; simp at hmap
        | some vr =>
            rw [hsr] at hmap
            rw [hp] at hmap
            exact ⟨vx, vr, rfl, rfl, by simpa using hmap.symm⟩
  obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := hxy
  subst hargsv
  have h1 : fullInterp (Ident.mk "set_in_reif")
      [vx, Value.setOfInt sv, vr] := interp_of_hname hname hinterp
  rw [fullInterp_std (by decide)] at h1
  cases vx with
  | int q =>
      cases vr with
      | bool rb =>
          exact ⟨q, rb, hsx, hsr,
            (reif_disj_iff (sv.Contains q) rb).mp h1⟩
      | int w => exact absurd h1 (by simp [stdInterp])
      | setOfInt w => exact absurd h1 (by simp [stdInterp])
      | array w => exact absurd h1 (by simp [stdInterp])
  | bool w => exact absurd h1 (by simp [stdInterp])
  | setOfInt w => exact absurd h1 (by simp [stdInterp])
  | array w => exact absurd h1 (by simp [stdInterp])

/-- Inversion of `Holds` for `set_in_reif(x, S, true)` at an
    arbitrary store: the slot name reads an integer the set
    contains (the literal-true reification forces membership). -/
theorem holds_set_in_reif_true_E_inv {store : Store} {c : ConstraintItem}
    {x : Ident} {s : SetLiteral}
    (hname : c.name.name = "set_in_reif")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.set s)),
        Expr.basic (.lit (.bool true))])
    (h : c.Holds fullInterp store) :
    ∃ p, store x = some (.int p) ∧ s.denote.Contains p := by
  obtain ⟨args, hmap, hinterp⟩ := h
  have hxy : ∃ vx, store x = some vx ∧
      args = [vx, (BasicLiteral.set s).denote,
          (BasicLiteral.bool true).denote] := by
    rw [hargs] at hmap
    simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval] at hmap
    cases hsx : store x with
    | none => rw [hsx] at hmap; simp at hmap
    | some vx =>
        rw [hsx] at hmap
        exact ⟨vx, rfl, by simpa using hmap.symm⟩
  obtain ⟨vx, hsx, hargsv⟩ := hxy
  subst hargsv
  have h1 : fullInterp (Ident.mk "set_in_reif")
      [vx, (BasicLiteral.set s).denote, (BasicLiteral.bool true).denote] :=
    interp_of_hname hname hinterp
  rw [fullInterp_std (by decide)] at h1
  cases vx with
  | int p =>
      have hiff : true = true ↔ s.denote.Contains p :=
        (reif_disj_iff (s.denote.Contains p) true).mp h1
      exact ⟨p, hsx, hiff.mp rfl⟩
  | bool w => exact absurd h1 (by simp [stdInterp])
  | setOfInt w => exact absurd h1 (by simp [stdInterp])
  | array w => exact absurd h1 (by simp [stdInterp])

/-- The coverage linker per constraint: a source constraint holding
    at the assembled store of an assignment whose slot reads agree
    with the store makes the compiled constraint satisfied. -/
theorem compile_holds_link {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {dc : DomConstraint}
    (hnu : (slots.map Prod.fst).Nodup)
    (halt : a.length = slots.length)
    (hcc : compileConstraint (parEnv m) (slots.map Prod.fst) c = .ok dc)
    (hh : c.Holds fullInterp ((assemble m slots dcs).toStore a)) :
    dc.SatisfiedBy a := by
  -- the compiled constraint came from extraction or fallback
  cases hex : extractConstraint (slots.map Prod.fst) c with
  | some dc' =>
      -- the compile took the extraction arm: dc = dc'
      have hcdc : dc = dc' := by
        unfold compileConstraint at hcc
        simp only [hex] at hcc
        exact (Except.ok.inj hcc).symm
      subst hcdc
      -- the store-direction bridge: the assembled store's reads agree
      -- with the assignment at every slot position
      have hvals : ∀ (i : Nat), i < (slots.map Prod.fst).length →
          ∃ v, a[i]? = some v ∧ ((assemble m slots dcs).toStore a)
              (Ident.mk (slots.map Prod.fst)[i]!) = some v := by
        intro i hilt
        have hlen : (slots.map Prod.fst).length = slots.length := by simp
        have hislt : i < slots.length := by omega
        have ha5 : i < a.length := by omega
        refine ⟨a[i]!, ?_, ?_⟩
        · rw [List.getElem!_eq_getElem?_getD,
            List.getElem?_eq_getElem ha5]
          rfl
        · exact toStore_slot (m := m) (dcs := dcs) hnu hislt ha5
      exact extractConstraint_holds hh hex hvals
  | none =>
      -- the fallback arm: case on the family; each arm inverts the
      -- source constraint at the assembled store and transports the
      -- reads to the assignment's slot values
      by_cases hle : c.name.name = "int_le"
      · have hlen2 := compileConstraint_fallback2_len hcc hex (Or.inl hle)
        rcases compileConstraint_le_fallback_inv hcc hle hlen2 hex with
          ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ | ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
        · subst hdc
          have hxread : ((assemble m slots dcs).toStore a) x = some a[i]! :=
            toStore_read (m := m) hnu hxi halt
          have hEread : Expr.eval ((assemble m slots dcs).toStore a) E =
              some (.int k) := eval_intValuedArg halt hE
          obtain ⟨p, hpx, hple⟩ :=
            holds_int_le_hi_E_inv (c := c) hle hargs hEread hh
          rw [hxread] at hpx
          have hap : a[i]! = Value.int p := int_of_some_read hpx
          have hilt : i < a.length := by
            have h1 := (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
            have hlen : (slots.map Prod.fst).length = slots.length := by simp
            omega
          exact ⟨p, getElem_int_of_bang hilt hap, hple⟩
        · subst hdc
          have hyread : ((assemble m slots dcs).toStore a) y = some a[j]! :=
            toStore_read (m := m) hnu hyi halt
          have hEread : Expr.eval ((assemble m slots dcs).toStore a) E =
              some (.int k) := eval_intValuedArg halt hE
          obtain ⟨p, hpy, hple⟩ :=
            holds_int_le_lo_E_inv (c := c) hle hargs hEread hh
          rw [hyread] at hpy
          have hap : a[j]! = Value.int p := int_of_some_read hpy
          have hjlt : j < a.length := by
            have h1 := (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
            have hlen : (slots.map Prod.fst).length = slots.length := by simp
            omega
          exact ⟨p, getElem_int_of_bang hjlt hap, hple⟩
      · by_cases hlt : c.name.name = "int_lt"
        · have hlen2 := compileConstraint_fallback2_len hcc hex
              (Or.inr (Or.inl hlt))
          rcases compileConstraint_lt_fallback_inv hcc hlt hlen2 hex with
            ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ |
            ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
          · subst hdc
            have hxread : ((assemble m slots dcs).toStore a) x =
                some a[i]! := toStore_read (m := m) hnu hxi halt
            have hEread : Expr.eval ((assemble m slots dcs).toStore a) E =
                some (.int k) := eval_intValuedArg halt hE
            obtain ⟨p, hpx, hple⟩ :=
              holds_int_lt_hi_E_inv (c := c) hlt hargs hEread hh
            rw [hxread] at hpx
            have hap : a[i]! = Value.int p := int_of_some_read hpx
            have hilt : i < a.length := by
              have h1 := (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
              have hlen : (slots.map Prod.fst).length = slots.length := by simp
              omega
            exact ⟨p, getElem_int_of_bang hilt hap, hple⟩
          · subst hdc
            have hyread : ((assemble m slots dcs).toStore a) y =
                some a[j]! := toStore_read (m := m) hnu hyi halt
            have hEread : Expr.eval ((assemble m slots dcs).toStore a) E =
                some (.int k) := eval_intValuedArg halt hE
            obtain ⟨p, hpy, hple⟩ :=
              holds_int_lt_lo_E_inv (c := c) hlt hargs hEread hh
            rw [hyread] at hpy
            have hap : a[j]! = Value.int p := int_of_some_read hpy
            have hjlt : j < a.length := by
              have h1 := (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
              have hlen : (slots.map Prod.fst).length = slots.length := by simp
              omega
            exact ⟨p, getElem_int_of_bang hjlt hap, hple⟩
        · by_cases hgt : c.name.name = "int_gt"
          · have hlen2 := compileConstraint_fallback2_len hcc hex
                (Or.inr (Or.inr (Or.inl hgt)))
            rcases compileConstraint_gt_fallback_inv hcc hgt hlen2 hex with
              ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ |
              ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
            · subst hdc
              have hxread : ((assemble m slots dcs).toStore a) x =
                  some a[i]! := toStore_read (m := m) hnu hxi halt
              have hEread : Expr.eval ((assemble m slots dcs).toStore a) E =
                  some (.int k) := eval_intValuedArg halt hE
              obtain ⟨p, hpx, hple⟩ :=
                holds_int_gt_hi_E_inv (c := c) hgt hargs hEread hh
              rw [hxread] at hpx
              have hap : a[i]! = Value.int p := int_of_some_read hpx
              have hilt : i < a.length := by
                have h1 := (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                have hlen : (slots.map Prod.fst).length = slots.length := by simp
                omega
              exact ⟨p, getElem_int_of_bang hilt hap, hple⟩
            · subst hdc
              have hyread : ((assemble m slots dcs).toStore a) y =
                  some a[j]! := toStore_read (m := m) hnu hyi halt
              have hEread : Expr.eval ((assemble m slots dcs).toStore a) E =
                  some (.int k) := eval_intValuedArg halt hE
              obtain ⟨p, hpy, hple⟩ :=
                holds_int_gt_lo_E_inv (c := c) hgt hargs hEread hh
              rw [hyread] at hpy
              have hap : a[j]! = Value.int p := int_of_some_read hpy
              have hjlt : j < a.length := by
                have h1 := (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
                have hlen : (slots.map Prod.fst).length = slots.length := by simp
                omega
              exact ⟨p, getElem_int_of_bang hjlt hap, hple⟩
          · by_cases hge : c.name.name = "int_ge"
            · have hlen2 := compileConstraint_fallback2_len hcc hex
                  (Or.inr (Or.inr (Or.inr hge)))
              rcases compileConstraint_ge_fallback_inv hcc hge hlen2 hex with
                ⟨x, E, i, k, hargs, hxi, hE, hdc⟩ |
                ⟨y, E, j, k, hargs, hyi, hE, hdc⟩
              · subst hdc
                have hxread : ((assemble m slots dcs).toStore a) x =
                    some a[i]! := toStore_read (m := m) hnu hxi halt
                have hEread :
                    Expr.eval ((assemble m slots dcs).toStore a) E =
                    some (.int k) := eval_intValuedArg halt hE
                obtain ⟨p, hpx, hple⟩ :=
                  holds_int_ge_hi_E_inv (c := c) hge hargs hEread hh
                rw [hxread] at hpx
                have hap : a[i]! = Value.int p := int_of_some_read hpx
                have hilt : i < a.length := by
                  have h1 := (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                  have hlen : (slots.map Prod.fst).length = slots.length := by simp
                  omega
                exact ⟨p, getElem_int_of_bang hilt hap, hple⟩
              · subst hdc
                have hyread : ((assemble m slots dcs).toStore a) y =
                    some a[j]! := toStore_read (m := m) hnu hyi halt
                have hEread :
                    Expr.eval ((assemble m slots dcs).toStore a) E =
                    some (.int k) := eval_intValuedArg halt hE
                obtain ⟨p, hpy, hple⟩ :=
                  holds_int_ge_lo_E_inv (c := c) hge hargs hEread hh
                rw [hyread] at hpy
                have hap : a[j]! = Value.int p := int_of_some_read hpy
                have hjlt : j < a.length := by
                  have h1 := (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
                  have hlen : (slots.map Prod.fst).length = slots.length := by simp
                  omega
                exact ⟨p, getElem_int_of_bang hjlt hap, hple⟩
            · by_cases hplus : c.name.name = "int_plus"
              · obtain ⟨x, y, E, i, j, k, hargs, hxi, hyi, hE, hdc⟩ :=
                  compileConstraint_plus_fallback_inv hcc hplus
                    (compileConstraint_fallback3_len hcc hex (Or.inl hplus)) hex
                subst hdc
                have hxread : ((assemble m slots dcs).toStore a) x =
                    some a[i]! := toStore_read (m := m) hnu hxi halt
                have hyread : ((assemble m slots dcs).toStore a) y =
                    some a[j]! := toStore_read (m := m) hnu hyi halt
                have hEread : Expr.eval ((assemble m slots dcs).toStore a) E =
                    some (.int k) := eval_intValuedArg halt hE
                obtain ⟨p, q, hpx, hpy, hpqk⟩ :=
                  holds_int_plus_E_inv (c := c) hplus hargs hEread hh
                rw [hxread] at hpx
                rw [hyread] at hpy
                have hapi : a[i]! = Value.int p := int_of_some_read hpx
                have hapj : a[j]! = Value.int q := int_of_some_read hpy
                -- the linEq satisfaction via the unit dot product
                have hdot : LeanFzn.Semantics.dotProduct (intVals [1, 1])
                    [a[i]!, a[j]!] = some k := by
                  rw [hapi, hapj,
                    show intVals [1, 1] = [Value.int 1, Value.int 1] from rfl]
                  have h2 := dotProduct_two_one (Value.int p) (Value.int q)
                  rw [h2]
                  exact congrArg _ hpqk
                exact hdot
              · by_cases hnot : c.name.name = "bool_not"
                · have hlen2 := compileConstraint_bool_not_len hcc hex hnot
                  rcases compileConstraint_bool_not_fallback_inv hcc hnot
                    hlen2 hex with
                  ⟨x, E, i, w, hargs, hxi, hE, hdc⟩ |
                    ⟨y, E, j, w, hargs, hyi, hE, hdc⟩
                  · subst hdc
                    have hxread : ((assemble m slots dcs).toStore a) x =
                        some a[i]! := toStore_read (m := m) hnu hxi halt
                    have hEread : Expr.eval ((assemble m slots dcs).toStore a)
                        E = some (.bool w) := eval_boolValuedArg halt hE
                    obtain hpx :=
                      holds_bool_not_hi_E_inv (c := c) hnot hargs hEread hh
                    rw [hxread] at hpx
                    have hip : a[i]! = Value.bool (!w) := (Option.some.inj hpx)
                    have hilt : i < a.length := by
                      have h1 :=
                        (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                      have hlen : (slots.map Prod.fst).length = slots.length := by simp
                      omega
                    exact (getElem_as_some hilt).trans (congrArg some hip)
                  · subst hdc
                    have hyread : ((assemble m slots dcs).toStore a) y =
                        some a[j]! := toStore_read (m := m) hnu hyi halt
                    have hEread : Expr.eval ((assemble m slots dcs).toStore a)
                        E = some (.bool w) := eval_boolValuedArg halt hE
                    obtain hpy :=
                      holds_bool_not_lo_E_inv (c := c) hnot hargs hEread hh
                    rw [hyread] at hpy
                    have hjp : a[j]! = Value.bool (!w) := (Option.some.inj hpy)
                    have hjlt : j < a.length := by
                      have h1 :=
                        (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
                      have hlen : (slots.map Prod.fst).length = slots.length := by simp
                      omega
                    exact (getElem_as_some hjlt).trans (congrArg some hjp)
                · by_cases hand : c.name.name = "bool_and"
                  · have hlen2 := compileConstraint_fallback3_len hcc hex
                        (Or.inr (Or.inl hand))
                    rcases compileConstraint_bool_and_fallback_inv hcc hand
                        hlen2 hex with
                    ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                      ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                      ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩ |
                      ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩
                    · subst hdc
                      have hEread : Expr.eval ((assemble m slots dcs).toStore
                          a) E = some (.bool true) := eval_boolValuedArg halt hE
                      obtain ⟨p, r, hpx, hpz, hpr⟩ :=
                        holds_bool_and_hi_E_inv (c := c) hand hargs hEread hh
                      have hxread : ((assemble m slots dcs).toStore a) x =
                          some a[i]! := toStore_read (m := m) hnu hxi halt
                      have hzread : ((assemble m slots dcs).toStore a) z =
                          some a[k]! := toStore_read (m := m) hnu hzi halt
                      rw [hpx] at hxread
                      rw [hpz] at hzread
                      have hilt : i < a.length := by
                        have h1 :=
                          (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                        have hlen : (slots.map Prod.fst).length = slots.length := by simp
                        omega
                      have hklt : k < a.length := by
                        have h1 :=
                          (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                        have hlen : (slots.map Prod.fst).length = slots.length := by simp
                        omega
                      have hxr : a[i]! = Value.bool p := (Option.some.inj hxread.symm)
                      have hzr : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                      have hrp : r = p := by
                        rw [hpr]; simp [Bool.and_true]
                      exact ⟨Value.bool p, Value.bool r,
                        (getElem_as_some hilt).trans (congrArg some hxr),
                        (getElem_as_some hklt).trans (congrArg some hzr),
                        by rw [hrp]⟩
                    · subst hdc
                      have hEread : Expr.eval ((assemble m slots dcs).toStore
                          a) E = some (.bool false) := eval_boolValuedArg halt hE
                      obtain ⟨p, r, hpx, hpz, hpr⟩ :=
                        holds_bool_and_hi_E_inv (c := c) hand hargs hEread hh
                      have hzread : ((assemble m slots dcs).toStore a) z =
                          some a[k]! := toStore_read (m := m) hnu hzi halt
                      rw [hpz] at hzread
                      have hkr : a[k]! = Value.bool false := by
                        have h1 : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                        rw [h1, hpr]
                        simp [Bool.false_and]
                      have hklt : k < a.length := by
                        have h1 :=
                          (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                        have hlen : (slots.map Prod.fst).length = slots.length := by simp
                        omega
                      exact (getElem_as_some hklt).trans (congrArg some hkr)
                    · subst hdc
                      have hEread : Expr.eval ((assemble m slots dcs).toStore
                          a) E = some (.bool true) := eval_boolValuedArg halt hE
                      obtain ⟨q, r, hpy, hpz, hpr⟩ :=
                        holds_bool_and_lo_E_inv (c := c) hand hargs hEread hh
                      have hyread : ((assemble m slots dcs).toStore a) y =
                          some a[j]! := toStore_read (m := m) hnu hyi halt
                      have hzread : ((assemble m slots dcs).toStore a) z =
                          some a[k]! := toStore_read (m := m) hnu hzi halt
                      rw [hpy] at hyread
                      rw [hpz] at hzread
                      have hjlt : j < a.length := by
                        have h1 :=
                          (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
                        have hlen : (slots.map Prod.fst).length = slots.length := by simp
                        omega
                      have hklt : k < a.length := by
                        have h1 :=
                          (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                        have hlen : (slots.map Prod.fst).length = slots.length := by simp
                        omega
                      have hyr : a[j]! = Value.bool q := (Option.some.inj hyread.symm)
                      have hzr : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                      have hrq : r = q := by
                        rw [hpr]; simp [Bool.true_and]
                      exact ⟨Value.bool q, Value.bool r,
                        (getElem_as_some hjlt).trans (congrArg some hyr),
                        (getElem_as_some hklt).trans (congrArg some hzr),
                        by rw [hrq]⟩
                    · subst hdc
                      have hEread : Expr.eval ((assemble m slots dcs).toStore
                          a) E = some (.bool false) := eval_boolValuedArg halt hE
                      obtain ⟨q, r, hpy, hpz, hpr⟩ :=
                        holds_bool_and_lo_E_inv (c := c) hand hargs hEread hh
                      have hzread : ((assemble m slots dcs).toStore a) z =
                          some a[k]! := toStore_read (m := m) hnu hzi halt
                      rw [hpz] at hzread
                      have hkr : a[k]! = Value.bool false := by
                        have h1 : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                        rw [h1, hpr]
                        simp [Bool.false_and]
                      have hklt : k < a.length := by
                        have h1 :=
                          (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                        have hlen : (slots.map Prod.fst).length = slots.length := by simp
                        omega
                      exact (getElem_as_some hklt).trans (congrArg some hkr)
                  · by_cases hor : c.name.name = "bool_or"
                    · have hlen2 := compileConstraint_fallback3_len hcc hex
                          (Or.inr (Or.inr hor))
                      rcases compileConstraint_bool_or_fallback_inv hcc hor
                          hlen2 hex with
                      ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                        ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩ |
                        ⟨x, z, E, i, k, hargs, hxi, hzi, hE, hdc⟩ |
                        ⟨y, z, E, j, k, hargs, hyi, hzi, hE, hdc⟩
                      · subst hdc
                        have hEread : Expr.eval ((assemble m slots dcs).toStore
                            a) E = some (.bool true) := eval_boolValuedArg halt hE
                        obtain ⟨p, r, hpx, hpz, hpr⟩ :=
                          holds_bool_or_hi_E_inv (c := c) hor hargs hEread hh
                        have hzread : ((assemble m slots dcs).toStore a) z =
                            some a[k]! := toStore_read (m := m) hnu hzi halt
                        rw [hpz] at hzread
                        have hkr : a[k]! = Value.bool true := by
                          have h1 : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                          rw [h1, hpr]
                          simp [Bool.true_or]
                        have hklt : k < a.length := by
                          have h1 :=
                            (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                          have hlen : (slots.map Prod.fst).length = slots.length := by simp
                          omega
                        exact (getElem_as_some hklt).trans (congrArg some hkr)
                      · subst hdc
                        have hEread : Expr.eval ((assemble m slots dcs).toStore
                            a) E = some (.bool true) := eval_boolValuedArg halt hE
                        obtain ⟨q, r, hpy, hpz, hpr⟩ :=
                          holds_bool_or_lo_E_inv (c := c) hor hargs hEread hh
                        have hzread : ((assemble m slots dcs).toStore a) z =
                            some a[k]! := toStore_read (m := m) hnu hzi halt
                        rw [hpz] at hzread
                        have hkr : a[k]! = Value.bool true := by
                          have h1 : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                          rw [h1, hpr]
                          simp [Bool.true_or]
                        have hklt : k < a.length := by
                          have h1 :=
                            (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                          have hlen : (slots.map Prod.fst).length = slots.length := by simp
                          omega
                        exact (getElem_as_some hklt).trans (congrArg some hkr)
                      · subst hdc
                        have hEread : Expr.eval ((assemble m slots dcs).toStore
                            a) E = some (.bool false) := eval_boolValuedArg halt hE
                        obtain ⟨p, r, hpx, hpz, hpr⟩ :=
                          holds_bool_or_hi_E_inv (c := c) hor hargs hEread hh
                        have hxread : ((assemble m slots dcs).toStore a) x =
                            some a[i]! := toStore_read (m := m) hnu hxi halt
                        have hzread : ((assemble m slots dcs).toStore a) z =
                            some a[k]! := toStore_read (m := m) hnu hzi halt
                        rw [hpx] at hxread
                        rw [hpz] at hzread
                        have hilt : i < a.length := by
                          have h1 :=
                            (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                          have hlen : (slots.map Prod.fst).length = slots.length := by simp
                          omega
                        have hklt : k < a.length := by
                          have h1 :=
                            (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                          have hlen : (slots.map Prod.fst).length = slots.length := by simp
                          omega
                        have hxr : a[i]! = Value.bool p := (Option.some.inj hxread.symm)
                        have hzr : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                        have hrp : r = p := by
                          rw [hpr]; simp [Bool.or_false]
                        exact ⟨Value.bool p, Value.bool r,
                          (getElem_as_some hilt).trans (congrArg some hxr),
                          (getElem_as_some hklt).trans (congrArg some hzr),
                          by rw [hrp]⟩
                      · subst hdc
                        have hEread : Expr.eval ((assemble m slots dcs).toStore
                            a) E = some (.bool false) := eval_boolValuedArg halt hE
                        obtain ⟨q, r, hpy, hpz, hpr⟩ :=
                          holds_bool_or_lo_E_inv (c := c) hor hargs hEread hh
                        have hyread : ((assemble m slots dcs).toStore a) y =
                            some a[j]! := toStore_read (m := m) hnu hyi halt
                        have hzread : ((assemble m slots dcs).toStore a) z =
                            some a[k]! := toStore_read (m := m) hnu hzi halt
                        rw [hpy] at hyread
                        rw [hpz] at hzread
                        have hjlt : j < a.length := by
                          have h1 :=
                            (nameIndex_some (slots.map Prod.fst) y.name j hyi).1
                          have hlen : (slots.map Prod.fst).length = slots.length := by simp
                          omega
                        have hklt : k < a.length := by
                          have h1 :=
                            (nameIndex_some (slots.map Prod.fst) z.name k hzi).1
                          have hlen : (slots.map Prod.fst).length = slots.length := by simp
                          omega
                        have hyr : a[j]! = Value.bool q := (Option.some.inj hyread.symm)
                        have hzr : a[k]! = Value.bool r := (Option.some.inj hzread.symm)
                        have hrq : r = q := by
                          rw [hpr]; simp [Bool.false_or]
                        exact ⟨Value.bool q, Value.bool r,
                          (getElem_as_some hjlt).trans (congrArg some hyr),
                          (getElem_as_some hklt).trans (congrArg some hzr),
                          by rw [hrq]⟩
                    · by_cases hsetin : c.name.name = "set_in"
                      · have hlen2 := compileConstraint_set_in_len hcc hex hsetin
                        rcases compileConstraint_set_in_fallback_inv hcc hsetin
                            hlen2 hex with
                          ⟨x, sv, i, hargs, hxi, hdc⟩ |
                            ⟨x, pv, i, sv, hargs, hxi, hpn, hp, hdc⟩
                        · subst hdc
                          obtain ⟨p, hpx, hpc⟩ :=
                            holds_set_in_lit_E_inv (c := c) hsetin hargs hh
                          have hxread : ((assemble m slots dcs).toStore a) x =
                              some a[i]! := toStore_read (m := m) hnu hxi halt
                          rw [hpx] at hxread
                          have hap : a[i]! = Value.int p :=
                            int_of_some_read hxread.symm
                          have hilt : i < a.length := by
                            have h1 :=
                              (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                            have hlen : (slots.map Prod.fst).length = slots.length := by simp
                            omega
                          exact ⟨p, getElem_int_of_bang hilt hap, hpc⟩
                        · subst hdc
                          have hpstore : ((assemble m slots dcs).toStore a) pv =
                              some (.setOfInt sv) := toStore_param hpn hp
                          obtain ⟨p, hpx, hpc⟩ :=
                            holds_set_in_param_E_inv (c := c) hsetin hargs
                              hpstore hh
                          have hxread : ((assemble m slots dcs).toStore a) x =
                              some a[i]! := toStore_read (m := m) hnu hxi halt
                          rw [hpx] at hxread
                          have hap : a[i]! = Value.int p :=
                            int_of_some_read hxread.symm
                          have hilt : i < a.length := by
                            have h1 :=
                              (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                            have hlen : (slots.map Prod.fst).length = slots.length := by simp
                            omega
                          exact ⟨p, getElem_int_of_bang hilt hap, hpc⟩
                      · by_cases hsetreif : c.name.name = "set_in_reif"
                        · have hlen2 := compileConstraint_set_in_reif_len hcc
                              hex hsetreif
                          rcases compileConstraint_set_in_reif_fallback_inv hcc
                              hsetreif hlen2 hex with
                            ⟨x, sv, r, i, k, hargs, hxi, hrk, hdc⟩ |
                              ⟨x, sv, i, hargs, hxi, hdc⟩ |
                              ⟨x, pv, r, i, sv, k, hargs, hxi, hpn, hp, hrk, hdc⟩
                          · subst hdc
                            obtain ⟨p, rb, hpx, hpr, hriff⟩ :=
                              holds_set_in_reif_lit_E_inv (c := c) hsetreif hargs hh
                            have hxread : ((assemble m slots dcs).toStore a) x =
                                some a[i]! := toStore_read (m := m) hnu hxi halt
                            have hrread : ((assemble m slots dcs).toStore a) r =
                                some a[k]! := toStore_read (m := m) hnu hrk halt
                            rw [hpx] at hxread
                            rw [hpr] at hrread
                            have hap : a[i]! = Value.int p :=
                              int_of_some_read hxread.symm
                            have hrb : a[k]! = Value.bool rb :=
                              (Option.some.inj hrread.symm)
                            have hilt : i < a.length := by
                              have h1 :=
                                (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                              have hlen : (slots.map Prod.fst).length = slots.length := by simp
                              omega
                            have hklt : k < a.length := by
                              have h1 :=
                                (nameIndex_some (slots.map Prod.fst) r.name k hrk).1
                              have hlen : (slots.map Prod.fst).length = slots.length := by simp
                              omega
                            exact ⟨p, rb, getElem_int_of_bang hilt hap,
                              (getElem_as_some hklt).trans (congrArg some hrb),
                              hriff⟩
                          · subst hdc
                            obtain ⟨p, hpx, hpc⟩ :=
                              holds_set_in_reif_true_E_inv (c := c) hsetreif hargs hh
                            have hxread : ((assemble m slots dcs).toStore a) x =
                                some a[i]! := toStore_read (m := m) hnu hxi halt
                            rw [hpx] at hxread
                            have hap : a[i]! = Value.int p :=
                              int_of_some_read hxread.symm
                            have hilt : i < a.length := by
                              have h1 :=
                                (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                              have hlen : (slots.map Prod.fst).length = slots.length := by simp
                              omega
                            exact ⟨p, getElem_int_of_bang hilt hap, hpc⟩
                          · subst hdc
                            have hpstore : ((assemble m slots dcs).toStore a) pv =
                                some (.setOfInt sv) := toStore_param hpn hp
                            obtain ⟨p, rb, hpx, hpr, hriff⟩ :=
                              holds_set_in_reif_param_E_inv (c := c) hsetreif
                                hargs hpstore hh
                            have hxread : ((assemble m slots dcs).toStore a) x =
                                some a[i]! := toStore_read (m := m) hnu hxi halt
                            have hrread : ((assemble m slots dcs).toStore a) r =
                                some a[k]! := toStore_read (m := m) hnu hrk halt
                            rw [hpx] at hxread
                            rw [hpr] at hrread
                            have hap : a[i]! = Value.int p :=
                              int_of_some_read hxread.symm
                            have hrb : a[k]! = Value.bool rb :=
                              (Option.some.inj hrread.symm)
                            have hilt : i < a.length := by
                              have h1 :=
                                (nameIndex_some (slots.map Prod.fst) x.name i hxi).1
                              have hlen : (slots.map Prod.fst).length = slots.length := by simp
                              omega
                            have hklt : k < a.length := by
                              have h1 :=
                                (nameIndex_some (slots.map Prod.fst) r.name k hrk).1
                              have hlen : (slots.map Prod.fst).length = slots.length := by simp
                              omega
                            exact ⟨p, rb, getElem_int_of_bang hilt hap,
                              (getElem_as_some hklt).trans (congrArg some hrb),
                              hriff⟩
                        · exfalso
                          have hfall : compileConstraint (parEnv m)
                              (slots.map Prod.fst) c
                              = .error s!"unsupported predicate '{c.name.name}'" := by
                            unfold compileConstraint
                            rw [hex]
                            have h1 : ¬(c.name.name = "int_plus" ∧
                                c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hplus
                            have h2 : ¬(c.name.name = "int_le" ∧
                                c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hle
                            have h3 : ¬(c.name.name = "int_lt" ∧
                                c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hlt
                            have h4 : ¬(c.name.name = "int_gt" ∧
                                c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hgt
                            have h5 : ¬(c.name.name = "int_ge" ∧
                                c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hge
                            have h6 : ¬(c.name.name = "bool_not" ∧
                                c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hnot
                            have h7 : ¬(c.name.name = "bool_and" ∧
                                c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hand
                            have h8 : ¬(c.name.name = "bool_or" ∧
                                c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hor
                            have h9 : ¬(c.name.name = "set_in" ∧
                                c.args.length = 2) := by
                              intro hcon
                              exact absurd hcon.1 hsetin
                            have h10 : ¬(c.name.name = "set_in_reif" ∧
                                c.args.length = 3) := by
                              intro hcon
                              exact absurd hcon.1 hsetreif
                            rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4,
                              if_neg h5, if_neg h6, if_neg h7, if_neg h8,
                              if_neg h9, if_neg h10]
                          rw [hfall] at hcc
                          exact absurd hcc (by simp)


/-- Every slot position of a successfully compiled model reads a
    store value in the slot's domain, provided the store satisfies
    the variable-declaration conditions. -/
theorem slot_reads_of_satisfying {m : Model}
    {problem : CompiledProblem DomConstraint}
    {slots0 : List (String × List Value)} {dcs : List DomConstraint}
    (hc : compileModel m = .ok problem)
    (hslots0 : slotsChecked m = .ok slots0)
    {store : Store}
    (hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array _ _ _ _ => False) :
    ∀ (i : Nat), ∀ hilt : i < slots0.length,
      ∃ v, store (Ident.mk (slots0[i]'hilt).1) = some v ∧
        v ∈ (slots0[i]'hilt).snd := by
  -- every slot of the extended list is a MODEL slot (the aux slots
  -- never appear: they are appended BEYOND the model slots, which
  -- is impossible)
  -- the slot at position i comes from a declared variable
  have hdecls : declSlots m.variables = .ok slots0 :=
    declSlots_of_slotsChecked hslots0
  intro i hilt
  obtain ⟨d, hd, hds⟩ := declSlots_mem m.variables slots0 hdecls
    (slots0[i]'hilt) (List.getElem_mem hilt)
  obtain ⟨ty, n, anns, hshape⟩ :=
    compileModel_vars_basic hc d hd
  subst hshape
  have hdslot : declSlot (.basic ty n anns none : VarDeclItem) =
      .ok (some (slots0[i]'hilt)) := hds
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  obtain ⟨v, hvstore, hcontains⟩ := hvars
    (.basic ty n anns none) hd
  have hvmem : v ∈ dom.values := (varDomain_values_iff hdom).mpr hcontains
  rw [hpair]
  exact ⟨v, by rw [show Ident.mk n.name = n from ident_eq_of_name rfl]; exact hvstore, hvmem⟩

/-- The extended assignment of a satisfying store: the model slots
    carry the store's reads (at the slots' names); the aux slots
    carry their singleton pins. -/
def extAssign (store : Store) (slots0 auxs : List (String × List Value))
    : List Value :=
  slots0.map (fun p => (store (Ident.mk p.1)).getD (.bool false)) ++
    auxs.map (fun p => p.2.head!)

/-- The extended assignment's total length. -/
theorem extAssign_length {store : Store}
    {slots0 auxs : List (String × List Value)} :
    (extAssign store slots0 auxs).length = slots0.length + auxs.length := by
  show (slots0.map _ ++ auxs.map _).length = _
  rw [List.length_append, List.length_map, List.length_map]

/-- The extended assignment's model-prefix read: the store's read at
    the slot's name (the default never fires for a satisfying
    store). -/
theorem extAssign_prefix_read {store : Store}
    {slots0 : List (String × List Value)} {auxs : List (String × List Value)}
    {i : Nat} (hilt : i < slots0.length)
    (hread : ∃ v, store (Ident.mk (slots0[i]'hilt).1) = some v) :
    (extAssign store slots0 auxs)[i]? =
      store (Ident.mk (slots0[i]'hilt).1) := by
  have hlen : (slots0.map
      (fun p => (store (Ident.mk p.1)).getD (.bool false))).length
      = slots0.length := by simp
  have hmap : (extAssign store slots0 auxs)[i]?
      = (slots0.map (fun p => (store (Ident.mk p.1)).getD (.bool false)))[i]? :=
    List.getElem?_append_left
      (l₁ := slots0.map (fun p => (store (Ident.mk p.1)).getD (.bool false)))
      (l₂ := auxs.map (fun p => p.2.head!)) (by rw [hlen]; exact hilt)
  rw [hmap, List.getElem?_map, List.getElem?_eq_getElem hilt]
  obtain ⟨v, hv⟩ := hread
  show Option.map (fun p => (store (Ident.mk p.1)).getD (.bool false))
      (some (slots0[i]'hilt)) = _
  rw [Option.map_some, hv, Option.getD_some]

/-- The extended assignment's aux-suffix read: the singleton pin's
    head (the aux domain is a singleton by construction). -/
theorem extAssign_aux_read {store : Store}
    {slots0 : List (String × List Value)} {auxs : List (String × List Value)}
    {i : Nat} (hilt : i < auxs.length) :
    (extAssign store slots0 auxs)[slots0.length + i]? = some auxs[i].2.head! := by
  have hlen1 : (slots0.map
      (fun p => (store (Ident.mk p.1)).getD (.bool false))).length
      = slots0.length := by simp
  have hlen : (extAssign store slots0 auxs).length
      = slots0.length + auxs.length := extAssign_length
  have hlt : slots0.length + i < (extAssign store slots0 auxs).length := by
    rw [hlen]
    omega
  have happ : (extAssign store slots0 auxs)[slots0.length + i]?
      = (auxs.map (fun p => p.2.head!))[i]? := by
    show (slots0.map (fun p => (store (Ident.mk p.1)).getD (.bool false)) ++
        auxs.map (fun p => p.2.head!))[slots0.length + i]?
      = (auxs.map (fun p => p.2.head!))[i]?
    rw [List.getElem?_append_right
      (l₁ := slots0.map (fun p => (store (Ident.mk p.1)).getD (.bool false)))
      (l₂ := auxs.map (fun p => p.2.head!))
      (by rw [hlen1]; exact Nat.le_add_right slots0.length i)]
    congr 1
    rw [hlen1]
    omega
  rw [happ, List.getElem?_map, List.getElem?_eq_getElem hilt, Option.map_some]

/-- The slot-identity bridge: an identifier that resolves at a
    MODEL position of the extended name list IS the slot's variable
    at that position. -/
theorem extAssign_slot_ident {slots0 auxs : List (String × List Value)}
    {x : Ident} {i : Nat}
    (hilt : i < slots0.length)
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i) :
    Ident.mk (slots0[i]'hilt).1 = x := by
  apply ident_eq_of_name
  -- the extended name list's i-th entry is x's name (the model half)
  have hnameilt : i < ((slots0 ++ auxs).map Prod.fst).length := by
    rw [List.length_map, List.length_append]
    omega
  have hnamei : ((slots0 ++ auxs).map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt
      ((nameIndex_some ((slots0 ++ auxs).map Prod.fst) x.name i hxi).2)
  have hmodelentry : ((slots0 ++ auxs).map Prod.fst)[i]!
      = (slots0.map Prod.fst)[i]! := by
    rw [getElem!_map_fst i, getElem!_map_fst (slots := slots0) i,
      getElem!_eq_getElem (by
        rw [List.length_append]; omega : i < (slots0 ++ auxs).length),
      getElem!_eq_getElem hilt, List.getElem_append_left hilt]
  have hslotname : (slots0.map Prod.fst)[i]! = (slots0[i]'hilt).1 := by
    rw [getElem!_map_fst (slots := slots0) i, getElem!_eq_getElem hilt]
  rw [← hslotname, ← hmodelentry, hnamei]

/-- The position-level read of the extended assignment at a MODEL
    position: the store's own read at the identifier. -/
theorem extAssign_read_ident {store : Store}
    {slots0 auxs : List (String × List Value)} {x : Ident} {i : Nat}
    (hilt : i < slots0.length)
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hread : ∃ v, store (Ident.mk (slots0[i]'hilt).1) = some v) :
    (extAssign store slots0 auxs)[i]? = store x := by
  rw [extAssign_prefix_read hilt hread, extAssign_slot_ident hilt hxi]

/-- The extended assembled store agrees with a satisfying store at
    every identifier that resolves at a MODEL slot position: the
    assignment's prefix read is the store's read at the slot's own
    variable, and the slot's variable IS the identifier. -/
theorem extAssign_toStore_agree {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {store : Store} {x : Ident} {i : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (hilt : i < slots0.length)
    (hxi : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i)
    (hread : ∃ v, store (Ident.mk (slots0[i]'hilt).1) = some v) :
    ((assemble m (slots0 ++ auxs) dcs).toStore
        (extAssign store slots0 auxs)) x = store x := by
  -- the store's read at the slot's name is some v
  obtain ⟨v, hvread⟩ := hread
  -- the assignment's prefix read at i is the same store read
  have hap : (extAssign store slots0 auxs)[i]? = store x :=
    extAssign_read_ident hilt hxi ⟨v, hvread⟩
  have hxid : Ident.mk (slots0[i]'hilt).1 = x :=
    extAssign_slot_ident hilt hxi
  rw [hxid] at hvread
  -- the assembled store reads the assignment at the slot position
  have hstore : ((assemble m (slots0 ++ auxs) dcs).toStore
      (extAssign store slots0 auxs)) x = some (extAssign store slots0 auxs)[i]! :=
    toStore_read (m := m) (slots := slots0 ++ auxs) (dcs := dcs) hnu hxi
      (by rw [extAssign_length, List.length_append])
  -- the bang read is the plain read (in bounds) — the store's read
  have hib : (extAssign store slots0 auxs)[i]! = v := by
    rw [List.getElem!_eq_getElem?_getD]
    have hsome : (extAssign store slots0 auxs)[i]? = some v := by
      rw [hap, hvread]
    rw [hsome]
    rfl
  rw [hstore, hib, hvread]

/-- Every identifier ARGUMENT of a well-formed model constraint is
    declared (its name resolves in the static environment). -/
theorem staticEnv_of_ident_arg {m : Model}
    (hwf : WellFormed fullSig m)
    {c : ConstraintItem} (hc : c ∈ m.constraints)
    {x : Ident} (hxarg : Expr.basic (.ident x) ∈ c.args) :
    m.staticEnv x ≠ none := by
  intro hnone
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  obtain ⟨pt, _, hchk⟩ :=
    forall2_mem (Expr.checkArg m.staticEnv) c.args params hfor
      (Expr.basic (.ident x)) hxarg
  cases pt with
  | basic bt =>
      simp only [Expr.checkArg, BasicExpr.checkBase] at hchk
      rw [hnone] at hchk
      exact hchk
  | array idx bt =>
      simp only [Expr.checkArg] at hchk
      rw [hnone] at hchk
      exact hchk

/-- A parameter-environment read of a parameter-honest store: the
    store itself reads the same value (the parameter's declared
    literal). -/
theorem store_of_parEnv {m : Model} {store : Store}
    (hparam : ParamHonest m store) {y : Ident} {v : Value}
    (henv : parEnv m y = some v) : store y = some v := by
  unfold parEnv at henv
  cases hlk : lookupIdent y (m.parameters.filterMap
      (fun d => parDeclValue d |>.map (fun v2 => (ParDeclItem.name d, v2))))
    with
  | none => rw [hlk] at henv; exact absurd henv (by simp)
  | some w =>
      rw [hlk] at henv
      have hw : w = v := Option.some.inj henv
      rw [hw] at hlk
      obtain ⟨z, hzmem, hzname⟩ := lookupIdent_inv_mem y
        (m.parameters.filterMap
          (fun d => parDeclValue d |>.map (fun v2 => (ParDeclItem.name d, v2))))
        v hlk
      obtain ⟨d, hdmem, hdget⟩ := mem_filterMap_src
        (fun d => parDeclValue d |>.map (fun v2 => (ParDeclItem.name d, v2)))
        m.parameters (z, v) hzmem
      -- the declaration's value and name
      obtain ⟨hdval, hdname⟩ : parDeclValue d = some v ∧ ParDeclItem.name d = z := by
        cases hpd : parDeclValue d with
        | none => rw [hpd] at hdget; exact absurd hdget (by simp)
        | some w2 =>
            rw [hpd] at hdget
            have hpair : (ParDeclItem.name d, w2) = (z, v) :=
              (Option.some.inj hdget)
            have hsnd : w2 = v := congrArg Prod.snd hpair
            have h2 : ParDeclItem.name d = z := congrArg Prod.fst hpair
            exact ⟨by rw [hsnd], h2⟩
      -- the store's read (parameter honesty)
      have hstore : store (ParDeclItem.name d) = some v :=
        hparam d hdmem v hdval
      have hnm : y.name = (ParDeclItem.name d).name := by
        have h1 : (ParDeclItem.name d).name = z.name :=
          congrArg (fun i => i.name) hdname
        rw [h1]
        exact hzname.symm
      rw [ident_eq_of_name hnm]
      exact hstore

/-- A store's read at a resolved variable slot whose declared type has
    base `int` is an integer (PLAN C9 remainder: the two-element array
    shapes' typing fact — `minValue`/`maxValue`'s non-integer-tail
    reading is vacuous on the WF-typed element slots). -/
theorem store_int_read_of_slot_checkArg {m : Model}
    {slots0 : List (String × List Value)} {store : Store} {x : Ident} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array _ _ _ _ => False)
    (hcheck : (Expr.basic (.ident x)).checkArg m.staticEnv
      (.basic (.var (.par .int))))
    (hxi : nameIndex (slots0.map Prod.fst) x.name = some i)
    (hilt : i < slots0.length) :
    ∃ p, store x = some (Value.int p) := by
  -- the slot's variable declaration and its static type
  obtain ⟨d, hd, hdslot, hstatic⟩ := staticEnv_of_slot hwf hslot hilt
  -- the checked identifier IS the slot's variable
  have hxget := (nameIndex_some (slots0.map Prod.fst) x.name i hxi).2
  have hnameilt : i < (slots0.map Prod.fst).length := by
    rw [List.length_map]
    omega
  have hnamei : (slots0.map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt hxget
  have hxslot : slots0[i]!.1 = x.name := by
    rw [show slots0[i]!.1 = (slots0.map Prod.fst)[i]! from
      (getElem!_map_fst i).symm]
    exact hnamei
  have hstaticx : m.staticEnv x = some (d.type, true) := by
    have hxmk : x = Ident.mk slots0[i]!.1 := by
      obtain ⟨s⟩ := x
      apply ident_eq_of_name
      rw [hxslot]
    rw [hxmk]
    exact hstatic
  -- the static type of the check
  obtain ⟨isVar, henv⟩ := staticEnv_int_of_checkArg hcheck
  -- d's declaration shape
  obtain ⟨ty, n, anns, hdshape⟩ : ∃ ty n anns, d = .basic ty n anns none := by
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
  -- the two staticEnv values glue: the declared type has base int
  have htyint : ty.base = BaseType.int := by
    have hboth : some (FznType.base ty.base, true)
        = some (FznType.base BaseType.int, isVar) :=
      hstaticx.symm.trans henv
    have h1 : (FznType.base ty.base, true)
        = (FznType.base BaseType.int, isVar) := Option.some.inj hboth
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, _⟩ := h1
    injection h2
  -- the declared variable's name is the slot's name
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  have hnm : n.name = x.name := by
    have h1 : n.name = slots0[i]!.1 := by
      rw [hpair]
    rw [h1, hxslot]
  -- the store's honest read
  obtain ⟨v, hvstore, hcontains⟩ := hvars (.basic ty n anns none) hd
  have hvint : ∃ p, v = Value.int p := by
    cases v with
    | int p => exact ⟨p, rfl⟩
    | bool b =>
        exfalso
        cases ty with
        | par t =>
            cases t with
            | bool =>
                have hb : BaseType.bool = BaseType.int := by
                  simpa [BasicVarType.base, BasicParType.base] using htyint
                exact BaseType.noConfusion hb
            | int => cases hcontains
            | setOfInt => cases hcontains
        | intRange lo hi => cases hcontains
        | intSet xs => cases hcontains
        | setOfIntRange lo hi =>
            have hb : BaseType.setOfInt = BaseType.int := by
              simpa [BasicVarType.base] using htyint
            exact BaseType.noConfusion hb
        | setOfIntSet allowed =>
            have hb : BaseType.setOfInt = BaseType.int := by
              simpa [BasicVarType.base] using htyint
            exact BaseType.noConfusion hb
    | setOfInt s =>
        exfalso
        cases ty with
        | par t =>
            cases t with
            | bool => cases hcontains
            | int => cases hcontains
            | setOfInt =>
                have hb : BaseType.setOfInt = BaseType.int := by
                  simpa [BasicVarType.base, BasicParType.base] using htyint
                exact BaseType.noConfusion hb
        | intRange lo hi => cases hcontains
        | intSet xs => cases hcontains
        | setOfIntRange lo hi =>
            have hb : BaseType.setOfInt = BaseType.int := by
              simpa [BasicVarType.base] using htyint
            exact BaseType.noConfusion hb
        | setOfIntSet allowed =>
            have hb : BaseType.setOfInt = BaseType.int := by
              simpa [BasicVarType.base] using htyint
            exact BaseType.noConfusion hb
    | array xs =>
        exfalso
        cases ty with
        | par t => cases t <;> cases hcontains
        | intRange lo hi => cases hcontains
        | intSet xs => cases hcontains
        | setOfIntRange lo hi => cases hcontains
        | setOfIntSet allowed => cases hcontains
  obtain ⟨p, hp⟩ := hvint
  refine ⟨p, ?_⟩
  have hnx : n = x := ident_eq_of_name hnm
  rw [hnx, hp] at hvstore
  exact hvstore

/-- WF typing of an array-extreme element argument (PLAN C9 remainder):
    every element identifier of the two-element array checks against
    the int element type of the FlatZinc signature. -/
theorem checkBase_int_of_array_elem {m : Model} {c : ConstraintItem}
    {r e1 e2 : Ident}
    (hpred : m.predicates = [])
    (hwf : WellFormed fullSig m) (hc : c ∈ m.constraints)
    (hname : c.name.name = "array_int_minimum" ∨ c.name.name = "array_int_maximum")
    (hargs : c.args = [.basic (.ident r),
      .array [BasicExpr.ident e1, BasicExpr.ident e2]]) :
    BasicExpr.checkBase m.staticEnv (.ident e1) (.var (.par .int)) ∧
    BasicExpr.checkBase m.staticEnv (.ident e2) (.var (.par .int)) := by
  obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc
  have hres : m.sigEnv fullSig c.name =
      some [.basic (.var (.par .int)), .array .int (.var (.par .int))] := by
    have h1 : m.sigEnv fullSig c.name = m.sigEnv fullSig (Ident.mk c.name.name) := rfl
    rw [h1]
    exact sigEnv_array_int_extreme hpred c.name.name hname
  have hparameq : params =
      [.basic (.var (.par .int)), .array .int (.var (.par .int))] := by
    rw [hres] at hsig
    exact (Option.some.inj hsig).symm
  rw [hargs, hparameq] at hfor
  obtain ⟨-, hfor2⟩ := hfor
  obtain ⟨harr, -⟩ := hfor2
  have hall : ∀ b ∈ [BasicExpr.ident e1, BasicExpr.ident e2],
      BasicExpr.checkBase m.staticEnv b (.var (.par .int)) := harr.2
  refine ⟨?_, ?_⟩
  · exact hall (.ident e1) List.mem_cons_self
  · exact hall (.ident e2) (by simp)

/-- The aux-chain reads against the EXTENDED candidate assignment (the
    coverage direction). -/
theorem auxChain_reads_cov {m : Model}
    {slots0 : List (String × List Value)} {dcs : List DomConstraint}
    {store : Store} {taken : List String} {vs : List Value}
    {n N : Nat}
    (hsub : ∀ s ∈ slots0.map Prod.fst, s ∈ taken)
    (hspec : ∀ j p, (modelAuxSlots m)[j]? = some p → p.1 = auxName taken j)
    (hnu : ((slots0 ++ modelAuxSlots m).map Prod.fst).Nodup)
    (halt : (extAssign store slots0 (modelAuxSlots m)).length
      = (slots0 ++ modelAuxSlots m).length)
    (hslot : ∀ j, j < N →
      (modelAuxSlots m)[n + j]?
        = some (auxName taken (n + j), [vs[j]!])) :
    ∀ j, j < N →
      ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
        (extAssign store slots0 (modelAuxSlots m)))
        (auxChain (Ident.mk (auxName taken n)) N)[j]! = some (vs[j]!) := by
  intro j hj
  have hchain : (auxChain (Ident.mk (auxName taken n)) N)[j]?
      = some (Ident.mk (auxName taken (n + j))) :=
    auxChain_getElem? (taken := taken) (n := n) (k := N) (j := j) hj
  have hget : (auxChain (Ident.mk (auxName taken n)) N)[j]!
      = Ident.mk (auxName taken (n + j)) := bang_of_getElem?_id hchain
  have hres : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
      (auxName taken (n + j)) = some (slots0.length + (n + j)) :=
    nameIndex_aux_slot (slots0 := slots0) (auxs := modelAuxSlots m)
      (taken := taken) (i := n + j) (vs := [vs[j]!])
      hsub hspec (hslot j hj)
  have hilt : n + j < (modelAuxSlots m).length :=
    (List.getElem?_eq_some_iff.mp (hslot j hj)).1
  have hstore : ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
      (extAssign store slots0 (modelAuxSlots m)))
      (Ident.mk (auxName taken (n + j)))
      = some (extAssign store slots0 (modelAuxSlots m))[slots0.length + (n + j)]! :=
    toStore_read_model (m := m) hnu halt hres
  have hpin : (extAssign store slots0 (modelAuxSlots m))[slots0.length + (n + j)]?
      = some (vs[j]!) := by
    rw [extAssign_aux_read hilt]
    have hpair : (modelAuxSlots m)[n + j]
        = (auxName taken (n + j), [vs[j]!]) := by
      have hplain : (modelAuxSlots m)[n + j]? = some (modelAuxSlots m)[n + j] :=
        List.getElem?_eq_getElem hilt
      rw [hslot j hj] at hplain
      exact (Option.some.inj hplain).symm
    rw [hpair]
    rfl
  rw [hget, hstore, bang_of_getElem? hpin]

set_option maxHeartbeats 800000
/-- `compile_covers` with AGREEMENT: the covering assignment's store
    reads every declared scalar variable exactly as the covered store. -/
theorem compile_covers_agree {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem)
    (hwf : WellFormed fullSig m)
    {store : Store}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    (hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array _ _ _ _ => False)
    (hparam : ParamHonest m store) :
    ∃ a, a ∈ allAssigns problem.domains ∧
      accepts problem a = true ∧
      ∀ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
        (.basic ty n anns none : VarDeclItem) ∈ m.variables →
        problem.toStore a n = store n := by
  -- invert the compile: the extended slot list (model slots ++ aux
  -- slots) and the compiled expanded constraints
  obtain ⟨_, slots, dcs, ⟨slots0, hslots0, hslots⟩, hcomp, hasm⟩ :=
    compileModel_ok_inv hc
  rw [hslots] at hcomp hasm
  -- the model-slot reads of the satisfying store
  have hreads := slot_reads_of_satisfying (dcs := dcs) hc hslots0 hvars
  -- the aux slots' spec (positioned names, singleton domains)
  obtain ⟨hspec, hsingle⟩ := modelAuxSlots_spec hslots0
  -- the aux names are fresh from the taken list
  have hauxfresh : ∀ (n2 : Nat) (p : String × List Value),
      (modelAuxSlots m)[n2]? = some p → p.1 ∉ auxTaken m slots0 := by
    intro n2 p hp
    have hname := hspec n2 p hp
    rw [hname]
    exact auxName_not_mem
  -- the extended candidate-space membership premise
  have hagreeVar : ∀ (ty : BasicVarType) (n : Ident) (anns : List Annotation),
      (.basic ty n anns none : VarDeclItem) ∈ m.variables →
      problem.toStore (extAssign store slots0 (modelAuxSlots m)) n = store n := by
    intro ty n anns hdmem
    have hnu0 : ((slots0 ++ modelAuxSlots m).map Prod.fst).Nodup :=
      extendedSlotNames_nodup hwf hslots0 rfl
    obtain ⟨i, hi⟩ := nameIndex_of_basic_var (m := m) hwf hslots0 ty n anns hdmem
    have hilt : i < slots0.length := by
      have h1 := (nameIndex_some (slots0.map Prod.fst) n.name i hi).1
      have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
      omega
    obtain ⟨v, hvread, _⟩ := hreads i hilt
    rw [hasm]
    exact extAssign_toStore_agree hnu0 hilt (nameIndex_ext_eq_model hi) ⟨v, hvread⟩
  refine ⟨extAssign store slots0 (modelAuxSlots m), ?_, ?_, hagreeVar⟩
  · -- membership: Fits
    have hdoms : problem.domains =
        (slots0 ++ modelAuxSlots m).map (fun p => Dom.ofList p.2) := by
      rw [hasm]
      rfl
    rw [hdoms, allAssigns_map_ofList]
    apply fits_mem_allAssigns
    refine ⟨?_, ?_⟩
    · -- the length
      rw [extAssign_length, List.length_map, List.length_append]
    · -- every read is in its slot's domain
      intro slot value hval
      by_cases hslt : slot < slots0.length
      · -- a model position: the read is the store's in-domain read
        have hap : (extAssign store slots0 (modelAuxSlots m))[slot]? =
            store (Ident.mk (slots0[slot]'hslt).1) := by
          apply extAssign_prefix_read hslt
          obtain ⟨v, hvread, hvdom⟩ := hreads slot hslt
          exact ⟨v, hvread⟩
        rw [hap] at hval
        obtain ⟨v, hvread, hvdom⟩ := hreads slot hslt
        rw [hvread] at hval
        have hvv : value = v := (Option.some.inj hval).symm
        rw [hvv]
        simp only [DomainLike.empty_list]
        rw [getD_map_snd_append_first hslt]
        exact hvdom
      · -- an aux position: the read is the singleton's pin
        have hlen : (extAssign store slots0 (modelAuxSlots m)).length
            = slots0.length + (modelAuxSlots m).length :=
          extAssign_length
        -- the read succeeded, so slot is in bounds
        have haltlt : slot < (extAssign store slots0 (modelAuxSlots m)).length :=
          (List.getElem?_eq_some_iff.mp hval).1
        -- slot = slots0.length + j for j < auxs.length
        obtain ⟨j, hj⟩ : ∃ j, slot = slots0.length + j :=
          ⟨slot - slots0.length, by omega⟩
        have hjlt : j < (modelAuxSlots m).length := by
          rw [hlen] at haltlt
          omega
        have happ : (extAssign store slots0 (modelAuxSlots m))[slot]? =
            some (modelAuxSlots m)[j].2.head! := by
          rw [hj]
          exact extAssign_aux_read hjlt
        rw [happ] at hval
        -- the aux slot's domain is the singleton [w]
        obtain ⟨w, hw⟩ := hsingle (modelAuxSlots m)[j]
          (List.getElem_mem hjlt)
        have hpin : value = w := by
          have h1 : some (modelAuxSlots m)[j].2.head! = some value := hval
          have h2 : (modelAuxSlots m)[j].2.head! = w := by
            rw [hw]
            rfl
          rw [h2] at h1
          exact (Option.some.inj h1).symm
        -- the extended domain at slot is the aux singleton
        have hdompos : ((slots0 ++ modelAuxSlots m).map Prod.snd).getD slot []
            = [w] := by
          rw [List.getD_eq_getElem?_getD, List.getElem?_map]
          -- the pair read at the extended position
          have hpairread : (slots0 ++ modelAuxSlots m)[slot]? =
              some (modelAuxSlots m)[j] := by
            rw [hj, List.getElem?_append_right
              (l₁ := slots0) (l₂ := modelAuxSlots m)
              (Nat.le_add_right slots0.length j),
              show slots0.length + j - slots0.length = j from by omega]
            exact List.getElem?_eq_getElem hjlt
          rw [hpairread]
          show ((Option.map Prod.snd (some (modelAuxSlots m)[j])).getD []) = _
          rw [Option.map_some]
          rw [hw]
          rfl
        show value ∈ ((slots0 ++ modelAuxSlots m).map Prod.snd).getD slot []
        rw [hdompos, hpin]
        exact List.mem_singleton_self _
  · -- acceptance: every compiled constraint is satisfied
    -- the expanded-list plan equation
    have hplan : expandPlan (auxTaken m slots0) [] m.constraints
        = (modelAuxSlots m, modelExpand m) := by
      have h1 := modelAuxSlots_eq hslots0
      have h2 := modelExpand_eq hslots0
      rw [h1, h2]
    -- the combined names are distinct
    have hnu : ((slots0 ++ modelAuxSlots m).map Prod.fst).Nodup :=
      extendedSlotNames_nodup hwf hslots0 rfl
    -- the model's variables are all basic initializer-free (the gate)
    have hvarsbasic : ∀ d ∈ m.variables, ∃ (ty : BasicVarType) (n : Ident)
      (anns : List Annotation), d = .basic ty n anns none :=
      compileModel_vars_basic hc
    -- the master store-agreement: every identifier of a well-formed
    -- model constraint reads the same value at the assembled store of
    -- the extended assignment as at the store itself
    have hagree : ∀ (c : ConstraintItem), c ∈ m.constraints →
        ∀ x, x ∈ (c.args.flatMap Expr.idents) →
          ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
              (extAssign store slots0 (modelAuxSlots m))) x = store x := by
      intro c hc' x hxarg
      -- Step 1: x is declared (the constraint's check resolves x in
      -- the static environment)
      have hstatic : m.staticEnv x ≠ none := by
        intro hnone
        obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hc'
        -- the argument of c whose idents contain x
        obtain ⟨e, hemem, hx2⟩ := mem_flatMap_src Expr.idents c.args x hxarg
        -- its check from the Forall2
        obtain ⟨pt, _, hchk⟩ :=
          forall2_mem (Expr.checkArg m.staticEnv) c.args params hfor e hemem
        -- case on the argument's shape
        cases e with
        | basic b =>
            cases b with
            | ident x3 =>
                -- x ∈ idents of the identifier argument: x = x3
                rcases List.mem_cons.mp hx2 with hxx | hxx
                · rw [hxx] at hnone
                  simp only [Expr.checkArg, BasicExpr.checkBase] at hchk
                  rw [hnone] at hchk
                  cases pt with
                  | basic bt => exact hchk
                  | array idx bt => exact hchk
                · cases hxx
            | lit l =>
                exfalso
                have himp : x ∈ BasicExpr.idents (.lit l) := hx2
                simp [BasicExpr.idents] at himp
        | array es =>
            cases pt with
            | basic bt =>
                exfalso
                exact hchk
            | array idx bt =>
                simp only [Expr.checkArg] at hchk
                -- x is in some element's idents
                obtain ⟨b, hbmem, hbx⟩ :=
                  mem_flatMap_src BasicExpr.idents es x hx2
                -- the element check (from the array-arm's Forall)
                have hbelem : b.checkBase m.staticEnv bt := by
                  have hall : ∀ b ∈ es, b.checkBase m.staticEnv bt :=
                    hchk.2
                  exact hall b hbmem
                cases b with
                | ident x3 =>
                    rcases List.mem_cons.mp hbx with hxx | hxx
                    · rw [hxx] at hnone
                      simp only [BasicExpr.checkBase] at hbelem
                      rw [hnone] at hbelem
                      cases hbelem
                    · cases hxx
                | lit l =>
                    exfalso
                    have himp : x ∈ BasicExpr.idents (.lit l) := hbx
                    simp [BasicExpr.idents] at himp
      -- Step 2: either x resolves at a model slot or x is a parameter
      -- (declared: variable or parameter)
      have hxdecl : (∃ d ∈ m.parameters, ParDeclItem.name d = x) ∨
          (∃ d ∈ m.variables, VarDeclItem.name d = x) := by
        unfold Model.staticEnv at hstatic
        cases hparam2 : lookupIdent x
            (m.parameters.map (fun d => (d.name, (d.type, false)))) with
        | some p =>
            obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x
              (m.parameters.map (fun d => (d.name, (d.type, false)))) p hparam2
            obtain ⟨d, hd, hdget⟩ :=
              (List.mem_map.mp hmem)
            refine Or.inl ⟨d, hd, ?_⟩
            have hyd : y = ParDeclItem.name d := (congrArg Prod.fst hdget).symm
            have hyn : y.name = x.name := hyname
            have hname : (ParDeclItem.name d).name = x.name := hyd ▸ hyn
            exact ident_eq_of_name hname
        | none =>
            cases hvar : lookupIdent x
                (m.variables.map (fun d => (d.name, (d.type, true)))) with
            | none =>
                exfalso
                apply hstatic
                rw [hparam2, hvar]
            | some p =>
                obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x
                  (m.variables.map (fun d => (d.name, (d.type, true)))) p hvar
                obtain ⟨d, hd, hdget⟩ :=
                  (List.mem_map.mp hmem)
                refine Or.inr ⟨d, hd, ?_⟩
                have hyd : y = VarDeclItem.name d := (congrArg Prod.fst hdget).symm
                have hyn : y.name = x.name := hyname
                have hname : (VarDeclItem.name d).name = x.name := hyd ▸ hyn
                exact ident_eq_of_name hname
      -- Step 3: the case analysis on the extended resolution
      by_cases hxi : ∃ i, nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
          x.name = some i
      · obtain ⟨i, hxi⟩ := hxi
        -- x resolves in the extended names; x is declared, so the
        -- resolution is at a MODEL position
        have hj := argIdent_model_position (c := c) hvarsbasic hslots0
          hauxfresh hstatic hxi
        obtain ⟨j, hj⟩ := hj
        -- the two resolutions agree: i = j
        have hij : j = i := by
          have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
              x.name = some j := nameIndex_ext_eq_model hj
          exact Option.some.inj (hext.symm.trans hxi)
        subst hij
        -- the model position's bounds
        have hjlt : j < slots0.length := by
          have h1 := (nameIndex_some (slots0.map Prod.fst) x.name j hj).1
          have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
          omega
        -- the agreement: the prefix read is the store's read at the
        -- slot's variable (which IS x)
        obtain ⟨v, hvread, _⟩ := hreads j hjlt
        exact extAssign_toStore_agree hnu hjlt hxi ⟨v, hvread⟩
      · -- parameter: nameIndex is none; toStore goes through parEnv
        have hxnone : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
            x.name = none := by
          cases h : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
              x.name with
          | none => rfl
          | some i => exact absurd ⟨i, h⟩ hxi
        show (match nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
            x.name with
          | some i => (extAssign store slots0 (modelAuxSlots m))[i]?
          | none => parEnv m x) = store x
        rw [hxnone]
        -- x is a parameter (a variable would have a model slot —
        -- contradiction with the extended none)
        rcases hxdecl with ⟨d, hd, hdname⟩ | ⟨d, hd, hdname⟩
        · -- the parameter: the scalar gate + the honest agreement
          have hscalar : ∃ v, parDeclValue d = some v := by
            cases hv : parDeclValue d with
            | none =>
                exfalso
                have hgate : m.parameters.filter
                    (fun d2 => parDeclValue d2 = none) = [] :=
                  compileModel_params_scalar hc
                have hmem : d ∈ m.parameters.filter
                    (fun d2 => parDeclValue d2 = none) :=
                  List.mem_filter.mpr ⟨hd, by rw [hv]; rfl⟩
                rw [hgate] at hmem
                exact absurd hmem (by simp)
            | some v => exact ⟨v, rfl⟩
          rw [show x = ParDeclItem.name d from hdname.symm]
          exact (parEnv_agrees hwf hslots0 hparam d hd hscalar).symm
        · -- the variable: it has a model slot (contradiction with none)
          exfalso
          obtain ⟨ty, n, anns, hshape⟩ := hvarsbasic d hd
          have hdmem : (.basic ty n anns none : VarDeclItem) ∈ m.variables :=
            hshape ▸ hd
          have ⟨i, hxi2⟩ := nameIndex_of_basic_var (m := m) hwf hslots0 ty n anns
            hdmem
          -- x IS n (both are d's name)
          have hxn : x.name = n.name := by
            have h1 : d.name = x := hdname
            have h2 : (VarDeclItem.name d).name = n.name := by
              rw [hshape]; rfl
            rw [← h1]
            rw [h2]
          rw [← hxn] at hxi2
          rw [nameIndex_ext_eq_model hxi2] at hxnone
          exact absurd hxnone (by simp)
    -- every compiled constraint is satisfied
    have hall : ∀ dc ∈ problem.constraints, dc.satisfiedB
        (extAssign store slots0 (modelAuxSlots m)) = true := by
      intro dc hdcmem
      -- the compiled list is problem.constraints (the assembly)
      have hdcs : dc ∈ dcs := by
        have hc2 : problem.constraints = dcs := by
          rw [hasm]; rfl
        exact hc2 ▸ hdcmem
      -- the compiled constraint came from an expanded constraint
      obtain ⟨c', hc'mem, hcc⟩ :=
        compileConstraints_mem_inv (modelExpand m) dcs hcomp dc hdcs
      -- the expansion's origin: an original passthrough or a piece
      rcases expandPlan_origin (taken := auxTaken m slots0) m.constraints []
        (modelAuxSlots m) (modelExpand m) hplan c' hc'mem with
        horig | ⟨c, hcmem, sh, hshape, i2, _, hpiece, hpin, hpin2, hpins⟩
      · -- an ORIGINAL constraint: the store satisfies it, the
        -- assembled store agrees, the coverage linker concludes
        have hh : c'.Holds fullInterp ((assemble m (slots0 ++ modelAuxSlots m)
            dcs).toStore (extAssign store slots0 (modelAuxSlots m))) :=
          Holds_ext_args (fun x hx => (hagree c' horig x hx).symm)
            (hcons c' horig)
        have hnuext : ((slots0 ++ modelAuxSlots m).map Prod.fst).Nodup := hnu
        have halt : (extAssign store slots0 (modelAuxSlots m)).length
            = (slots0 ++ modelAuxSlots m).length := by
          rw [extAssign_length, List.length_append]
        have hsat : dc.SatisfiedBy (extAssign store slots0 (modelAuxSlots m)) :=
          compile_holds_link hnuext halt hcc hh
        exact (DomConstraint.satisfiedB_iff dc _).mpr hsat
      · -- a PIECE of a pinning shape: the per-shape coverage
        -- the shape's pin info and the piece's membership
        -- (hpin : sh.pin = none ∨ ∃ v, sh.pin = some v ∧
        --   (modelAuxSlots m)[i2]? = some (auxName taken i2, [v]))
        -- the pieces' compiles and the store's semantic facts
        cases sh with
        | timesRK x y k =>
            -- the args inversion: c is int_times(x, y, lit k)
            have hargsc : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
                Expr.basic (.lit (.int k))] := auxShapeOf_timesRK_args hshape
            have hnamec : c.name.name = "int_times" :=
              auxShapeOf_timesRK_name hshape
            -- the store's semantic facts: store x = .int p,
            -- store y = .int q, p * q = k
            obtain ⟨p, q, hsx, hsy, hpqk⟩ : ∃ p q, store x = some (.int p) ∧
                store y = some (.int q) ∧ p * q = k := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              obtain ⟨v1, v2, v3, hv1, hv2, hv3, hargsv⟩ :=
                eval_three_inv (e3 := Expr.basic (.lit (.int k))) hmap
              have hv3' : Expr.eval store (Expr.basic (.lit (.int k)))
                  = some (.int k) := rfl
              have hv3k : v3 = Value.int k :=
                Option.some.inj (hv3.symm.trans hv3')
              subst hv3k
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_times") [v1, v2, .int k] :=
                interp_of_hname hnamec hinterp
              rw [fullInterp_std (by decide)] at h1
              have hmatch : (match [v1, v2, Value.int k] with
                | [Value.int a, Value.int b, Value.int w] => a * b = w
                | _ => False) := h1
              cases v1 with
              | int p =>
                  cases v2 with
                  | int q =>
                      exact ⟨p, q, hv1, hv2, by simpa using hmatch⟩
                  | bool w => exact absurd hmatch (by simp)
                  | setOfInt w => exact absurd hmatch (by simp)
                  | array w => exact absurd hmatch (by simp)
              | bool w => exact absurd hmatch (by simp)
              | setOfInt w => exact absurd hmatch (by simp)
              | array w => exact absurd hmatch (by simp)
            -- the piece's compile inversion: dc = timesSlot i j AUXPOS
            -- with the name resolutions
            -- the piece IS int_times(x, y, AUX)
            have hc'eq : c' =
                { name := Ident.mk "int_times"
                , args := [Expr.basic (.ident x), Expr.basic (.ident y),
                    Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2)))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the three names resolve, the form
            obtain ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the pin: the aux slot at i2 carries [.int k]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              -- the aux position: iAUX = slots0.length + i2
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              -- the model positions: x and y are declared (their args
              -- are members of the original constraint's args)
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hyarg : Expr.basic (.ident y) ∈ c.args := by
                rw [hargsc]
                exact List.mem_cons_of_mem _ List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hystatic : m.staticEnv y ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hyarg
              -- x's model position (i < slots0.length)
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hyjlt : j < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hystatic hyi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              -- the reads: a[i]? = store x, a[j]? = store y (the
              -- prefix reads at the model positions)
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                  = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
              -- the aux read: a[slots0.length + i2]? = some (the pin)
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the satisfaction
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, q, k, hareadi.trans hsx, hareadj.trans hsy,
                  hareadaux, hpqk⟩
        | timesKR x y k =>
            -- the args inversion: c is int_times(x, lit k, y)
            have hargsc : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k)),
                Expr.basic (.ident y)] := auxShapeOf_timesKR_args hshape
            have hnamec : c.name.name = "int_times" :=
              auxShapeOf_timesKR_name hshape
            -- the store's semantic facts: store x = .int p,
            -- store y = .int q, p * k = q
            obtain ⟨p, q, hsx, hsy, hpkq⟩ : ∃ p q, store x = some (.int p) ∧
                store y = some (.int q) ∧ p * k = q := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.lit (.int k))))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv2' : Expr.eval store (Expr.basic (.lit (.int k)))
                  = some (.int k) := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              have hredy : Expr.eval store (Expr.basic (.ident y))
                  = store y := rfl
              rw [hv2', hredx, hredy] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v1 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  cases hsy : store y with
                  | none => rw [hsy] at hchain; simp at hchain
                  | some v3 =>
                      rw [hsy] at hchain
                      simp only [Option.bind_some] at hchain
                      have hargsv : args = [v1, .int k, v3] := by
                        simpa using hchain.symm
                      subst hargsv
                      have h1 : fullInterp (Ident.mk "int_times") [v1, .int k, v3] :=
                        interp_of_hname hnamec hinterp
                      rw [fullInterp_std (by decide)] at h1
                      have hmatch : (match [v1, Value.int k, v3] with
                        | [Value.int a, Value.int b, Value.int w] => a * b = w
                        | _ => False) := h1
                      cases v1 with
                      | int p =>
                          cases v3 with
                          | int q =>
                              exact ⟨p, q, rfl, rfl, by simpa using hmatch⟩
                          | bool w => exact absurd hmatch (by simp)
                          | setOfInt w => exact absurd hmatch (by simp)
                          | array w => exact absurd hmatch (by simp)
                      | bool w => exact absurd hmatch (by simp)
                      | setOfInt w => exact absurd hmatch (by simp)
                      | array w => exact absurd hmatch (by simp)
            -- the piece IS int_times(x, AUX, y)
            have hc'eq : c' =
                { name := Ident.mk "int_times"
                , args := [Expr.basic (.ident x), Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident y)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the three names resolve, the form
            obtain ⟨i, iAUX, j, hxi, hAUXi, hyi, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the pin: the aux slot at i2 carries [.int k]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              -- the aux position: iAUX = slots0.length + i2
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              -- the model positions: x and y are declared
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hyarg : Expr.basic (.ident y) ∈ c.args := by
                rw [hargsc]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  List.mem_cons_self)
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hystatic : m.staticEnv y ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hyarg
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hyjlt : j < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hystatic hyi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              -- the reads
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                  = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the satisfaction
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, k, q, hareadi.trans hsx, hareadaux,
                  hareadj.trans hsy, hpkq⟩
        | timesKR' x y k =>
            -- the args inversion: c is int_times(lit k, x, y)
            have hargsc : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident x),
                Expr.basic (.ident y)] := auxShapeOf_timesKR'_args hshape
            have hnamec : c.name.name = "int_times" :=
              auxShapeOf_timesKR'_name hshape
            -- the store's semantic facts: store x = .int p,
            -- store y = .int q, k * p = q
            obtain ⟨p, q, hsx, hsy, hkpq⟩ : ∃ p q, store x = some (.int p) ∧
                store y = some (.int q) ∧ k * p = q := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.lit (.int k))))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident x)))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv1' : Expr.eval store (Expr.basic (.lit (.int k)))
                  = some (.int k) := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              have hredy : Expr.eval store (Expr.basic (.ident y))
                  = store y := rfl
              rw [hv1', hredx, hredy] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v2 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  cases hsy : store y with
                  | none => rw [hsy] at hchain; simp at hchain
                  | some v3 =>
                      rw [hsy] at hchain
                      simp only [Option.bind_some] at hchain
                      have hargsv : args = [.int k, v2, v3] := by
                        simpa using hchain.symm
                      subst hargsv
                      have h1 : fullInterp (Ident.mk "int_times") [.int k, v2, v3] :=
                        interp_of_hname hnamec hinterp
                      rw [fullInterp_std (by decide)] at h1
                      have hmatch : (match [Value.int k, v2, v3] with
                        | [Value.int a, Value.int b, Value.int w] => a * b = w
                        | _ => False) := h1
                      cases v2 with
                      | int p =>
                          cases v3 with
                          | int q =>
                              exact ⟨p, q, rfl, rfl, by simpa using hmatch⟩
                          | bool w => exact absurd hmatch (by simp)
                          | setOfInt w => exact absurd hmatch (by simp)
                          | array w => exact absurd hmatch (by simp)
                      | bool w => exact absurd hmatch (by simp)
                      | setOfInt w => exact absurd hmatch (by simp)
                      | array w => exact absurd hmatch (by simp)
            -- the piece IS int_times(AUX, x, y)
            have hc'eq : c' =
                { name := Ident.mk "int_times"
                , args := [Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x), Expr.basic (.ident y)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the three names resolve, the form
            obtain ⟨iAUX, i, j, hAUXi, hxi, hyi, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the pin: the aux slot at i2 carries [.int k]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              -- the aux position: iAUX = slots0.length + i2
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              -- the model positions: x and y are declared
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]
                exact List.mem_cons_of_mem _ List.mem_cons_self
              have hyarg : Expr.basic (.ident y) ∈ c.args := by
                rw [hargsc]
                exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                  List.mem_cons_self)
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hystatic : m.staticEnv y ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hyarg
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hyjlt : j < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hystatic hyi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              -- the reads
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                  = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the satisfaction
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨k, p, q, hareadaux, hareadi.trans hsx,
                  hareadj.trans hsy, hkpq⟩
        | timesRKK x k k' =>
            -- the args inversion: c is int_times(x, lit k, lit k')
            have hargsc : c.args = [Expr.basic (.ident x), Expr.basic (.lit (.int k)),
                Expr.basic (.lit (.int k'))] := auxShapeOf_timesRKK_args hshape
            have hnamec : c.name.name = "int_times" :=
              auxShapeOf_timesRKK_name hshape
            -- the store's semantic facts: store x = .int p, p * k = k'
            obtain ⟨p, hsx, hpkk'⟩ : ∃ p, store x = some (.int p) ∧ p * k = k' := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.lit (.int k))))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.lit (.int k'))))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv2' : Expr.eval store (Expr.basic (.lit (.int k)))
                  = some (.int k) := rfl
              have hv3' : Expr.eval store (Expr.basic (.lit (.int k')))
                  = some (.int k') := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              rw [hredx, hv2', hv3'] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v1 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  have hargsv : args = [v1, .int k, .int k'] := by
                    simpa using hchain.symm
                  subst hargsv
                  have h1 : fullInterp (Ident.mk "int_times") [v1, .int k, .int k'] :=
                    interp_of_hname hnamec hinterp
                  rw [fullInterp_std (by decide)] at h1
                  have hmatch : (match [v1, Value.int k, Value.int k'] with
                    | [Value.int a, Value.int b, Value.int w] => a * b = w
                    | _ => False) := h1
                  cases v1 with
                  | int p => exact ⟨p, rfl, by simpa using hmatch⟩
                  | bool w => exact absurd hmatch (by simp)
                  | setOfInt w => exact absurd hmatch (by simp)
                  | array w => exact absurd hmatch (by simp)
            -- the piece IS int_times(x, AUX₁, AUX₂)
            have hc'eq : c' =
                { name := Ident.mk "int_times"
                , args := [Expr.basic (.ident x), Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) (i2 + 1))))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the three names resolve, the form
            obtain ⟨i, iAUX1, iAUX2, hxi, hAUX1i, hAUX2i, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the two pins: the aux slots at i2 and i2+1
            obtain ⟨hp1, hp2⟩ := And.intro hpin hpin2
            rcases hp1 with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              rcases hp2 with hpin2none | ⟨v2, hpin2v, hslot2get⟩
              · rw [AuxShape.pin2] at hpin2none; exact absurd hpin2none (by simp)
              · rw [AuxShape.pin2] at hpin2v
                have hvk' : v2 = Value.int k' :=
                  (Option.some.inj hpin2v).symm
                subst hvk'
                -- the two aux positions
                have hnlt : i2 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslotget).1
                have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslot2get).1
                have hAUX1pos : iAUX1 = slots0.length + i2 := by
                  have hres := nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2)
                    (vs := [Value.int k])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    hspec hslotget
                  have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                      = auxName (auxTaken m slots0) i2 := rfl
                  rw [hAUXname] at hAUX1i
                  rw [hres] at hAUX1i
                  exact (Option.some.inj hAUX1i).symm
                have hAUX2pos : iAUX2 = slots0.length + (i2 + 1) := by
                  have hres := nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2 + 1)
                    (vs := [Value.int k'])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    hspec hslot2get
                  have hAUX2name : (Ident.mk
                      (auxName (auxTaken m slots0) (i2 + 1))).name
                      = auxName (auxTaken m slots0) (i2 + 1) := rfl
                  rw [hAUX2name] at hAUX2i
                  rw [hres] at hAUX2i
                  exact (Option.some.inj hAUX2i).symm
                rw [hdcform, hAUX1pos, hAUX2pos]
                -- x's model position
                have hxarg : Expr.basic (.ident x) ∈ c.args := by
                  rw [hargsc]; exact List.mem_cons_self
                have hxstatic : m.staticEnv x ≠ none :=
                  staticEnv_of_ident_arg hwf hcmem hxarg
                have hxilt : i < slots0.length := by
                  obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                    hvarsbasic hslots0 hauxfresh hxstatic hxi
                  have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      x.name = some j2 := nameIndex_ext_eq_model hj2
                  have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                  subst hji
                  have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                  omega
                -- the reads
                obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
                have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                    = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
                have hareadaux1 :
                    (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                      = some (Value.int k) := by
                  rw [extAssign_aux_read hnlt]
                  have hpair : (modelAuxSlots m)[i2]
                      = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                    have hplain : (modelAuxSlots m)[i2]?
                        = some (modelAuxSlots m)[i2] :=
                      List.getElem?_eq_getElem hnlt
                    rw [hslotget] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                have hareadaux2 :
                    (extAssign store slots0 (modelAuxSlots m))[slots0.length + (i2 + 1)]?
                      = some (Value.int k') := by
                  rw [extAssign_aux_read hnlt2]
                  have hpair : (modelAuxSlots m)[i2 + 1]
                      = (auxName (auxTaken m slots0) (i2 + 1), [Value.int k']) := by
                    have hplain : (modelAuxSlots m)[i2 + 1]?
                        = some (modelAuxSlots m)[i2 + 1] :=
                      List.getElem?_eq_getElem hnlt2
                    rw [hslot2get] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                -- the satisfaction
                exact (DomConstraint.satisfiedB_iff _ _).mpr
                  ⟨p, k, k', hareadi.trans hsx, hareadaux1,
                    hareadaux2, hpkk'⟩
        | timesKRR x k k' =>
            -- the args inversion: c is int_times(lit k, x, lit k')
            have hargsc : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.ident x),
                Expr.basic (.lit (.int k'))] := auxShapeOf_timesKRR_args hshape
            have hnamec : c.name.name = "int_times" :=
              auxShapeOf_timesKRR_name hshape
            -- the store's semantic facts: store x = .int p, k * p = k'
            obtain ⟨p, hsx, hkpk'⟩ : ∃ p, store x = some (.int p) ∧ k * p = k' := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.lit (.int k))))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident x)))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.lit (.int k'))))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv1' : Expr.eval store (Expr.basic (.lit (.int k)))
                  = some (.int k) := rfl
              have hv3' : Expr.eval store (Expr.basic (.lit (.int k')))
                  = some (.int k') := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              rw [hv1', hredx, hv3'] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v2 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  have hargsv : args = [.int k, v2, .int k'] := by
                    simpa using hchain.symm
                  subst hargsv
                  have h1 : fullInterp (Ident.mk "int_times") [.int k, v2, .int k'] :=
                    interp_of_hname hnamec hinterp
                  rw [fullInterp_std (by decide)] at h1
                  have hmatch : (match [Value.int k, v2, Value.int k'] with
                    | [Value.int a, Value.int b, Value.int w] => a * b = w
                    | _ => False) := h1
                  cases v2 with
                  | int p => exact ⟨p, rfl, by simpa using hmatch⟩
                  | bool w => exact absurd hmatch (by simp)
                  | setOfInt w => exact absurd hmatch (by simp)
                  | array w => exact absurd hmatch (by simp)
            -- the piece IS int_times(AUX₁, x, AUX₂)
            have hc'eq : c' =
                { name := Ident.mk "int_times"
                , args := [Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x), Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) (i2 + 1))))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the three names resolve, the form
            obtain ⟨iAUX1, i, iAUX2, hAUX1i, hxi, hAUX2i, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the two pins: the aux slots at i2 and i2+1
            obtain ⟨hp1, hp2⟩ := And.intro hpin hpin2
            rcases hp1 with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              rcases hp2 with hpin2none | ⟨v2, hpin2v, hslot2get⟩
              · rw [AuxShape.pin2] at hpin2none; exact absurd hpin2none (by simp)
              · rw [AuxShape.pin2] at hpin2v
                have hvk' : v2 = Value.int k' :=
                  (Option.some.inj hpin2v).symm
                subst hvk'
                -- the two aux positions
                have hnlt : i2 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslotget).1
                have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslot2get).1
                have hAUX1pos : iAUX1 = slots0.length + i2 := by
                  have hres := nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2)
                    (vs := [Value.int k])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    hspec hslotget
                  have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                      = auxName (auxTaken m slots0) i2 := rfl
                  rw [hAUXname] at hAUX1i
                  rw [hres] at hAUX1i
                  exact (Option.some.inj hAUX1i).symm
                have hAUX2pos : iAUX2 = slots0.length + (i2 + 1) := by
                  have hres := nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2 + 1)
                    (vs := [Value.int k'])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    hspec hslot2get
                  have hAUX2name : (Ident.mk
                      (auxName (auxTaken m slots0) (i2 + 1))).name
                      = auxName (auxTaken m slots0) (i2 + 1) := rfl
                  rw [hAUX2name] at hAUX2i
                  rw [hres] at hAUX2i
                  exact (Option.some.inj hAUX2i).symm
                rw [hdcform, hAUX1pos, hAUX2pos]
                -- x's model position
                have hxarg : Expr.basic (.ident x) ∈ c.args := by
                  rw [hargsc]
                  exact List.mem_cons_of_mem _ List.mem_cons_self
                have hxstatic : m.staticEnv x ≠ none :=
                  staticEnv_of_ident_arg hwf hcmem hxarg
                have hxilt : i < slots0.length := by
                  obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                    hvarsbasic hslots0 hauxfresh hxstatic hxi
                  have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      x.name = some j2 := nameIndex_ext_eq_model hj2
                  have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                  subst hji
                  have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                  omega
                -- the reads
                obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
                have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                    = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
                have hareadaux1 :
                    (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                      = some (Value.int k) := by
                  rw [extAssign_aux_read hnlt]
                  have hpair : (modelAuxSlots m)[i2]
                      = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                    have hplain : (modelAuxSlots m)[i2]?
                        = some (modelAuxSlots m)[i2] :=
                      List.getElem?_eq_getElem hnlt
                    rw [hslotget] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                have hareadaux2 :
                    (extAssign store slots0 (modelAuxSlots m))[slots0.length + (i2 + 1)]?
                      = some (Value.int k') := by
                  rw [extAssign_aux_read hnlt2]
                  have hpair : (modelAuxSlots m)[i2 + 1]
                      = (auxName (auxTaken m slots0) (i2 + 1), [Value.int k']) := by
                    have hplain : (modelAuxSlots m)[i2 + 1]?
                        = some (modelAuxSlots m)[i2 + 1] :=
                      List.getElem?_eq_getElem hnlt2
                    rw [hslot2get] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                -- the satisfaction
                exact (DomConstraint.satisfiedB_iff _ _).mpr
                  ⟨k, p, k', hareadaux1, hareadi.trans hsx,
                    hareadaux2, hkpk'⟩
        | timesKKR x k k' =>
            -- the args inversion: c is int_times(lit k, lit k', x)
            have hargsc : c.args = [Expr.basic (.lit (.int k)), Expr.basic (.lit (.int k')),
                Expr.basic (.ident x)] := auxShapeOf_timesKKR_args hshape
            have hnamec : c.name.name = "int_times" :=
              auxShapeOf_timesKKR_name hshape
            -- the store's semantic facts: store x = .int p, k * k' = p
            obtain ⟨p, hsx, hkk'p⟩ : ∃ p, store x = some (.int p) ∧ k * k' = p := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.lit (.int k))))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.lit (.int k'))))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.ident x)))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv1' : Expr.eval store (Expr.basic (.lit (.int k)))
                  = some (.int k) := rfl
              have hv2' : Expr.eval store (Expr.basic (.lit (.int k')))
                  = some (.int k') := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              rw [hv1', hv2', hredx] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v3 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  have hargsv : args = [.int k, .int k', v3] := by
                    simpa using hchain.symm
                  subst hargsv
                  have h1 : fullInterp (Ident.mk "int_times") [.int k, .int k', v3] :=
                    interp_of_hname hnamec hinterp
                  rw [fullInterp_std (by decide)] at h1
                  have hmatch : (match [Value.int k, Value.int k', v3] with
                    | [Value.int a, Value.int b, Value.int w] => a * b = w
                    | _ => False) := h1
                  cases v3 with
                  | int p => exact ⟨p, rfl, by simpa using hmatch⟩
                  | bool w => exact absurd hmatch (by simp)
                  | setOfInt w => exact absurd hmatch (by simp)
                  | array w => exact absurd hmatch (by simp)
            -- the piece IS int_times(AUX₁, AUX₂, x)
            have hc'eq : c' =
                { name := Ident.mk "int_times"
                , args := [Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) (i2 + 1)))),
                    Expr.basic (.ident x)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the three names resolve, the form
            obtain ⟨iAUX1, iAUX2, i, hAUX1i, hAUX2i, hxi, hdcform⟩ :=
              compileConstraint_int_times3_inv hcc
            -- the two pins: the aux slots at i2 and i2+1
            obtain ⟨hp1, hp2⟩ := And.intro hpin hpin2
            rcases hp1 with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              rcases hp2 with hpin2none | ⟨v2, hpin2v, hslot2get⟩
              · rw [AuxShape.pin2] at hpin2none; exact absurd hpin2none (by simp)
              · rw [AuxShape.pin2] at hpin2v
                have hvk' : v2 = Value.int k' :=
                  (Option.some.inj hpin2v).symm
                subst hvk'
                -- the two aux positions
                have hnlt : i2 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslotget).1
                have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslot2get).1
                have hAUX1pos : iAUX1 = slots0.length + i2 := by
                  have hres := nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2)
                    (vs := [Value.int k])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    hspec hslotget
                  have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                      = auxName (auxTaken m slots0) i2 := rfl
                  rw [hAUXname] at hAUX1i
                  rw [hres] at hAUX1i
                  exact (Option.some.inj hAUX1i).symm
                have hAUX2pos : iAUX2 = slots0.length + (i2 + 1) := by
                  have hres := nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2 + 1)
                    (vs := [Value.int k'])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    hspec hslot2get
                  have hAUX2name : (Ident.mk
                      (auxName (auxTaken m slots0) (i2 + 1))).name
                      = auxName (auxTaken m slots0) (i2 + 1) := rfl
                  rw [hAUX2name] at hAUX2i
                  rw [hres] at hAUX2i
                  exact (Option.some.inj hAUX2i).symm
                rw [hdcform, hAUX1pos, hAUX2pos]
                -- x's model position
                have hxarg : Expr.basic (.ident x) ∈ c.args := by
                  rw [hargsc]
                  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
                    List.mem_cons_self)
                have hxstatic : m.staticEnv x ≠ none :=
                  staticEnv_of_ident_arg hwf hcmem hxarg
                have hxilt : i < slots0.length := by
                  obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                    hvarsbasic hslots0 hauxfresh hxstatic hxi
                  have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      x.name = some j2 := nameIndex_ext_eq_model hj2
                  have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                  subst hji
                  have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                  omega
                -- the reads
                obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
                have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                    = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
                have hareadaux1 :
                    (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                      = some (Value.int k) := by
                  rw [extAssign_aux_read hnlt]
                  have hpair : (modelAuxSlots m)[i2]
                      = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                    have hplain : (modelAuxSlots m)[i2]?
                        = some (modelAuxSlots m)[i2] :=
                      List.getElem?_eq_getElem hnlt
                    rw [hslotget] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                have hareadaux2 :
                    (extAssign store slots0 (modelAuxSlots m))[slots0.length + (i2 + 1)]?
                      = some (Value.int k') := by
                  rw [extAssign_aux_read hnlt2]
                  have hpair : (modelAuxSlots m)[i2 + 1]
                      = (auxName (auxTaken m slots0) (i2 + 1), [Value.int k']) := by
                    have hplain : (modelAuxSlots m)[i2 + 1]?
                        = some (modelAuxSlots m)[i2 + 1] :=
                      List.getElem?_eq_getElem hnlt2
                    rw [hslot2get] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                -- the satisfaction
                exact (DomConstraint.satisfiedB_iff _ _).mpr
                  ⟨k, k', p, hareadaux1, hareadaux2,
                    hareadi.trans hsx, hkk'p⟩
        | neRK x k =>
            -- the args + name inversion: c is int_ne(x, lit k)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neRK_inv hshape
            -- the store's semantic facts: store x = .int p, p ≠ k
            obtain ⟨p, hsx, hpne⟩ : ∃ p, store x = some (.int p) ∧ p ≠ k := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, hsx, hargsv⟩ := mapM_two_const hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_ne") [vx, .int k] :=
                interp_of_hname hnamec hinterp
              rw [fullInterp_std (by decide)] at h1
              have hmatch : (match [vx, Value.int k] with
                | [Value.int a, Value.int b] => a ≠ b
                | _ => False) := h1
              cases vx with
              | int p =>
                  exact ⟨p, hsx, by simpa using hmatch⟩
              | bool w => exact absurd hmatch (by simp)
              | setOfInt w => exact absurd hmatch (by simp)
              | array w => exact absurd hmatch (by simp)
            -- the piece IS int_ne(x, AUX)
            have hc'eq : c' =
                { name := Ident.mk "int_ne"
                , args := [Expr.basic (.ident x), Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2)))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the two names resolve, the form
            obtain ⟨i, iAUX, hxi, hAUXi, hdcform⟩ :=
              compileConstraint_int_ne2_inv hcc
            -- the pin: the aux slot at i2 carries [.int k]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              -- the aux position: iAUX = slots0.length + i2
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              -- x's model position: x is declared
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              -- the reads
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the satisfaction
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨Value.int p, Value.int k, hareadi.trans hsx, hareadaux,
                  by
                    intro hcon
                    exact hpne (Value.int.inj hcon)⟩
        | neKR x k =>
            -- the args + name inversion: c is int_ne(lit k, x)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neKR_inv hshape
            -- the store's semantic facts: store x = .int p, p ≠ k
            obtain ⟨p, hsx, hpne⟩ : ∃ p, store x = some (.int p) ∧ p ≠ k := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, hsx, hargsv⟩ := mapM_two_const' hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_ne") [.int k, vx] :=
                interp_of_hname hnamec hinterp
              rw [fullInterp_std (by decide)] at h1
              have hmatch : (match [Value.int k, vx] with
                | [Value.int a, Value.int b] => a ≠ b
                | _ => False) := h1
              cases vx with
              | int p =>
                  exact ⟨p, hsx, Ne.symm (by simpa using hmatch)⟩
              | bool w => exact absurd hmatch (by simp)
              | setOfInt w => exact absurd hmatch (by simp)
              | array w => exact absurd hmatch (by simp)
            -- the piece IS int_ne(AUX, x)
            have hc'eq : c' =
                { name := Ident.mk "int_ne"
                , args := [Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the compile inversion: the two names resolve, the form
            obtain ⟨iAUX, i, hAUXi, hxi, hdcform⟩ :=
              compileConstraint_int_ne2_inv hcc
            -- the pin: the aux slot at i2 carries [.int k]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              -- the aux position: iAUX = slots0.length + i2
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              -- x's model position: x is declared
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]
                exact List.mem_cons_of_mem _ List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              -- the reads
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the satisfaction
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨Value.int k, Value.int p, hareadaux, hareadi.trans hsx,
                  by
                    intro hcon
                    exact hpne (Value.int.inj hcon).symm⟩
        | eqReifRK x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_eqReifRK_inv hshape
            obtain ⟨p, rb, hsx, hsr, hR⟩ : ∃ (p : Int) (rb : Bool), store x = some (.int p) ∧
                store r = some (.bool rb) ∧ (rb = true ↔ p = k) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := mapM_ident_const_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_eq_reif") [vx, .int k, vr] :=
                interp_of_hname hnamec hinterp
              cases vx with
              | int p =>
                  cases vr with
                  | bool rb => exact ⟨p, rb, hsx, hsr, (fullInterp_int_eq_reif_iff p k rb).mp h1⟩
                  | int w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
                  | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
                  | array w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
              | bool w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
              | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
              | array w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
            have hc'eq : c' =
                { name := Ident.mk "int_eq_reif"
                , args := [Expr.basic (.ident x),
                    Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
              compileConstraint_int_eq_reif_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident r) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv r ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    r.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) r.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store r := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, k, rb, hareadi.trans hsx, hareadaux, hareadr.trans hsr, hR⟩
        | eqReifKR x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_eqReifKR_inv hshape
            obtain ⟨p, rb, hsx, hsr, hR⟩ : ∃ (p : Int) (rb : Bool), store x = some (.int p) ∧
                store r = some (.bool rb) ∧ (rb = true ↔ k = p) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := mapM_const_ident_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_eq_reif") [.int k, vx, vr] :=
                interp_of_hname hnamec hinterp
              cases vx with
              | int p =>
                  cases vr with
                  | bool rb => exact ⟨p, rb, hsx, hsr, (fullInterp_int_eq_reif_iff k p rb).mp h1⟩
                  | int w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
                  | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
                  | array w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
              | bool w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
              | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
              | array w => exfalso; rw [fullInterp_of_extracted_reif "int_eq_reif" (Or.inl rfl)] at h1; exact h1.elim
            have hc'eq : c' =
                { name := Ident.mk "int_eq_reif"
                , args := [Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x), Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
              compileConstraint_int_eq_reif_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident r) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv r ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    r.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) r.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store r := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨k, p, rb, hareadaux, hareadi.trans hsx, hareadr.trans hsr, hR⟩
        | leReifRK x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_leReifRK_inv hshape
            obtain ⟨p, rb, hsx, hsr, hR⟩ : ∃ (p : Int) (rb : Bool), store x = some (.int p) ∧
                store r = some (.bool rb) ∧ (rb = true ↔ p ≤ k) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := mapM_ident_const_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_le_reif") [vx, .int k, vr] :=
                interp_of_hname hnamec hinterp
              cases vx with
              | int p =>
                  cases vr with
                  | bool rb => exact ⟨p, rb, hsx, hsr, (fullInterp_int_le_reif_iff p k rb).mp h1⟩
                  | int w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
                  | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
                  | array w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
              | bool w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
              | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
              | array w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
            have hc'eq : c' =
                { name := Ident.mk "int_le_reif"
                , args := [Expr.basic (.ident x),
                    Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
              compileConstraint_int_le_reif_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident r) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv r ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    r.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) r.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store r := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, k, rb, hareadi.trans hsx, hareadaux, hareadr.trans hsr, hR⟩
        | leReifKR x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_leReifKR_inv hshape
            obtain ⟨p, rb, hsx, hsr, hR⟩ : ∃ (p : Int) (rb : Bool), store x = some (.int p) ∧
                store r = some (.bool rb) ∧ (rb = true ↔ k ≤ p) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := mapM_const_ident_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_le_reif") [.int k, vx, vr] :=
                interp_of_hname hnamec hinterp
              cases vx with
              | int p =>
                  cases vr with
                  | bool rb => exact ⟨p, rb, hsx, hsr, (fullInterp_int_le_reif_iff k p rb).mp h1⟩
                  | int w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
                  | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
                  | array w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
              | bool w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
              | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
              | array w => exfalso; rw [fullInterp_of_extracted_reif "int_le_reif" (Or.inr (Or.inl rfl))] at h1; exact h1.elim
            have hc'eq : c' =
                { name := Ident.mk "int_le_reif"
                , args := [Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x), Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
              compileConstraint_int_le_reif_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident r) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv r ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    r.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) r.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store r := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨k, p, rb, hareadaux, hareadi.trans hsx, hareadr.trans hsr, hR⟩
        | neReifRK x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neReifRK_inv hshape
            obtain ⟨p, rb, hsx, hsr, hR⟩ : ∃ (p : Int) (rb : Bool), store x = some (.int p) ∧
                store r = some (.bool rb) ∧ (rb = true ↔ p ≠ k) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := mapM_ident_const_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_ne_reif") [vx, .int k, vr] :=
                interp_of_hname hnamec hinterp
              cases vx with
              | int p =>
                  cases vr with
                  | bool rb => exact ⟨p, rb, hsx, hsr, (fullInterp_int_ne_reif_iff p k rb).mp h1⟩
                  | int w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
                  | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
                  | array w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
              | bool w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
              | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
              | array w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
            have hc'eq : c' =
                { name := Ident.mk "int_ne_reif"
                , args := [Expr.basic (.ident x),
                    Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
              compileConstraint_int_ne_reif_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident r) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv r ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    r.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) r.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store r := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, k, rb, hareadi.trans hsx, hareadaux, hareadr.trans hsr, hR⟩
        | neReifKR x r k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_neReifKR_inv hshape
            obtain ⟨p, rb, hsx, hsr, hR⟩ : ∃ (p : Int) (rb : Bool), store x = some (.int p) ∧
                store r = some (.bool rb) ∧ (rb = true ↔ k ≠ p) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vr, hsx, hsr, hargsv⟩ := mapM_const_ident_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_ne_reif") [.int k, vx, vr] :=
                interp_of_hname hnamec hinterp
              cases vx with
              | int p =>
                  cases vr with
                  | bool rb => exact ⟨p, rb, hsx, hsr, (fullInterp_int_ne_reif_iff k p rb).mp h1⟩
                  | int w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
                  | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
                  | array w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
              | bool w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
              | setOfInt w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
              | array w => exfalso; rw [fullInterp_of_extracted_reif "int_ne_reif" (Or.inr (Or.inr (Or.inl rfl)))] at h1; exact h1.elim
            have hc'eq : c' =
                { name := Ident.mk "int_ne_reif"
                , args := [Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x), Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
              compileConstraint_int_ne_reif_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident r) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv r ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    r.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) r.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store r := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨k, p, rb, hareadaux, hareadi.trans hsx, hareadr.trans hsr, hR⟩
        | minRK x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minRK_inv hshape
            obtain ⟨p, w, hsx, hsr, hR⟩ : ∃ (p w : Int), store x = some (.int p) ∧
                store z = some (.int w) ∧ w = min p k := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vz, hsx, hsr, hargsv⟩ := mapM_ident_const_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_min") [vx, .int k, vz] :=
                interp_of_hname hnamec hinterp
              cases vx <;> cases vz <;>
                first
                | exact ⟨_, _, hsx, hsr, (fullInterp_int_min_iff _ _ _).mp h1⟩
                | (exfalso; rw [fullInterp_std (by decide)] at h1; exact h1.elim)
            have hc'eq : c' =
                { name := Ident.mk "int_min"
                , args := [Expr.basic (.ident x),
                    Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident z)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
              compileConstraint_int_min_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident z) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv z ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    z.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) z.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store z := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, k, w, hareadi.trans hsx, hareadaux, hareadr.trans hsr, hR.symm⟩
        | minKR x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minKR_inv hshape
            obtain ⟨p, w, hsx, hsr, hR⟩ : ∃ (p w : Int), store x = some (.int p) ∧
                store z = some (.int w) ∧ w = min k p := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vz, hsx, hsr, hargsv⟩ := mapM_const_ident_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_min") [.int k, vx, vz] :=
                interp_of_hname hnamec hinterp
              cases vx <;> cases vz <;>
                first
                | exact ⟨_, _, hsx, hsr, (fullInterp_int_min_iff _ _ _).mp h1⟩
                | (exfalso; rw [fullInterp_std (by decide)] at h1; exact h1.elim)
            have hc'eq : c' =
                { name := Ident.mk "int_min"
                , args := [Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x), Expr.basic (.ident z)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
              compileConstraint_int_min_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident z) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv z ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    z.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) z.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store z := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨k, p, w, hareadaux, hareadi.trans hsx, hareadr.trans hsr, hR.symm⟩
        | maxRK x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxRK_inv hshape
            obtain ⟨p, w, hsx, hsr, hR⟩ : ∃ (p w : Int), store x = some (.int p) ∧
                store z = some (.int w) ∧ w = max p k := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vz, hsx, hsr, hargsv⟩ := mapM_ident_const_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_max") [vx, .int k, vz] :=
                interp_of_hname hnamec hinterp
              cases vx <;> cases vz <;>
                first
                | exact ⟨_, _, hsx, hsr, (fullInterp_int_max_iff _ _ _).mp h1⟩
                | (exfalso; rw [fullInterp_std (by decide)] at h1; exact h1.elim)
            have hc'eq : c' =
                { name := Ident.mk "int_max"
                , args := [Expr.basic (.ident x),
                    Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident z)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, iAUX, ir, hxi, hAUXi, hri, hdcform⟩ :=
              compileConstraint_int_max_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident z) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv z ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    z.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) z.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store z := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, k, w, hareadi.trans hsx, hareadaux, hareadr.trans hsr, hR.symm⟩
        | maxKR x z k =>
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxKR_inv hshape
            obtain ⟨p, w, hsx, hsr, hR⟩ : ∃ (p w : Int), store x = some (.int p) ∧
                store z = some (.int w) ∧ w = max k p := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vz, hsx, hsr, hargsv⟩ := mapM_const_ident_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_max") [.int k, vx, vz] :=
                interp_of_hname hnamec hinterp
              cases vx <;> cases vz <;>
                first
                | exact ⟨_, _, hsx, hsr, (fullInterp_int_max_iff _ _ _).mp h1⟩
                | (exfalso; rw [fullInterp_std (by decide)] at h1; exact h1.elim)
            have hc'eq : c' =
                { name := Ident.mk "int_max"
                , args := [Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2))),
                    Expr.basic (.ident x), Expr.basic (.ident z)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨iAUX, i, ir, hAUXi, hxi, hri, hdcform⟩ :=
              compileConstraint_int_max_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hrarg : Expr.basic (.ident z) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
              have hrstatic : m.staticEnv z ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hrarg
              have hrlt : ir < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hrstatic hri
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    z.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : ir = j2 := Option.some.inj (hri.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) z.name ir hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v3, hv3read, _⟩ := hreads ir hrlt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadr : (extAssign store slots0 (modelAuxSlots m))[ir]?
                  = store z := extAssign_read_ident hrlt hri ⟨v3, hv3read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨k, p, w, hareadaux, hareadi.trans hsx, hareadr.trans hsr, hR.symm⟩
        | minRRK x y k =>
            -- PLAN C9 remainder: the literal is the RESULT operand
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minRRK_inv hshape
            obtain ⟨p, q, hsx, hsy, hR⟩ : ∃ (p q : Int), store x = some (.int p) ∧
                store y = some (.int q) ∧ k = min p q := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_ident_ident_const hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_min") [vx, vy, .int k] :=
                interp_of_hname hnamec hinterp
              cases vx <;> cases vy <;>
                first
                | exact ⟨_, _, hsx, hsy, (fullInterp_int_min_iff _ _ _).mp h1⟩
                | (exfalso; rw [fullInterp_std (by decide)] at h1; exact h1.elim)
            have hc'eq : c' =
                { name := Ident.mk "int_min"
                , args := [Expr.basic (.ident x), Expr.basic (.ident y),
                    Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2)))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ :=
              compileConstraint_int_min_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hyarg : Expr.basic (.ident y) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hystatic : m.staticEnv y ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hyarg
              have hylt : j < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hystatic hyi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v2, hv2read, _⟩ := hreads j hylt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                  = store y := extAssign_read_ident hylt hyi ⟨v2, hv2read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, q, k, hareadi.trans hsx, hareadj.trans hsy, hareadaux, hR.symm⟩
        | maxRRK x y k =>
            -- PLAN C9 remainder: the literal is the RESULT operand
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxRRK_inv hshape
            obtain ⟨p, q, hsx, hsy, hR⟩ : ∃ (p q : Int), store x = some (.int p) ∧
                store y = some (.int q) ∧ k = max p q := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vy, hsx, hsy, hargsv⟩ := mapM_ident_ident_const hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "int_max") [vx, vy, .int k] :=
                interp_of_hname hnamec hinterp
              cases vx <;> cases vy <;>
                first
                | exact ⟨_, _, hsx, hsy, (fullInterp_int_max_iff _ _ _).mp h1⟩
                | (exfalso; rw [fullInterp_std (by decide)] at h1; exact h1.elim)
            have hc'eq : c' =
                { name := Ident.mk "int_max"
                , args := [Expr.basic (.ident x), Expr.basic (.ident y),
                    Expr.basic (.ident (Ident.mk (auxName (auxTaken m slots0) i2)))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ :=
              compileConstraint_int_max_inv hcc
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxlt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              have hyarg : Expr.basic (.ident y) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
              have hystatic : m.staticEnv y ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hyarg
              have hylt : j < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hystatic hyi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxlt
              obtain ⟨v2, hv2read, _⟩ := hreads j hylt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxlt hxi ⟨v1, hv1read⟩
              have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                  = store y := extAssign_read_ident hylt hyi ⟨v2, hv2read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨p, q, k, hareadi.trans hsx, hareadj.trans hsy, hareadaux, hR.symm⟩
        | minGen2 e1 e2 r =>
            -- PLAN C9 remainder: the two-element array minimum chains
            -- over the element slots themselves (no aux slot)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_minGen2_inv hshape
            have hpred : m.predicates = [] := compileModel_predicates_nil hc
            -- the piece: int_min(e₁, e₂, r) → minSlot i j k
            have hc'eq : c' =
                { name := Ident.mk "int_min"
                , args := [Expr.basic (.ident e1), Expr.basic (.ident e2),
                    Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, j, k, hxi, hyi, hki, hdcform⟩ :=
              compileConstraint_int_min_inv hcc
            rw [hdcform]
            -- the WF typing of the array's element slots
            have hcb := checkBase_int_of_array_elem hpred hwf hcmem
              (Or.inl hnamec) hargsc
            have h1static : m.staticEnv e1 ≠ none := by
              intro hcon
              have hcb1 := hcb.1
              simp only [BasicExpr.checkBase] at hcb1
              rw [hcon] at hcb1
              exact hcb1
            have h2static : m.staticEnv e2 ≠ none := by
              intro hcon
              have hcb2 := hcb.2
              simp only [BasicExpr.checkBase] at hcb2
              rw [hcon] at hcb2
              exact hcb2
            -- the store's semantic facts (the element reads are
            -- integers: the second one by the WF-typed element slots)
            obtain ⟨p, q, hs1, hs2, hsr⟩ : ∃ (p q : Int),
                store e1 = some (.int p) ∧ store e2 = some (.int q) ∧
                store r = some (.int (min p q)) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vr, v1, v2, hsr, hs1, hs2, hargsv⟩ :=
                mapM_ident_ident_arr hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "array_int_minimum")
                  [vr, .array [v1, v2]] := interp_of_hname hnamec hinterp
              -- the interpreted reading, in the `minValue` match form
              have hsem : (match [vr, .array [v1, v2]] with
                  | [.int m, .array xs] => minValue xs = some m
                  | _ => False) := by
                rw [fullInterp_std (by decide)] at h1
                exact h1
              -- the second element's integer read (the WF typing fact)
              have h2int : ∃ q, v2 = Value.int q := by
                obtain ⟨j2, hj2⟩ :=
                  argIdent_model_position (c := c)
                    hvarsbasic hslots0 hauxfresh h2static hyi
                have hj2lt : j2 < slots0.length := by
                  have h1' := (nameIndex_some (slots0.map Prod.fst) e2.name j2 hj2).1
                  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                  omega
                obtain ⟨q, hq⟩ := store_int_read_of_slot_checkArg hwf hslots0
                  hvars hcb.2 hj2 hj2lt
                exact ⟨q, Option.some.inj (hs2.symm.trans hq)⟩
              obtain ⟨q, hv2⟩ := h2int
              subst hv2
              -- the result read forces the first element's integer read
              -- (the `minValue` reading's head)
              cases vr with
              | int m =>
                  have hsem2 : minValue [v1, Value.int q] = some m := hsem
                  obtain ⟨p, hv1p, hmin⟩ := minValue_pair_int_tail hsem2
                  subst hv1p
                  refine ⟨p, q, hs1, hs2, ?_⟩
                  rw [← hmin] at hsr
                  exact hsr
              | bool b => exact (hsem : False).elim
              | setOfInt s => exact (hsem : False).elim
              | array xs => exact (hsem : False).elim
            -- the extended positions are MODEL positions
            have hrarg : Expr.basic (.ident r) ∈ c.args := by
              rw [hargsc]; exact List.mem_cons_self
            have hrstatic : m.staticEnv r ≠ none :=
              staticEnv_of_ident_arg hwf hcmem hrarg
            have hx0 := argIdent_model_position (c := c)
              hvarsbasic hslots0 hauxfresh h1static hxi
            obtain ⟨i0, hi0⟩ := hx0
            have hii : i = i0 := by
              have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  e1.name = some i0 := nameIndex_ext_eq_model hi0
              exact Option.some.inj (hxi.symm.trans hext)
            subst hii
            have hxlt : i < slots0.length := by
              have h1' := (nameIndex_some (slots0.map Prod.fst) e1.name i hi0).1
              have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
              omega
            have hy0 := argIdent_model_position (c := c)
              hvarsbasic hslots0 hauxfresh h2static hyi
            obtain ⟨j0, hj0⟩ := hy0
            have hjj : j = j0 := by
              have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  e2.name = some j0 := nameIndex_ext_eq_model hj0
              exact Option.some.inj (hyi.symm.trans hext)
            subst hjj
            have hylt : j < slots0.length := by
              have h1' := (nameIndex_some (slots0.map Prod.fst) e2.name j hj0).1
              have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
              omega
            have hk0 := argIdent_model_position (c := c)
              hvarsbasic hslots0 hauxfresh hrstatic hki
            obtain ⟨k0, hk0'⟩ := hk0
            have hkk : k = k0 := by
              have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  r.name = some k0 := nameIndex_ext_eq_model hk0'
              exact Option.some.inj (hki.symm.trans hext)
            subst hkk
            have hklt : k < slots0.length := by
              have h1' := (nameIndex_some (slots0.map Prod.fst) r.name k hk0').1
              have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
              omega
            -- the reads of the extended assignment
            obtain ⟨v1r, hv1r, _⟩ := hreads i hxlt
            obtain ⟨v2r, hv2r, _⟩ := hreads j hylt
            obtain ⟨v3r, hv3r, _⟩ := hreads k hklt
            have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                = store e1 := extAssign_read_ident hxlt hxi ⟨v1r, hv1r⟩
            have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                = store e2 := extAssign_read_ident hylt hyi ⟨v2r, hv2r⟩
            have hareadr : (extAssign store slots0 (modelAuxSlots m))[k]?
                = store r := extAssign_read_ident hklt hki ⟨v3r, hv3r⟩
            exact (DomConstraint.satisfiedB_iff _ _).mpr
              ⟨p, q, min p q, hareadi.trans hs1, hareadj.trans hs2,
                hareadr.trans hsr, rfl⟩
        | maxGen2 e1 e2 r =>
            -- PLAN C9 remainder: the two-element array maximum chains
            -- over the element slots themselves (no aux slot)
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_maxGen2_inv hshape
            have hpred : m.predicates = [] := compileModel_predicates_nil hc
            -- the piece: int_max(e₁, e₂, r) → maxSlot i j k
            have hc'eq : c' =
                { name := Ident.mk "int_max"
                , args := [Expr.basic (.ident e1), Expr.basic (.ident e2),
                    Expr.basic (.ident r)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            obtain ⟨i, j, k, hxi, hyi, hki, hdcform⟩ :=
              compileConstraint_int_max_inv hcc
            rw [hdcform]
            -- the WF typing of the array's element slots
            have hcb := checkBase_int_of_array_elem hpred hwf hcmem
              (Or.inr hnamec) hargsc
            have h1static : m.staticEnv e1 ≠ none := by
              intro hcon
              have hcb1 := hcb.1
              simp only [BasicExpr.checkBase] at hcb1
              rw [hcon] at hcb1
              exact hcb1
            have h2static : m.staticEnv e2 ≠ none := by
              intro hcon
              have hcb2 := hcb.2
              simp only [BasicExpr.checkBase] at hcb2
              rw [hcon] at hcb2
              exact hcb2
            -- the store's semantic facts (the element reads are
            -- integers: the second one by the WF-typed element slots)
            obtain ⟨p, q, hs1, hs2, hsr⟩ : ∃ (p q : Int),
                store e1 = some (.int p) ∧ store e2 = some (.int q) ∧
                store r = some (.int (max p q)) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vr, v1, v2, hsr, hs1, hs2, hargsv⟩ :=
                mapM_ident_ident_arr hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "array_int_maximum")
                  [vr, .array [v1, v2]] := interp_of_hname hnamec hinterp
              -- the interpreted reading, in the `maxValue` match form
              have hsem : (match [vr, .array [v1, v2]] with
                  | [.int m, .array xs] => maxValue xs = some m
                  | _ => False) := by
                rw [fullInterp_std (by decide)] at h1
                exact h1
              -- the second element's integer read (the WF typing fact)
              have h2int : ∃ q, v2 = Value.int q := by
                obtain ⟨j2, hj2⟩ :=
                  argIdent_model_position (c := c)
                    hvarsbasic hslots0 hauxfresh h2static hyi
                have hj2lt : j2 < slots0.length := by
                  have h1' := (nameIndex_some (slots0.map Prod.fst) e2.name j2 hj2).1
                  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                  omega
                obtain ⟨q, hq⟩ := store_int_read_of_slot_checkArg hwf hslots0
                  hvars hcb.2 hj2 hj2lt
                exact ⟨q, Option.some.inj (hs2.symm.trans hq)⟩
              obtain ⟨q, hv2⟩ := h2int
              subst hv2
              -- the result read forces the first element's integer read
              -- (the `maxValue` reading's head)
              cases vr with
              | int m =>
                  have hsem2 : maxValue [v1, Value.int q] = some m := hsem
                  obtain ⟨p, hv1p, hmax⟩ := maxValue_pair_int_tail hsem2
                  subst hv1p
                  refine ⟨p, q, hs1, hs2, ?_⟩
                  rw [← hmax] at hsr
                  exact hsr
              | bool b => exact (hsem : False).elim
              | setOfInt s => exact (hsem : False).elim
              | array xs => exact (hsem : False).elim
            -- the extended positions are MODEL positions
            have hrarg : Expr.basic (.ident r) ∈ c.args := by
              rw [hargsc]; exact List.mem_cons_self
            have hrstatic : m.staticEnv r ≠ none :=
              staticEnv_of_ident_arg hwf hcmem hrarg
            have hx0 := argIdent_model_position (c := c)
              hvarsbasic hslots0 hauxfresh h1static hxi
            obtain ⟨i0, hi0⟩ := hx0
            have hii : i = i0 := by
              have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  e1.name = some i0 := nameIndex_ext_eq_model hi0
              exact Option.some.inj (hxi.symm.trans hext)
            subst hii
            have hxlt : i < slots0.length := by
              have h1' := (nameIndex_some (slots0.map Prod.fst) e1.name i hi0).1
              have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
              omega
            have hy0 := argIdent_model_position (c := c)
              hvarsbasic hslots0 hauxfresh h2static hyi
            obtain ⟨j0, hj0⟩ := hy0
            have hjj : j = j0 := by
              have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  e2.name = some j0 := nameIndex_ext_eq_model hj0
              exact Option.some.inj (hyi.symm.trans hext)
            subst hjj
            have hylt : j < slots0.length := by
              have h1' := (nameIndex_some (slots0.map Prod.fst) e2.name j hj0).1
              have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
              omega
            have hk0 := argIdent_model_position (c := c)
              hvarsbasic hslots0 hauxfresh hrstatic hki
            obtain ⟨k0, hk0'⟩ := hk0
            have hkk : k = k0 := by
              have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  r.name = some k0 := nameIndex_ext_eq_model hk0'
              exact Option.some.inj (hki.symm.trans hext)
            subst hkk
            have hklt : k < slots0.length := by
              have h1' := (nameIndex_some (slots0.map Prod.fst) r.name k hk0').1
              have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
              omega
            -- the reads of the extended assignment
            obtain ⟨v1r, hv1r, _⟩ := hreads i hxlt
            obtain ⟨v2r, hv2r, _⟩ := hreads j hylt
            obtain ⟨v3r, hv3r, _⟩ := hreads k hklt
            have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                = store e1 := extAssign_read_ident hxlt hxi ⟨v1r, hv1r⟩
            have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                = store e2 := extAssign_read_ident hylt hyi ⟨v2r, hv2r⟩
            have hareadr : (extAssign store slots0 (modelAuxSlots m))[k]?
                = store r := extAssign_read_ident hklt hki ⟨v3r, hv3r⟩
            exact (DomConstraint.satisfiedB_iff _ _).mpr
              ⟨p, q, max p q, hareadi.trans hs1, hareadj.trans hs2,
                hareadr.trans hsr, rfl⟩
        | xorSlots x y z =>
            -- PLAN C0: the Boolean XOR channel over its four clauses
            obtain ⟨hnamec, hargsc⟩ := auxShapeOf_xorSlots_inv hshape
            -- the store's Boolean reads and the XOR clause conditions
            obtain ⟨p, q, rb, hsx, hsy, hsz, hcl⟩ : ∃ p q rb,
                store x = some (Value.bool p) ∧
                store y = some (Value.bool q) ∧
                store z = some (Value.bool rb) ∧
                ((p = true ∨ q = true ∨ rb = false) ∧
                 (p = false ∨ q = false ∨ rb = false) ∧
                 (q = true ∨ rb = true ∨ p = false) ∧
                 (p = true ∨ rb = true ∨ q = false)) := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              obtain ⟨vx, vy, vz, hsx, hsy, hsz, hargsv⟩ :=
                mapM_three_ident hargsc hmap
              subst hargsv
              have h1 : fullInterp (Ident.mk "bool_xor")
                  [vx, vy, vz] := interp_of_hname hnamec hinterp
              rw [fullInterp_std (by decide)] at h1
              cases vx with
              | bool p =>
                cases vy with
                | bool q =>
                  cases vz with
                  | bool rb =>
                    exact ⟨p, q, rb, hsx, hsy, hsz,
                      bool_xor_to_clauses h1⟩
                  | int w => exact (h1 : False).elim
                  | setOfInt w => exact (h1 : False).elim
                  | array w => exact (h1 : False).elim
                | int w => exact (h1 : False).elim
                | setOfInt w => exact (h1 : False).elim
                | array w => exact (h1 : False).elim
              | int w => exact (h1 : False).elim
              | setOfInt w => exact (h1 : False).elim
              | array w => exact (h1 : False).elim
            rcases hcl with ⟨hcl1, hcl2, hcl3, hcl4⟩
            -- the three argument memberships
            have hxarg : Expr.basic (.ident x) ∈ c.args := by
              rw [hargsc]; exact List.mem_cons_self
            have hyarg : Expr.basic (.ident y) ∈ c.args := by
              rw [hargsc]; exact List.mem_cons_of_mem _ List.mem_cons_self
            have hzarg : Expr.basic (.ident z) ∈ c.args := by
              rw [hargsc]
              exact List.mem_cons_of_mem _
                (List.mem_cons_of_mem _ List.mem_cons_self)
            -- a resolved argument IS a model position, with its
            -- extended read
            have modelpos : ∀ (w : Ident) (iw : Nat),
                Expr.basic (.ident w) ∈ c.args →
                nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst) w.name
                  = some iw →
                iw < slots0.length ∧
                  (extAssign store slots0 (modelAuxSlots m))[iw]? = store w := by
              intro w iw hwarg hwi
              have hwstatic : m.staticEnv w ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hwarg
              obtain ⟨j, hj⟩ := argIdent_model_position (c := c)
                hvarsbasic hslots0 hauxfresh hwstatic hwi
              have hwj : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  w.name = some j := nameIndex_ext_eq_model hj
              have hji : j = iw := Option.some.inj (hwj.symm.trans hwi)
              have hjlt : j < slots0.length := by
                have h1 := (nameIndex_some (slots0.map Prod.fst) w.name j hj).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v, hvread, _⟩ := hreads j hjlt
              refine ⟨hji ▸ hjlt, ?_⟩
              rw [← hji]
              exact extAssign_read_ident hjlt hwj ⟨v, hvread⟩
            -- the position lists of one- and two-element ident arrays
            have singlepos : ∀ (w : Ident) (is : List Nat),
                linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    [BasicExpr.ident w] = some is →
                ∃ iw, nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    w.name = some iw ∧ is = [iw] := by
              intro w is h
              cases hw : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  w.name with
              | none => simp only [linIndices, hw] at h; exact absurd h (by simp)
              | some iw =>
                  refine ⟨iw, rfl, ?_⟩
                  simp only [linIndices, hw] at h
                  simpa using h.symm
            have pairpos : ∀ (w1 w2 : Ident) (is : List Nat),
                linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    [BasicExpr.ident w1, BasicExpr.ident w2] = some is →
                ∃ i1 i2, nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    w1.name = some i1 ∧
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    w2.name = some i2 ∧ is = [i1, i2] := by
              intro w1 w2 is h
              cases h1 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  w1.name with
              | none => simp only [linIndices, h1] at h; exact absurd h (by simp)
              | some i1 =>
                  cases h2 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      w2.name with
                  | none => simp only [linIndices, h1, h2] at h; exact absurd h (by simp)
                  | some i2 =>
                      refine ⟨i1, i2, rfl, rfl, ?_⟩
                      simp only [linIndices, h1, h2] at h
                      simpa using h.symm
            have triplepos : ∀ (is : List Nat),
                linIndices ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    [BasicExpr.ident x, BasicExpr.ident y,
                      BasicExpr.ident z] = some is →
                ∃ i1 i2 i3,
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some i1 ∧
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some i2 ∧
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    z.name = some i3 ∧ is = [i1, i2, i3] := by
              intro is h
              cases h1 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                  x.name with
              | none => simp only [linIndices, h1] at h; exact absurd h (by simp)
              | some i1 =>
                  cases h2 : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      y.name with
                  | none => simp only [linIndices, h1, h2] at h; exact absurd h (by simp)
                  | some i2 =>
                      cases h3 : nameIndex
                          ((slots0 ++ modelAuxSlots m).map Prod.fst) z.name with
                      | none => simp only [linIndices, h1, h2, h3] at h; exact absurd h (by simp)
                      | some i3 =>
                          refine ⟨i1, i2, i3, rfl, rfl, rfl, ?_⟩
                          simp only [linIndices, h1, h2, h3] at h
                          simpa using h.symm
            -- the piece is ONE of the four bool_clause items
            simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
              at hpiece
            rcases hpiece with hp1 | hp2 | hp3 | hp4 | hc
            · -- bool_clause([x, y], [z])
              have hc'eq : c' =
                  { name := Ident.mk "bool_clause"
                  , args := [Expr.array [BasicExpr.ident x, BasicExpr.ident y],
                      Expr.array [BasicExpr.ident z]]
                  , anns := [] } := hp1
              subst hc'eq
              obtain ⟨ps, ns, hps, hns, hdcform⟩ :=
                compileConstraint_bool_clause_inv hcc
              obtain ⟨ix, iy, hix, hiy, hps'⟩ := pairpos x y ps hps
              obtain ⟨iz, hiz, hns'⟩ := singlepos z ns hns
              obtain ⟨hixlt, readi⟩ := modelpos x ix hxarg hix
              obtain ⟨hiylt, readj⟩ := modelpos y iy hyarg hiy
              obtain ⟨hizlt, readk⟩ := modelpos z iz hzarg hiz
              rw [hdcform, hps', hns']
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ((boolClauseSlot_iff_1 (readi.trans hsx) (readj.trans hsy)
                  (readk.trans hsz)).mpr hcl1)
            · -- bool_clause([], [x, y, z])
              have hc'eq : c' =
                  { name := Ident.mk "bool_clause"
                  , args := [Expr.array [],
                      Expr.array [BasicExpr.ident x, BasicExpr.ident y,
                        BasicExpr.ident z]]
                  , anns := [] } := hp2
              subst hc'eq
              obtain ⟨ps, ns, hps, hns, hdcform⟩ :=
                compileConstraint_bool_clause_inv hcc
              have hps' : ps = [] :=
                Option.some.inj (hps.symm.trans (by simp [linIndices]))
              obtain ⟨ix, iy, iz, hix, hiy, hiz, hns'⟩ := triplepos ns hns
              obtain ⟨hixlt, readi⟩ := modelpos x ix hxarg hix
              obtain ⟨hiylt, readj⟩ := modelpos y iy hyarg hiy
              obtain ⟨hizlt, readk⟩ := modelpos z iz hzarg hiz
              rw [hdcform, hps', hns']
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ((boolClauseSlot_iff_2 (readi.trans hsx) (readj.trans hsy)
                  (readk.trans hsz)).mpr hcl2)
            · -- bool_clause([y, z], [x])
              have hc'eq : c' =
                  { name := Ident.mk "bool_clause"
                  , args := [Expr.array [BasicExpr.ident y, BasicExpr.ident z],
                      Expr.array [BasicExpr.ident x]]
                  , anns := [] } := hp3
              subst hc'eq
              obtain ⟨ps, ns, hps, hns, hdcform⟩ :=
                compileConstraint_bool_clause_inv hcc
              obtain ⟨iy, iz, hiy, hiz, hps'⟩ := pairpos y z ps hps
              obtain ⟨ix, hix, hns'⟩ := singlepos x ns hns
              obtain ⟨hixlt, readi⟩ := modelpos x ix hxarg hix
              obtain ⟨hiylt, readj⟩ := modelpos y iy hyarg hiy
              obtain ⟨hizlt, readk⟩ := modelpos z iz hzarg hiz
              rw [hdcform, hps', hns']
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ((boolClauseSlot_iff_3 (readi.trans hsx) (readj.trans hsy)
                  (readk.trans hsz)).mpr hcl3)
            · -- bool_clause([x, z], [y])
              have hc'eq : c' =
                  { name := Ident.mk "bool_clause"
                  , args := [Expr.array [BasicExpr.ident x, BasicExpr.ident z],
                      Expr.array [BasicExpr.ident y]]
                  , anns := [] } := hp4
              subst hc'eq
              obtain ⟨ps, ns, hps, hns, hdcform⟩ :=
                compileConstraint_bool_clause_inv hcc
              obtain ⟨ix, iz, hix, hiz, hps'⟩ := pairpos x z ps hps
              obtain ⟨iy, hiy, hns'⟩ := singlepos y ns hns
              obtain ⟨hixlt, readi⟩ := modelpos x ix hxarg hix
              obtain ⟨hiylt, readj⟩ := modelpos y iy hyarg hiy
              obtain ⟨hizlt, readk⟩ := modelpos z iz hzarg hiz
              rw [hdcform, hps', hns']
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ((boolClauseSlot_iff_4 (readi.trans hsx) (readj.trans hsy)
                  (readk.trans hsz)).mpr hcl4)
            · exact absurd hc (by simp)
        | andTrue x y =>
            -- the args + name inversion: c is bool_and(x, y, true)
            have hargsc : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
                Expr.basic (.lit (.bool true))] := auxShapeOf_andTrue_args hshape
            have hnamec : c.name.name = "bool_and" :=
              auxShapeOf_andTrue_name hshape
            -- the store's semantic facts: store x = .bool p,
            -- store y = .bool q, true = p && q
            obtain ⟨p, q, hsx, hsy, hpq⟩ : ∃ p q, store x = some (.bool p) ∧
                store y = some (.bool q) ∧ (p && q) = true := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.lit (.bool true))))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv3' : Expr.eval store (Expr.basic (.lit (.bool true)))
                  = some (.bool true) := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              have hredy : Expr.eval store (Expr.basic (.ident y))
                  = store y := rfl
              rw [hv3', hredx, hredy] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v1 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  cases hsy : store y with
                  | none => rw [hsy] at hchain; simp at hchain
                  | some v2 =>
                      rw [hsy] at hchain
                      simp only [Option.bind_some] at hchain
                      have hargsv : args = [v1, v2, .bool true] := by
                        simpa using hchain.symm
                      subst hargsv
                      have h1 : fullInterp (Ident.mk "bool_and") [v1, v2, .bool true] :=
                        interp_of_hname hnamec hinterp
                      rw [fullInterp_std (by decide)] at h1
                      have hmatch : (match [v1, v2, Value.bool true] with
                        | [Value.bool a, Value.bool b, Value.bool w] => w = (a && b)
                        | _ => False) := h1
                      cases v1 with
                      | bool p =>
                          cases v2 with
                          | bool q =>
                              exact ⟨p, q, rfl, rfl, by simpa using hmatch⟩
                          | int w => exact absurd hmatch (by simp)
                          | setOfInt w => exact absurd hmatch (by simp)
                          | array w => exact absurd hmatch (by simp)
                      | int w => exact absurd hmatch (by simp)
                      | setOfInt w => exact absurd hmatch (by simp)
                      | array w => exact absurd hmatch (by simp)
            -- p = true and q = true (the conjunction is true)
            have hp : p = true := (Bool.and_eq_true p q).mp hpq |>.1
            have hq : q = true := (Bool.and_eq_true p q).mp hpq |>.2
            -- the piece is ONE of the two bool_not pieces
            rcases List.mem_cons.mp hpiece with hp1 | hrest
            · -- piece 1: bool_not(x, false)
              have hc'eq : c' =
                  { name := Ident.mk "bool_not"
                  , args := [Expr.basic (.ident x), Expr.basic (.lit (.bool false))]
                  , anns := [] } := hp1
              subst hc'eq
              obtain ⟨i, hxi, hdcform⟩ := compileConstraint_bool_not_lit_inv hcc
              rw [show (Bool.not false) = true from rfl] at hdcform
              rw [hdcform]
              -- x's model position: x is declared
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              -- the satisfaction: constEq i (.bool true)
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                (by
                  show (extAssign store slots0 (modelAuxSlots m))[i]? =
                    some (Value.bool true)
                  rw [hareadi, hsx, ← hp])
            · -- piece 2: bool_not(y, false)
              have hp2 := List.mem_singleton.mp hrest
              have hc'eq : c' =
                  { name := Ident.mk "bool_not"
                  , args := [Expr.basic (.ident y), Expr.basic (.lit (.bool false))]
                  , anns := [] } := hp2
              subst hc'eq
              obtain ⟨j, hyi, hdcform⟩ := compileConstraint_bool_not_lit_inv hcc
              rw [show (Bool.not false) = true from rfl] at hdcform
              rw [hdcform]
              -- y's model position: y is declared
              have hyarg : Expr.basic (.ident y) ∈ c.args := by
                rw [hargsc]
                exact List.mem_cons_of_mem _ List.mem_cons_self
              have hystatic : m.staticEnv y ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hyarg
              have hyjlt : j < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hystatic hyi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
              have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                  = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
              -- the satisfaction: constEq j (.bool true)
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                (by
                  show (extAssign store slots0 (modelAuxSlots m))[j]? =
                    some (Value.bool true)
                  rw [hareadj, hsy, ← hq])
        | andFalse x y =>
            -- the args + name inversion: c is bool_and(x, y, false)
            have hargsc : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
                Expr.basic (.lit (.bool false))] := auxShapeOf_andFalse_args hshape
            have hnamec : c.name.name = "bool_and" :=
              auxShapeOf_andFalse_name hshape
            -- the store's semantic facts: store x = .bool p,
            -- store y = .bool q, (p && q) = false
            obtain ⟨p, q, hsx, hsy, hpq⟩ : ∃ p q, store x = some (.bool p) ∧
                store y = some (.bool q) ∧ (p && q) = false := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.lit (.bool false))))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv3' : Expr.eval store (Expr.basic (.lit (.bool false)))
                  = some (.bool false) := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              have hredy : Expr.eval store (Expr.basic (.ident y))
                  = store y := rfl
              rw [hv3', hredx, hredy] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v1 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  cases hsy : store y with
                  | none => rw [hsy] at hchain; simp at hchain
                  | some v2 =>
                      rw [hsy] at hchain
                      simp only [Option.bind_some] at hchain
                      have hargsv : args = [v1, v2, .bool false] := by
                        simpa using hchain.symm
                      subst hargsv
                      have h1 : fullInterp (Ident.mk "bool_and") [v1, v2, .bool false] :=
                        interp_of_hname hnamec hinterp
                      rw [fullInterp_std (by decide)] at h1
                      have hmatch : (match [v1, v2, Value.bool false] with
                        | [Value.bool a, Value.bool b, Value.bool w] => w = (a && b)
                        | _ => False) := h1
                      cases v1 with
                      | bool p =>
                          cases v2 with
                          | bool q =>
                              exact ⟨p, q, rfl, rfl, by simpa using hmatch⟩
                          | int w => exact absurd hmatch (by simp)
                          | setOfInt w => exact absurd hmatch (by simp)
                          | array w => exact absurd hmatch (by simp)
                      | int w => exact absurd hmatch (by simp)
                      | setOfInt w => exact absurd hmatch (by simp)
                      | array w => exact absurd hmatch (by simp)
            -- the pin: the aux slot at i2 carries [.bool false]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.bool false :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              -- the aux read: a[slots0.length + i2]? = some (.bool false)
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.bool false) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.bool false]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the aux position: every resolution of the aux name
              -- lands at slots0.length + i2
              have hAUXposOf : ∀ (n3 : Nat),
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    (Ident.mk (auxName (auxTaken m slots0) i2)).name = some n3 →
                  n3 = slots0.length + i2 := by
                intro n3 hn3
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.bool false])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hn3
                rw [hres] at hn3
                exact (Option.some.inj hn3).symm
              -- the piece is ONE of the two expansion pieces
              rcases List.mem_cons.mp hpiece with hp1 | hrest
              · -- piece 1: bool_and(x, y, AUX)
                have hc'eq : c' =
                    { name := Ident.mk "bool_and"
                    , args := [Expr.basic (.ident x), Expr.basic (.ident y),
                        Expr.basic (.ident
                          (Ident.mk (auxName (auxTaken m slots0) i2)))]
                    , anns := [] } := hp1
                subst hc'eq
                rcases compileConstraint_bool_and3_inv hcc with
                  ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ |
                  ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                  ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                  ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩ |
                  ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩
                · -- the main case: boolAndSlot i j AUX over the
                  -- resolved positions and the pinned aux position
                  have hAUXpos : iAUX = slots0.length + i2 :=
                    hAUXposOf _ hAUXi
                  rw [hdcform, hAUXpos]
                  -- the model positions: x and y are declared
                  have hxarg : Expr.basic (.ident x) ∈ c.args := by
                    rw [hargsc]; exact List.mem_cons_self
                  have hyarg : Expr.basic (.ident y) ∈ c.args := by
                    rw [hargsc]
                    exact List.mem_cons_of_mem _ List.mem_cons_self
                  have hxstatic : m.staticEnv x ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hxarg
                  have hystatic : m.staticEnv y ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hyarg
                  have hxilt : i < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hxstatic hxi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        x.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  have hyjlt : j < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hystatic hyi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        y.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  -- the reads
                  obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
                  obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
                  have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                      = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
                  have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                      = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
                  -- the satisfaction
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    ⟨p, q, false, hareadi.trans hsx, hareadj.trans hsy,
                      hareadaux, hpq⟩
                · -- the parameter case: y is a par-bool parameter with
                  -- value true; the piece compiled to eqSlot i AUXpos —
                  -- x's read is false (the pin and the conjunction)
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  -- x's model position: x is declared
                  have hxarg : Expr.basic (.ident x) ∈ c.args := by
                    rw [hargsc]; exact List.mem_cons_self
                  have hxstatic : m.staticEnv x ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hxarg
                  have hxilt : i < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hxstatic hxi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        x.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
                  have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                      = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
                  -- the store's y read: the parameter's declared value
                  have hyread : store y = some (Value.bool true) :=
                    store_of_parEnv hparam henvy
                  have hq : q = true := by
                    have h1 : some (Value.bool q) = some (Value.bool true) :=
                      hsy.symm.trans hyread
                    exact Value.bool.inj (Option.some.inj h1)
                  have hp : p = false := by
                    rw [hq, Bool.and_true] at hpq; exact hpq
                  -- the satisfaction: eqSlot i (slots0.length + i2)
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    ⟨Value.bool false, Value.bool false,
                      by rw [hareadi, hsx, ← hp], hareadaux, rfl⟩
                · -- the parameter case: y is a par-bool parameter with
                  -- value false; the piece compiled to constEq AUXpos
                  -- false — the pin satisfies it outright
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    (by
                      show (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                          = some (Value.bool false)
                      exact hareadaux)
                · -- the parameter case: x is a par-bool parameter with
                  -- value true; the piece compiled to eqSlot j AUXpos —
                  -- y's read is false (the pin and the conjunction)
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  -- y's model position: y is declared
                  have hyarg : Expr.basic (.ident y) ∈ c.args := by
                    rw [hargsc]
                    exact List.mem_cons_of_mem _ List.mem_cons_self
                  have hystatic : m.staticEnv y ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hyarg
                  have hyjlt : j < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hystatic hyi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        y.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
                  have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                      = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
                  -- the store's x read: the parameter's declared value
                  have hxread : store x = some (Value.bool true) :=
                    store_of_parEnv hparam henvx
                  have hp : p = true := by
                    have h1 : some (Value.bool p) = some (Value.bool true) :=
                      hsx.symm.trans hxread
                    exact Value.bool.inj (Option.some.inj h1)
                  have hq : q = false := by
                    rw [hp, Bool.true_and] at hpq; exact hpq
                  -- the satisfaction: eqSlot j (slots0.length + i2)
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    ⟨Value.bool false, Value.bool false,
                      by rw [hareadj, hsy, ← hq], hareadaux, rfl⟩
                · -- the parameter case: x is a par-bool parameter with
                  -- value false; the piece compiled to constEq AUXpos
                  -- false — the pin satisfies it outright
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    (by
                      show (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                          = some (Value.bool false)
                      exact hareadaux)
              · -- piece 2: bool_not(AUX, true)
                have hp2 := List.mem_singleton.mp hrest
                have hc'eq : c' =
                    { name := Ident.mk "bool_not"
                    , args := [Expr.basic (.ident
                          (Ident.mk (auxName (auxTaken m slots0) i2))),
                        Expr.basic (.lit (.bool true))]
                    , anns := [] } := hp2
                subst hc'eq
                obtain ⟨iAUX, hAUXi, hdcform⟩ :=
                  compileConstraint_bool_not_lit_inv hcc
                rw [show (Bool.not true) = false from rfl] at hdcform
                -- the aux position: iAUX = slots0.length + i2
                have hAUXpos : iAUX = slots0.length + i2 :=
                  hAUXposOf _ hAUXi
                rw [hdcform, hAUXpos]
                -- the satisfaction: constEq AUXpos (.bool false)
                exact (DomConstraint.satisfiedB_iff _ _).mpr
                  (by
                    show (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                        = some (Value.bool false)
                    exact hareadaux)
        | orTrue x y =>
            -- the args + name inversion: c is bool_or(x, y, true)
            have hargsc : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
                Expr.basic (.lit (.bool true))] := auxShapeOf_orTrue_args hshape
            have hnamec : c.name.name = "bool_or" :=
              auxShapeOf_orTrue_name hshape
            -- the store's semantic facts: store x = .bool p,
            -- store y = .bool q, (p || q) = true
            obtain ⟨p, q, hsx, hsy, hpq⟩ : ∃ p q, store x = some (.bool p) ∧
                store y = some (.bool q) ∧ (p || q) = true := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.lit (.bool true))))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv3' : Expr.eval store (Expr.basic (.lit (.bool true)))
                  = some (.bool true) := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              have hredy : Expr.eval store (Expr.basic (.ident y))
                  = store y := rfl
              rw [hv3', hredx, hredy] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v1 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  cases hsy : store y with
                  | none => rw [hsy] at hchain; simp at hchain
                  | some v2 =>
                      rw [hsy] at hchain
                      simp only [Option.bind_some] at hchain
                      have hargsv : args = [v1, v2, .bool true] := by
                        simpa using hchain.symm
                      subst hargsv
                      have h1 : fullInterp (Ident.mk "bool_or") [v1, v2, .bool true] :=
                        interp_of_hname hnamec hinterp
                      rw [fullInterp_std (by decide)] at h1
                      have hmatch : (match [v1, v2, Value.bool true] with
                        | [Value.bool a, Value.bool b, Value.bool w] => w = (a || b)
                        | _ => False) := h1
                      cases v1 with
                      | bool p =>
                          cases v2 with
                          | bool q =>
                              exact ⟨p, q, rfl, rfl, by simpa using hmatch⟩
                          | int w => exact absurd hmatch (by simp)
                          | setOfInt w => exact absurd hmatch (by simp)
                          | array w => exact absurd hmatch (by simp)
                      | int w => exact absurd hmatch (by simp)
                      | setOfInt w => exact absurd hmatch (by simp)
                      | array w => exact absurd hmatch (by simp)
            -- the pin: the aux slot at i2 carries [.bool true]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.bool true :=
                (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              -- the aux read: a[slots0.length + i2]? = some (.bool true)
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.bool true) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.bool true]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the aux position: every resolution of the aux name
              -- lands at slots0.length + i2
              have hAUXposOf : ∀ (n3 : Nat),
                  nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    (Ident.mk (auxName (auxTaken m slots0) i2)).name = some n3 →
                  n3 = slots0.length + i2 := by
                intro n3 hn3
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.bool true])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hn3
                rw [hres] at hn3
                exact (Option.some.inj hn3).symm
              -- the piece is ONE of the two expansion pieces
              rcases List.mem_cons.mp hpiece with hp1 | hrest
              · -- piece 1: bool_or(x, y, AUX)
                have hc'eq : c' =
                    { name := Ident.mk "bool_or"
                    , args := [Expr.basic (.ident x), Expr.basic (.ident y),
                        Expr.basic (.ident
                          (Ident.mk (auxName (auxTaken m slots0) i2)))]
                    , anns := [] } := hp1
                subst hc'eq
                rcases compileConstraint_bool_or3_inv hcc with
                  ⟨i, j, iAUX, hxi, hyi, hAUXi, hdcform⟩ |
                  ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                  ⟨i, k, hxi, hki, hynone, henvy, hdcform⟩ |
                  ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩ |
                  ⟨j, k, hyi, hki, hxnone, henvx, hdcform⟩
                · -- the main case: boolOrSlot i j AUX over the
                  -- resolved positions and the pinned aux position
                  have hAUXpos : iAUX = slots0.length + i2 :=
                    hAUXposOf _ hAUXi
                  rw [hdcform, hAUXpos]
                  -- the model positions: x and y are declared
                  have hxarg : Expr.basic (.ident x) ∈ c.args := by
                    rw [hargsc]; exact List.mem_cons_self
                  have hyarg : Expr.basic (.ident y) ∈ c.args := by
                    rw [hargsc]
                    exact List.mem_cons_of_mem _ List.mem_cons_self
                  have hxstatic : m.staticEnv x ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hxarg
                  have hystatic : m.staticEnv y ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hyarg
                  have hxilt : i < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hxstatic hxi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        x.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  have hyjlt : j < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hystatic hyi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        y.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  -- the reads
                  obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
                  obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
                  have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                      = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
                  have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                      = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
                  -- the satisfaction
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    ⟨p, q, true, hareadi.trans hsx, hareadj.trans hsy,
                      hareadaux, hpq⟩
                · -- the parameter case: y is a par-bool parameter with
                  -- value true; the piece compiled to constEq AUXpos
                  -- true — the pin satisfies it outright
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    (by
                      show (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                          = some (Value.bool true)
                      exact hareadaux)
                · -- the parameter case: y is a par-bool parameter with
                  -- value false; the piece compiled to eqSlot i AUXpos —
                  -- x's read is true (the pin and the disjunction)
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  -- x's model position: x is declared
                  have hxarg : Expr.basic (.ident x) ∈ c.args := by
                    rw [hargsc]; exact List.mem_cons_self
                  have hxstatic : m.staticEnv x ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hxarg
                  have hxilt : i < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hxstatic hxi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        x.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
                  have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                      = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
                  -- the store's y read: the parameter's declared value
                  have hyread : store y = some (Value.bool false) :=
                    store_of_parEnv hparam henvy
                  have hq : q = false := by
                    have h1 : some (Value.bool q) = some (Value.bool false) :=
                      hsy.symm.trans hyread
                    exact Value.bool.inj (Option.some.inj h1)
                  have hp : p = true := by
                    rw [hq, Bool.or_false] at hpq; exact hpq
                  -- the satisfaction: eqSlot i (slots0.length + i2)
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    ⟨Value.bool true, Value.bool true,
                      by rw [hareadi, hsx, ← hp], hareadaux, rfl⟩
                · -- the parameter case: x is a par-bool parameter with
                  -- value true; the piece compiled to constEq AUXpos
                  -- true — the pin satisfies it outright
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    (by
                      show (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                          = some (Value.bool true)
                      exact hareadaux)
                · -- the parameter case: x is a par-bool parameter with
                  -- value false; the piece compiled to eqSlot j AUXpos —
                  -- y's read is true (the pin and the disjunction)
                  have hkpos : k = slots0.length + i2 :=
                    hAUXposOf _ hki
                  -- y's model position: y is declared
                  have hyarg : Expr.basic (.ident y) ∈ c.args := by
                    rw [hargsc]
                    exact List.mem_cons_of_mem _ List.mem_cons_self
                  have hystatic : m.staticEnv y ≠ none :=
                    staticEnv_of_ident_arg hwf hcmem hyarg
                  have hyjlt : j < slots0.length := by
                    obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                      hvarsbasic hslots0 hauxfresh hystatic hyi
                    have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                        y.name = some j2 := nameIndex_ext_eq_model hj2
                    have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                    subst hji
                    have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                    have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                    omega
                  obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
                  have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                      = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
                  -- the store's x read: the parameter's declared value
                  have hxread : store x = some (Value.bool false) :=
                    store_of_parEnv hparam henvx
                  have hp : p = false := by
                    have h1 : some (Value.bool p) = some (Value.bool false) :=
                      hsx.symm.trans hxread
                    exact Value.bool.inj (Option.some.inj h1)
                  have hq : q = true := by
                    rw [hp, Bool.false_or] at hpq; exact hpq
                  -- the satisfaction: eqSlot j (slots0.length + i2)
                  rw [hdcform, hkpos]
                  exact (DomConstraint.satisfiedB_iff _ _).mpr
                    ⟨Value.bool true, Value.bool true,
                      by rw [hareadj, hsy, ← hq], hareadaux, rfl⟩
              · -- piece 2: bool_not(AUX, false)
                have hp2 := List.mem_singleton.mp hrest
                have hc'eq : c' =
                    { name := Ident.mk "bool_not"
                    , args := [Expr.basic (.ident
                          (Ident.mk (auxName (auxTaken m slots0) i2))),
                        Expr.basic (.lit (.bool false))]
                    , anns := [] } := hp2
                subst hc'eq
                obtain ⟨iAUX, hAUXi, hdcform⟩ :=
                  compileConstraint_bool_not_lit_inv hcc
                rw [show (Bool.not false) = true from rfl] at hdcform
                -- the aux position: iAUX = slots0.length + i2
                have hAUXpos : iAUX = slots0.length + i2 :=
                  hAUXposOf _ hAUXi
                rw [hdcform, hAUXpos]
                -- the satisfaction: constEq AUXpos (.bool true)
                exact (DomConstraint.satisfiedB_iff _ _).mpr
                  (by
                    show (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                        = some (Value.bool true)
                    exact hareadaux)
        | constElemValL x xs k =>
            -- PLAN C0 element values: the value-literal array_int_element
            -- over an all-literal table
            have hinv := auxShapeOf_constElemValL_inv hshape
            have hnamec : c.name.name = "array_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array (litTab xs),
                Expr.basic (.lit (.int k))] := hinv.2
            -- the store's semantic facts
            obtain ⟨idx, hsx, hval⟩ :=
              holds_arrayIntElement_litVal hnamec hargsc (hcons c hcmem)
            -- the piece's form
            have hc'eq : c' =
                { name := Ident.mk "array_int_element"
                , args := [Expr.basic (.ident x), Expr.array (litTab xs),
                    Expr.basic (.ident
                      (Ident.mk (auxName (auxTaken m slots0) i2)))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the piece's compile inversion
            obtain ⟨i, iAUX, hxi, hAUXi, hdcform⟩ :=
              compileConstraint_constElemValL_inv hcc
            -- the pin: the aux slot at i2 carries [.int k]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k := (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              -- the aux position: iAUX = slots0.length + i2
              have hAUXpos : iAUX = slots0.length + i2 := by
                have hspec : ∀ j2 p, (modelAuxSlots m)[j2]? = some p →
                    p.1 = auxName (auxTaken m slots0) j2 :=
                  (modelAuxSlots_spec hslots0).1
                have hres := nameIndex_aux_slot
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (taken := auxTaken m slots0) (i := i2)
                  (vs := [Value.int k])
                  (hsub := by
                    intro s hs
                    exact List.mem_append.mpr (Or.inl hs))
                  hspec hslotget
                have hAUXname : (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = auxName (auxTaken m slots0) i2 := rfl
                rw [hAUXname] at hAUXi
                rw [hres] at hAUXi
                exact (Option.some.inj hAUXi).symm
              rw [hdcform, hAUXpos]
              -- x's model position
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              -- the reads
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x :=
                extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              have hareadaux : (extAssign store slots0 (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the satisfaction
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                ⟨idx, k, hareadi.trans hsx, hareadaux, hval⟩
        | varElemTabLit x y pre k post =>
            -- PLAN C0 element values: the one-literal mixed table with
            -- a slot value; the piece is the all-slot table over the
            -- pinned aux slot
            have hinv := auxShapeOf_varElemTabLit_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x),
                Expr.array (litSplitTab pre k post),
                Expr.basic (.ident y)] := hinv.2
            -- the source's semantic facts at the satisfying store
            obtain ⟨vs, vx, vy, hvs, hsx, hsy, hmatch⟩ :=
              holds_array_var_int_element hnamec hargsc (hcons c hcmem)
            obtain ⟨idx, e, hidx, he, hget⟩ : ∃ (idx : Int) (e : Int),
                vx = Value.int idx ∧ vy = Value.int e ∧
                valuesGet1 vs idx = some (.int e) := by
              cases vx with
              | int i =>
                  cases vy with
                  | int e =>
                      have h2 : (match [Value.int i, .array vs,
                          Value.int e] with
                        | [.int i, .array xs, .int e] =>
                            valuesGet1 xs i = some (.int e)
                        | _ => False) := hmatch
                      exact ⟨i, e, rfl, rfl, by simpa using h2⟩
                  | bool w => exact absurd hmatch (by simp)
                  | setOfInt w => exact absurd hmatch (by simp)
                  | array w => exact absurd hmatch (by simp)
              | bool w => exact absurd hmatch (by simp)
              | setOfInt w => exact absurd hmatch (by simp)
              | array w => exact absurd hmatch (by simp)
            subst hidx
            subst he
            -- the piece's form
            have hc'eq : c' =
                { name := Ident.mk "array_var_int_element"
                , args := [Expr.basic (.ident x),
                    Expr.array (auxTab pre
                      (Ident.mk (auxName (auxTaken m slots0) i2)) post),
                    Expr.basic (.ident y)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the pin: the aux slot at i2 carries [.int k]
            rcases hpin with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k := (Option.some.inj hpinv).symm
              subst hvk
              have hnlt : i2 < (modelAuxSlots m).length :=
                (List.getElem?_eq_some_iff.mp hslotget).1
              -- the extended assignment's aux read is the pin
              have hareadaux : (extAssign store slots0
                    (modelAuxSlots m))[slots0.length + i2]?
                  = some (Value.int k) := by
                rw [extAssign_aux_read hnlt]
                have hpair : (modelAuxSlots m)[i2]
                    = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                  have hplain : (modelAuxSlots m)[i2]?
                      = some (modelAuxSlots m)[i2] :=
                    List.getElem?_eq_getElem hnlt
                  rw [hslotget] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              -- the extended store's aux read is the pin
              have hauxread : ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore (extAssign store slots0 (modelAuxSlots m)))
                    (Ident.mk (auxName (auxTaken m slots0) i2))
                  = some (Value.int k) := by
                have hres : nameIndex
                    ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    (Ident.mk (auxName (auxTaken m slots0) i2)).name
                    = some (slots0.length + i2) := by
                  show nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    (auxName (auxTaken m slots0) i2)
                    = some (slots0.length + i2)
                  exact nameIndex_aux_slot
                    (slots0 := slots0) (auxs := modelAuxSlots m)
                    (taken := auxTaken m slots0) (i := i2)
                    (vs := [Value.int k])
                    (hsub := by
                      intro s hs
                      exact List.mem_append.mpr (Or.inl hs))
                    (modelAuxSlots_spec hslots0).1 hslotget
                have halt' : (extAssign store slots0 (modelAuxSlots m)).length
                    = (slots0 ++ modelAuxSlots m).length := by
                  rw [extAssign_length, List.length_append]
                rw [toStore_read_model (m := m) hnu halt' hres,
                  bang_of_getElem? hareadaux]
              -- the store reads at the table's names agree
              have hpre : ∀ w ∈ pre,
                  ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                    (extAssign store slots0 (modelAuxSlots m))) w = store w := by
                intro w hw
                apply hagree c hcmem w
                rw [hargsc]
                apply List.mem_flatMap.mpr
                refine ⟨Expr.array (litSplitTab pre k post),
                  List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                rw [Expr.idents, flatMap_idents_litSplitTab]
                exact List.mem_append_left _ hw
              have hpost : ∀ w ∈ post,
                  ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                    (extAssign store slots0 (modelAuxSlots m))) w = store w := by
                intro w hw
                apply hagree c hcmem w
                rw [hargsc]
                apply List.mem_flatMap.mpr
                refine ⟨Expr.array (litSplitTab pre k post),
                  List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                rw [Expr.idents, flatMap_idents_litSplitTab]
                exact List.mem_append_right _ hw
              -- the table-read congruence
              have hvs' : (auxTab pre
                    (Ident.mk (auxName (auxTaken m slots0) i2)) post).mapM
                  (BasicExpr.eval ((assemble m (slots0 ++ modelAuxSlots m)
                    dcs).toStore (extAssign store slots0 (modelAuxSlots m))))
                  = some vs := by
                rw [mapM_eval_auxTab_congr (s := store) hauxread hpre hpost]
                exact hvs
              -- the piece's Holds at the extended store
              have hxmem : x ∈ c.args.flatMap Expr.idents := by
                rw [hargsc]
                exact List.mem_flatMap.mpr
                  ⟨Expr.basic (.ident x), List.mem_cons_self,
                    List.mem_cons_self⟩
              have hymem : y ∈ c.args.flatMap Expr.idents := by
                rw [hargsc]
                exact List.mem_flatMap.mpr
                  ⟨Expr.basic (.ident y),
                    List.mem_cons_of_mem _
                      (List.mem_cons_of_mem _ List.mem_cons_self),
                    List.mem_cons_self⟩
              have hh : ({ name := Ident.mk "array_var_int_element"
                         , args := [Expr.basic (.ident x),
                             Expr.array (auxTab pre
                               (Ident.mk (auxName (auxTaken m slots0) i2))
                               post),
                             Expr.basic (.ident y)]
                         , anns := [] } : ConstraintItem).Holds fullInterp
                  ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                    (extAssign store slots0 (modelAuxSlots m))) := by
                refine ⟨[.int idx, .array vs, .int e], ?_, ?_⟩
                · show (do
                      let v1 ← ((assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore
                        (extAssign store slots0 (modelAuxSlots m))) x
                      let v2 ← Option.map Value.array ((auxTab pre
                        (Ident.mk (auxName (auxTaken m slots0) i2))
                        post).mapM
                        (BasicExpr.eval ((assemble m
                          (slots0 ++ modelAuxSlots m) dcs).toStore
                          (extAssign store slots0 (modelAuxSlots m)))))
                      let v3 ← ((assemble m (slots0 ++ modelAuxSlots m)
                        dcs).toStore
                        (extAssign store slots0 (modelAuxSlots m))) y
                      pure [v1, v2, v3]) = _
                  rw [hagree c hcmem x hxmem, hagree c hcmem y hymem,
                    hvs', hsx, hsy]
                  rfl
                · change fullInterp (Ident.mk "array_var_int_element")
                    [.int idx, .array vs, .int e]
                  rw [fullInterp_of_extracted_elem "array_var_int_element"
                    (Or.inr (Or.inl rfl))]
                  show (match ([.int idx, .array vs, .int e] : List Value)
                      with
                    | [.int i', .array xs, .int e'] =>
                        valuesGet1 xs i' = some (.int e')
                    | _ => False)
                  exact hget
              have halt' : (extAssign store slots0 (modelAuxSlots m)).length
                  = (slots0 ++ modelAuxSlots m).length := by
                rw [extAssign_length, List.length_append]
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                (compile_holds_link hnu halt' hcc hh)
        | varElemTabValLit x pre k post k' =>
            -- PLAN C0 element values: the one-literal mixed table with
            -- a literal value; the piece is the all-slot table over
            -- the first pinned aux slot and the value on the second
            have hinv := auxShapeOf_varElemTabValLit_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x),
                Expr.array (litSplitTab pre k post),
                Expr.basic (.lit (.int k'))] := hinv.2
            -- the source's semantic facts at the satisfying store
            obtain ⟨idx, vs, hsx, hvs, hget⟩ :=
              holds_arrayVarElement_litVal hnamec hargsc (hcons c hcmem)
            -- the piece's form
            have hc'eq : c' =
                { name := Ident.mk "array_var_int_element"
                , args := [Expr.basic (.ident x),
                    Expr.array (auxTab pre (Ident.mk (auxName (auxTaken m slots0) i2)) post),
                    Expr.basic (.ident (nextAuxIdent
                      (Ident.mk (auxName (auxTaken m slots0) i2))))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the two pins
            obtain ⟨hp1, hp2⟩ := And.intro hpin hpin2
            rcases hp1 with hpinnone | ⟨v, hpinv, hslotget⟩
            · rw [AuxShape.pin] at hpinnone; exact absurd hpinnone (by simp)
            · rw [AuxShape.pin] at hpinv
              have hvk : v = Value.int k := (Option.some.inj hpinv).symm
              subst hvk
              rcases hp2 with hpin2none | ⟨v2, hpin2v, hslot2get⟩
              · rw [AuxShape.pin2] at hpin2none
                exact absurd hpin2none (by simp)
              · rw [AuxShape.pin2] at hpin2v
                have hvk' : v2 = Value.int k' :=
                  (Option.some.inj hpin2v).symm
                subst hvk'
                have hnlt : i2 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslotget).1
                have hnlt2 : i2 + 1 < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hslot2get).1
                -- the extended assignment's aux reads are the pins
                have hareadaux : (extAssign store slots0
                      (modelAuxSlots m))[slots0.length + i2]?
                    = some (Value.int k) := by
                  rw [extAssign_aux_read hnlt]
                  have hpair : (modelAuxSlots m)[i2]
                      = (auxName (auxTaken m slots0) i2, [Value.int k]) := by
                    have hplain : (modelAuxSlots m)[i2]?
                        = some (modelAuxSlots m)[i2] :=
                      List.getElem?_eq_getElem hnlt
                    rw [hslotget] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                have hareadaux2 : (extAssign store slots0
                      (modelAuxSlots m))[slots0.length + (i2 + 1)]?
                    = some (Value.int k') := by
                  rw [extAssign_aux_read hnlt2]
                  have hpair : (modelAuxSlots m)[i2 + 1]
                      = (auxName (auxTaken m slots0) (i2 + 1),
                          [Value.int k']) := by
                    have hplain : (modelAuxSlots m)[i2 + 1]?
                        = some (modelAuxSlots m)[i2 + 1] :=
                      List.getElem?_eq_getElem hnlt2
                    rw [hslot2get] at hplain
                    exact (Option.some.inj hplain).symm
                  rw [hpair]
                  rfl
                -- the extended store's aux reads are the pins
                have hauxread : ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore (extAssign store slots0 (modelAuxSlots m)))
                      (Ident.mk (auxName (auxTaken m slots0) i2))
                    = some (Value.int k) := by
                  have hres : nameIndex
                      ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      (Ident.mk (auxName (auxTaken m slots0) i2)).name
                      = some (slots0.length + i2) := by
                    show nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      (auxName (auxTaken m slots0) i2)
                      = some (slots0.length + i2)
                    exact nameIndex_aux_slot
                      (slots0 := slots0) (auxs := modelAuxSlots m)
                      (taken := auxTaken m slots0) (i := i2)
                      (vs := [Value.int k])
                      (hsub := by
                        intro s hs
                        exact List.mem_append.mpr (Or.inl hs))
                      (modelAuxSlots_spec hslots0).1 hslotget
                  have halt' : (extAssign store slots0
                      (modelAuxSlots m)).length
                      = (slots0 ++ modelAuxSlots m).length := by
                    rw [extAssign_length, List.length_append]
                  rw [toStore_read_model (m := m) hnu halt' hres,
                    bang_of_getElem? hareadaux]
                have haux2read : ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore (extAssign store slots0 (modelAuxSlots m)))
                      (nextAuxIdent (Ident.mk
                        (auxName (auxTaken m slots0) i2)))
                    = some (Value.int k') := by
                  have hres : nameIndex
                      ((slots0 ++ modelAuxSlots m).map Prod.fst)
                      (nextAuxIdent (Ident.mk
                        (auxName (auxTaken m slots0) i2))).name
                      = some (slots0.length + (i2 + 1)) := by
                    have hres2 := nameIndex_aux_slot
                      (slots0 := slots0) (auxs := modelAuxSlots m)
                      (taken := auxTaken m slots0) (i := i2 + 1)
                      (vs := [Value.int k'])
                      (hsub := by
                        intro s hs
                        exact List.mem_append.mpr (Or.inl hs))
                      (modelAuxSlots_spec hslots0).1 hslot2get
                    have hname2 : (nextAuxIdent (Ident.mk
                        (auxName (auxTaken m slots0) i2))).name
                        = auxName (auxTaken m slots0) (i2 + 1) :=
                      nextAuxIdent_name (auxTaken m slots0) i2
                    rw [hname2]
                    exact hres2
                  have halt' : (extAssign store slots0
                      (modelAuxSlots m)).length
                      = (slots0 ++ modelAuxSlots m).length := by
                    rw [extAssign_length, List.length_append]
                  rw [toStore_read_model (m := m) hnu halt' hres,
                    bang_of_getElem? hareadaux2]
                -- the store reads at the table's names agree
                have hpre : ∀ w ∈ pre,
                    ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) w
                    = store w := by
                  intro w hw
                  apply hagree c hcmem w
                  rw [hargsc]
                  apply List.mem_flatMap.mpr
                  refine ⟨Expr.array (litSplitTab pre k post),
                    List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                  rw [Expr.idents, flatMap_idents_litSplitTab]
                  exact List.mem_append_left _ hw
                have hpost : ∀ w ∈ post,
                    ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) w
                    = store w := by
                  intro w hw
                  apply hagree c hcmem w
                  rw [hargsc]
                  apply List.mem_flatMap.mpr
                  refine ⟨Expr.array (litSplitTab pre k post),
                    List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
                  rw [Expr.idents, flatMap_idents_litSplitTab]
                  exact List.mem_append_right _ hw
                have hvs' : (auxTab pre (Ident.mk (auxName (auxTaken m slots0) i2)) post).mapM
                    (BasicExpr.eval ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore (extAssign store slots0 (modelAuxSlots m))))
                    = some vs := by
                  rw [mapM_eval_auxTab_congr (s := store) hauxread hpre hpost]
                  exact hvs
                -- the piece's Holds at the extended store
                have hxmem : x ∈ c.args.flatMap Expr.idents := by
                  rw [hargsc]
                  exact List.mem_flatMap.mpr
                    ⟨Expr.basic (.ident x), List.mem_cons_self,
                      List.mem_cons_self⟩
                have hh : ({ name := Ident.mk "array_var_int_element"
                           , args := [Expr.basic (.ident x),
                               Expr.array (auxTab pre (Ident.mk (auxName (auxTaken m slots0) i2)) post),
                               Expr.basic (.ident (nextAuxIdent
                                 (Ident.mk (auxName (auxTaken m slots0) i2))))]
                           , anns := [] } : ConstraintItem).Holds fullInterp
                    ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) := by
                  refine ⟨[.int idx, .array vs, .int k'], ?_, ?_⟩
                  · show (do
                        let v1 ← ((assemble m (slots0 ++ modelAuxSlots m)
                          dcs).toStore
                          (extAssign store slots0 (modelAuxSlots m))) x
                        let v2 ← Option.map Value.array ((auxTab pre (Ident.mk (auxName (auxTaken m slots0) i2)) post).mapM
                          (BasicExpr.eval ((assemble m
                            (slots0 ++ modelAuxSlots m) dcs).toStore
                            (extAssign store slots0 (modelAuxSlots m)))))
                        let v3 ← ((assemble m (slots0 ++ modelAuxSlots m)
                          dcs).toStore
                          (extAssign store slots0 (modelAuxSlots m)))
                          (nextAuxIdent (Ident.mk
                            (auxName (auxTaken m slots0) i2)))
                        pure [v1, v2, v3]) = _
                    rw [hagree c hcmem x hxmem, haux2read, hvs', hsx]
                    rfl
                  · change fullInterp (Ident.mk "array_var_int_element")
                      [.int idx, .array vs, .int k']
                    rw [fullInterp_of_extracted_elem "array_var_int_element"
                      (Or.inr (Or.inl rfl))]
                    show (match ([.int idx, .array vs, .int k'] : List Value)
                        with
                      | [.int i', .array xs, .int e'] =>
                          valuesGet1 xs i' = some (.int e')
                      | _ => False)
                    exact hget
                have halt' : (extAssign store slots0
                    (modelAuxSlots m)).length
                    = (slots0 ++ modelAuxSlots m).length := by
                  rw [extAssign_length, List.length_append]
                exact (DomConstraint.satisfiedB_iff _ _).mpr
                  (compile_holds_link hnu halt' hcc hh)
        | varElemTabKs x y tab =>
            -- PLAN C0 element values: the k-literal mixed table with a
            -- slot value; the piece is the all-slot table over the k
            -- pinned aux slots
            have hinv := auxShapeOf_varElemTabKs_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.ident y)] := hinv.2.1
            -- the source's semantic facts at the satisfying store
            obtain ⟨vs, vx, vy, hvs, hsx, hsy, hmatch⟩ :=
              holds_array_var_int_element hnamec hargsc (hcons c hcmem)
            obtain ⟨idx, e, hidx, he, hget⟩ : ∃ (idx : Int) (e : Int),
                vx = Value.int idx ∧ vy = Value.int e ∧
                valuesGet1 vs idx = some (.int e) := by
              cases vx with
              | int i =>
                  cases vy with
                  | int e =>
                      have h2 : (match [Value.int i, .array vs,
                          Value.int e] with
                        | [.int i, .array xs, .int e] =>
                            valuesGet1 xs i = some (.int e)
                        | _ => False) := hmatch
                      exact ⟨i, e, rfl, rfl, by simpa using h2⟩
                  | bool w => exact absurd hmatch (by simp)
                  | setOfInt w => exact absurd hmatch (by simp)
                  | array w => exact absurd hmatch (by simp)
              | bool w => exact absurd hmatch (by simp)
              | setOfInt w => exact absurd hmatch (by simp)
              | array w => exact absurd hmatch (by simp)
            subst hidx
            subst he
            -- the piece's form
            have hc'eq : c' =
                { name := Ident.mk "array_var_int_element"
                , args := [Expr.basic (.ident x),
                    Expr.array (mixSubst tab (auxChain (Ident.mk
                      (auxName (auxTaken m slots0) i2))
                      (tabLitVals tab).length)),
                    Expr.basic (.ident y)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hyi, hdcform⟩ :=
              compileConstraint_varElemTab_inv hcc
            -- the pinned aux reads at the extended store
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m)))
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabLitVals tab).length)[j]!
                  = some (.int (tabLitVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads_cov (m := m) (slots0 := slots0)
                (dcs := dcs) (store := store) (taken := auxTaken m slots0)
                (n := i2) (N := (tabLitVals tab).length)
                (vs := (tabLitVals tab).map Value.int)
                (by intro s hs; exact List.mem_append.mpr (Or.inl hs))
                (fun j p hp => (modelAuxSlots_spec hslots0).1 j p hp)
                hnu (by rw [extAssign_length, List.length_append])
                (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varElemTabKs]
                    exact hi2')
                  rw [pinsK_varElemTabKs] at h2
                  exact h2)
                j hj
              rw [getElem!_map_eq (tabLitVals tab) Value.int hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length = (tabLitVals tab).length :=
              auxChain_length _ _
            -- the store reads at the table's names agree
            have hid : ∀ w, (.ident w : BasicExpr) ∈ tab →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) w = store w := by
              intro w hw
              apply hagree c hcmem w
              rw [hargsc]
              apply List.mem_flatMap.mpr
              refine ⟨Expr.array tab,
                List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
              rw [Expr.idents]
              exact mem_flatMap_idents_of_mem hw
            -- the table-read congruence
            have hvs' : (mixSubst tab (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length)).mapM
                (BasicExpr.eval ((assemble m (slots0 ++ modelAuxSlots m)
                  dcs).toStore (extAssign store slots0 (modelAuxSlots m))))
                = some vs := by
              rw [mapM_eval_mixSubst_congr (s := store) hlen hauxread hid]
              exact hvs
            -- the piece's Holds at the extended store
            have hxmem : x ∈ c.args.flatMap Expr.idents := by
              rw [hargsc]
              exact List.mem_flatMap.mpr
                ⟨Expr.basic (.ident x), List.mem_cons_self,
                  List.mem_cons_self⟩
            have hymem : y ∈ c.args.flatMap Expr.idents := by
              rw [hargsc]
              exact List.mem_flatMap.mpr
                ⟨Expr.basic (.ident y),
                  List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self),
                  List.mem_cons_self⟩
            have hh : ({ name := Ident.mk "array_var_int_element"
                       , args := [Expr.basic (.ident x),
                           Expr.array (mixSubst tab (auxChain (Ident.mk
                             (auxName (auxTaken m slots0) i2))
                             (tabLitVals tab).length)),
                           Expr.basic (.ident y)]
                       , anns := [] } : ConstraintItem).Holds fullInterp
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) := by
              refine ⟨[.int idx, .array vs, .int e], ?_, ?_⟩
              · show (do
                    let v1 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) x
                    let v2 ← Option.map Value.array ((mixSubst tab (auxChain
                      (Ident.mk (auxName (auxTaken m slots0) i2))
                      (tabLitVals tab).length)).mapM
                      (BasicExpr.eval ((assemble m
                        (slots0 ++ modelAuxSlots m) dcs).toStore
                        (extAssign store slots0 (modelAuxSlots m)))))
                    let v3 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) y
                    pure [v1, v2, v3]) = _
                rw [hagree c hcmem x hxmem, hagree c hcmem y hymem,
                  hvs', hsx, hsy]
                rfl
              · change fullInterp (Ident.mk "array_var_int_element")
                  [.int idx, .array vs, .int e]
                rw [fullInterp_of_extracted_elem "array_var_int_element"
                  (Or.inr (Or.inl rfl))]
                show (match ([.int idx, .array vs, .int e] : List Value)
                    with
                  | [.int i', .array xs, .int e'] =>
                      valuesGet1 xs i' = some (.int e')
                  | _ => False)
                exact hget
            have halt' : (extAssign store slots0 (modelAuxSlots m)).length
                = (slots0 ++ modelAuxSlots m).length := by
              rw [extAssign_length, List.length_append]
            exact (DomConstraint.satisfiedB_iff _ _).mpr
              (compile_holds_link hnu halt' hcc hh)
        | varElemTabValKs x tab k' =>
            -- PLAN C0 element values: the k-literal mixed table with a
            -- literal value; the value rides the successor slot
            have hinv := auxShapeOf_varElemTabValKs_inv hshape
            have hnamec : c.name.name = "array_var_int_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.lit (.int k'))] := hinv.2.1
            -- the source's semantic facts at the satisfying store
            obtain ⟨idx, vs, hsx, hvs, hget⟩ :=
              holds_arrayVarElement_litVal_gen hnamec hargsc (hcons c hcmem)
            -- the piece's form
            have hc'eq : c' =
                { name := Ident.mk "array_var_int_element"
                , args := [Expr.basic (.ident x),
                    Expr.array (mixSubst tab (auxChain (Ident.mk
                      (auxName (auxTaken m slots0) i2))
                      (tabLitVals tab).length)),
                    Expr.basic (.ident (auxChainLast (Ident.mk
                      (auxName (auxTaken m slots0) i2))
                      (tabLitVals tab).length))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hki, hdcform⟩ :=
              compileConstraint_varElemTab_inv hcc
            -- the pinned aux reads at the extended store
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m)))
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabLitVals tab).length)[j]!
                  = some (.int (tabLitVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads_cov (m := m) (slots0 := slots0)
                (dcs := dcs) (store := store) (taken := auxTaken m slots0)
                (n := i2) (N := (tabLitVals tab).length)
                (vs := (tabLitVals tab).map Value.int)
                (by intro s hs; exact List.mem_append.mpr (Or.inl hs))
                (fun j p hp => (modelAuxSlots_spec hslots0).1 j p hp)
                hnu (by rw [extAssign_length, List.length_append])
                (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varElemTabValKs]
                    omega)
                  rw [pinsK_varElemTabValKs] at h2
                  rwa [getElem!_append_left (by rw [List.length_map]; exact hi2')] at h2)
                j hj
              rw [getElem!_map_eq (tabLitVals tab) Value.int hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length).length = (tabLitVals tab).length :=
              auxChain_length _ _
            -- the value slot's resolution and extended-store read
            have hvres : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                  (tabLitVals tab).length).name
                = some (slots0.length + (i2 + (tabLitVals tab).length)) := by
              have hname2 : (auxChainLast (Ident.mk
                  (auxName (auxTaken m slots0) i2))
                  (tabLitVals tab).length).name
                  = auxName (auxTaken m slots0)
                      (i2 + (tabLitVals tab).length) := by
                rw [auxChainLast_eq]
              rw [hname2]
              exact nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0)
                (i := i2 + (tabLitVals tab).length)
                (vs := [Value.int k'])
                (hsub := by
                  intro s hs
                  exact List.mem_append.mpr (Or.inl hs))
                (modelAuxSlots_spec hslots0).1
                (by
                  have h2 := hpins (tabLitVals tab).length (by
                    rw [pinsK_length_varElemTabValKs]
                    omega)
                  rw [pinsK_varElemTabValKs] at h2
                  rw [getElem!_append_right
                    (by rw [List.length_map]; omega)] at h2
                  have hsub2 : (tabLitVals tab).length
                      - (List.map Value.int (tabLitVals tab)).length = 0 := by
                    rw [List.length_map, Nat.sub_self]
                  rw [hsub2] at h2
                  simpa using h2)
            have hvalpin : (modelAuxSlots m)[i2 + (tabLitVals tab).length]?
                = some (auxName (auxTaken m slots0)
                    (i2 + (tabLitVals tab).length), [Value.int k']) := by
              have h2 := hpins (tabLitVals tab).length (by
                rw [pinsK_length_varElemTabValKs]
                omega)
              rw [pinsK_varElemTabValKs] at h2
              rw [getElem!_append_right
                (by rw [List.length_map]; omega)] at h2
              have hsub2 : (tabLitVals tab).length
                  - (List.map Value.int (tabLitVals tab)).length = 0 := by
                rw [List.length_map, Nat.sub_self]
              rw [hsub2] at h2
              simpa using h2
            have haux2read : ((assemble m (slots0 ++ modelAuxSlots m)
                  dcs).toStore (extAssign store slots0 (modelAuxSlots m)))
                  (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabLitVals tab).length) = some (.int k') := by
              have halt'' : (extAssign store slots0 (modelAuxSlots m)).length
                  = (slots0 ++ modelAuxSlots m).length := by
                rw [extAssign_length, List.length_append]
              have hvalread : (extAssign store slots0 (modelAuxSlots m))[slots0.length + (i2 + (tabLitVals tab).length)]?
                  = some (Value.int k') := by
                have hread := extAssign_aux_read (store := store)
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (i := i2 + (tabLitVals tab).length)
                  (List.getElem?_eq_some_iff.mp hvalpin).1
                rw [hread]
                have hlt : i2 + (tabLitVals tab).length
                    < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hvalpin).1
                have hpair : (modelAuxSlots m)[i2 + (tabLitVals tab).length]
                    = (auxName (auxTaken m slots0)
                        (i2 + (tabLitVals tab).length), [Value.int k']) := by
                  have hplain : (modelAuxSlots m)[i2 + (tabLitVals tab).length]?
                      = some (modelAuxSlots m)[i2 + (tabLitVals tab).length] :=
                    List.getElem?_eq_getElem hlt
                  rw [hvalpin] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              rw [toStore_read_model (m := m) hnu halt'' hvres,
                bang_of_getElem? hvalread]
            have hvalkk : kk = slots0.length + (i2 + (tabLitVals tab).length) := by
              exact Option.some.inj (hki.symm.trans hvres)
            -- the store reads at the table's names agree
            have hid : ∀ w, (.ident w : BasicExpr) ∈ tab →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) w = store w := by
              intro w hw
              apply hagree c hcmem w
              rw [hargsc]
              apply List.mem_flatMap.mpr
              refine ⟨Expr.array tab,
                List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
              rw [Expr.idents]
              exact mem_flatMap_idents_of_mem hw
            have hvs' : (mixSubst tab (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabLitVals tab).length)).mapM
                (BasicExpr.eval ((assemble m (slots0 ++ modelAuxSlots m)
                  dcs).toStore (extAssign store slots0 (modelAuxSlots m))))
                = some vs := by
              rw [mapM_eval_mixSubst_congr (s := store) hlen hauxread hid]
              exact hvs
            -- the piece's Holds at the extended store
            have hxmem : x ∈ c.args.flatMap Expr.idents := by
              rw [hargsc]
              exact List.mem_flatMap.mpr
                ⟨Expr.basic (.ident x), List.mem_cons_self,
                  List.mem_cons_self⟩
            have hh : ({ name := Ident.mk "array_var_int_element"
                       , args := [Expr.basic (.ident x),
                           Expr.array (mixSubst tab (auxChain (Ident.mk
                             (auxName (auxTaken m slots0) i2))
                             (tabLitVals tab).length)),
                           Expr.basic (.ident (auxChainLast (Ident.mk
                             (auxName (auxTaken m slots0) i2))
                             (tabLitVals tab).length))]
                       , anns := [] } : ConstraintItem).Holds fullInterp
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) := by
              refine ⟨[.int idx, .array vs, .int k'], ?_, ?_⟩
              · show (do
                    let v1 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) x
                    let v2 ← Option.map Value.array ((mixSubst tab (auxChain
                      (Ident.mk (auxName (auxTaken m slots0) i2))
                      (tabLitVals tab).length)).mapM
                      (BasicExpr.eval ((assemble m
                        (slots0 ++ modelAuxSlots m) dcs).toStore
                        (extAssign store slots0 (modelAuxSlots m)))))
                    let v3 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m)))
                      (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                        (tabLitVals tab).length)
                    pure [v1, v2, v3]) = _
                rw [hagree c hcmem x hxmem, haux2read, hvs', hsx]
                rfl
              · change fullInterp (Ident.mk "array_var_int_element")
                  [.int idx, .array vs, .int k']
                rw [fullInterp_of_extracted_elem "array_var_int_element"
                  (Or.inr (Or.inl rfl))]
                show (match ([.int idx, .array vs, .int k'] : List Value)
                    with
                  | [.int i', .array xs, .int e'] =>
                      valuesGet1 xs i' = some (.int e')
                  | _ => False)
                exact hget
            have halt' : (extAssign store slots0 (modelAuxSlots m)).length
                = (slots0 ++ modelAuxSlots m).length := by
              rw [extAssign_length, List.length_append]
            exact (DomConstraint.satisfiedB_iff _ _).mpr
              (compile_holds_link hnu halt' hcc hh)
        | varBoolTabLits x y tab =>
            -- PLAN C0 element values, bool tables: the mixed bool table
            -- with a slot value; the piece is the all-slot table over
            -- the pinned aux slots
            have hinv := auxShapeOf_varBoolTabLits_inv hshape
            have hnamec : c.name.name = "array_var_bool_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.ident y)] := hinv.2.1
            -- the source's semantic facts at the satisfying store
            obtain ⟨vs, vx, vy, hvs, hsx, hsy, hmatch⟩ :=
              holds_array_var_bool_element hnamec hargsc (hcons c hcmem)
            obtain ⟨idx, e, hidx, he, hget⟩ : ∃ (idx : Int) (e : Bool),
                vx = Value.int idx ∧ vy = Value.bool e ∧
                valuesGet1 vs idx = some (.bool e) := by
              cases vx with
              | int i =>
                  cases vy with
                  | bool e =>
                      have h2 : (match [Value.int i, .array vs,
                          Value.bool e] with
                        | [.int i, .array xs, .bool e] =>
                            valuesGet1 xs i = some (.bool e)
                        | _ => False) := hmatch
                      exact ⟨i, e, rfl, rfl, by simpa using h2⟩
                  | int w => exact absurd hmatch (by simp)
                  | setOfInt w => exact absurd hmatch (by simp)
                  | array w => exact absurd hmatch (by simp)
              | bool w => exact absurd hmatch (by simp)
              | setOfInt w => exact absurd hmatch (by simp)
              | array w => exact absurd hmatch (by simp)
            subst hidx
            subst he
            -- the piece's form
            have hc'eq : c' =
                { name := Ident.mk "array_var_bool_element"
                , args := [Expr.basic (.ident x),
                    Expr.array (mixSubstB tab (auxChain (Ident.mk
                      (auxName (auxTaken m slots0) i2))
                      (tabBoolVals tab).length)),
                    Expr.basic (.ident y)]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hyi, hdcform⟩ :=
              compileConstraint_varBoolTab_inv hcc
            -- the pinned aux reads at the extended store
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m)))
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabBoolVals tab).length)[j]!
                  = some (.bool (tabBoolVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads_cov (m := m) (slots0 := slots0)
                (dcs := dcs) (store := store) (taken := auxTaken m slots0)
                (n := i2) (N := (tabBoolVals tab).length)
                (vs := (tabBoolVals tab).map Value.bool)
                (by intro w hw; exact List.mem_append.mpr (Or.inl hw))
                (fun j2 p hp => (modelAuxSlots_spec hslots0).1 j2 p hp)
                hnu (by rw [extAssign_length, List.length_append])
                (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varBoolTabLits]
                    exact hi2')
                  rw [pinsK_varBoolTabLits] at h2
                  exact h2)
                j hj
              rw [getElem!_map_eq (tabBoolVals tab) Value.bool hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length = (tabBoolVals tab).length :=
              auxChain_length _ _
            -- the store reads at the table's names agree
            have hid : ∀ w, (.ident w : BasicExpr) ∈ tab →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) w = store w := by
              intro w hw
              apply hagree c hcmem w
              rw [hargsc]
              apply List.mem_flatMap.mpr
              refine ⟨Expr.array tab,
                List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
              rw [Expr.idents]
              exact mem_flatMap_idents_of_mem hw
            -- the table-read congruence
            have hvs' : (mixSubstB tab (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length)).mapM
                (BasicExpr.eval ((assemble m (slots0 ++ modelAuxSlots m)
                  dcs).toStore (extAssign store slots0 (modelAuxSlots m))))
                = some vs := by
              rw [mapM_eval_mixSubstB_congr (s := store) hlen hauxread hid]
              exact hvs
            -- the piece's Holds at the extended store
            have hxmem : x ∈ c.args.flatMap Expr.idents := by
              rw [hargsc]
              exact List.mem_flatMap.mpr
                ⟨Expr.basic (.ident x), List.mem_cons_self,
                  List.mem_cons_self⟩
            have hymem : y ∈ c.args.flatMap Expr.idents := by
              rw [hargsc]
              exact List.mem_flatMap.mpr
                ⟨Expr.basic (.ident y),
                  List.mem_cons_of_mem _
                    (List.mem_cons_of_mem _ List.mem_cons_self),
                  List.mem_cons_self⟩
            have hh : ({ name := Ident.mk "array_var_bool_element"
                       , args := [Expr.basic (.ident x),
                           Expr.array (mixSubstB tab (auxChain (Ident.mk
                             (auxName (auxTaken m slots0) i2))
                             (tabBoolVals tab).length)),
                           Expr.basic (.ident y)]
                       , anns := [] } : ConstraintItem).Holds fullInterp
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) := by
              refine ⟨[.int idx, .array vs, .bool e], ?_, ?_⟩
              · show (do
                    let v1 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) x
                    let v2 ← Option.map Value.array ((mixSubstB tab (auxChain
                      (Ident.mk (auxName (auxTaken m slots0) i2))
                      (tabBoolVals tab).length)).mapM
                      (BasicExpr.eval ((assemble m
                        (slots0 ++ modelAuxSlots m) dcs).toStore
                        (extAssign store slots0 (modelAuxSlots m)))))
                    let v3 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) y
                    pure [v1, v2, v3]) = _
                rw [hagree c hcmem x hxmem, hagree c hcmem y hymem,
                  hvs', hsx, hsy]
                rfl
              · change fullInterp (Ident.mk "array_var_bool_element")
                  [.int idx, .array vs, .bool e]
                rw [fullInterp_of_extracted_elem "array_var_bool_element"
                  (Or.inr (Or.inr rfl))]
                show (match ([.int idx, .array vs, .bool e] : List Value)
                    with
                  | [.int i', .array xs, .bool e'] =>
                      valuesGet1 xs i' = some (.bool e')
                  | _ => False)
                exact hget
            have halt' : (extAssign store slots0 (modelAuxSlots m)).length
                = (slots0 ++ modelAuxSlots m).length := by
              rw [extAssign_length, List.length_append]
            exact (DomConstraint.satisfiedB_iff _ _).mpr
              (compile_holds_link hnu halt' hcc hh)
        | varBoolTabValLit x tab b' =>
            -- PLAN C0 element values, bool tables: the mixed bool table
            -- with a literal value; the value rides the successor slot
            have hinv := auxShapeOf_varBoolTabValLit_inv hshape
            have hnamec : c.name.name = "array_var_bool_element" := hinv.1
            have hargsc : c.args = [Expr.basic (.ident x), Expr.array tab,
                Expr.basic (.lit (.bool b'))] := hinv.2.1
            -- the source's semantic facts at the satisfying store
            obtain ⟨idx, vs, hsx, hvs, hget⟩ :=
              holds_arrayVarBoolElement_litVal_gen hnamec hargsc
                (hcons c hcmem)
            -- the piece's form
            have hc'eq : c' =
                { name := Ident.mk "array_var_bool_element"
                , args := [Expr.basic (.ident x),
                    Expr.array (mixSubstB tab (auxChain (Ident.mk
                      (auxName (auxTaken m slots0) i2))
                      (tabBoolVals tab).length)),
                    Expr.basic (.ident (auxChainLast (Ident.mk
                      (auxName (auxTaken m slots0) i2))
                      (tabBoolVals tab).length))]
                , anns := [] } := by
              simp only [AuxShape.expand, List.mem_cons, List.not_mem_nil]
                at hpiece
              rcases hpiece with hpiece | hcontr
              · exact hpiece
              · exact absurd hcontr (by simp)
            subst hc'eq
            -- the piece's compile inversion
            obtain ⟨is, i, kk, his, hxi, hki, hdcform⟩ :=
              compileConstraint_varBoolTab_inv hcc
            -- the pinned aux reads at the extended store
            have hauxread : ∀ j, j < (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m)))
                  (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabBoolVals tab).length)[j]!
                  = some (.bool (tabBoolVals tab)[j]!) := by
              intro j hj
              rw [auxChain_length] at hj
              have h := auxChain_reads_cov (m := m) (slots0 := slots0)
                (dcs := dcs) (store := store) (taken := auxTaken m slots0)
                (n := i2) (N := (tabBoolVals tab).length)
                (vs := (tabBoolVals tab).map Value.bool)
                (by intro w hw; exact List.mem_append.mpr (Or.inl hw))
                (fun j2 p hp => (modelAuxSlots_spec hslots0).1 j2 p hp)
                hnu (by rw [extAssign_length, List.length_append])
                (fun i2' hi2' => by
                  have h2 := hpins i2' (by
                    rw [pinsK_length_varBoolTabValLit]
                    omega)
                  rw [pinsK_varBoolTabValLit] at h2
                  rwa [getElem!_append_left
                    (by rw [List.length_map]; exact hi2')] at h2)
                j hj
              rw [getElem!_map_eq (tabBoolVals tab) Value.bool hj] at h
              exact h
            have hlen : (auxChain (Ident.mk (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length).length = (tabBoolVals tab).length :=
              auxChain_length _ _
            -- the value slot's resolution and extended-store read
            have hvres : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                  (tabBoolVals tab).length).name
                = some (slots0.length + (i2 + (tabBoolVals tab).length)) := by
              have hname2 : (auxChainLast (Ident.mk
                  (auxName (auxTaken m slots0) i2))
                  (tabBoolVals tab).length).name
                  = auxName (auxTaken m slots0)
                      (i2 + (tabBoolVals tab).length) := by
                rw [auxChainLast_eq]
              rw [hname2]
              exact nameIndex_aux_slot
                (slots0 := slots0) (auxs := modelAuxSlots m)
                (taken := auxTaken m slots0)
                (i := i2 + (tabBoolVals tab).length)
                (vs := [Value.bool b'])
                (hsub := by
                  intro w hw
                  exact List.mem_append.mpr (Or.inl hw))
                (modelAuxSlots_spec hslots0).1
                (by
                  have h2 := hpins (tabBoolVals tab).length (by
                    rw [pinsK_length_varBoolTabValLit]
                    omega)
                  rw [pinsK_varBoolTabValLit] at h2
                  rw [getElem!_append_right
                    (by rw [List.length_map]; omega)] at h2
                  have hsub2 : (tabBoolVals tab).length
                      - (List.map Value.bool (tabBoolVals tab)).length = 0 := by
                    rw [List.length_map, Nat.sub_self]
                  rw [hsub2] at h2
                  simpa using h2)
            have hvalpin : (modelAuxSlots m)[i2 + (tabBoolVals tab).length]?
                = some (auxName (auxTaken m slots0)
                    (i2 + (tabBoolVals tab).length), [Value.bool b']) := by
              have h2 := hpins (tabBoolVals tab).length (by
                rw [pinsK_length_varBoolTabValLit]
                omega)
              rw [pinsK_varBoolTabValLit] at h2
              rw [getElem!_append_right
                (by rw [List.length_map]; omega)] at h2
              have hsub2 : (tabBoolVals tab).length
                  - (List.map Value.bool (tabBoolVals tab)).length = 0 := by
                rw [List.length_map, Nat.sub_self]
              rw [hsub2] at h2
              simpa using h2
            have haux2read : ((assemble m (slots0 ++ modelAuxSlots m)
                  dcs).toStore (extAssign store slots0 (modelAuxSlots m)))
                  (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                    (tabBoolVals tab).length) = some (.bool b') := by
              have halt'' : (extAssign store slots0 (modelAuxSlots m)).length
                  = (slots0 ++ modelAuxSlots m).length := by
                rw [extAssign_length, List.length_append]
              have hvalread : (extAssign store slots0
                    (modelAuxSlots m))[slots0.length + (i2 + (tabBoolVals tab).length)]?
                  = some (Value.bool b') := by
                have hread := extAssign_aux_read (store := store)
                  (slots0 := slots0) (auxs := modelAuxSlots m)
                  (i := i2 + (tabBoolVals tab).length)
                  (List.getElem?_eq_some_iff.mp hvalpin).1
                rw [hread]
                have hlt : i2 + (tabBoolVals tab).length
                    < (modelAuxSlots m).length :=
                  (List.getElem?_eq_some_iff.mp hvalpin).1
                have hpair : (modelAuxSlots m)[i2 + (tabBoolVals tab).length]
                    = (auxName (auxTaken m slots0)
                        (i2 + (tabBoolVals tab).length), [Value.bool b']) := by
                  have hplain : (modelAuxSlots m)[i2 + (tabBoolVals tab).length]?
                      = some (modelAuxSlots m)[i2 + (tabBoolVals tab).length] :=
                    List.getElem?_eq_getElem hlt
                  rw [hvalpin] at hplain
                  exact (Option.some.inj hplain).symm
                rw [hpair]
                rfl
              rw [toStore_read_model (m := m) hnu halt'' hvres,
                bang_of_getElem? hvalread]
            have hvalkk : kk = slots0.length + (i2 + (tabBoolVals tab).length) := by
              exact Option.some.inj (hki.symm.trans hvres)
            -- the store reads at the table's names agree
            have hid : ∀ w, (.ident w : BasicExpr) ∈ tab →
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) w = store w := by
              intro w hw
              apply hagree c hcmem w
              rw [hargsc]
              apply List.mem_flatMap.mpr
              refine ⟨Expr.array tab,
                List.mem_cons_of_mem _ List.mem_cons_self, ?_⟩
              rw [Expr.idents]
              exact mem_flatMap_idents_of_mem hw
            have hvs' : (mixSubstB tab (auxChain (Ident.mk
                (auxName (auxTaken m slots0) i2))
                (tabBoolVals tab).length)).mapM
                (BasicExpr.eval ((assemble m (slots0 ++ modelAuxSlots m)
                  dcs).toStore (extAssign store slots0 (modelAuxSlots m))))
                = some vs := by
              rw [mapM_eval_mixSubstB_congr (s := store) hlen hauxread hid]
              exact hvs
            -- the piece's Holds at the extended store
            have hxmem : x ∈ c.args.flatMap Expr.idents := by
              rw [hargsc]
              exact List.mem_flatMap.mpr
                ⟨Expr.basic (.ident x), List.mem_cons_self,
                  List.mem_cons_self⟩
            have hh : ({ name := Ident.mk "array_var_bool_element"
                       , args := [Expr.basic (.ident x),
                           Expr.array (mixSubstB tab (auxChain (Ident.mk
                             (auxName (auxTaken m slots0) i2))
                             (tabBoolVals tab).length)),
                           Expr.basic (.ident (auxChainLast (Ident.mk
                             (auxName (auxTaken m slots0) i2))
                             (tabBoolVals tab).length))]
                       , anns := [] } : ConstraintItem).Holds fullInterp
                ((assemble m (slots0 ++ modelAuxSlots m) dcs).toStore
                  (extAssign store slots0 (modelAuxSlots m))) := by
              refine ⟨[.int idx, .array vs, .bool b'], ?_, ?_⟩
              · show (do
                    let v1 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m))) x
                    let v2 ← Option.map Value.array ((mixSubstB tab (auxChain
                      (Ident.mk (auxName (auxTaken m slots0) i2))
                      (tabBoolVals tab).length)).mapM
                      (BasicExpr.eval ((assemble m
                        (slots0 ++ modelAuxSlots m) dcs).toStore
                        (extAssign store slots0 (modelAuxSlots m)))))
                    let v3 ← ((assemble m (slots0 ++ modelAuxSlots m)
                      dcs).toStore
                      (extAssign store slots0 (modelAuxSlots m)))
                      (auxChainLast (Ident.mk (auxName (auxTaken m slots0) i2))
                        (tabBoolVals tab).length)
                    pure [v1, v2, v3]) = _
                rw [hagree c hcmem x hxmem, haux2read, hvs', hsx]
                rfl
              · change fullInterp (Ident.mk "array_var_bool_element")
                  [.int idx, .array vs, .bool b']
                rw [fullInterp_of_extracted_elem "array_var_bool_element"
                  (Or.inr (Or.inr rfl))]
                show (match ([.int idx, .array vs, .bool b'] : List Value)
                    with
                  | [.int i', .array xs, .bool e'] =>
                      valuesGet1 xs i' = some (.bool e')
                  | _ => False)
                exact hget
            have halt' : (extAssign store slots0 (modelAuxSlots m)).length
                = (slots0 ++ modelAuxSlots m).length := by
              rw [extAssign_length, List.length_append]
            exact (DomConstraint.satisfiedB_iff _ _).mpr
              (compile_holds_link hnu halt' hcc hh)
        | orFalse x y =>
            -- the args + name inversion: c is bool_or(x, y, false)
            have hargsc : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
                Expr.basic (.lit (.bool false))] := auxShapeOf_orFalse_args hshape
            have hnamec : c.name.name = "bool_or" :=
              auxShapeOf_orFalse_name hshape
            -- the store's semantic facts: store x = .bool p,
            -- store y = .bool q, (p || q) = false
            obtain ⟨p, q, hsx, hsy, hpq⟩ : ∃ p q, store x = some (.bool p) ∧
                store y = some (.bool q) ∧ (p || q) = false := by
              obtain ⟨args, hmap, hinterp⟩ := hcons c hcmem
              rw [hargsc] at hmap
              have hchain : Option.bind (Expr.eval store (Expr.basic (.ident x)))
                  (fun v1 => Option.bind (Expr.eval store (Expr.basic (.ident y)))
                    (fun v2 => Option.bind (Expr.eval store (Expr.basic (.lit (.bool false))))
                      (fun v3 => some [v1, v2, v3]))) = some args := by
                simpa [List.mapM_cons, List.mapM_nil, Option.bind_assoc] using hmap
              have hv3' : Expr.eval store (Expr.basic (.lit (.bool false)))
                  = some (.bool false) := rfl
              have hredx : Expr.eval store (Expr.basic (.ident x))
                  = store x := rfl
              have hredy : Expr.eval store (Expr.basic (.ident y))
                  = store y := rfl
              rw [hv3', hredx, hredy] at hchain
              cases hsx : store x with
              | none => rw [hsx] at hchain; simp at hchain
              | some v1 =>
                  rw [hsx] at hchain
                  simp only [Option.bind_some] at hchain
                  cases hsy : store y with
                  | none => rw [hsy] at hchain; simp at hchain
                  | some v2 =>
                      rw [hsy] at hchain
                      simp only [Option.bind_some] at hchain
                      have hargsv : args = [v1, v2, .bool false] := by
                        simpa using hchain.symm
                      subst hargsv
                      have h1 : fullInterp (Ident.mk "bool_or") [v1, v2, .bool false] :=
                        interp_of_hname hnamec hinterp
                      rw [fullInterp_std (by decide)] at h1
                      have hmatch : (match [v1, v2, Value.bool false] with
                        | [Value.bool a, Value.bool b, Value.bool w] => w = (a || b)
                        | _ => False) := h1
                      cases v1 with
                      | bool p =>
                          cases v2 with
                          | bool q =>
                              exact ⟨p, q, rfl, rfl, by simpa using hmatch⟩
                          | int w => exact absurd hmatch (by simp)
                          | setOfInt w => exact absurd hmatch (by simp)
                          | array w => exact absurd hmatch (by simp)
                      | int w => exact absurd hmatch (by simp)
                      | setOfInt w => exact absurd hmatch (by simp)
                      | array w => exact absurd hmatch (by simp)
            -- p = false and q = false (the disjunction is false)
            obtain ⟨hp, hq⟩ := Bool.or_eq_false_iff.mp hpq
            -- the piece is ONE of the two bool_not pieces
            rcases List.mem_cons.mp hpiece with hp1 | hrest
            · -- piece 1: bool_not(x, true)
              have hc'eq : c' =
                  { name := Ident.mk "bool_not"
                  , args := [Expr.basic (.ident x), Expr.basic (.lit (.bool true))]
                  , anns := [] } := hp1
              subst hc'eq
              obtain ⟨i, hxi, hdcform⟩ := compileConstraint_bool_not_lit_inv hcc
              rw [show (Bool.not true) = false from rfl] at hdcform
              rw [hdcform]
              -- x's model position: x is declared
              have hxarg : Expr.basic (.ident x) ∈ c.args := by
                rw [hargsc]; exact List.mem_cons_self
              have hxstatic : m.staticEnv x ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hxarg
              have hxilt : i < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hxstatic hxi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    x.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : i = j2 := Option.some.inj (hxi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) x.name i hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v1, hv1read, _⟩ := hreads i hxilt
              have hareadi : (extAssign store slots0 (modelAuxSlots m))[i]?
                  = store x := extAssign_read_ident hxilt hxi ⟨v1, hv1read⟩
              -- the satisfaction: constEq i (.bool false)
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                (by
                  show (extAssign store slots0 (modelAuxSlots m))[i]? =
                    some (Value.bool false)
                  rw [hareadi, hsx, ← hp])
            · -- piece 2: bool_not(y, true)
              have hp2 := List.mem_singleton.mp hrest
              have hc'eq : c' =
                  { name := Ident.mk "bool_not"
                  , args := [Expr.basic (.ident y), Expr.basic (.lit (.bool true))]
                  , anns := [] } := hp2
              subst hc'eq
              obtain ⟨j, hyi, hdcform⟩ := compileConstraint_bool_not_lit_inv hcc
              rw [show (Bool.not true) = false from rfl] at hdcform
              rw [hdcform]
              -- y's model position: y is declared
              have hyarg : Expr.basic (.ident y) ∈ c.args := by
                rw [hargsc]
                exact List.mem_cons_of_mem _ List.mem_cons_self
              have hystatic : m.staticEnv y ≠ none :=
                staticEnv_of_ident_arg hwf hcmem hyarg
              have hyjlt : j < slots0.length := by
                obtain ⟨j2, hj2⟩ := argIdent_model_position (c := c)
                  hvarsbasic hslots0 hauxfresh hystatic hyi
                have hext : nameIndex ((slots0 ++ modelAuxSlots m).map Prod.fst)
                    y.name = some j2 := nameIndex_ext_eq_model hj2
                have hji : j = j2 := Option.some.inj (hyi.symm.trans hext)
                subst hji
                have h1 := (nameIndex_some (slots0.map Prod.fst) y.name j hj2).1
                have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
                omega
              obtain ⟨v2, hv2read, _⟩ := hreads j hyjlt
              have hareadj : (extAssign store slots0 (modelAuxSlots m))[j]?
                  = store y := extAssign_read_ident hyjlt hyi ⟨v2, hv2read⟩
              -- the satisfaction: constEq j (.bool false)
              exact (DomConstraint.satisfiedB_iff _ _).mpr
                (by
                  show (extAssign store slots0 (modelAuxSlots m))[j]? =
                    some (Value.bool false)
                  rw [hareadj, hsy, ← hq])
    rw [show accepts problem (extAssign store slots0 (modelAuxSlots m))
        = problem.constraints.all
        (fun c => c.satisfiedB (extAssign store slots0 (modelAuxSlots m)))
        from rfl]
    exact List.all_eq_true.mpr hall

/-- Every value of a successfully compiled problem's domains has an
    integer view: the compiler's slot extraction only produces
    int/bool values (`varDomain` yields only `.intDom`/`.boolDom`,
    whose `values` are `.int`/`.bool`), and `assemble` copies the
    slots' value lists verbatim. -/
theorem domains_intViewed {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem) :
    ∀ d ∈ problem.domains, ∀ v ∈ d, LeanFzn.Semantics.Value.intView v ≠ none := by
  obtain ⟨_, slots, dcs, ⟨slots0, hslots0, hslots⟩, hcomp, hasm⟩ :=
    compileModel_ok_inv hc
  -- the domains are the extended slots' value lists
  have hdoms : problem.domains = slots.map (fun p => Dom.ofList p.2) := by
    show problem.domains = slots.map (fun p => Dom.ofList p.2)
    rw [hasm]
    rfl
  rw [hdoms, hslots, List.map_append]
  intro d hd v hv
  -- the model half or the aux half
  rcases List.mem_append.mp hd with hmodel | haux
  · -- a model slot's domain: the original argument
    obtain ⟨p, hpmem, hpget⟩ := List.mem_map.mp hmodel
    -- the slot at some position comes from a declared variable
    obtain ⟨d2, hd2mem, hds⟩ := declSlots_mem m.variables slots0
      (declSlots_of_slotsChecked hslots0) p hpmem
    -- the variable is basic and initializer-free (the gate)
    obtain ⟨ty, n, anns, hshape⟩ := compileModel_vars_basic hc d2 hd2mem
    -- the slot pair is (n.name, dom.values) with varDomain ty = .ok dom
    obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv
      (p := p) (by rw [← hshape]; exact hds)
    -- v ∈ dom.values (via the pair equality)
    have hvdom : v ∈ dom.values := by
      rw [← hpget, hpair] at hv
      simpa using (mem_ofList_iff v ((n.name, dom.values).2)).mp hv
    -- dom is intDom or boolDom; values are int/bool
    cases hdom2 : dom with
    | intDom xs =>
        have hvals : dom.values = xs.map LeanFzn.Semantics.Value.int := by
          show dom.values = xs.map LeanFzn.Semantics.Value.int
          rw [hdom2]
          rfl
        rw [hvals] at hvdom
        obtain ⟨x, hxmem, hxv⟩ := List.mem_map.mp hvdom
        intro hcon
        rw [← hxv] at hcon
        exact absurd hcon (by simp [LeanFzn.Semantics.Value.intView])
    | boolDom =>
        have hvals : dom.values = [LeanFzn.Semantics.Value.bool false,
          LeanFzn.Semantics.Value.bool true] := by
          show dom.values = _
          rw [hdom2]
          rfl
        rw [hvals] at hvdom
        rcases List.mem_cons.mp hvdom with rfl | htl
        · intro hcon; exact absurd hcon (by simp [LeanFzn.Semantics.Value.intView])
        · rcases List.mem_cons.mp htl with rfl | hnil
          · intro hcon
            exact absurd hcon (by simp [LeanFzn.Semantics.Value.intView])
          · exact absurd hnil (by simp)
  · -- an aux slot's domain: a singleton pin (an int or bool value)
    obtain ⟨p, hpmem, hpget⟩ := List.mem_map.mp haux
    obtain ⟨v2, hsingle⟩ := (modelAuxSlots_spec hslots0).2 p hpmem
    rw [← hpget, hsingle] at hv
    have hvmem : v ∈ [v2] := by
      simpa using (mem_ofList_iff v [v2]).mp hv
    -- the pin is an int or bool (the pin shapes are int/bool only)
    have hpinval := modelAuxSlots_pinval hslots0 p hpmem v2 hsingle
    rw [← List.mem_singleton.mp hvmem] at hpinval
    rcases hpinval with ⟨k, hk⟩ | ⟨b, hb⟩
    · rw [hk]
      intro hcon
      exact absurd hcon (by simp [LeanFzn.Semantics.Value.intView])
    · rw [hb]
      intro hcon
      exact absurd hcon (by simp [LeanFzn.Semantics.Value.intView])


theorem compile_covers {m : Model}
    {problem : CompiledProblem DomConstraint}
    (hc : compileModel m = .ok problem)
    (hwf : WellFormed fullSig m)
    {store : Store}
    (hcons : ∀ c ∈ m.constraints, c.Holds fullInterp store)
    (hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array _ _ _ _ => False)
    (hparam : ParamHonest m store) :
    ∃ a, a ∈ allAssigns problem.domains ∧
      accepts problem a = true := by
  obtain ⟨a, h1, h2, _⟩ := compile_covers_agree hc hwf hcons hvars hparam
  exact ⟨a, h1, h2⟩

end LeanFzn.Compiler
