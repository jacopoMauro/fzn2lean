/-
File: solver/Direct/Proofs/Exact.lean

Purpose:
  The whole-model correspondence between `Direct.compileModel` and the
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
  - solver.Direct.Proofs.Compile: the per-shape correspondence,
    the slot machinery, the compile-list inversions, and the
    whole-model gate inversions.
  - solver.Direct.Compile: the executable compiler.
  - LeanFzn.FznSemantics: `Satisfies`.

DAG:
  solver.Direct.Proofs.Compile -> solver.Direct.Proofs.Exact
    -> solver.Direct.Correctness
-/

import solver.Direct.Proofs.Compile

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core

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
  have hdot : LeanFzn.dotProduct (intVals [1, 1]) [a[i]!, a[j]!]
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

/-- `int_plus(x, y, k)` with a literal third argument: the store's
    first two values are integers with `p + q = k` (the
    `linEq [1,1]` coverage premise). -/
theorem holds_int_plus_lit_inv {store : Store} {c : ConstraintItem}
    {x y : Ident} {k : Int}
    (hname : c.name.name = "int_plus")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
        Expr.basic (.lit (.int k))])
    (h : c.Holds fullInterp store) :
    ∃ p q, store x = some (.int p) ∧ store y = some (.int q) ∧
      p + q = k := by
  obtain ⟨args, hmap, hinterp⟩ := h
  rw [hargs] at hmap
  simp only [List.mapM_cons, List.mapM_nil, Expr.eval, BasicExpr.eval,
    BasicLiteral.denote] at hmap
  cases hsx : store x with
  | none => rw [hsx] at hmap; simp at hmap
  | some vx =>
      rw [hsx] at hmap
      cases hsy : store y with
      | none => rw [hsy] at hmap; simp at hmap
      | some vy =>
          rw [hsy] at hmap
          have hargsv : args = [vx, vy, .int k] := by
            simpa using hmap.symm
          subst hargsv
          have h1 : fullInterp (Ident.mk "int_plus") [vx, vy, .int k] :=
            interp_of_hname hname hinterp
          rw [fullInterp_std (by decide :
            ¬ "int_plus" ∈ globalsNames)] at h1
          have hmatch : (match [vx, vy, .int k] with
            | [Value.int a, Value.int b, Value.int w] => a + b = w
            | _ => False) := h1
          cases vx with
          | int p =>
              cases vy with
              | int q =>
                  have hk : p + q = k := by simpa using hmatch
                  exact ⟨p, q, rfl, rfl, hk⟩
              | bool w => exact absurd hmatch (by simp)
              | setOfInt w => exact absurd hmatch (by simp)
              | array w => exact absurd hmatch (by simp)
          | bool w => exact absurd hmatch (by simp)
          | setOfInt w => exact absurd hmatch (by simp)
          | array w => exact absurd hmatch (by simp)

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

/-- If `argOf c k` succeeds with an identifier, the k-th argument is
    that identifier's basic expression. -/
theorem argOf_ident_inv {c : ConstraintItem} {k : Nat} {x : Ident}
    (h : argOf c k = .ok (.ident x)) :
    c.args[k]! = .basic (.ident x) := by
  unfold argOf at h
  cases he : c.args[k]! with
  | basic b =>
      rw [he] at h
      cases hb : b with
      | ident x2 =>
          have h2 : (Except.ok (BasicExpr.ident x2) :
              Except String BasicExpr) = .ok (.ident x) := by
            rw [← hb]; exact h
          have hred : BasicExpr.ident x2 = BasicExpr.ident x :=
            (Except.ok.inj h2)
          injection hred with hx
          subst hx
          rfl
      | lit l =>
          exfalso
          have h2 : (Except.ok (BasicExpr.lit l) :
              Except String BasicExpr) = .ok (.ident x) := by
            rw [← hb]; exact h
          cases l <;> exact absurd h2 (by simp)
  | array es =>
      exfalso
      rw [he] at h
      exact absurd h (by simp)

/-- If `argOf c k` succeeds with an int literal, the k-th argument is
    that literal's basic expression or a parameter identifier. -/
theorem argOf_lit_int_inv {c : ConstraintItem} {k : Nat} {v : Int}
    (h : argOf c k = .ok (.lit (.int v))) :
    c.args[k]! = .basic (.lit (.int v)) ∨ ∃ x, c.args[k]! = .basic (.ident x) := by
  unfold argOf at h
  cases he : c.args[k]! with
  | basic b =>
      rw [he] at h
      cases hb : b with
      | ident x2 => exact Or.inr ⟨x2, rfl⟩
      | lit l =>
          cases l with
          | int i2 =>
              have h2 : (Except.ok (BasicExpr.lit (BasicLiteral.int i2)) :
                  Except String BasicExpr) = .ok (.lit (.int v)) := by
                rw [← hb]; exact h
              have h3 : BasicExpr.lit (BasicLiteral.int i2)
                  = BasicExpr.lit (.int v) := (Except.ok.inj h2)
              injection h3 with h4
              injection h4 with h5
              subst h5
              exact Or.inl rfl
          | bool w =>
              exfalso
              have h2 : (Except.ok (BasicExpr.lit (BasicLiteral.bool w)) :
                  Except String BasicExpr) = .ok (.lit (.int v)) := by
                rw [← hb]; exact h
              exact absurd h2 (by simp)
          | set w =>
              exfalso
              have h2 : (Except.ok (BasicExpr.lit (BasicLiteral.set w)) :
                  Except String BasicExpr) = .ok (.lit (.int v)) := by
                rw [← hb]; exact h
              exact absurd h2 (by simp)
  | array es =>
      exfalso
      rw [he] at h
      exact absurd h (by simp)


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
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
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
      [PredParamType.basic (BasicPredParamType.var (BasicVarType.par
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

/-- The int-reads dispatch on an extracted constraint's name: every
    name of the 21 extracted shapes that takes identifier arguments in
    slot positions either is an int-binary/int_plus name (the typing
    chain) or never consults the reads premise (its slot arms force
    the reads through the satisfaction premise itself). This helper
    covers the names that CAN appear with identifier arguments. -/
theorem int_reads_of_extracted {m : Model}
    {slots : List (String × List Value)} {a : List Value}
    {c : ConstraintItem}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hc : c ∈ m.constraints)
    (hpred : m.predicates = [])
    (hmem : a ∈ allAssigns (slots.map Prod.snd))
    (hn : c.name.name = "int_eq" ∨ c.name.name = "int_ne" ∨
      c.name.name = "int_le" ∨ c.name.name = "int_lt" ∨
      c.name.name = "int_ge" ∨ c.name.name = "int_gt" ∨
      c.name.name = "int_plus")
    (x : Ident) (i : Nat)
    (hxarg : Expr.basic (.ident x) ∈ c.args)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i) :
    ∃ p, a[i]! = Value.int p := by
  rcases hn with h | h | h | h | h | h | h
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inl h) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inl h)) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inl h))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inr (Or.inl h)))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h))))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_plus hwf hslot hc hpred h hmem x i hxarg hxi

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

/-! ## The fallback gate inversions (per family) -/


/-! ## The fallback gate inversions (per family) -/

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


/-! ## The master fallback SAT linker -/

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
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
    rw [hfall] at h
    exact absurd h (by simp)

/-- A successful fallback compile of `int_plus` pins the argument
    count: the gate condition fired, so `c.args.length = 3`. -/
theorem compileConstraint_fallback3_len {env : Store}
    {names : List String} {c : ConstraintItem} {dc : DomConstraint}
    (h : compileConstraint env names c = .ok dc)
    (hnone : extractConstraint names c = none)
    (hname : c.name.name = "int_plus") :
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
        exact absurd hcon.2 hlen
      have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) := by
        intro hcon
        exact absurd hcon.1 (by rw [hname]; simp)
      have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) := by
        intro hcon
        exact absurd hcon.1 (by rw [hname]; simp)
      have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) := by
        intro hcon
        exact absurd hcon.1 (by rw [hname]; simp)
      have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) := by
        intro hcon
        exact absurd hcon.1 (by rw [hname]; simp)
      rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
    rw [hfall] at h
    exact absurd h (by simp)

/-! ## The master fallback SAT linker -/

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
                (compileConstraint_fallback3_len hcc hnone hplus) hnone
            rw [hdc] at hsat
            exact holds_int_plus_lit_E hnu halt hplus hargs hxi hyi
              (eval_intValuedArg halt hE) hsat
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
              rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
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
  -- invert the compile into the assembled problem
  obtain ⟨_, slots, dcs, hslot, hcomp, hasm⟩ :=
    compileModel_ok_inv hc
  -- the assembled problem's fields
  have hdoms : problem.domains = slots.map Prod.snd := by
    show problem.domains = slots.map Prod.snd
    rw [hasm]
    rfl
  have hstore : ∀ x, problem.toStore a x =
      (assemble m slots dcs).toStore a x := by
    intro x
    show problem.toStore a x = (assemble m slots dcs).toStore a x
    rw [hasm]
  rw [hdoms] at hmem
  -- the constraints half
  have hpred : m.predicates = [] := compileModel_predicates_nil hc
  have hacc' : accepts (assemble m slots dcs) a = true := by
    rw [← hasm]
    exact hacc
  have hcons : ∀ c ∈ m.constraints, c.Holds fullInterp
      ((assemble m slots dcs).toStore a) :=
    compile_sat_link_all hwf hslot hpred hcomp hmem hacc'
  -- the variables half
  have hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, ((assemble m slots dcs).toStore a) n =
          some v ∧ ty.contains v
      | .array _ _ _ _ => False := by
    intro d hd
    obtain ⟨ty, n, anns, hshape⟩ :=
      compileModel_vars_basic hc d hd
    subst hshape
    exact decl_var_basic_holds hwf hd hslot hmem
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

end LeanFzn.Solver.Direct













