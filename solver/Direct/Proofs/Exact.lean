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

/-! ## The store-agreement transport (identifier-restricted) -/

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

/-! ## The coverage direction (`compile_covers`) -/

/-- The coverage linker per constraint: a source constraint holding
    at the assembled store of an assignment whose slot reads agree
    with the store makes the compiled constraint satisfied. -/
theorem compile_holds_link {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {dc : DomConstraint}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots)
    (hnu : (slots.map Prod.fst).Nodup)
    (halt : a.length = slots.length)
    (hc : c ∈ m.constraints)
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
                    (compileConstraint_fallback3_len hcc hex hplus) hex
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
                have hdot : LeanFzn.dotProduct (intVals [1, 1])
                    [a[i]!, a[j]!] = some k := by
                  rw [hapi, hapj,
                    show intVals [1, 1] = [Value.int 1, Value.int 1] from rfl]
                  have h2 := dotProduct_two_one (Value.int p) (Value.int q)
                  rw [h2]
                  exact congrArg _ hpqk
                exact hdot
              · exfalso
                have hfall : compileConstraint (parEnv m) (slots.map Prod.fst) c
                    = .error s!"unsupported predicate '{c.name.name}'" := by
                  unfold compileConstraint
                  rw [hex]
                  have h1 : ¬(c.name.name = "int_plus" ∧ c.args.length = 3) :=
                    by
                    intro hcon
                    exact absurd hcon.1 hplus
                  have h2 : ¬(c.name.name = "int_le" ∧ c.args.length = 2) :=
                    by
                    intro hcon
                    exact absurd hcon.1 hle
                  have h3 : ¬(c.name.name = "int_lt" ∧ c.args.length = 2) :=
                    by
                    intro hcon
                    exact absurd hcon.1 hlt
                  have h4 : ¬(c.name.name = "int_gt" ∧ c.args.length = 2) :=
                    by
                    intro hcon
                    exact absurd hcon.1 hgt
                  have h5 : ¬(c.name.name = "int_ge" ∧ c.args.length = 2) :=
                    by
                    intro hcon
                    exact absurd hcon.1 hge
                  rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4, if_neg h5]
                rw [hfall] at hcc
                exact absurd hcc (by simp)


/-- Every slot position of a successfully compiled model reads a
    store value in the slot's domain, provided the store satisfies
    the variable-declaration conditions. -/
theorem slot_reads_of_satisfying {m : Model}
    {problem : CompiledProblem DomConstraint}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    (hc : compileModel m = .ok problem)
    (hasm : problem = assemble m slots dcs)
    (hslot : slotsChecked m = .ok slots)
    {store : Store}
    (hvars : ∀ d ∈ m.variables, match d with
      | .basic ty n _ _ => ∃ v, store n = some v ∧ ty.contains v
      | .array _ _ _ _ => False) :
    ∀ (i : Nat), ∀ hilt : i < slots.length,
      ∃ v, store (Ident.mk (slots[i]'hilt).1) = some v ∧
        v ∈ (slots[i]'hilt).snd := by
  intro i hilt
  -- the slot at position i comes from a declared variable
  obtain ⟨d, hd, hds⟩ := declSlots_mem m.variables slots
    (declSlots_of_slotsChecked hslot) (slots[i]'hilt)
    (List.getElem_mem hilt)
  -- the variable is basic and initializer-free (the gate)
  obtain ⟨ty, n, anns, hshape⟩ :=
    compileModel_vars_basic hc d hd
  subst hshape
  -- the slot pair is (n.name, dom.values)
  have hdslot : declSlot (.basic ty n anns none : VarDeclItem) =
      .ok (some (slots[i]'hilt)) := hds
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  -- the store's value at n: in the declared domain
  obtain ⟨v, hvstore, hcontains⟩ := hvars (.basic ty n anns none) hd
  -- v ∈ dom.values ↔ ty.contains v
  have hvmem : v ∈ dom.values := (varDomain_values_iff hdom).mpr hcontains
  rw [show (slots[i]'hilt) = (n.name, dom.values) from hpair] at *
  exact ⟨v, by rw [show Ident.mk n.name = n from ident_eq_of_name rfl]; exact hvstore, hvmem⟩

/-- **WHOLE-MODEL COVERAGE (`compile_covers`)**: every store that
    satisfies the model's dynamic conditions (constraints, variable
    domains) AND is parameter-honest yields an assignment in the
    compiled candidate space that passes the internal evaluator. -/
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
  -- invert the compile
  obtain ⟨_, slots, dcs, hslot, hcomp, hasm⟩ :=
    compileModel_ok_inv hc
  -- every declared basic variable has a slot; choose the store's
  -- value at each slot position
  have hreads := slot_reads_of_satisfying hc hasm hslot hvars
  -- the assignment: the store's read at each slot's name (the read
  -- is `some` of an in-domain value, so the default never fires)
  refine ⟨slots.map (fun p => (store (Ident.mk p.1)).getD (.bool false)),
    ?_, ?_⟩
  · -- membership in the candidate space: Fits
    have hdoms : problem.domains = slots.map Prod.snd := by
      show problem.domains = slots.map Prod.snd
      rw [hasm]
      rfl
    apply fits_mem_allAssigns (doms := problem.domains)
    refine ⟨?_, ?_⟩
    · rw [hdoms, List.length_map, List.length_map]
    · intro slot value hval
      by_cases hslt : slot < slots.length
      · obtain ⟨v, hvread, hvdom⟩ := hreads slot hslt
        -- the read at slot through the map
        have hap : (slots.map (fun p =>
            (store (Ident.mk p.1)).getD (.bool false)))[slot]?
            = some ((store (Ident.mk (slots[slot]'hslt).1)).getD (.bool false)) := by
          rw [List.getElem?_map, List.getElem?_eq_getElem hslt, Option.map_some]
        rw [hap] at hval
        rw [hvread] at hval
        have hvv : value = v := by
          injection hval with h1
          rw [Option.getD_some] at h1
          exact h1.symm
        rw [hvv, hdoms, getD_map_snd hslt]
        exact hvdom
      · exfalso
        rw [List.getElem?_map] at hval
        rw [List.getElem?_eq_none (by omega : slots.length ≤ slot)] at hval
        rw [Option.map_none] at hval
        cases hval
  · -- acceptance: every compiled constraint is satisfied
    -- generalize over the assignment: prove the agreement + acceptance
    -- for the specific map construction
    have hmain : ∀ (a : List Value),
        a = slots.map (fun p => (store (Ident.mk p.1)).getD (.bool false)) →
        (∀ (c : ConstraintItem), c ∈ m.constraints →
          ∀ x, x ∈ (c.args.flatMap Expr.idents) →
            ((assemble m slots dcs).toStore a) x = store x) →
        accepts problem a = true := by
      intro a ha hagree
      -- every compiled constraint is satisfied
      have hall : ∀ dc ∈ problem.constraints, dc.satisfiedB a := by
        intro dc hdcmem
        -- problem.constraints = dcs
        -- the compiled constraint came from a model constraint
        have hdcsmem : dc ∈ dcs := by
          have hc2 : problem.constraints = dcs := by
            rw [hasm]; rfl
          exact hc2 ▸ hdcmem
        obtain ⟨c, hcmem, hcc⟩ :=
          compileConstraints_mem_inv m.constraints dcs hcomp dc hdcsmem
        -- c.Holds at the assembled store (by the agreement)
        have hholds : c.Holds fullInterp ((assemble m slots dcs).toStore a) :=
          Holds_ext_args (fun x hx => (hagree c hcmem x hx).symm)
            (hcons c hcmem)
        -- the coverage linker: the compiled constraint is satisfied
        have hnu : (slots.map Prod.fst).Nodup := slotNames_nodup hwf hslot
        have halt : a.length = slots.length := by
          rw [ha, List.length_map]
        exact (DomConstraint.satisfiedB_iff dc a).mpr
          (compile_holds_link hwf hslot hnu halt hcmem hcc hholds)
      -- accepts = List.all satisfiedB
      rw [show accepts problem a = problem.constraints.all
        (fun c => c.satisfiedB a) from rfl]
      exact List.all_eq_true.mpr hall
    refine hmain _ rfl ?_
    intro c hcmem x hxarg
    -- the identifier is a slot name or a parameter name (declared);
    -- case on the name resolution
    by_cases hx : ∃ i, nameIndex (slots.map Prod.fst) x.name = some i
    · obtain ⟨i, hxi⟩ := hx
      -- slot: the assembled store reads a[i]?; a's i-th value is the
      -- store's read at the slot's name
      show (match nameIndex (slots.map Prod.fst) x.name with
        | some j => (slots.map (fun p =>
            (store (Ident.mk p.1)).getD (.bool false)))[j]?
        | none => parEnv m x) = store x
      rw [hxi]
      show (slots.map (fun p =>
          (store (Ident.mk p.1)).getD (.bool false)))[i]? = store x
      -- the store's read at the slot's name is some v
      obtain ⟨hlt, hget⟩ := nameIndex_some (slots.map Prod.fst) x.name i hxi
      have hlen : (slots.map Prod.fst).length = slots.length := by simp
      have hislt : i < slots.length := by omega
      obtain ⟨v, hvread, _⟩ := hreads i hislt
      -- a[i]? = some v (the map's read at i)
      have hap : (slots.map (fun p =>
          (store (Ident.mk p.1)).getD (.bool false)))[i]?
          = some ((store (Ident.mk (slots[i]'hislt).1)).getD (.bool false)) := by
        rw [List.getElem?_map, List.getElem?_eq_getElem hislt, Option.map_some]
      -- x IS the slot's name
      have hname : (slots.map Prod.fst)[i]! = x.name := getElem_of_getElem? hlt hget
      have hxid : Ident.mk (slots[i]'hislt).1 = x := by
        apply ident_eq_of_name
        rw [show (slots[i]'hislt).1 = (slots.map Prod.fst)[i]! from by
          rw [getElem!_map_fst i, getElem!_eq_getElem hislt]]
        exact hname
      rw [hxid] at hvread
      rw [hap, hxid, hvread, Option.getD_some]
    · -- parameter: nameIndex is none; toStore goes through parEnv
      have hxnone : nameIndex (slots.map Prod.fst) x.name = none := by
        cases h : nameIndex (slots.map Prod.fst) x.name with
        | none => rfl
        | some i => exact absurd ⟨i, h⟩ hx
      show (match nameIndex (slots.map Prod.fst) x.name with
        | some j => (slots.map (fun p =>
            (store (Ident.mk p.1)).getD (.bool false)))[j]?
        | none => parEnv m x) = store x
      rw [hxnone]
      show parEnv m x = store x
      -- x is a variable or a parameter (staticEnv resolution)
      -- (well-formedness: the constraint's identifiers are declared)
      -- First: the case analysis driver — x declared as a variable
      -- leads to a slot (contradiction); so x is a parameter.
      -- We derive x's declaration from the constraint's check:
      -- a full staticEnv inversion is heavy; instead we use the
      -- classic trick: either x ∈ parameters or x ∈ variables or x
      -- is undeclared. In all cases we must reach the agreement.
      -- (For undeclared x, parEnv m x = none = store x is NOT
      -- derivable — but undeclared identifiers cannot appear in
      -- well-formed constraints.)
      -- The identifier x appears in c's args; c is well-formed, so
      -- x resolves in m.staticEnv (params first, then vars).
      -- We prove the disjunction from checkArg:
      have hxdecl : (∃ d ∈ m.parameters, ParDeclItem.name d = x) ∨
          (∃ d ∈ m.variables, VarDeclItem.name d = x) := by
        -- the staticEnv inversion: x ∈ staticEnv means x is a
        -- parameter or a variable of the model
        -- Step 1: the constraint's check resolves x in staticEnv
        -- (the checkBase ident arm forces the resolution)
        have hstatic : m.staticEnv x ≠ none := by
          intro hnone
          obtain ⟨params, hsig, hfor⟩ := hwf.constraintsChecked c hcmem
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
                  · -- hxx : x = x3: substitute x := x3
                    rw [hxx] at hnone
                    simp only [Expr.checkArg, BasicExpr.checkBase] at hchk
                    rw [hnone] at hchk
                    cases pt with
                    | basic bt => exact hchk
                    | array idx bt => exact hchk
                  · cases hxx
              | lit l =>
                  -- x cannot be in a literal's idents
                  exfalso
                  have himp : x ∈ BasicExpr.idents (.lit l) := hx2
                  simp [BasicExpr.idents] at himp
          | array es =>
              -- the array-arm: every element checks against bt
              cases pt with
              | basic bt =>
                  -- an array argument cannot fill a basic parameter
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
        -- Step 2: staticEnv is the params-then-vars lookup
        unfold Model.staticEnv at hstatic
        cases hparam : lookupIdent x
            (m.parameters.map (fun d => (d.name, (d.type, false)))) with
        | some p =>
            -- x is a parameter
            obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x
              (m.parameters.map (fun d => (d.name, (d.type, false)))) p hparam
            obtain ⟨d, hd, hdget⟩ :=
              (List.mem_map.mp hmem)
            refine Or.inl ⟨d, hd, ?_⟩
            -- the map pair: (d.name, (d.type, false)) = (y, p)
            have hyd : y = ParDeclItem.name d := (congrArg Prod.fst hdget).symm
            have hyn : y.name = x.name := hyname
            have hname : (ParDeclItem.name d).name = x.name := hyd ▸ hyn
            exact ident_eq_of_name hname
        | none =>
            -- the vars lookup resolves
            cases hvar : lookupIdent x
                (m.variables.map (fun d => (d.name, (d.type, true)))) with
            | none =>
                exact absurd hparam (by
                  intro hcon
                  apply hstatic
                  rw [hcon]
                  exact hvar)
            | some p =>
                obtain ⟨y, hmem, hyname⟩ := lookupIdent_inv_mem x
                  (m.variables.map (fun d => (d.name, (d.type, true)))) p hvar
                obtain ⟨d, hd, hdget⟩ :=
                  (List.mem_map.mp hmem)
                refine Or.inr ⟨d, hd, ?_⟩
                have hyd : y = VarDeclItem.name d :=
                  (congrArg Prod.fst hdget).symm
                have hyn : y.name = x.name := hyname
                have hname : (VarDeclItem.name d).name = x.name := hyd ▸ hyn
                exact ident_eq_of_name hname
      rcases hxdecl with ⟨d, hd, hdname⟩ | ⟨d, hd, hdname⟩
      · -- parameter: the scalar gate + agreement
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
        exact (parEnv_agrees hwf hslot hparam d hd hscalar).symm
      · -- variable: it has a slot (contradiction with nameIndex none)
        exfalso
        obtain ⟨ty, n, anns, hshape⟩ := compileModel_vars_basic hc d hd
        have hdmem : (.basic ty n anns none : VarDeclItem) ∈ m.variables :=
          hshape ▸ hd
        have ⟨i, hxi⟩ := nameIndex_of_basic_var (m := m) hwf hslot ty n anns hdmem
        -- x IS n (both are d's name)
        have hxn : x.name = n.name := by
          have h1 : d.name = x := hdname
          -- x = d.name and d.name = n (the basic var's own name)
          have h2 : (VarDeclItem.name d).name = n.name := by
            rw [hshape]; rfl
          rw [← h1]
          rw [h2]
        rw [← hxn] at hxi
        exact absurd hxi (fun hex => hx ⟨i, hex⟩)

end LeanFzn.Solver.Direct















