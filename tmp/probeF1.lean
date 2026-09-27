import solver.Direct.Proofs.Compile
import solver.Direct.Compile
import solver.Propagators

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

/-! ## E-generalized semantic linkers (the fallback shapes' premises) -/

/-- int_le(x, E) with E evaluating to `.int k`: a bounded read makes
    the source constraint hold at the assembled store. -/
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
  obtain ⟨p, hw, hpc⟩ := hsat
  have hib : a[j]! = Value.int p := bang_of_getElem? hw
  refine ⟨[.int k, a[j]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_E_any hnu halt hyi hE
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [Value.int k, a[j]!] with
      | [Value.int p, Value.int q] => p ≥ q
      | _ => False)
    rw [hib]
    exact hpc

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
    show (do
        let v1 ← (assemble m slots dcs).toStore a x
        let v2 ← (assemble m slots dcs).toStore a y
        let v3 ← Expr.eval ((assemble m slots dcs).toStore a) E
        pure [v1, v2, v3]) = _
    rw [toStore_read (m := m) hnu hxi halt,
      toStore_read (m := m) hnu hyi halt, hE]
    rfl
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, .int k] with
      | [Value.int p, Value.int q, Value.int r] => p + q = r
      | _ => False)
    rw [hib, hjb]
    exact hpqk
