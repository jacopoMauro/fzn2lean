/-
File: LeanFzn/Compiler/Proofs/CompileAux2d.lean

Purpose:
  The Boolean XOR channel's certification layer (PLAN C0): the
  truth-table lemmas for the four-clause encoding of `z = (x ^^ y)`,
  the `slotIsBoolB` read conversions and the clause-satisfaction
  equivalences, the three-identifier argument evaluation, the SAT
  bridge for the expanded `bool_clause` pieces (`sat_aux_xor`), and
  the source-to-clauses bridge used by `compile_covers_agree`.

Dependencies:
  - LeanFzn.Compiler.Proofs.CompileAux2c (the per-shape inversions
    and per-piece compile inversions).  The module is imported by
    Proofs.Compile and therefore by Proofs.Exact.

DAG:
  LeanFzn.Compiler.Compile -> Proofs.CompileCore -> Proofs.CompileAux1
    -> Proofs.CompileAux2a -> Proofs.CompileAux2b -> Proofs.CompileAux2c
    -> Proofs.CompileAux2d -> Proofs.Compile (shell)
-/

import LeanFzn.Compiler.Proofs.CompileAux2c
open LeanFzn.Compiler.Domains


namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Core

/-! ## The four-clause XOR truth table -/

/-- The four equivalence clauses of `bool_xor(x, y, z)` (positive
    lists `[x,y]`, `[]`, `[y,z]`, `[x,z]`; negative lists `[z]`,
    `[x,y,z]`, `[x]`, `[y]`) are satisfied exactly by `r = (p ^^ q)`. -/
theorem bool_xor_of_clauses {p q r : Bool}
    (h1 : p = true ∨ q = true ∨ r = false)
    (h2 : p = false ∨ q = false ∨ r = false)
    (h3 : q = true ∨ r = true ∨ p = false)
    (h4 : p = true ∨ r = true ∨ q = false) :
    r = (p ^^ q) := by
  cases p <;> cases q <;> cases r <;> simp_all

/-- The converse direction of the truth table: the XOR relation
    entails each of the four clauses. -/
theorem bool_xor_to_clauses {p q r : Bool} (h : r = (p ^^ q)) :
    (p = true ∨ q = true ∨ r = false) ∧
    (p = false ∨ q = false ∨ r = false) ∧
    (q = true ∨ r = true ∨ p = false) ∧
    (p = true ∨ r = true ∨ q = false) := by
  cases p <;> cases q <;> cases r <;> simp_all

/-! ## Boolean read conversions -/

/-- The `slotIsBoolB` read conversion: the readable predicate is the
    exact `?`-read of the slot. -/
theorem slotIsBoolB_eq_true_iff {a : List Value} {i : Nat} {b : Bool} :
    slotIsBoolB a i b = true ↔ a[i]? = some (.bool b) := by
  unfold slotIsBoolB
  cases h : a[i]? with
  | none => simp
  | some v => cases v <;> cases b <;> simp [value_eqB_iff]

/-- Two Boolean reads of the same slot determine the same value. -/
theorem bool_read_eq {a : List Value} {i : Nat} {p b : Bool}
    (hpi : a[i]? = some (.bool p)) (h : a[i]? = some (.bool b)) :
    p = b :=
  Value.bool.inj (Option.some.inj (hpi.symm.trans h))

/-- The `slotIsBoolB` positive read of a Boolean-valued slot IS the
    read's Boolean. -/
theorem slotIsBoolB_true_eq {a : List Value} {i : Nat} {p : Bool}
    (hi : a[i]? = some (.bool p)) :
    slotIsBoolB a i true = p := by
  cases p <;> simp [slotIsBoolB, hi, Value.eqB]

/-- The `slotIsBoolB` negative read of a Boolean-valued slot is the
    negation of the read's Boolean. -/
theorem slotIsBoolB_false_eq {a : List Value} {i : Nat} {p : Bool}
    (hi : a[i]? = some (.bool p)) :
    slotIsBoolB a i false = !p := by
  cases p <;> simp [slotIsBoolB, hi, Value.eqB]

/-! ## The clause-satisfaction equivalences -/

/-- The first XOR clause `x ∨ y ∨ ¬z` as a `boolClauseSlot`. -/
theorem boolClauseSlot_iff_1 {a : List Value} {i j k : Nat}
    {p q r : Bool}
    (hi : a[i]? = some (.bool p)) (hj : a[j]? = some (.bool q))
    (hk : a[k]? = some (.bool r)) :
    (DomConstraint.boolClauseSlot [i, j] [k]).SatisfiedBy a ↔
      (p = true ∨ q = true ∨ r = false) := by
  rw [← DomConstraint.satisfiedB_iff]
  simp only [DomConstraint.satisfiedB, List.any_cons, List.any_nil,
    Bool.or_false]
  rw [slotIsBoolB_true_eq hi, slotIsBoolB_true_eq hj,
    slotIsBoolB_false_eq hk]
  cases p <;> cases q <;> cases r <;> simp

/-- The second XOR clause `¬x ∨ ¬y ∨ ¬z`. -/
theorem boolClauseSlot_iff_2 {a : List Value} {i j k : Nat}
    {p q r : Bool}
    (hi : a[i]? = some (.bool p)) (hj : a[j]? = some (.bool q))
    (hk : a[k]? = some (.bool r)) :
    (DomConstraint.boolClauseSlot [] [i, j, k]).SatisfiedBy a ↔
      (p = false ∨ q = false ∨ r = false) := by
  rw [← DomConstraint.satisfiedB_iff]
  simp only [DomConstraint.satisfiedB, List.any_cons, List.any_nil,
    Bool.or_false]
  rw [slotIsBoolB_false_eq hi, slotIsBoolB_false_eq hj,
    slotIsBoolB_false_eq hk]
  cases p <;> cases q <;> cases r <;> simp

/-- The third XOR clause `¬x ∨ y ∨ z`. -/
theorem boolClauseSlot_iff_3 {a : List Value} {i j k : Nat}
    {p q r : Bool}
    (hi : a[i]? = some (.bool p)) (hj : a[j]? = some (.bool q))
    (hk : a[k]? = some (.bool r)) :
    (DomConstraint.boolClauseSlot [j, k] [i]).SatisfiedBy a ↔
      (q = true ∨ r = true ∨ p = false) := by
  rw [← DomConstraint.satisfiedB_iff]
  simp only [DomConstraint.satisfiedB, List.any_cons, List.any_nil,
    Bool.or_false]
  rw [slotIsBoolB_true_eq hj, slotIsBoolB_true_eq hk,
    slotIsBoolB_false_eq hi]
  cases p <;> cases q <;> cases r <;> simp

/-- The fourth XOR clause `x ∨ ¬y ∨ z`. -/
theorem boolClauseSlot_iff_4 {a : List Value} {i j k : Nat}
    {p q r : Bool}
    (hi : a[i]? = some (.bool p)) (hj : a[j]? = some (.bool q))
    (hk : a[k]? = some (.bool r)) :
    (DomConstraint.boolClauseSlot [i, k] [j]).SatisfiedBy a ↔
      (p = true ∨ r = true ∨ q = false) := by
  rw [← DomConstraint.satisfiedB_iff]
  simp only [DomConstraint.satisfiedB, List.any_cons, List.any_nil,
    Bool.or_false]
  rw [slotIsBoolB_true_eq hi, slotIsBoolB_true_eq hk,
    slotIsBoolB_false_eq hj]
  cases p <;> cases q <;> cases r <;> simp

/-! ## The SAT bridge -/

/-- The SAT bridge for `bool_xor(x, y, z)` (xorSlots): the four
    compiled `bool_clause` pieces with the exact positive/negative
    slot lists of the expansion force the XOR truth table at a
    Boolean-valued triple of reads. -/
theorem sat_aux_xor {m : Model}
    {slots : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {c : ConstraintItem} {x y z : Ident} {i j k : Nat}
    {p q r : Bool}
    (hnu : (slots.map Prod.fst).Nodup) (halt : a.length = slots.length)
    (hname : c.name.name = "bool_xor")
    (hargs : c.args = [.basic (.ident x), .basic (.ident y),
      .basic (.ident z)])
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i)
    (hyi : nameIndex (slots.map Prod.fst) y.name = some j)
    (hzi : nameIndex (slots.map Prod.fst) z.name = some k)
    (hpi : a[i]! = Value.bool p) (hqj : a[j]! = Value.bool q)
    (hrk : a[k]! = Value.bool r)
    (hsat1 : (DomConstraint.boolClauseSlot [i, j] [k]).SatisfiedBy a)
    (hsat2 : (DomConstraint.boolClauseSlot [] [i, j, k]).SatisfiedBy a)
    (hsat3 : (DomConstraint.boolClauseSlot [j, k] [i]).SatisfiedBy a)
    (hsat4 : (DomConstraint.boolClauseSlot [i, k] [j]).SatisfiedBy a) :
    c.Holds fullInterp ((assemble m slots dcs).toStore a) := by
  have hbounds : ∀ (w : Ident) (iw : Nat),
      nameIndex (slots.map Prod.fst) w.name = some iw → iw < a.length := by
    intro w iw hwi
    have hlt := (nameIndex_some (slots.map Prod.fst) w.name iw hwi).1
    have hlen : (slots.map Prod.fst).length = slots.length := by simp
    rw [hlen] at hlt
    omega
  have hpib : a[i]? = some (Value.bool p) := by
    rw [← hpi]
    exact getElem_as_some (hbounds x i hxi)
  have hqjb : a[j]? = some (Value.bool q) := by
    rw [← hqj]
    exact getElem_as_some (hbounds y j hyi)
  have hrkb : a[k]? = some (Value.bool r) := by
    rw [← hrk]
    exact getElem_as_some (hbounds z k hzi)
  have cl1 : p = true ∨ q = true ∨ r = false :=
    (boolClauseSlot_iff_1 hpib hqjb hrkb).mp hsat1
  have cl2 : p = false ∨ q = false ∨ r = false :=
    (boolClauseSlot_iff_2 hpib hqjb hrkb).mp hsat2
  have cl3 : q = true ∨ r = true ∨ p = false :=
    (boolClauseSlot_iff_3 hpib hqjb hrkb).mp hsat3
  have cl4 : p = true ∨ r = true ∨ q = false :=
    (boolClauseSlot_iff_4 hpib hqjb hrkb).mp hsat4
  have hxor : r = (p ^^ q) := bool_xor_of_clauses cl1 cl2 cl3 cl4
  refine ⟨[a[i]!, a[j]!, a[k]!], ?_, ?_⟩
  · rw [hargs]
    exact eval_three_ident (m := m) hnu halt hxi hyi hzi
  · rw [ident_eq_of_name hname, fullInterp_std (by decide)]
    show (match [a[i]!, a[j]!, a[k]!] with
      | [Value.bool p, Value.bool q, Value.bool r] => r = (p ^^ q)
      | _ => False)
    rw [hpi, hqj, hrk]
    exact hxor

/-! ## The signature of the XOR channel -/

/-- The signature environment resolves `bool_xor` to its three
    bool-var parameter types. -/
theorem sigEnv_bool_xor {m : Model} (hpred : m.predicates = []) :
    m.sigEnv fullSig (Ident.mk "bool_xor") =
    some [.basic (.var (.par .bool)), .basic (.var (.par .bool)),
      .basic (.var (.par .bool))] := by
  show (match m.declaredSigs (Ident.mk "bool_xor") with
    | some params => some params
    | none => fullSig (Ident.mk "bool_xor")) = _
  have hdecl : m.declaredSigs (Ident.mk "bool_xor") = none := by
    show lookupIdent (Ident.mk "bool_xor")
      (m.predicates.map (fun p => (p.name, p.params.map (·.type)))) = none
    rw [hpred]
    rfl
  rw [hdecl]
  rfl

/-! ## The source-to-clauses bridge -/

/-- The source-to-clauses bridge: a store satisfying `bool_xor(x,y,z)`
    with Boolean reads p, q, r satisfies each of the four XOR clauses
    (the `compile_covers_agree` direction's per-piece obligations). -/
theorem xor_clauses_of_holds {store : Store} {c : ConstraintItem}
    {x y z : Ident} {p q r : Bool}
    (hname : c.name.name = "bool_xor")
    (hargs : c.args = [Expr.basic (.ident x), Expr.basic (.ident y),
      Expr.basic (.ident z)])
    (hx : store x = some (Value.bool p)) (hy : store y = some (Value.bool q))
    (hz : store z = some (Value.bool r))
    (hholds : c.Holds fullInterp store) :
    (p = true ∨ q = true ∨ r = false) ∧
    (p = false ∨ q = false ∨ r = false) ∧
    (q = true ∨ r = true ∨ p = false) ∧
    (p = true ∨ r = true ∨ q = false) := by
  obtain ⟨args, hmap, hint⟩ := hholds
  obtain ⟨vx, vy, vz, hx', hy', hz', hargsv⟩ := mapM_three_ident hargs hmap
  have hvx : vx = Value.bool p := by
    rw [hx] at hx'
    exact (Option.some.inj hx').symm
  have hvy : vy = Value.bool q := by
    rw [hy] at hy'
    exact (Option.some.inj hy').symm
  have hvz : vz = Value.bool r := by
    rw [hz] at hz'
    exact (Option.some.inj hz').symm
  have hxor : r = (p ^^ q) := by
    have h := hint
    rw [hargsv, ident_eq_of_name hname] at h
    rw [fullInterp_std (by decide)] at h
    rw [hvx, hvy, hvz] at h
    exact h
  exact bool_xor_to_clauses hxor

end LeanFzn.Compiler
