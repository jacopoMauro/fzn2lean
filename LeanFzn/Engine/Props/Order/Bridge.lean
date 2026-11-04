/-
Purpose: Order propagators: bridge definitions and their required entailment proofs.
Dependencies: LeanFzn.Engine.Props.Order.Compare
DAG: LeanFzn.Engine.Props.Order.Compare -> LeanFzn.Engine.Props.Order.Bridge.
-/
import LeanFzn.Engine.Props.Order.Compare

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-! ## Boolean/integer bridge -/

/-! ## Literal evaluation at fixed integer / Boolean views -/

/-- A domain fixed to an integer does not contain any other integer view. -/
theorem DomC.memIntView_false_of_fixed_int_other {d : DomC} (hWF : d.WF)
    {q c : Int} (h : d.fixedValue = some (.int q)) (hq : q ≠ c) :
    d.memIntView c = false := by
  have hsound := DomC.fixedValue_sound d hWF h
  have hmc : d.mem (.int c) = false := by
    cases hc : d.mem (.int c) with
    | false => rfl
    | true =>
        have hcq : c = q := Value.int.inj (hsound.2 (.int c) hc)
        exact absurd hcq.symm hq
  cases d with
  | bool bits =>
      have hmem : (DomC.mem (.bool bits) (.int q)) = true := hsound.1
      simp [DomC.mem] at hmem
  | bounds lo hi => simpa [DomC.memIntView] using hmc
  | bitset lo words => simpa [DomC.memIntView] using hmc
  | boundsHoles lo hi holes => simpa [DomC.memIntView] using hmc

theorem DomC.evalLit_posNe_true_of_fixed_int_other {d : DomC} (hWF : d.WF)
    {s : Nat} {c q : Int} (h : d.fixedValue = some (.int q)) (hq : q ≠ c) :
    d.evalLit (posNe s c) = some true := by
  have hm := DomC.memIntView_false_of_fixed_int_other hWF h hq
  simp [posNe, DomC.evalLit, h, hm]

theorem DomC.evalLit_negNe_false_of_fixed_int_other {d : DomC} (hWF : d.WF)
    {s : Nat} {c q : Int} (h : d.fixedValue = some (.int q)) (hq : q ≠ c) :
    d.evalLit (negNe s c) = some false := by
  have hm := DomC.memIntView_false_of_fixed_int_other hWF h hq
  simp [negNe, DomC.evalLit, h, hm]

/-- Value equality to an integer is false on a domain fixed to another
integer. -/
theorem DomC.evalLit_eqLit_int_false_of_fixed_int_other {d : DomC} (hWF : d.WF)
    {s : Nat} {c q : Int} (h : d.fixedValue = some (.int q)) (hq : q ≠ c) :
    d.evalLit (eqLit s (.int c)) = some false := by
  change d.evalLit (negNe s c) = some false
  exact DomC.evalLit_negNe_false_of_fixed_int_other hWF h hq

/-- Value equality to an integer is unassigned on an unfixed domain whose
integer view contains it. -/
theorem DomC.evalLit_eqLit_int_none_of_memIntView {d : DomC} {s : Nat} {c : Int}
    (hfv : d.fixedValue = none) (hm : d.memIntView c = true) :
    d.evalLit (eqLit s (.int c)) = none := by
  change d.evalLit (negNe s c) = none
  simp [negNe, DomC.evalLit, hfv, hm]

/-- Value equality to an integer is false on an unfixed domain whose
integer view omits it. -/
theorem DomC.evalLit_eqLit_int_false_of_not_mem {d : DomC} {s : Nat} {c : Int}
    (hfv : d.fixedValue = none) (hm : d.memIntView c = false) :
    d.evalLit (eqLit s (.int c)) = some false := by
  change d.evalLit (negNe s c) = some false
  exact DomC.evalLit_negNe_false_of_not_mem hfv hm

/-- Value equality to a Boolean is false on a domain fixed to the other
Boolean. -/
theorem DomC.evalLit_eqLit_bool_false_of_fixed_other {d : DomC} {s : Nat}
    {c b : Bool} (h : d.fixedValue = some (.bool b)) (hne : b ≠ c) :
    d.evalLit (eqLit s (.bool c)) = some false := by
  show d.evalLit ⟨.boolEq s (!c), false⟩ = some false
  simp only [DomC.evalLit, h]
  cases b <;> cases c <;> simp_all

/-- Value equality to a Boolean is unassigned on an unfixed domain. -/
theorem DomC.evalLit_eqLit_bool_none_of_not_fixed {d : DomC} {s : Nat} {c : Bool}
    (hfv : d.fixedValue = none) :
    d.evalLit (eqLit s (.bool c)) = none := by
  show d.evalLit ⟨.boolEq s (!c), false⟩ = none
  simp [DomC.evalLit, hfv]

/-- Accepted assignments of `bool2intSlot i k` read a Boolean in `i` and
its `0`/`1` image in `k`. -/
theorem bool2int_accepts_data (p : CompiledProblem DomConstraint)
    (i k : Nat) (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints)
    {a : Assignment} (ha : a ∈ allAssigns p.domains) (hacc : accepts p a = true) :
    ∃ b : Bool, a[i]? = some (.bool b) ∧
      a[k]? = some (.int (if b then 1 else 0)) := by
  have hdc : (DomConstraint.bool2intSlot i k).satisfiedB a = true :=
    List.all_eq_true.mp hacc _ hmem
  exact (DomConstraint.satisfiedB_iff _ _).mp hdc

/-- `eqLit` on a Boolean is true exactly at that Boolean. -/
theorem eval_eqLit_bool_true_iff (a : Assignment) (s : Nat) (b : Bool) :
    (eqLit s (.bool b)).eval a = some true ↔ a[s]? = some (.bool b) := by
  unfold eqLit neLit posBool Literal.negate
  simp only [Literal.eval, Atom.eval]
  cases h : a[s]? with
  | none => simp
  | some v =>
      cases v with
      | bool c => cases b <;> cases c <;> simp [h]
      | int x => simp [h]
      | setOfInt x => simp [h]
      | array xs => simp [h]

/-- A Boolean value in `i` forces the `0`/`1` image in `k`. -/
theorem bool2int_i_reason_entailed (p : CompiledProblem DomConstraint)
    (i k : Nat) (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints)
    (b : Bool) :
    Entailed p [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))] := by
  intro a ha hacc
  obtain ⟨bv, hbi, hbk⟩ := bool2int_accepts_data p i k hmem ha hacc
  by_cases hb : bv = b
  · rw [hb] at hbk
    refine ⟨eqLit k (.int (if b then 1 else 0)), by simp, ?_⟩
    change (negNe k (if b then 1 else 0)).eval a = some true
    refine (eval_negNe_iff a k (if b then 1 else 0)).mpr
      ⟨(if b then 1 else 0), ?_, rfl⟩
    rw [slotInt, hbk]
    rfl
  · have hnb : bv ≠ b := hb
    refine ⟨neLit i (.bool b), by simp, ?_⟩
    cases bv <;> cases b <;> simp_all [neLit, posBool, Literal.eval, Atom.eval]

/-- A `0`/`1` integer in `k` forces the corresponding Boolean in `i`. -/
theorem bool2int_k_reason_entailed (p : CompiledProblem DomConstraint)
    (i k : Nat) (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints)
    (q : Int) (hq : q = 0 ∨ q = 1) :
    Entailed p [neLit k (.int q), eqLit i (.bool (q == 1))] := by
  intro a ha hacc
  obtain ⟨bv, hbi, hbk⟩ := bool2int_accepts_data p i k hmem ha hacc
  by_cases hk : (if bv then (1 : Int) else 0) = q
  · have hbv : bv = (q == 1) := by
      cases bv <;> rcases hq with h | h <;> simp_all
    rw [hbv] at hbi
    refine ⟨eqLit i (.bool (q == 1)), by simp, ?_⟩
    exact (eval_eqLit_bool_true_iff a i (q == 1)).mpr hbi
  · refine ⟨neLit k (.int q), by simp, ?_⟩
    change (posNe k q).eval a = some true
    refine (eval_posNe_iff a k q).mpr ⟨(if bv then 1 else 0), ?_, ?_⟩
    · rw [slotInt, hbk]
      rfl
    · intro h
      exact hk h

/-- Every accepted assignment puts `k` in `{0, 1}`. -/
theorem bool2int_k01_reason_entailed (p : CompiledProblem DomConstraint)
    (i k : Nat) (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) :
    Entailed p [negNe k 0, negNe k 1] := by
  intro a ha hacc
  obtain ⟨b, _hbi, hbk⟩ := bool2int_accepts_data p i k hmem ha hacc
  cases b
  · refine ⟨negNe k 0, by simp, (eval_negNe_iff a k 0).mpr ?_⟩
    refine ⟨0, ?_, rfl⟩
    rw [slotInt, hbk]
    rfl
  · refine ⟨negNe k 1, by simp, (eval_negNe_iff a k 1).mpr ?_⟩
    refine ⟨1, ?_, rfl⟩
    rw [slotInt, hbk]
    rfl

/-- `bool2intSlot i k` propagator: a Boolean in `i` fixes `k` to its `0`/`1`
image, a `0`/`1` integer in `k` fixes `i`, and a `k`-domain disjoint from
`{0, 1}` conflicts.  Decisions on other fixed shapes are left to `.fix`. -/
def bool2intPropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (i k : Nat) (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) : PropV2 p T :=
  { vars := (dcSlotsFull (DomConstraint.bool2intSlot i k)).toArray
    events := #[(i, .fix), (k, .bounds), (k, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dk := view.doms.getD k DomC.empty
      match domBounds di, domBounds dk with
      | some _, some _ =>
          match di.fixedValue with
          | some (.bool b) =>
              match dk.fixedValue with
              | some (.int q) =>
                  if _hq : q = (if b then 1 else 0) then .fix
                  else .conflict (EClause.ofLiterals p T
                    [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]
                    (bool2int_i_reason_entailed p i k hmem b))
              | some _ => .fix
              | none =>
                  if _hdk : dk.memIntView (if b then 1 else 0) = true then
                    .prune #[(pLit (eqLit k (.int (if b then 1 else 0))),
                      EClause.ofLiterals p T
                        [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]
                        (bool2int_i_reason_entailed p i k hmem b))]
                  else .conflict (EClause.ofLiterals p T
                    [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]
                    (bool2int_i_reason_entailed p i k hmem b))
          | _ =>
              match dk.fixedValue with
              | some (.int q) =>
                  if hq : q = 0 ∨ q = 1 then
                    match di.fixedValue with
                    | some (.bool b) =>
                        if _hb : b = (q == 1) then .fix
                        else .conflict (EClause.ofLiterals p T
                          [neLit k (.int q), eqLit i (.bool (q == 1))]
                          (bool2int_k_reason_entailed p i k hmem q hq))
                    | some _ => .fix
                    | none =>
                        .prune #[(pLit (eqLit i (.bool (q == 1))),
                          EClause.ofLiterals p T
                            [neLit k (.int q), eqLit i (.bool (q == 1))]
                            (bool2int_k_reason_entailed p i k hmem q hq))]
                  else
                    .conflict (EClause.ofLiterals p T [negNe k 0, negNe k 1]
                      (bool2int_k01_reason_entailed p i k hmem))
              | some _ => .fix
              | none =>
                  if _hk0 : dk.memIntView 0 = false then
                    if _hk1 : dk.memIntView 1 = false then
                      .conflict (EClause.ofLiterals p T [negNe k 0, negNe k 1]
                        (bool2int_k01_reason_entailed p i k hmem))
                    else .fix
                  else .fix
      | _, _ => .fix }

theorem bool2intPropWith_run_conflict (p : CompiledProblem DomConstraint)
    (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (bool2intPropWith p T i k hmem).run view = .conflict ec) :
    (∃ b q,
      (view.doms.getD i DomC.empty).fixedValue = some (.bool b) ∧
      (view.doms.getD k DomC.empty).fixedValue = some (.int q) ∧
      q ≠ (if b then 1 else 0) ∧
      T.decodeClause ec.lits =
        [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))] ∧
      Entailed p [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]) ∨
    (∃ b,
      (view.doms.getD i DomC.empty).fixedValue = some (.bool b) ∧
      (view.doms.getD k DomC.empty).fixedValue = none ∧
      (view.doms.getD k DomC.empty).memIntView (if b then 1 else 0) = false ∧
      T.decodeClause ec.lits =
        [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))] ∧
      Entailed p [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]) ∨
    (∃ q,
      (view.doms.getD k DomC.empty).fixedValue = some (.int q) ∧
      ¬ (q = 0 ∨ q = 1) ∧
      T.decodeClause ec.lits = [negNe k 0, negNe k 1] ∧
      Entailed p [negNe k 0, negNe k 1]) ∨
    (∃ b q,
      (view.doms.getD k DomC.empty).fixedValue = some (.int q) ∧
      (q = 0 ∨ q = 1) ∧
      (view.doms.getD i DomC.empty).fixedValue = some (.bool b) ∧
      b ≠ (q == 1) ∧
      T.decodeClause ec.lits = [neLit k (.int q), eqLit i (.bool (q == 1))] ∧
      Entailed p [neLit k (.int q), eqLit i (.bool (q == 1))]) ∨
    ((view.doms.getD k DomC.empty).fixedValue = none ∧
      (view.doms.getD k DomC.empty).memIntView 0 = false ∧
      (view.doms.getD k DomC.empty).memIntView 1 = false ∧
      T.decodeClause ec.lits = [negNe k 0, negNe k 1] ∧
      Entailed p [negNe k 0, negNe k 1]) := by
  unfold bool2intPropWith at h
  dsimp only at h
  split at h
  · split at h
    · rename_i b hfi
      split at h
      · rename_i q hfk
        by_cases hq : q = (if b then 1 else 0)
        · rw [dif_pos hq] at h
          cases h
        · rw [dif_neg hq] at h
          injection h with hec
          subst hec
          refine Or.inl ⟨b, q, hfi, hfk, hq, ?_,
            bool2int_i_reason_entailed p i k hmem b⟩
          change T.decodeClause
            ([neLit i (.bool b), eqLit k (.int (if b then 1 else 0))].toArray.map pLit) =
            [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]
          exact LitTable.decodeClause_map_pLit T _
      · cases h
      · rename_i hfk
        by_cases hdk : (view.doms.getD k DomC.empty).memIntView (if b then 1 else 0) = true
        · rw [dif_pos hdk] at h
          cases h
        · rw [dif_neg hdk] at h
          injection h with hec
          subst hec
          refine Or.inr (Or.inl ⟨b, hfi, hfk, by simpa using hdk, ?_,
            bool2int_i_reason_entailed p i k hmem b⟩)
          change T.decodeClause
            ([neLit i (.bool b), eqLit k (.int (if b then 1 else 0))].toArray.map pLit) =
            [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]
          exact LitTable.decodeClause_map_pLit T _
    · rename_i hfi
      split at h
      · rename_i q hfk
        by_cases hq : q = 0 ∨ q = 1
        · rw [dif_pos hq] at h
          split at h
          · rename_i b hdi
            by_cases hb : b = (q == 1)
            · rw [dif_pos hb] at h
              cases h
            · rw [dif_neg hb] at h
              injection h with hec
              subst hec
              refine Or.inr (Or.inr (Or.inr (Or.inl ⟨b, q, hfk, hq, hdi, hb, ?_,
                bool2int_k_reason_entailed p i k hmem q hq⟩)))
              change T.decodeClause
                ([neLit k (.int q), eqLit i (.bool (q == 1))].toArray.map pLit) =
                [neLit k (.int q), eqLit i (.bool (q == 1))]
              exact LitTable.decodeClause_map_pLit T _
          · cases h
          · cases h
        · rw [dif_neg hq] at h
          injection h with hec
          subst hec
          refine Or.inr (Or.inr (Or.inl ⟨q, hfk, hq, ?_,
            bool2int_k01_reason_entailed p i k hmem⟩))
          change T.decodeClause ([negNe k 0, negNe k 1].toArray.map pLit) =
            [negNe k 0, negNe k 1]
          exact LitTable.decodeClause_map_pLit T _
      · cases h
      · rename_i hfk
        by_cases hk0 : (view.doms.getD k DomC.empty).memIntView 0 = false
        · rw [dif_pos hk0] at h
          by_cases hk1 : (view.doms.getD k DomC.empty).memIntView 1 = false
          · rw [dif_pos hk1] at h
            injection h with hec
            subst hec
            refine Or.inr (Or.inr (Or.inr (Or.inr ⟨hfk, hk0, hk1, ?_,
              bool2int_k01_reason_entailed p i k hmem⟩)))
            change T.decodeClause ([negNe k 0, negNe k 1].toArray.map pLit) =
              [negNe k 0, negNe k 1]
            exact LitTable.decodeClause_map_pLit T _
          · rw [dif_neg hk1] at h
            cases h
        · rw [dif_neg hk0] at h
          cases h
  · cases h

theorem bool2intPropWith_run_prune (p : CompiledProblem DomConstraint)
    (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (bool2intPropWith p T i k hmem).run view = .prune ps) :
    (∃ b,
      (view.doms.getD i DomC.empty).fixedValue = some (.bool b) ∧
      (view.doms.getD k DomC.empty).fixedValue = none ∧
      (view.doms.getD k DomC.empty).memIntView (if b then 1 else 0) = true ∧
      (∀ q ∈ ps.toList,
        q.1.lit = eqLit k (.int (if b then 1 else 0)) ∧
        T.decodeClause q.2.lits =
          [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))] ∧
        Entailed p [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))])) ∨
    (∃ q,
      (view.doms.getD k DomC.empty).fixedValue = some (.int q) ∧
      (q = 0 ∨ q = 1) ∧
      (view.doms.getD i DomC.empty).fixedValue = none ∧
      (∀ q' ∈ ps.toList,
        q'.1.lit = eqLit i (.bool (q == 1)) ∧
        T.decodeClause q'.2.lits = [neLit k (.int q), eqLit i (.bool (q == 1))] ∧
        Entailed p [neLit k (.int q), eqLit i (.bool (q == 1))])) := by
  unfold bool2intPropWith at h
  dsimp only at h
  split at h
  · split at h
    · rename_i b hfi
      split at h
      · rename_i q hfk
        by_cases hq : q = (if b then 1 else 0)
        · rw [dif_pos hq] at h
          cases h
        · rw [dif_neg hq] at h
          cases h
      · cases h
      · rename_i hfk
        by_cases hdk : (view.doms.getD k DomC.empty).memIntView (if b then 1 else 0) = true
        · rw [dif_pos hdk] at h
          injection h with hec
          subst hec
          refine Or.inl ⟨b, hfi, hfk, hdk, ?_⟩
          intro q hq
          have hq' : q = (pLit (eqLit k (.int (if b then 1 else 0))),
              EClause.ofLiterals p T
                [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]
                (bool2int_i_reason_entailed p i k hmem b)) := by
            simpa using hq
          subst hq'
          refine ⟨rfl, ?_, bool2int_i_reason_entailed p i k hmem b⟩
          change T.decodeClause
            ([neLit i (.bool b), eqLit k (.int (if b then 1 else 0))].toArray.map pLit) =
            [neLit i (.bool b), eqLit k (.int (if b then 1 else 0))]
          exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hdk] at h
          cases h
    · rename_i hfi
      split at h
      · rename_i q hfk
        by_cases hq : q = 0 ∨ q = 1
        · rw [dif_pos hq] at h
          split at h
          · rename_i b hdi
            by_cases hb : b = (q == 1)
            · rw [dif_pos hb] at h
              cases h
            · rw [dif_neg hb] at h
              cases h
          · cases h
          · rename_i hdi
            injection h with hec
            subst hec
            refine Or.inr ⟨q, hfk, hq, hdi, ?_⟩
            intro q' hq'
            have hq'' : q' = (pLit (eqLit i (.bool (q == 1))),
                EClause.ofLiterals p T
                  [neLit k (.int q), eqLit i (.bool (q == 1))]
                  (bool2int_k_reason_entailed p i k hmem q hq)) := by
              simpa using hq'
            subst hq''
            refine ⟨rfl, ?_, bool2int_k_reason_entailed p i k hmem q hq⟩
            change T.decodeClause
              ([neLit k (.int q), eqLit i (.bool (q == 1))].toArray.map pLit) =
              [neLit k (.int q), eqLit i (.bool (q == 1))]
            exact LitTable.decodeClause_map_pLit T _
        · rw [dif_neg hq] at h
          cases h
      · cases h
      · by_cases hk0 : (view.doms.getD k DomC.empty).memIntView 0 = false
        · rw [dif_pos hk0] at h
          by_cases hk1 : (view.doms.getD k DomC.empty).memIntView 1 = false
          · rw [dif_pos hk1] at h
            cases h
          · rw [dif_neg hk1] at h
            cases h
        · rw [dif_neg hk0] at h
          cases h
  · cases h

theorem bool2intPropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    {ec : EClause p T}
    (h : (bool2intPropWith p T i k hmem).run view = .conflict ec) :
    Entailed p (T.decodeClause ec.lits) := by
  rcases bool2intPropWith_run_conflict p T i k hmem view h with
    ⟨_, _, _, _, _, hdec, hent⟩ | ⟨_, _, _, _, hdec, hent⟩ |
    ⟨_, _, _, hdec, hent⟩ | ⟨_, _, _, _, _, _, hdec, hent⟩ |
    ⟨_, _, _, hdec, hent⟩
  all_goals rw [hdec]; exact hent

theorem bool2intPropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFk : (view.doms.getD k DomC.empty).WF)
    {ec : EClause p T}
    (h : (bool2intPropWith p T i k hmem).run view = .conflict ec) :
    ∀ q ∈ T.decodeClause ec.lits,
      (view.doms.getD (atomSlot q.atom) DomC.empty).evalLit q = some false := by
  rcases bool2intPropWith_run_conflict p T i k hmem view h with
    hA | hB | hC | hD | hE
  · obtain ⟨b, q, hfi, hfk, hqne, hdec, _hent⟩ := hA
    rw [hdec]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFi hfi
    · rw [atomSlot_eqLit]
      exact DomC.evalLit_eqLit_int_false_of_fixed_int_other hWFk hfk hqne
  · obtain ⟨b, hfi, hfk, hdk, hdec, _hent⟩ := hB
    rw [hdec]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFi hfi
    · rw [atomSlot_eqLit]
      exact DomC.evalLit_eqLit_int_false_of_not_mem hfk hdk
  · obtain ⟨q, hfk, hqnot, hdec, _hent⟩ := hC
    rw [hdec]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact DomC.evalLit_negNe_false_of_fixed_int_other hWFk hfk
        (by intro hq0; exact hqnot (Or.inl hq0))
    · exact DomC.evalLit_negNe_false_of_fixed_int_other hWFk hfk
        (by intro hq1; exact hqnot (Or.inr hq1))
  · obtain ⟨b, q, hfk, hq, hfi, hb, hdec, _hent⟩ := hD
    rw [hdec]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · rw [atomSlot_neLit]
      exact DomC.evalLit_neLit_fixed_false hWFk hfk
    · rw [atomSlot_eqLit]
      exact DomC.evalLit_eqLit_bool_false_of_fixed_other hfi hb
  · obtain ⟨hfk, hk0, hk1, hdec, _hent⟩ := hE
    rw [hdec]
    intro l hl
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact DomC.evalLit_negNe_false_of_not_mem hfk hk0
    · exact DomC.evalLit_negNe_false_of_not_mem hfk hk1

theorem bool2intPropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    {ps : Array (PLit × EClause p T)}
    (h : (bool2intPropWith p T i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    Entailed p (T.decodeClause q.2.lits) := by
  rcases bool2intPropWith_run_prune p T i k hmem view h with
    ⟨_, _, _, _, hfacts⟩ | ⟨_, _, _, _, hfacts⟩
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]
  · obtain ⟨_, hdec, hent⟩ := hfacts q hq
    rwa [hdec]

theorem bool2intPropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFk : (view.doms.getD k DomC.empty).WF)
    {ps : Array (PLit × EClause p T)}
    (h : (bool2intPropWith p T i k hmem).run view = .prune ps)
    {q : PLit × EClause p T} (hq : q ∈ ps.toList) :
    (view.doms.getD (atomSlot q.1.lit.atom) DomC.empty).evalLit q.1.lit = none ∧
      ∀ q' ∈ T.decodeClause q.2.lits, q' ≠ q.1.lit →
        (view.doms.getD (atomSlot q'.atom) DomC.empty).evalLit q' = some false := by
  rcases bool2intPropWith_run_prune p T i k hmem view h with
    ⟨b, hfi, hfk, hdk, hfacts⟩ | ⟨q0, hfk, _hq, hfi, hfacts⟩
  · obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_eqLit]
      exact DomC.evalLit_eqLit_int_none_of_memIntView hfk hdk
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFi hfi
      · exact absurd hlit.symm hne
  · obtain ⟨hlit, hdec, _hent⟩ := hfacts q hq
    refine ⟨?_, ?_⟩
    · rw [hlit, atomSlot_eqLit]
      exact DomC.evalLit_eqLit_bool_none_of_not_fixed hfi
    · intro q' hq' hne
      rw [hdec] at hq'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq'
      rcases hq' with rfl | rfl
      · rw [atomSlot_neLit]
        exact DomC.evalLit_neLit_fixed_false hWFk hfk
      · exact absurd hlit.symm hne

theorem bool2intPropWith_run_fix_of_bounds_none
    (p : CompiledProblem DomConstraint) (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    (hi : domBounds (view.doms.getD i DomC.empty) = none) :
    (bool2intPropWith p T i k hmem).run view = .fix := by
  unfold bool2intPropWith
  dsimp only
  rw [hi]

theorem bool2intPropWith_run_fix_of_bounds_none_right
    (p : CompiledProblem DomConstraint) (T : LitTable) (i k : Nat)
    (hmem : DomConstraint.bool2intSlot i k ∈ p.constraints) (view : EngineView)
    (hk : domBounds (view.doms.getD k DomC.empty) = none) :
    (bool2intPropWith p T i k hmem).run view = .fix := by
  unfold bool2intPropWith
  dsimp only
  rw [hk]
  cases hb : domBounds (view.doms.getD i DomC.empty) with
  | none => rfl
  | some q => cases q; rfl


end LeanFzn.Engine
