/-
File: LeanFzn/Engine/Props/Ne.lean

Dedicated `int_ne` propagator: when one side is fixed to `v` and the other
side still contains `v`, remove `v` from the other side.  The reason is
`(x ≠ v) ∨ (y ≠ v)`, entailed by the disequality together with the
kind-homogeneity guard: `v` must be a member of both initial converted
domains so that `neLit` (an integer singleton negation or a Boolean
complement pin) is exact across value constructors.

`nePropWith` is the real propagator; it takes the initial domains, their
conversion proofs, and the constraint-membership proof; `propsOf`
registers it.
-/
import LeanFzn.Engine.Prop

open LeanFzn LeanFzn.Compiler LeanFzn.Semantics LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Engine

/-- The literal "slot `s` is not `v`": `intNe` for integers, `boolEq (!b)`
for Booleans. -/
def neLit (s : Nat) (v : Value) : Literal :=
  match v with
  | .int i => posNe s i
  | .bool b => posBool s (!b)
  | _ => posNe s 0

/-- On a kind-homogeneous initial domain containing both `vi` and the
slot's value `w`, the literal `neLit s vi` holds exactly when `w ≠ vi`.
This is the kind-agreement bridge that makes `int_ne` sound. -/
theorem neLit_eval_true_iff_of_mem {init : DomC} {vi w : Value} {s : Nat}
    {a : List Value} (hvi : init.mem vi = true) (hw : init.mem w = true)
    (ha : a[s]? = some w) :
    (neLit s vi).eval a = some true ↔ w ≠ vi := by
  cases vi with
  | int x =>
      obtain ⟨y, rfl⟩ := DomC.mem_int_kind (x := x) hvi hw
      rw [show neLit s (.int x) = posNe s x from rfl, eval_posNe_iff]
      constructor
      · rintro ⟨i, hi, hix⟩
        have hiy : i = y := by
          have hsi : slotInt a s = some y := by
            simp [slotInt, ha, Value.intView]
          rw [hsi] at hi
          exact (Option.some.inj hi).symm
        subst hiy
        intro h
        exact hix (Value.int.inj h)
      · intro hne
        refine ⟨y, ?_, ?_⟩
        · simp [slotInt, ha, Value.intView]
        · intro hyx
          exact hne (by rw [hyx])
  | bool b =>
      obtain ⟨y, rfl⟩ := DomC.mem_bool_kind (b := b) hvi hw
      rw [show neLit s (.bool b) = posBool s (!b) from rfl, eval_posBool_iff, ha]
      constructor
      · intro h
        have hy : y = !b := by simpa using h
        intro hyb
        have hyb' : y = b := by simpa using hyb
        rw [hy] at hyb'
        cases b <;> simp at hyb'
      · intro hne
        have hy : y = !b := by
          cases y <;> cases b <;> simp_all
        simp [hy]
  | setOfInt _ => simp [DomC.mem] at hvi
  | array _ => simp [DomC.mem] at hvi

/-- Both fixed values equal: the two-literal disequality clause is
entailed. -/
theorem nePropWith_conflict_entailed (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.neSlot i j ∈ p.constraints)
    (vi vj : Value) (heq : vi = vj)
    (hgi : (init.getD i DomC.empty).mem vi = true)
    (hgj : (init.getD j DomC.empty).mem vj = true) :
    Entailed p [neLit i vi, neLit j vj] := by
  subst vj
  intro b hb hacc
  have hfit := allAssigns_fits_dom p.domains b hb
  have hne : (DomConstraint.neSlot i j).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨wi, wj, hbi, hbj, hwij⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hne
  have hbi' : (init.getD i DomC.empty).mem wi = true :=
    (DomC.mem_iff _ _ (hinit i (by simp)) wi).mpr (hfit.2 i wi hbi)
  have hbj' : (init.getD j DomC.empty).mem wj = true :=
    (DomC.mem_iff _ _ (hinit j (by simp)) wj).mpr (hfit.2 j wj hbj)
  have hiffi := neLit_eval_true_iff_of_mem (init := (init.getD i DomC.empty))
    (vi := vi) (w := wi) hgi hbi' hbi
  have hiffj := neLit_eval_true_iff_of_mem (init := (init.getD j DomC.empty))
    (vi := vi) (w := wj) hgj hbj' hbj
  by_cases htrue : (neLit i vi).eval b = some true
  · exact ⟨neLit i vi, by simp, htrue⟩
  · have hvi : wi = vi := by
      apply Classical.byContradiction
      intro hne'
      exact htrue (hiffi.mpr hne')
    have hwjne : wj ≠ vi := by
      intro h
      exact hwij (hvi.trans h.symm)
    exact ⟨neLit j vi, by simp, hiffj.mpr hwjne⟩

end LeanFzn.Engine

namespace LeanFzn.Engine

/-- One side fixed to `vi` and `vi` a member of both initial domains: the
disequality reason `x_i ≠ vi ∨ x_j ≠ vi` is entailed. -/
theorem nePropWith_prune_reason_entailed (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.neSlot i j ∈ p.constraints)
    (vi : Value)
    (hgi : (init.getD i DomC.empty).mem vi = true)
    (hgj : (init.getD j DomC.empty).mem vi = true) :
    Entailed p [neLit i vi, neLit j vi] := by
  intro b hb hacc
  have hfit := allAssigns_fits_dom p.domains b hb
  have hne : (DomConstraint.neSlot i j).satisfiedB b = true :=
    List.all_eq_true.mp hacc _ hmem
  obtain ⟨wi, wj, hbi, hbj, hwij⟩ :=
    (DomConstraint.satisfiedB_iff _ _).mp hne
  have hbi' : (init.getD i DomC.empty).mem wi = true :=
    (DomC.mem_iff _ _ (hinit i (by simp)) wi).mpr (hfit.2 i wi hbi)
  have hbj' : (init.getD j DomC.empty).mem wj = true :=
    (DomC.mem_iff _ _ (hinit j (by simp)) wj).mpr (hfit.2 j wj hbj)
  have hiffi := neLit_eval_true_iff_of_mem (init := (init.getD i DomC.empty))
    (vi := vi) (w := wi) hgi hbi' hbi
  have hiffj := neLit_eval_true_iff_of_mem (init := (init.getD j DomC.empty))
    (vi := vi) (w := wj) hgj hbj' hbj
  by_cases htrue : (neLit i vi).eval b = some true
  · exact ⟨neLit i vi, by simp, htrue⟩
  · have hvi : wi = vi := by
      apply Classical.byContradiction
      intro hne'
      exact htrue (hiffi.mpr hne')
    have hwjne : wj ≠ vi := by
      intro h
      exact hwij (hvi.trans h.symm)
    exact ⟨neLit j vi, by simp, hiffj.mpr hwjne⟩

/-- Second prune branch (the `j`-fixed mirror), same clause. -/
theorem nePropWith_prune_reason_entailed_symm (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.neSlot i j ∈ p.constraints)
    (vj : Value)
    (hgi : (init.getD i DomC.empty).mem vj = true)
    (hgj : (init.getD j DomC.empty).mem vj = true) :
    Entailed p [neLit i vj, neLit j vj] :=
  nePropWith_prune_reason_entailed p init i j hinit hmem vj hgi hgj

end LeanFzn.Engine

namespace LeanFzn.Engine

/-- A fixed value makes its own disequality literal false. -/
theorem DomC.evalLit_neLit_fixed_false {d : DomC} {s : Nat} {v : Value}
    (hWF : d.WF) (h : d.fixedValue = some v) :
    d.evalLit (neLit s v) = some false := by
  cases v with
  | int x =>
      have hm : d.mem (.int x) = true := (DomC.fixedValue_sound d hWF h).1
      have hmiv := DomC.memIntView_eq_mem_int hm
      simp [neLit, posNe, DomC.evalLit, h, hmiv]
  | bool b =>
      simp only [neLit, posBool, DomC.evalLit, h]
      cases b <;> rfl
  | setOfInt x =>
      have hm := (DomC.fixedValue_sound d hWF h).1
      cases d <;> simp [DomC.mem] at hm
  | array xs =>
      have hm := (DomC.fixedValue_sound d hWF h).1
      cases d <;> simp [DomC.mem] at hm

/-- An unfixed domain containing `v` leaves the disequality literal
unassigned. -/
theorem DomC.evalLit_neLit_none_of_not_fixed {d : DomC} {s : Nat} {v : Value}
    (hfv : d.fixedValue = none) (hmem : d.mem v = true) :
    d.evalLit (neLit s v) = none := by
  cases v with
  | int x =>
      have hmiv := DomC.memIntView_eq_mem_int hmem
      simp [neLit, posNe, DomC.evalLit, hfv, hmiv]
  | bool b =>
      simp [neLit, posBool, DomC.evalLit, hfv]
  | setOfInt x => simp [DomC.mem] at hmem
  | array xs => simp [DomC.mem] at hmem

/-- Applying `x ≠ v` removes exactly the members equal to `v`, when `v`
is itself a member of the well-formed domain. -/
theorem DomC.mem_applyLit_neLit {d : DomC} (s : Nat) {v : Value}
    (hWF : d.WF) (hm : d.mem v = true) (w : Value) :
    (d.applyLit (neLit s v)).mem w = true ↔ d.mem w = true ∧ w ≠ v := by
  cases v with
  | int x =>
      change (d.applyLit (posNe s x)).mem w = true ↔
        d.mem w = true ∧ w ≠ .int x
      rw [DomC.mem_applyLit d _ hWF w]
      change d.mem w = true ∧ Literal.valueHolds ⟨.intNe s x, true⟩ w = true ↔
        d.mem w = true ∧ w ≠ .int x
      rw [valueHolds_intNe_pos_iff]
      constructor
      · rintro ⟨hw, i, hiv, hix⟩
        refine ⟨hw, ?_⟩
        intro hwv
        rw [hwv] at hiv
        simp [Value.intView] at hiv
        exact hix hiv.symm
      · rintro ⟨hw, hwne⟩
        obtain ⟨y, rfl⟩ := DomC.mem_int_kind (x := x) hm hw
        refine ⟨hw, y, ?_, ?_⟩
        · simp [Value.intView]
        · intro hyx
          exact hwne (by rw [hyx])
  | bool b =>
      change (d.applyLit (posBool s (!b))).mem w = true ↔
        d.mem w = true ∧ w ≠ .bool b
      rw [DomC.mem_applyLit d _ hWF w]
      change d.mem w = true ∧ Literal.valueHolds ⟨.boolEq s (!b), true⟩ w = true ↔
        d.mem w = true ∧ w ≠ .bool b
      rw [valueHolds_boolEq_iff]
      constructor
      · rintro ⟨hw, hwv⟩
        refine ⟨hw, ?_⟩
        intro hwb
        rw [hwb] at hwv
        cases b <;> simp [Value.bool.injEq] at hwv
      · rintro ⟨hw, hwne⟩
        obtain ⟨y, rfl⟩ := DomC.mem_bool_kind (b := b) hm hw
        refine ⟨hw, ?_⟩
        have hy : y = !b := by
          cases y <;> cases b <;> simp_all
        simp [hy]
  | setOfInt x => simp [DomC.mem] at hm
  | array xs => simp [DomC.mem] at hm

end LeanFzn.Engine

namespace LeanFzn.Engine

/-- The `int_ne` propagator with the initial-domain kind guard and the
constraint-membership proof needed to build entailed reasons. -/
def nePropWith (p : CompiledProblem DomConstraint) (T : LitTable)
    (init : Array DomC) (i j : Nat)
    (hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (hmem : DomConstraint.neSlot i j ∈ p.constraints) : PropV2 p T :=
  { vars := #[i, j]
    events := #[(i, .bounds), (j, .bounds), (i, .fix), (j, .fix)]
    run := fun view =>
      let di := view.doms.getD i DomC.empty
      let dj := view.doms.getD j DomC.empty
      match di.fixedValue, dj.fixedValue with
      | some vi, some vj =>
          if heq : vi == vj then
            if hgi : (init.getD i DomC.empty).mem vi = true then
              if hgj : (init.getD j DomC.empty).mem vj = true then
                let ls := [neLit i vi, neLit j vj]
                .conflict (EClause.ofLiterals p T ls
                  (nePropWith_conflict_entailed p init i j hinit hmem vi vj
                    (eq_of_beq heq) hgi hgj))
              else .fix
            else .fix
          else .fix
      | some vi, none =>
          if _hdj : dj.mem vi = true then
            if hgi : (init.getD i DomC.empty).mem vi = true then
              if hgj : (init.getD j DomC.empty).mem vi = true then
                let ls := [neLit i vi, neLit j vi]
                .prune #[(pLit (neLit j vi), EClause.ofLiterals p T ls
                  (nePropWith_prune_reason_entailed p init i j hinit hmem vi hgi hgj))]
              else .fix
            else .fix
          else .fix
      | none, some vj =>
          if _hdi : di.mem vj = true then
            if hgi : (init.getD i DomC.empty).mem vj = true then
              if hgj : (init.getD j DomC.empty).mem vj = true then
                let ls := [neLit i vj, neLit j vj]
                .prune #[(pLit (neLit i vj), EClause.ofLiterals p T ls
                  (nePropWith_prune_reason_entailed_symm p init i j hinit hmem vj hgi hgj))]
              else .fix
            else .fix
          else .fix
      | none, none => .fix }

theorem nePropWith_conflict_lits_false (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (_hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (_hmem : DomConstraint.neSlot i j ∈ p.constraints) (view : EngineView)
    (vi vj : Value)
    (hdi : (view.doms.getD i DomC.empty).fixedValue = some vi)
    (hdj : (view.doms.getD j DomC.empty).fixedValue = some vj)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hWFj : (view.doms.getD j DomC.empty).WF) :
    (view.doms.getD i DomC.empty).evalLit (neLit i vi) = some false ∧
    (view.doms.getD j DomC.empty).evalLit (neLit j vj) = some false :=
  ⟨DomC.evalLit_neLit_fixed_false hWFi hdi,
   DomC.evalLit_neLit_fixed_false hWFj hdj⟩

theorem nePropWith_prune_lit_none (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (_hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (_hmem : DomConstraint.neSlot i j ∈ p.constraints) (view : EngineView)
    (vi : Value)
    (hdi : (view.doms.getD i DomC.empty).fixedValue = some vi)
    (hdj : (view.doms.getD j DomC.empty).fixedValue = none)
    (hWFi : (view.doms.getD i DomC.empty).WF)
    (hdjm : (view.doms.getD j DomC.empty).mem vi = true) :
    (view.doms.getD i DomC.empty).evalLit (neLit i vi) = some false ∧
    (view.doms.getD j DomC.empty).evalLit (neLit j vi) = none :=
  ⟨DomC.evalLit_neLit_fixed_false hWFi hdi,
   DomC.evalLit_neLit_none_of_not_fixed hdj hdjm⟩

theorem nePropWith_prune_lit_none_symm (p : CompiledProblem DomConstraint)
    (init : Array DomC) (i j : Nat)
    (_hinit : ∀ s ∈ [i, j],
      DomC.ofDom? (p.domains.getD s Dom.empty) = some (init.getD s DomC.empty))
    (_hmem : DomConstraint.neSlot i j ∈ p.constraints) (view : EngineView)
    (vj : Value)
    (hdi : (view.doms.getD i DomC.empty).fixedValue = none)
    (hdj : (view.doms.getD j DomC.empty).fixedValue = some vj)
    (hWFj : (view.doms.getD j DomC.empty).WF)
    (hdim : (view.doms.getD i DomC.empty).mem vj = true) :
    (view.doms.getD i DomC.empty).evalLit (neLit i vj) = none ∧
    (view.doms.getD j DomC.empty).evalLit (neLit j vj) = some false :=
  ⟨DomC.evalLit_neLit_none_of_not_fixed hdi hdim,
   DomC.evalLit_neLit_fixed_false hWFj hdj⟩

/-- Membership effect of the literal emitted by the prune branches. -/
theorem nePropWith_mem_prune (d : DomC) (s : Nat) {v : Value}
    (hWF : d.WF) (hm : d.mem v = true) (w : Value) :
    (d.applyLit (neLit s v)).mem w = true ↔ d.mem w = true ∧ w ≠ v :=
  DomC.mem_applyLit_neLit s hWF hm w

end LeanFzn.Engine
