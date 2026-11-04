/-
File: LeanFzn/Compiler/Proofs/Objective.lean

Purpose:
  Correctness of the optimization front end `compileModelOpt` (PLAN.md
  task O1).  The satisfy part is exact and covering exactly as for
  `compileModelFull`; the objective slot reads the source objective; and
  `compileOpt_optimal` is the source-level optimality transfer lemma a
  branch-and-bound driver consumes: an accepted assignment whose
  improving-bound extension of the compiled problem has no accepted
  assignment yields a source `IsSolution`, i.e. an optimal store in the
  `Semantics` sense.

Dependencies:
  - LeanFzn.Compiler.Objective, LeanFzn.Compiler.Proofs.Normalize.
-/

import LeanFzn.Compiler.Objective
import LeanFzn.Compiler.Proofs.Normalize

namespace LeanFzn.Compiler
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Core

theorem wf_satisfyPart {m : Model} (hwf : WellFormed fullSig m) :
    WellFormed fullSig (satisfyPart m) :=
  { hwf with objectiveType := trivial }

/-- Inversion of a successful `compileModelOpt`. -/
theorem compileOpt_inv {m : Model} {p : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} (hc : compileModelOpt m = .ok (p, spec)) :
    ∃ p0, compileModelFull (satisfyPart m) = .ok p0 ∧
      p = { p0 with source := m } ∧
      objectiveOf m.solve = some (spec.dir, spec.var) ∧
      objVarOkB m spec.var = true ∧
      nameIndex p0.names spec.var.name = some spec.slot := by
  unfold compileModelOpt at hc
  split at hc
  · cases hc
  · rename_i dir x hobj
    split at hc
    · rename_i hok
      split at hc
      · cases hc
      · rename_i p0 hp0
        split at hc
        · cases hc
        · rename_i i hi
          cases hc
          exact ⟨p0, hp0, rfl, hobj, hok, hi⟩
    · cases hc

/-- The objective variable is a declared initializer-free `var int`. -/
theorem objVarOkB_decl {m : Model} {x : Ident} (h : objVarOkB m x = true) :
    ∃ (ty : BasicVarType) (anns : List Annotation),
      (.basic ty x anns none : VarDeclItem) ∈ m.variables ∧ ty.base = .int := by
  unfold objVarOkB at h
  obtain ⟨d, hd, hdd⟩ := List.any_eq_true.mp h
  cases d with
  | array _ _ _ _ => simp at hdd
  | basic ty n anns init =>
      cases init with
      | some _ => simp at hdd
      | none =>
          simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hdd
          have hxn : n = x := ident_eq_of_name hdd.1
          subst hxn
          exact ⟨ty, anns, hd, hdd.2⟩

/-- The satisfy-part compiled store reads the objective variable at its
    slot. -/
theorem optToStore_slot {m : Model} {p0 : CompiledProblem DomConstraint}
    (hc : compileModelFull m = .ok p0) (hwf : WellFormed fullSig m)
    {x : Ident} {ty : BasicVarType} {anns : List Annotation}
    (hd : (.basic ty x anns none : VarDeclItem) ∈ m.variables)
    {i : Nat} (hi : nameIndex p0.names x.name = some i) (a : List Value) :
    p0.toStore a x = a[i]? := by
  obtain ⟨hgate, p00, hcn, rfl⟩ := compileFull_inv hc
  have hnu : NamesNodup m := hwf.valueNamesUnique
  have hnone := lookup_arrayDefs_none hnu (x := x) (Or.inr ⟨_, hd, rfl, rfl⟩)
  show fullStore (arrayDefs m) (p00.toStore a) x = a[i]?
  rw [fullStore_of_none hnone]
  obtain ⟨_, slots, dcs, _, _, hasm⟩ := compileModel_ok_inv hcn
  have hi' : nameIndex (slots.map Prod.fst) x.name = some i := by
    have : p00.names = slots.map Prod.fst := by rw [hasm]; rfl
    rw [← this]; exact hi
  rw [hasm]
  show (match nameIndex (slots.map Prod.fst) x.name with
    | some i => a[i]?
    | none => parEnv (normalizeModel m) x) = a[i]?
  rw [hi']

/-- Value shape: an `int`-based variable reads an `int`. -/
theorem int_of_contains {ty : BasicVarType} {v : Value} (hb : ty.base = .int)
    (h : ty.contains v) : ∃ i, v = .int i := by
  have := valOf_of_contains hb (Or.inl rfl) h
  cases v <;> simp [ValOf] at this ⊢

theorem objectiveOf_cases {sv : SolveItem} {dir : OptDir} {x : Ident}
    (h : objectiveOf sv = some (dir, x)) :
    (∃ anns, sv = .minimize anns (.ident x) ∧ dir = .minimize) ∨
    (∃ anns, sv = .maximize anns (.ident x) ∧ dir = .maximize) := by
  cases sv with
  | satisfy _ => simp [objectiveOf] at h
  | minimize anns e =>
      cases e with
      | ident y =>
          simp only [objectiveOf, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inl ⟨anns, rfl, rfl⟩
      | lit _ => simp [objectiveOf] at h
  | maximize anns e =>
      cases e with
      | ident y =>
          simp only [objectiveOf, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl⟩ := h
          exact Or.inr ⟨anns, rfl, rfl⟩
      | lit _ => simp [objectiveOf] at h

/-- The source objective of a variable objective reads the variable. -/
theorem objective_of_ident {m : Model} {dir : OptDir} {x : Ident}
    (hobj : objectiveOf m.solve = some (dir, x)) (s : Store) :
    m.solve.objective s = (match s x with | some (.int i) => some i | _ => none) := by
  rcases objectiveOf_cases hobj with ⟨anns, h, _⟩ | ⟨anns, h, _⟩ <;>
    (rw [h]; rfl)

/-- **(a) + (b)** Exactness of the optimization front end together with
    objective correspondence: an accepted assignment's store satisfies
    the original model's dynamic conditions, is parameter-honest, and
    the source objective evaluates to the integer at the objective
    slot. -/
theorem compileOpt_exact {m : Model} {p : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} (hc : compileModelOpt m = .ok (p, spec))
    (hwf : WellFormed fullSig m) {a : List Value}
    (hmem : a ∈ allAssigns p.domains) (hacc : accepts p a = true) :
    SatisfiesDyn fullInterp m (p.toStore a) ∧
      LeanFzn.Semantics.ParamHonest m (p.toStore a) ∧
      ∃ i, m.solve.objective (p.toStore a) = some i ∧
        a[spec.slot]? = some (.int i) := by
  obtain ⟨p0, hp0, rfl, hobj, hok, hslot⟩ := compileOpt_inv hc
  obtain ⟨ty, anns, hd, hty⟩ := objVarOkB_decl hok
  have hwf' := wf_satisfyPart hwf
  obtain ⟨hsat, hpar⟩ := compileFull_exact hp0 hwf' hmem hacc
  refine ⟨hsat, hpar, ?_⟩
  have hts := optToStore_slot hp0 hwf' (m := satisfyPart m) hd hslot a
  obtain ⟨v, hv, hcont⟩ : ∃ v, p0.toStore a spec.var = some v ∧ ty.contains v := by
    have := hsat.2.1 _ hd
    simpa using this
  obtain ⟨i, rfl⟩ := int_of_contains hty hcont
  refine ⟨i, ?_, ?_⟩
  · rw [objective_of_ident hobj]
    show (match p0.toStore a spec.var with | some (.int i) => some i | _ => none) = _
    rw [hv]
  · rw [← hts]; exact hv

/-- Coverage with agreement: every satisfying parameter-honest store of
    the original model is covered by an accepted assignment whose store
    gives the same value to the objective variable. -/
theorem compileOpt_covers {m : Model} {p : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} (hc : compileModelOpt m = .ok (p, spec))
    (hwf : WellFormed fullSig m) {store : Store}
    (hsat : SatisfiesDyn fullInterp m store)
    (hparam : LeanFzn.Semantics.ParamHonest m store) :
    ∃ a, a ∈ allAssigns p.domains ∧ accepts p a = true ∧
      p.toStore a spec.var = store spec.var := by
  obtain ⟨p0, hp0, rfl, hobj, hok, hslot⟩ := compileOpt_inv hc
  obtain ⟨ty, anns, hd, hty⟩ := objVarOkB_decl hok
  obtain ⟨a, h1, h2, h3⟩ := compileFull_covers_agree hp0 (wf_satisfyPart hwf)
    (m := satisfyPart m) hsat hparam
  exact ⟨a, h1, h2, h3 ty spec.var anns hd⟩

/-- **(c) Optimality transfer.**  Let `a` be an accepted assignment with
    objective value `v` at the objective slot.  If no assignment of the
    compiled problem extended with the improving bound
    (`spec.improveBound v`: `leConstHi slot (v-1)` for minimize,
    `leConstLo slot (v+1)` for maximize) is accepted, then the source
    store of `a` is a solution of the optimization model: satisfying,
    parameter-honest, objective attained, and optimal. -/
theorem compileOpt_optimal {m : Model} {p : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} (hc : compileModelOpt m = .ok (p, spec))
    (hwf : WellFormed fullSig m) {a : List Value}
    (hmem : a ∈ allAssigns p.domains) (hacc : accepts p a = true)
    {v : Int} (hv : a[spec.slot]? = some (.int v))
    (hnone : ∀ b ∈ allAssigns p.domains,
      accepts (p.addConstraint (spec.improveBound v)) b = false) :
    IsSolution fullSig fullInterp m (p.toStore a) := by
  obtain ⟨hsat, hpar, i, hi, hai⟩ := compileOpt_exact hc hwf hmem hacc
  have hiv : i = v := by
    rw [hv] at hai
    simpa using hai.symm
  subst hiv
  have hc' := hc
  obtain ⟨p0, hp0, rfl, hobj, hok, hslot⟩ := compileOpt_inv hc'
  obtain ⟨ty, anns, hd, hty⟩ := objVarOkB_decl hok
  have hwf' := wf_satisfyPart hwf
  -- any competing store is covered by an accepted assignment reading its
  -- objective at the slot
  have hbound : ∀ other : Store, Satisfies fullSig fullInterp m other →
      LeanFzn.Semantics.ParamHonest m other → ∀ j,
      m.solve.objective other = some j →
      ∃ b ∈ allAssigns p0.domains, accepts p0 b = true ∧
        b[spec.slot]? = some (.int j) := by
    intro other hs hph j hj
    obtain ⟨b, hb1, hb2, hb3⟩ := compileOpt_covers hc hwf hs.2 hph
    refine ⟨b, hb1, hb2, ?_⟩
    have hx : p0.toStore b spec.var = other spec.var := hb3
    rw [optToStore_slot hp0 hwf' (m := satisfyPart m) hd hslot b] at hx
    rw [objective_of_ident hobj] at hj
    cases hr : other spec.var with
    | none => rw [hr] at hj; simp at hj
    | some w =>
        rw [hr] at hj hx
        cases w with
        | int k => simp at hj; rw [hj] at hx; exact hx
        | _ => simp at hj
  refine ⟨⟨hwf, hsat⟩, hpar, ?_, ?_⟩
  · unfold ObjectiveAttained
    split
    · trivial
    · exact ⟨_, hi⟩
    · exact ⟨_, hi⟩
  · unfold IsOptimal
    have key : ∀ other : Store, Satisfies fullSig fullInterp m other →
        LeanFzn.Semantics.ParamHonest m other → ∀ i' j,
        m.solve.objective (p0.toStore a) = some i' →
        m.solve.objective other = some j →
        (spec.dir = .minimize → i' ≤ j) ∧ (spec.dir = .maximize → j ≤ i') := by
      intro other hs hph i' j hi' hj
      have hi'v : i' = i := by rw [hi] at hi'; exact (Option.some.inj hi').symm
      subst hi'v
      obtain ⟨b, hb1, hb2, hb3⟩ := hbound other hs hph j hj
      have hn : accepts (p0.addConstraint (spec.improveBound i')) b = false :=
        hnone b hb1
      constructor
      · intro hdir
        refine Classical.byContradiction fun hlt => ?_
        have hlt' : j ≤ i' - 1 := by omega
        have hsat : (spec.improveBound i').satisfiedB b = true := by
          rw [DomConstraint.satisfiedB_iff]
          simp only [ObjectiveSpec.improveBound, hdir, DomConstraint.SatisfiedBy]
          exact ⟨j, hb3, hlt'⟩
        have : accepts (p0.addConstraint (spec.improveBound i')) b = true := by
          simp only [accepts, CompiledProblem.addConstraint, List.all_append,
            List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨hb2, hsat⟩
        rw [hn] at this
        exact Bool.false_ne_true this
      · intro hdir
        refine Classical.byContradiction fun hlt => ?_
        have hlt' : i' + 1 ≤ j := by omega
        have hsat : (spec.improveBound i').satisfiedB b = true := by
          rw [DomConstraint.satisfiedB_iff]
          simp only [ObjectiveSpec.improveBound, hdir, DomConstraint.SatisfiedBy]
          exact ⟨j, hb3, hlt'⟩
        have : accepts (p0.addConstraint (spec.improveBound i')) b = true := by
          simp only [accepts, CompiledProblem.addConstraint, List.all_append,
            List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨hb2, hsat⟩
        rw [hn] at this
        exact Bool.false_ne_true this
    rcases objectiveOf_cases hobj with ⟨anns', hsolve, hdir⟩ | ⟨anns', hsolve, hdir⟩
    · rw [hsolve] at hi ⊢
      intro other i' j hs hph hi' hj
      have := (key other hs hph i' j (by rw [hsolve]; exact hi') (by rw [hsolve]; exact hj))
      exact (this.1 (hdir ▸ rfl))
    · rw [hsolve] at hi ⊢
      intro other i' j hs hph hi' hj
      have := (key other hs hph i' j (by rw [hsolve]; exact hi') (by rw [hsolve]; exact hj))
      exact (this.2 (hdir ▸ rfl))

/-- **Optimality from a checked source store (PLAN F6 T1).**  The second half
of `compileOpt_optimal` with the accepted compiled assignment replaced by the
checker's source store: if the store attains the objective value `v` and no
accepted compiled assignment satisfies the strict improving bound `v`, then
the store is a source-level optimal solution. -/
theorem compileOpt_optimal_of_bound {m : Model} {p : CompiledProblem DomConstraint}
    {spec : ObjectiveSpec} (hc : compileModelOpt m = .ok (p, spec))
    (hwf : WellFormed fullSig m) {store : Store}
    (hsat : Satisfies fullSig fullInterp m store)
    (hpar : LeanFzn.Semantics.ParamHonest m store) {v : Int}
    (hobj : m.solve.objective store = some v)
    (hnone : ∀ b ∈ allAssigns p.domains,
      accepts (p.addConstraint (spec.improveBound v)) b = false) :
    IsSolution fullSig fullInterp m store := by
  obtain ⟨p0, hp0, rfl, hobjOf, hok, hslot⟩ := compileOpt_inv hc
  obtain ⟨ty, anns, hd, hty⟩ := objVarOkB_decl hok
  have hwf' := wf_satisfyPart hwf
  -- any competing store is covered by an accepted assignment reading its
  -- objective at the slot
  have hbound : ∀ other : Store, Satisfies fullSig fullInterp m other →
      LeanFzn.Semantics.ParamHonest m other → ∀ j,
      m.solve.objective other = some j →
      ∃ b ∈ allAssigns p0.domains, accepts p0 b = true ∧
        b[spec.slot]? = some (.int j) := by
    intro other hs hph j hj
    obtain ⟨b, hb1, hb2, hb3⟩ := compileOpt_covers hc hwf hs.2 hph
    refine ⟨b, hb1, hb2, ?_⟩
    have hx : p0.toStore b spec.var = other spec.var := hb3
    rw [optToStore_slot hp0 hwf' (m := satisfyPart m) hd hslot b] at hx
    rw [objective_of_ident hobjOf] at hj
    cases hr : other spec.var with
    | none => rw [hr] at hj; simp at hj
    | some w =>
        rw [hr] at hj hx
        cases w with
        | int k => simp at hj; rw [hj] at hx; exact hx
        | _ => simp at hj
  refine ⟨hsat, hpar, ?_, ?_⟩
  · unfold ObjectiveAttained
    split
    · trivial
    · exact ⟨v, hobj⟩
    · exact ⟨v, hobj⟩
  · unfold IsOptimal
    have key : ∀ other : Store, Satisfies fullSig fullInterp m other →
        LeanFzn.Semantics.ParamHonest m other → ∀ i' j,
        m.solve.objective store = some i' →
        m.solve.objective other = some j →
        (spec.dir = .minimize → i' ≤ j) ∧ (spec.dir = .maximize → j ≤ i') := by
      intro other hs hph i' j hi' hj
      have hi'v : i' = v := by rw [hobj] at hi'; exact (Option.some.inj hi').symm
      rw [hi'v]
      obtain ⟨b, hb1, hb2, hb3⟩ := hbound other hs hph j hj
      have hn : accepts (p0.addConstraint (spec.improveBound v)) b = false :=
        hnone b hb1
      constructor
      · intro hdir
        refine Classical.byContradiction fun hlt => ?_
        have hlt' : j ≤ v - 1 := by omega
        have hsat : (spec.improveBound v).satisfiedB b = true := by
          rw [DomConstraint.satisfiedB_iff]
          simp only [ObjectiveSpec.improveBound, hdir, DomConstraint.SatisfiedBy]
          exact ⟨j, hb3, hlt'⟩
        have : accepts (p0.addConstraint (spec.improveBound v)) b = true := by
          simp only [accepts, CompiledProblem.addConstraint, List.all_append,
            List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨hb2, hsat⟩
        rw [hn] at this
        exact Bool.false_ne_true this
      · intro hdir
        refine Classical.byContradiction fun hlt => ?_
        have hlt' : v + 1 ≤ j := by omega
        have hsat : (spec.improveBound v).satisfiedB b = true := by
          rw [DomConstraint.satisfiedB_iff]
          simp only [ObjectiveSpec.improveBound, hdir, DomConstraint.SatisfiedBy]
          exact ⟨j, hb3, hlt'⟩
        have : accepts (p0.addConstraint (spec.improveBound v)) b = true := by
          simp only [accepts, CompiledProblem.addConstraint, List.all_append,
            List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true]
          exact ⟨hb2, hsat⟩
        rw [hn] at this
        exact Bool.false_ne_true this
    rcases objectiveOf_cases hobjOf with ⟨anns', hsolve, hdir⟩ | ⟨anns', hsolve, hdir⟩
    · rw [hsolve] at hobj ⊢
      intro other i' j hs hph hi' hj
      have := (key other hs hph i' j (by rw [hsolve]; exact hi')
        (by rw [hsolve]; exact hj))
      exact (this.1 (hdir ▸ rfl))
    · rw [hsolve] at hobj ⊢
      intro other i' j hs hph hi' hj
      have := (key other hs hph i' j (by rw [hsolve]; exact hi')
        (by rw [hsolve]; exact hj))
      exact (this.2 (hdir ▸ rfl))

end LeanFzn.Compiler
