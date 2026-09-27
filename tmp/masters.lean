
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
