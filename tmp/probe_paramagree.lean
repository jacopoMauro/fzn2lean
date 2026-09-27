import solver.Direct.Proofs.Exact
open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.Direct

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
  have hnu : ((m.parameters.filterMap
      (fun d2 => parDeclValue d2 |>.map (fun v2 => (ParDeclItem.name d2, v2)))).map
    Prod.fst).Nodup := by
    -- the parameter names are distinct (WellFormed's value-namespace
    -- uniqueness restricts to parameters)
    have hfull : (m.parameters.map ParDeclItem.name ++ m.variables.map
        VarDeclItem.name).Nodup := hwf.valueNamesUnique
    -- the tail of a nodup append is nodup (mirror of slotNames_nodup)
    have hparnames : (m.parameters.map ParDeclItem.name).Nodup := by
      have hsplit : (m.parameters.map ParDeclItem.name ++
          m.variables.map VarDeclItem.name).Nodup := hfull
      -- the head of a nodup append is nodup: core lemma
      exact (List.Nodup.append hsplit).1
    -- the filterMap's names are a sublist of the parameter names
    induction m.parameters with
    | nil => simp
    | cons d2 rest ih =>
        simp only [List.filterMap_cons, List.map_cons, List.nodup_cons] at *
        obtain ⟨h1, h2⟩ := ‹(m.parameters.map ParDeclItem.name).Nodup›
        sorry
  have hpar : parEnv m (ParDeclItem.name d) = some v := parEnv_of_decl hd hv hnu
  rw [hpar]
  exact hstore
