
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
    {n : String}
    (hn : n = "int_eq" ∨ n = "int_ne" ∨ n = "int_le" ∨ n = "int_lt" ∨
      n = "int_ge" ∨ n = "int_gt" ∨ n = "int_plus")
    (x : Ident) (i : Nat)
    (hxarg : Expr.basic (.ident x) ∈ c.args)
    (hxi : nameIndex (slots.map Prod.fst) x.name = some i) :
    ∃ p, a[i]! = Value.int p := by
  rcases hn with h | h | h | h | h | h | h
  all_goals
    rw [show c.name.name = n from h] at hxarg ⊢
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inl rfl) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inl rfl)) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inl rfl))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inr (Or.inl rfl)))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_binary hwf hslot hc hpred
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))) hmem x i hxarg hxi
  · exact int_reads_of_mem_int_plus hwf hslot hc hpred rfl hmem x i hxarg hxi

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
  -- the int-reads premise: the extracted constraint's name selects
  -- the dispatch; a name outside the dispatching set never has
  -- identifier slot arguments in its extracted shape (all_different
  -- and int_lin_* take array arguments; bool_*/times/min/max/abs
  -- force their reads through hsat)
  have hreads : ∀ (x : Ident) (i : Nat),
      Expr.basic (.ident x) ∈ c.args →
      nameIndex (slots.map Prod.fst) x.name = some i →
      ∃ p, a[i]! = Value.int p := by
    intro x i hxarg hxi
    -- extract the constraint's name shape
    obtain ⟨x', y', i', j', hname, hargs, _, _⟩ |
      ⟨x', k', i', hname, hargs, _⟩ |
      ⟨k', y', i', hname, hargs, _⟩ |
      ⟨x', y', i'', j'', hname, hargs, _, _⟩ |
      ⟨x', k'', i'', hname, hargs, _⟩ |
      ⟨k'', y', i'', hname, hargs, _⟩ |
      ⟨x', y', z', i', j', k', hname, hargs, _, _, _⟩ |
      ⟨elems, is, hname, hargs, _, _⟩ |
      ⟨ks, elems, coeffs, is, b, hname, hargs, _, _, _, _⟩ |
      ⟨ks, elems, coeffs, is, b, hname, hargs, _, _, _, _⟩ |
      ⟨x', y', z', i', j', k', hname, hargs, _, _, _⟩ |
      ⟨x', y', z', i', j', k', hname, hargs, _, _, _⟩ |
      ⟨x', y', z', i', j', k', hname, hargs, _, _, _⟩ |
      ⟨x', y', i', k', hname, hargs, _, _⟩ |
      ⟨x', y', i', j', hname, hargs, _, _⟩ |
      ⟨x', k', i', hname, hargs, _⟩ |
      ⟨k', y', i', hname, hargs, _⟩ |
      ⟨x', y', i', j', hname, hargs, _, _⟩ |
      ⟨x', y', z', i', j', k', hname, hargs, _, _, _⟩ |
      ⟨x', y', z', i', j', k', hname, hargs, _, _, _⟩ :=
      extractConstraint_inv hex
    all_goals
      first
      | exact int_reads_of_extracted hwf hslot hc hpred hmem
          (Or.inl hname) x i hxarg hxi
      | exact int_reads_of_extracted hwf hslot hc hpred hmem
          (Or.inr (Or.inl hname)) x i hxarg hxi
      | exact int_reads_of_extracted hwf hslot hc hpred hmem
          (Or.inr (Or.inr (Or.inl hname))) x i hxarg hxi
      | exact int_reads_of_extracted hwf hslot hc hpred hmem
          (Or.inr (Or.inr (Or.inr (Or.inl hname)))) x i hxarg hxi
      | exact int_reads_of_extracted hwf hslot hc hpred hmem
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hname))))) x i hxarg hxi
      | exact int_reads_of_extracted hwf hslot hc hpred hmem
          (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hname))))))
          x i hxarg hxi
      | exact int_reads_of_mem_int_plus hwf hslot hc hpred hname hmem
          x i hxarg hxi
      | (exfalso; rw [hargs] at hxarg; cases hxarg)
  exact extractConstraint_holds_converse hnu halt hex hreads hsat
