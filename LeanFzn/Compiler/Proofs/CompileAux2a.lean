/-
File: LeanFzn/Compiler/Proofs/CompileAux2a.lean

Purpose:
  The auxiliary-slot expansion layer, part 2a: the per-shape semantic
  bridges (SAT and coverage), the extended read chains, and the first
  argument inversions (times/ne shapes). Split from CompileAux2 (P1c)
  to bound elaboration memory; the statements are unchanged.

DAG:
  CompileCore -> CompileAux1 -> CompileAux2a -> CompileAux2b
    -> CompileAux2c -> Compile (shell)
-/

import LeanFzn.Compiler.Proofs.CompileAux1
open LeanFzn.Compiler.Domains


namespace LeanFzn.Compiler
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics.Globals LeanFzn.Solver LeanFzn.Solver.Core
/-! ### The per-shape semantic bridges (SAT and coverage) -/

/-- The assembled store reads the aux slot at the extended position
    (the generic read bridge, position-indexed). -/
theorem toStore_read_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {dcs : List DomConstraint}
    {a : List Value} {x : Ident} {i : Nat}
    (hnu : ((slots0 ++ auxs).map Prod.fst).Nodup)
    (halt : a.length = (slots0 ++ auxs).length)
    (hx : nameIndex ((slots0 ++ auxs).map Prod.fst) x.name = some i) :
    (assemble m (slots0 ++ auxs) dcs).toStore a x = some a[i]! := by
  exact toStore_read (m := m) (slots := slots0 ++ auxs) (dcs := dcs)
    hnu hx halt

/-- The expansion keeps every passthrough constraint (not a pinning
    shape) in the expanded list. -/
theorem expandPlan_keep {taken : List String} :
    ∀ (cs : List ConstraintItem) (auxs auxs' : List (String × List Value))
      (cs' : List ConstraintItem),
      expandPlan taken auxs cs = (auxs', cs') →
      ∀ c ∈ cs, auxShapeOf c = none → c ∈ cs' := by
  intro cs
  induction cs with
  | nil =>
      intro auxs auxs' cs' h c hc _
      cases hc
  | cons head rest ih =>
      intro auxs auxs' cs' h c hc hshape
      rw [expandPlan] at h
      split at h
      · -- the head passes through (hshapeNone : auxShapeOf head = none)
        rename_i hshapeNone
        cases hrec : expandPlan taken auxs rest with
        | mk auxs2 cs2 =>
            rw [hrec] at h
            simp only at h
            obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ head :: cs2 = cs' :=
              Prod.mk.injEq _ _ _ _ ▸ h
            subst h1 h2
            rcases List.mem_cons.mp hc with rfl | htl
            · rw [hshape] at hshapeNone
              cases hshapeNone
              exact List.mem_cons_self
            · exact List.mem_cons_of_mem _ (ih auxs auxs2 cs2 hrec c htl hshape)
      · -- the head is a pinning shape: the member must be in the tail
        -- (the head is not a passthrough)
        rcases List.mem_cons.mp hc with hhead | htl
        · -- c = head, but the head is a pinning shape: contradiction
          exfalso
          rw [hhead] at hshape
          rename_i sh hshape2
          rw [hshape] at hshape2
          exact absurd hshape2 (by simp)
        · -- the tail's passthroughs survive inside the pieces' append
          -- The head is a pinning shape; split on its pins to find the
          -- accumulator the tail's recursion used.
          split at h
          · -- TWO aux slots
            rename_i v v2 hpin hpin2
            cases hrec2 : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v]),
                   ((auxName taken auxs.length).push '$', [v2])]) rest with
            | mk auxs2 cs2 =>
                simp only [hrec2] at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' := by
                  simpa using h
                subst h1 h2
                exact List.mem_append.mpr (Or.inr
                  (ih (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2
                    hrec2 c htl hshape))
          · -- ONE aux slot
            -- the arm's binders: the VALUE first (the match binder),
            -- then the two equations
            rename_i v hpin hneq2
            cases hrec2 : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v])]) rest with
            | mk auxs2 cs2 =>
                simp only [hrec2] at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' := by
                  simpa using h
                subst h1 h2
                exact List.mem_append.mpr (Or.inr
                  (ih (auxs ++ [(auxName taken auxs.length, [v])]) auxs2 cs2
                    hrec2 c htl hshape))
          · -- no aux slot
            rename_i hpin
            cases hrec2 : expandPlan taken auxs rest with
            | mk auxs2 cs2 =>
                rw [hrec2] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                exact List.mem_append.mpr (Or.inr
                  (ih auxs auxs2 cs2 hrec2 c htl hshape))


/-- The extended candidate space's domain at a model position is the
    model slot's own domain (the append's first half). -/
theorem getD_map_snd_append_first {slots0 auxs : List (String × List Value)}
    {i : Nat} (hilt : i < slots0.length) :
    ((slots0 ++ auxs).map Prod.snd).getD i [] = slots0[i].snd := by
  have hmap : (slots0 ++ auxs).map Prod.snd
      = slots0.map Prod.snd ++ auxs.map Prod.snd := List.map_append
  rw [hmap]
  have main : ∀ (l1 l2 : List (List Value)) (i : Nat),
      i < l1.length → (l1 ++ l2).getD i [] = l1.getD i [] := by
    intro l1
    induction l1 with
    | nil => intro _ i hilt; exact absurd hilt (by simp)
    | cons p rest ih =>
        intro l2 i hilt
        cases i with
        | zero => rfl
        | succ i2 =>
            show (p :: (rest ++ l2)).getD (i2 + 1) []
              = (p :: rest).getD (i2 + 1) []
            rw [List.getD_cons_succ, List.getD_cons_succ, ih l2 i2 (by simp at hilt; omega)]
  rw [main (slots0.map Prod.snd) (auxs.map Prod.snd) i
    (by rw [List.length_map]; omega)]
  rw [show (slots0.map Prod.snd).getD i [] = slots0[i].snd from
    getD_map_snd hilt]

/-- The model-slot positions of an extended slot list agree with the
    model slots (the prefix). -/
theorem extendedSlots_prefix {slots0 auxs : List (String × List Value)}
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd))
    (i : Nat) (hilt : i < slots0.length) :
    ∃ v, a[i]? = some v ∧ v ∈ slots0[i].snd := by
  have hlen : a.length = (slots0 ++ auxs).length := by
    have h1 := mem_allAssigns_length ((slots0 ++ auxs).map Prod.snd) a hmem
    rw [List.length_map] at h1
    exact h1
  have hsome : a[i]? = some a[i]! := getElem_as_some (by
    rw [hlen, List.length_append]
    omega)
  have hfits := mem_allAssigns_fits ((slots0 ++ auxs).map Prod.snd) a hmem i
    a[i]! hsome
  rw [getD_map_snd_append_first hilt] at hfits
  exact ⟨a[i]!, hsome, hfits⟩

/-! ### The extended read chains (the aux-slot linker's premises) -/

/-- The int-reads premise over an EXTENDED candidate space: a
    slot-position read of an assignment in the extended space is an
    integer whenever the constraint's argument checks against the
    int-typed signature (the domain membership comes from the model
    prefix). -/
theorem int_read_of_checkArg_slot_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType}
    {x : Ident} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hcheck :
      (Expr.basic (.ident x)).checkArg m.staticEnv (.basic (.var (.par .int))))
    (hxi : nameIndex (slots0.map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd)) :
    ∃ p, a[i]! = Value.int p := by
  -- the slot is in bounds
  obtain ⟨hxlt, hxget⟩ :=
    nameIndex_some (slots0.map Prod.fst) x.name i hxi
  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
  have hislt : i < slots0.length := by omega
  -- the check supplies the int base type for x
  obtain ⟨isVar, henv⟩ := staticEnv_int_of_checkArg hcheck
  -- the slot's variable, with its staticEnv resolution
  obtain ⟨d, hd, hdslot, hstatic⟩ := staticEnv_of_slot hwf hslot hislt
  -- the checked identifier IS the slot's name
  have hnameilt : i < (slots0.map Prod.fst).length := by
    rw [List.length_map]
    omega
  have hnamei : (slots0.map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt hxget
  have hxslot : slots0[i]!.1 = x.name := by
    rw [show slots0[i]!.1 = (slots0.map Prod.fst)[i]! from
      (getElem!_map_fst i).symm]
    exact hnamei
  have hstaticx : m.staticEnv x = some (d.type, true) := by
    have hxmk : x = Ident.mk slots0[i]!.1 := by
      obtain ⟨sn⟩ := x
      apply ident_eq_of_name
      rw [hxslot]
    rw [hxmk]
    exact hstatic
  -- both resolutions describe the same staticEnv value: the type is int
  obtain ⟨ty, n, anns, hdshape⟩ : ∃ ty n anns,
      d = .basic ty n anns none := by
    match hs : declSlot d with
    | .error e => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok none => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok (some p) =>
        cases d with
        | basic ty n anns opt2 =>
            cases opt2 with
            | none => exact ⟨ty, n, anns, rfl⟩
            | some e => rw [hs] at *; exact absurd hdslot (by simp [declSlot])
        | array ty n anns vs =>
            rw [hs] at *; exact absurd hdslot (by simp [declSlot])
  subst hdshape
  -- combine the two staticEnv values: the variable's type is base int
  have htyint : ty.base = BaseType.int := by
    have hboth : some (FznType.base ty.base, true)
        = some (FznType.base BaseType.int, isVar) :=
      hstaticx.symm.trans henv
    have h1 : (FznType.base ty.base, true)
        = (FznType.base BaseType.int, isVar) := Option.some.inj hboth
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, _⟩ := h1
    injection h2
  -- the slot's domain is an intDom
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  obtain ⟨xs, hxs⟩ := varDomain_int_of_base hdom htyint
  -- the assignment's read is in the slot's values — all int (the
  -- EXTENDED candidate space's model-prefix membership)
  have hmemv : a[i]! ∈ slots0[i].snd := by
    obtain ⟨v, hsv, hvdom⟩ :=
      extendedSlots_prefix (slots0 := slots0) (auxs := auxs) hmem i hislt
    have hib : a[i]! = v := bang_of_getElem? hsv
    rw [hib]
    exact hvdom
  -- the slot pair is (n.name, dom.values)
  have hpairplain : slots0[i] = (n.name, dom.values) := by
    have hslotpair : slots0[i]! = (n.name, dom.values) := by rw [← hpair]
    have hplain : slots0[i]! = slots0[i] := getElem!_eq_getElem hislt
    rw [← hplain]
    exact hslotpair
  rw [hpairplain] at hmemv
  rw [hxs] at hmemv
  obtain ⟨p, hp⟩ := intDom_values_int a[i]! hmemv
  exact ⟨p, hp⟩

/-- The bool-reads twin of `int_read_of_checkArg_slot_ext`. -/
theorem bool_read_of_checkArg_slot_ext {m : Model}
    {slots0 auxs : List (String × List Value)} {a : List Value}
    {c : ConstraintItem} {params : List PredParamType}
    {x : Ident} {i : Nat}
    (hwf : WellFormed fullSig m)
    (hslot : slotsChecked m = .ok slots0)
    (hchecked : Forall2 (Expr.checkArg m.staticEnv) c.args params)
    (hcheck :
      (Expr.basic (.ident x)).checkArg m.staticEnv (.basic (.var (.par .bool))))
    (hxi : nameIndex (slots0.map Prod.fst) x.name = some i)
    (hmem : a ∈ allAssigns ((slots0 ++ auxs).map Prod.snd)) :
    ∃ p, a[i]! = Value.bool p := by
  obtain ⟨hxlt, hxget⟩ :=
    nameIndex_some (slots0.map Prod.fst) x.name i hxi
  have hlen : (slots0.map Prod.fst).length = slots0.length := by simp
  have hislt : i < slots0.length := by omega
  obtain ⟨isVar, henv⟩ := staticEnv_bool_of_checkArg hcheck
  obtain ⟨d, hd, hdslot, hstatic⟩ := staticEnv_of_slot hwf hslot hislt
  have hnameilt : i < (slots0.map Prod.fst).length := by
    rw [List.length_map]
    omega
  have hnamei : (slots0.map Prod.fst)[i]! = x.name :=
    getElem_of_getElem? hnameilt hxget
  have hxslot : slots0[i]!.1 = x.name := by
    rw [show slots0[i]!.1 = (slots0.map Prod.fst)[i]! from
      (getElem!_map_fst i).symm]
    exact hnamei
  have hstaticx : m.staticEnv x = some (d.type, true) := by
    have hxmk : x = Ident.mk slots0[i]!.1 := by
      obtain ⟨sn⟩ := x
      apply ident_eq_of_name
      rw [hxslot]
    rw [hxmk]
    exact hstatic
  obtain ⟨ty, n, anns, hdshape⟩ : ∃ ty n anns,
      d = .basic ty n anns none := by
    match hs : declSlot d with
    | .error e => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok none => rw [hs] at hdslot; exact absurd hdslot (by simp)
    | .ok (some p) =>
        cases d with
        | basic ty n anns opt2 =>
            cases opt2 with
            | none => exact ⟨ty, n, anns, rfl⟩
            | some e => rw [hs] at *; exact absurd hdslot (by simp [declSlot])
        | array ty n anns vs =>
            rw [hs] at *; exact absurd hdslot (by simp [declSlot])
  subst hdshape
  have htybool : ty.base = BaseType.bool := by
    have hboth : some (FznType.base ty.base, true)
        = some (FznType.base BaseType.bool, isVar) :=
      hstaticx.symm.trans henv
    have h1 : (FznType.base ty.base, true)
        = (FznType.base BaseType.bool, isVar) := Option.some.inj hboth
    simp only [Prod.mk.injEq] at h1
    obtain ⟨h2, _⟩ := h1
    injection h2
  obtain ⟨dom, hdom, hpair⟩ := declSlot_basic_inv hdslot
  have hbooldom : dom = .boolDom := varDomain_bool_of_base hdom htybool
  have hmemv : a[i]! ∈ slots0[i].snd := by
    obtain ⟨v, hsv, hvdom⟩ :=
      extendedSlots_prefix (slots0 := slots0) (auxs := auxs) hmem i hislt
    have hib : a[i]! = v := bang_of_getElem? hsv
    rw [hib]
    exact hvdom
  have hpairplain : slots0[i] = (n.name, dom.values) := by
    have hslotpair : slots0[i]! = (n.name, dom.values) := by rw [← hpair]
    have hplain : slots0[i]! = slots0[i] := getElem!_eq_getElem hislt
    rw [← hplain]
    exact hslotpair
  rw [hpairplain] at hmemv
  rw [hbooldom] at hmemv
  have hmemv' : a[i]! ∈ VarDomain.boolDom.values := hmemv
  obtain ⟨p, hp⟩ := boolDom_values_bool hmemv'
  exact ⟨p, hp⟩




/-- The timesRK shape's argument inversion: the classified
    constraint's arguments are the two identifiers and the int literal. -/
theorem auxShapeOf_timesRK_args {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesRK x y k)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.int k))] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next x2 k2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))



/-- The timesKR shape's argument inversion. -/
theorem auxShapeOf_timesKR_args {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR x y k)) :
    c.args = [.basic (.ident x), .basic (.lit (.int k)), .basic (.ident y)] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 y2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next k2 x2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))

/-- The timesKR' shape's argument inversion. -/
theorem auxShapeOf_timesKR'_args {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR' x y k)) :
    c.args = [.basic (.lit (.int k)), .basic (.ident x), .basic (.ident y)] := by
  rw [auxShapeOf] at h
  split at h
  next heq1 =>
    split at h
    next x2 y2 k2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next x2 k2 y2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 y2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 k'2 x2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next heq2 =>
      exact absurd h (by simp)
  next heq1 =>
    -- int_ne
    repeat' (first | (split at h) | (skip))
    all_goals
      first
        | exact absurd h (by simp)
        | (exfalso; injection h with h1; cases h1)
        | (exfalso; cases h)
  -- bool_and / bool_or / other names
  all_goals
    first
      | exact absurd h (by simp)
      | (exfalso
         split at h
         all_goals
           first
             | exact absurd h (by simp)
             | (exfalso; injection h with h1; cases h1)
             | (exfalso; cases h))
end LeanFzn.Compiler
