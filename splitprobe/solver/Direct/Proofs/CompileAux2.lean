/-
File: solver/Direct/Proofs/Compile.lean

Purpose:
  The exact semantic-correspondence theorems for the certified
  FlatZinc fragment compiler (`solver/Direct/Compile.lean`).

Dependencies:
  - solver.Direct.Compile: the executable compiler.
DAG:
  solver.Direct.Compile -> solver.Direct.Proofs.Compile
     -> solver.Direct.Correctness
-/

import solver.Core
import solver.Direct.Compile
import solver.Direct.Proofs.CompileCore
import solver.Direct.Proofs.CompileAux1

namespace LeanFzn.Solver.Direct

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
                rw [hrec2] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
                subst h1 h2
                exact List.mem_append.mpr (Or.inr
                  (ih (auxs ++ [(auxName taken auxs.length, [v]),
                     ((auxName taken auxs.length).push '$', [v2])]) auxs2 cs2
                    hrec2 c htl hshape))
          · -- ONE aux slot
            rename_i v hpin
            cases hrec2 : expandPlan taken
                (auxs ++ [(auxName taken auxs.length, [v])]) rest with
            | mk auxs2 cs2 =>
                rw [hrec2] at h
                simp only at h
                obtain ⟨h1, h2⟩ : auxs2 = auxs' ∧ _ = cs' :=
                  Prod.mk.injEq _ _ _ _ ▸ h
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

/-- The timesRKK shape's argument inversion. -/
theorem auxShapeOf_timesRKK_args {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesRKK x k k')) :
    c.args = [.basic (.ident x), .basic (.lit (.int k)), .basic (.lit (.int k'))] := by
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
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
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

/-- The timesKRR shape's argument inversion. -/
theorem auxShapeOf_timesKRR_args {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKRR x k k')) :
    c.args = [.basic (.lit (.int k)), .basic (.ident x), .basic (.lit (.int k'))] := by
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
      exfalso
      injection h with h1
      cases h1
    next x2 k2 k'2 heq2 =>
      exfalso
      injection h with h1
      cases h1
    next k2 x2 k'2 heq2 =>
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
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

/-- The timesKKR shape's argument inversion. -/
theorem auxShapeOf_timesKKR_args {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKKR x k k')) :
    c.args = [.basic (.lit (.int k)), .basic (.lit (.int k')), .basic (.ident x)] := by
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
      injection h with h1
      injection h1 with h3 h4 h5
      subst h3 h4 h5
      exact heq2
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


/-- The neRK shape's argument inversion. -/
theorem auxShapeOf_neRK_inv {c : ConstraintItem} {x : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.neRK x k)) :
    c.name.name = "int_ne" ∧ c.args = [.basic (.ident x), .basic (.lit (.int k))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: the two arms
    split at h
    · -- neRK arm
      next x2 k2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact ⟨heq1, heq2⟩
    · -- neKR arm
      next k2 x2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- no pattern
      exact absurd h (by simp)
  -- bool_and / bool_or / other names: 3-arg arms clash with the
  -- 2-arg ne shapes
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

/-- The neKR shape's argument inversion. -/
theorem auxShapeOf_neKR_inv {c : ConstraintItem} {x : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.neKR x k)) :
    c.name.name = "int_ne" ∧ c.args = [.basic (.lit (.int k)), .basic (.ident x)] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: the two arms
    split at h
    · -- neRK arm: the clash
      next x2 k2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- neKR arm: the match
      next k2 x2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact ⟨heq1, heq2⟩
    · -- no pattern
      exact absurd h (by simp)
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



/-- The andTrue shape's argument inversion. -/
theorem auxShapeOf_andTrue_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andTrue x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool true))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: the two arms
    split at h
    · -- true arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- false arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- no pattern
      exact absurd h (by simp)
  next heq1 =>
    -- bool_or: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)

/-- The andFalse shape's argument inversion. -/
theorem auxShapeOf_andFalse_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andFalse x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool false))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: the two arms
    split at h
    · -- true arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- false arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- no pattern
      exact absurd h (by simp)
  next heq1 =>
    -- bool_or: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)

/-- The orTrue shape's argument inversion. -/
theorem auxShapeOf_orTrue_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orTrue x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool true))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_or: the two arms
    split at h
    · -- true arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- false arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- no pattern
      exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)

/-- The orFalse shape's argument inversion. -/
theorem auxShapeOf_orFalse_args {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orFalse x y)) :
    c.args = [.basic (.ident x), .basic (.ident y), .basic (.lit (.bool false))] := by
  rw [auxShapeOf] at h
  split at h
  · -- int_times: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- int_ne: 2-arg clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_and: clash
    exfalso
    split at h <;> exact absurd h (by simp)
  next heq1 =>
    -- bool_or: the two arms
    split at h
    · -- true arm
      next x2 y2 heq2 =>
        exfalso
        injection h with h1
        cases h1
    · -- false arm: THE match
      next x2 y2 heq2 =>
        injection h with h1
        injection h1 with h3 h4
        subst h3 h4
        exact heq2
    · -- no pattern
      exact absurd h (by simp)
  · -- other names
    exact absurd h (by simp)


/-- The timesRK shape's name inversion: the classification's int_times
    branch fired, so the constraint's name is `int_times`. -/
theorem auxShapeOf_timesRK_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesRK x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.int k))] := auxShapeOf_timesRK_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKR shape's name inversion. -/
theorem auxShapeOf_timesKR_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
    .basic (.ident y)] := auxShapeOf_timesKR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKR' shape's name inversion. -/
theorem auxShapeOf_timesKR'_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR' x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
    .basic (.ident y)] := auxShapeOf_timesKR'_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesRKK shape's name inversion. -/
theorem auxShapeOf_timesRKK_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesRKK x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
    .basic (.lit (.int k'))] := auxShapeOf_timesRKK_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKRR shape's name inversion. -/
theorem auxShapeOf_timesKRR_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKRR x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
    .basic (.lit (.int k'))] := auxShapeOf_timesKRR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The timesKKR shape's name inversion. -/
theorem auxShapeOf_timesKKR_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKKR x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.lit (.int k')),
    .basic (.ident x)] := auxShapeOf_timesKKR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The andTrue shape's name inversion. -/
theorem auxShapeOf_andTrue_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andTrue x y)) :
    c.name.name = "bool_and" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool true))] := auxShapeOf_andTrue_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The andFalse shape's name inversion. -/
theorem auxShapeOf_andFalse_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andFalse x y)) :
    c.name.name = "bool_and" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool false))] := auxShapeOf_andFalse_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The orTrue shape's name inversion. -/
theorem auxShapeOf_orTrue_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orTrue x y)) :
    c.name.name = "bool_or" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool true))] := auxShapeOf_orTrue_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)

/-- The orFalse shape's name inversion. -/
theorem auxShapeOf_orFalse_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orFalse x y)) :
    c.name.name = "bool_or" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool false))] := auxShapeOf_orFalse_args h
  rw [auxShapeOf, hargs] at h
  split at h
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · exact absurd h (by simp)
  · next heq1 => exact heq1
  · exact absurd h (by simp)


/-- The successful compile of a 3-identifier `int_times` piece gives
    the slot resolutions and the timesSlot form (the extraction arm's
    inversion: a failed resolution would have made the compile fail). -/
theorem compileConstraint_int_times3_inv {env : Store} {names : List String}
    {x y z : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "int_times"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    ∃ i j k, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      dc = .timesSlot i j k := by
  -- the extraction's result IS the compiled dc (the compile's first arm)
  unfold compileConstraint at hcc
  split at hcc
  · -- the extraction arm: the result IS the extraction's value
    rename_i dc' hext
    -- hext : extractConstraint ... = some dc'; hcc : .ok dc' = .ok dc
    have hcdc : dc' = dc := (Except.ok.inj hcc)
    -- the extraction's inversion: the int_times 3-identifier arm is
    -- the only one matching this piece's shape
    rcases extractConstraint_inv hext with
      -- int_eq 2-identifier: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_eq ident-literal: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_eq literal-ident: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_ne: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_le 2-identifier: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_le ident-literal: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_le literal-ident: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_plus: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- all_different: name mismatch
      ⟨-, -, hname, -, -, -⟩ |
      -- int_lin_eq: name mismatch
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_lin_le: name mismatch
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_times: THE arm
      ⟨x', y', z', i, j, k, hname, hargs, hi, hj, hk, h'⟩ |
      -- int_min: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_max: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- int_abs: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_lt 2-identifier: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- int_lt ident-literal: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- int_lt literal-ident: name mismatch
      ⟨-, -, -, hname, -, -, -⟩ |
      -- bool_not: name mismatch
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      -- bool_and: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      -- bool_or: name mismatch
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩
    all_goals
      first
        | (simp only [Ident.mk] at hname; exact absurd hname (by decide))
        | (
          -- the int_times arm: resolve the identifiers from the args
          injection hargs with hx' hrest
          injection hrest with hy' hz'
          injection hx' with hxb
          injection hy' with hyb
          injection hz' with hzb
          injection hxb with hx
          injection hyb with hy
          injection hzb with hzi
          injection hzi with hz
          subst hx
          subst hy
          subst hz
          exact ⟨i, j, k, hi, hj, hk, hcdc.symm.trans h'⟩)
  · -- the fallback arm: int_times is not among the fallback names
    -- (the gates all fail) — the compile errors, contradicting hcc
    exact absurd hcc (by intro hc; cases hc)

/-- An aux slot's name resolves at its extended position (fresh in the
    model prefix, positioned in the aux suffix). -/
theorem nameIndex_aux_slot {slots0 auxs : List (String × List Value)}
    {taken : List String} {i : Nat} {vs : List Value}
    (hsub : ∀ s ∈ slots0.map Prod.fst, s ∈ taken)
    (hspec : ∀ j p, auxs[j]? = some p → p.1 = auxName taken j)
    (hslot : auxs[i]? = some (auxName taken i, vs)) :
    nameIndex ((slots0 ++ auxs).map Prod.fst) (auxName taken i)
      = some (slots0.length + i) := by
  -- the name is a member of the extended list
  have hilt : i < auxs.length := (List.getElem?_eq_some_iff.mp hslot).1
  have hpair : auxs[i] = (auxName taken i, vs) := by
    have h1 : auxs[i]? = some auxs[i] := List.getElem?_eq_getElem hilt
    rw [hslot] at h1
    exact (Option.some.inj h1).symm
  have hp : (auxName taken i, vs) ∈ auxs := by
    rw [← hpair]
    exact List.getElem_mem hilt
  have hmem : auxName taken i ∈ (slots0 ++ auxs).map Prod.fst := by
    rw [List.map_append]
    exact List.mem_append.mpr (Or.inr (List.mem_map_of_mem (f := Prod.fst) hp))
  obtain ⟨i3, hi3⟩ := nameIndex_of_mem hmem
  -- the position is IN the aux half (freshness rules out the model half)
  rw [List.map_append] at hi3
  rcases nameIndex_append_inv hi3 with hmodel | ⟨j, hjaux, hjeq⟩
  · exfalso
    have hnotmem : auxName taken i ∉ slots0.map Prod.fst := by
      intro hcon
      exact auxName_not_mem (hsub _ hcon)
    obtain ⟨hlt4, hget4⟩ := nameIndex_some _ _ i3 hmodel
    exact hnotmem (List.mem_of_getElem? (a := auxName taken i)
      (i := i3) (l := slots0.map Prod.fst) (by rw [hget4]))
  · -- the aux-half index j: the name at j is auxName taken j, which
    -- equals auxName taken i only when j = i
    obtain ⟨hjlt, hnamej⟩ := nameIndex_some _ _ j hjaux
    -- auxs[j] is positioned (its name is auxName taken j)
    have hjlt' : j < auxs.length := by
      rw [List.length_map] at hjlt
      exact hjlt
    have hpairj : (auxs.map Prod.fst)[j]? = some (auxName taken j) := by
      have hget : auxs[j]? = some auxs[j] := List.getElem?_eq_getElem hjlt'
      have hname : auxs[j].1 = auxName taken j := hspec j auxs[j] hget
      have hmap : (auxs.map Prod.fst)[j]? = some auxs[j].1 := by
        have h2 : (auxs.map Prod.fst)[j]? = Option.map Prod.fst auxs[j]? :=
          List.getElem?_map
        rw [h2, hget]
        rfl
      rw [hmap, hname]
    rw [hnamej] at hpairj
    -- the names agree, so their positions agree
    have hsame : auxName taken j = auxName taken i :=
      (Option.some.inj hpairj.symm)
    have hji : j = i := auxName_inj hsame
    subst hji
    -- the lengths and shapes line up
    rw [List.length_map] at hjeq
    rw [List.map_append, ← hjeq]
    exact hi3

/-- A successful `compileArgVal` of an identifier through a slot
    position: the name resolved at that position. -/
theorem cav_slotRef {env : Store} {names : List String} {x : Ident} {i : Nat}
    (h : compileArgVal env names (.ident x) = .ok (.slotRef i)) :
    nameIndex names x.name = some i := by
  simp only [compileArgVal] at h
  cases hn : nameIndex names x.name with
  | none =>
      rw [hn] at h
      cases hex : env x with
      | none => rw [hex] at h; cases h
      | some v => rw [hex] at h; cases h
  | some i2 =>
      rw [hn] at h
      have : ArgVal.slotRef i2 = ArgVal.slotRef i := (Except.ok.inj h)
      injection this
      subst i2
      rfl

/-- A successful `compileArgVal` of an identifier to a Boolean
    literal value: the name did NOT resolve as a slot, and the
    parameter environment supplied the Boolean. -/
theorem cav_litVal_bool {env : Store} {names : List String} {x : Ident}
    {b : Bool}
    (h : compileArgVal env names (.ident x) = .ok (.litVal (.bool b))) :
    nameIndex names x.name = none ∧ env x = some (.bool b) := by
  simp only [compileArgVal] at h
  cases hn : nameIndex names x.name with
  | none =>
      rw [hn] at h
      cases hex : env x with
      | none => rw [hex] at h; cases h
      | some v =>
          rw [hex] at h
          have : ArgVal.litVal v = ArgVal.litVal (Value.bool b) :=
            (Except.ok.inj h)
          have h2 : v = Value.bool b := by injection this
          exact ⟨rfl, by rw [← h2]⟩
  | some i2 => rw [hn] at h; cases h

/-- The successful compile of a 2-identifier `int_ne` piece gives the
    slot resolutions and the neSlot form. -/
theorem compileConstraint_int_ne2_inv {env : Store} {names : List String}
    {x y : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "int_ne"
        , args := [.basic (.ident x), .basic (.ident y)]
        , anns := [] } = .ok dc) :
    ∃ i j, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      dc = .neSlot i j := by
  unfold compileConstraint at hcc
  split at hcc
  · rename_i dc' hext
    have hcdc : dc' = dc := (Except.ok.inj hcc)
    rcases extractConstraint_inv hext with
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨x', y', i, j, hname, hargs, hxi, hyi, h'⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, hname, -, -, -⟩ |
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, hname, -, -, -⟩ |
      ⟨-, -, -, -, hname, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩ |
      ⟨-, -, -, -, -, -, hname, -, -, -, -, -⟩
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · -- the int_ne arm: the identifiers resolve from the args
      injection hargs with hx' hrest
      injection hrest with hy'
      injection hx' with hxb
      injection hy' with hyb
      injection hxb with hx
      injection hyb with hy
      subst hx
      subst hy
      refine ⟨i, j, ?_, ?_, ?_⟩
      · rw [← hxi]
      · rw [← hyi]
      · exact hcdc.symm.trans h'
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
    · exact absurd hname (by simp)
  · -- the fallback arm: `int_ne` is not among the fallback gate
    -- names (int_plus/int_le/int_lt/int_gt/int_ge/bool_not/bool_and/
    -- bool_or), so every gate's name test fails by `decide` and the
    -- compile reduces to the unsupported-predicate error —
    -- contradicting hcc
    exact absurd hcc (by intro hc; cases hc)

/-- The successful compile of a 3-identifier `bool_and` piece: either
    the extraction arm (all three names resolve, `boolAndSlot`), or
    the fallback arm — `bool_and`'s gate fires and a parameter-resolved
    operand compiles to `eqSlot`/`constEq` (the parameter case: the
    name does NOT resolve as a slot, and `env` supplies the Boolean).
    The honest five-way disjunction of the possible compiled forms. -/
theorem compileConstraint_bool_and3_inv {env : Store} {names : List String}
    {x y z : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "bool_and"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    (∃ i j k, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      dc = .boolAndSlot i j k) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool true) ∧ dc = .eqSlot i k) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool false) ∧ dc = .constEq k (.bool false)) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool true) ∧ dc = .eqSlot j k) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool false) ∧ dc = .constEq k (.bool false)) := by
  unfold compileConstraint at hcc
  split at hcc
  · -- the extraction arm
    rename_i dc' hres
    cases hx : nameIndex names x.name with
    | some i =>
      cases hy : nameIndex names y.name with
      | some j =>
        cases hz : nameIndex names z.name with
        | some k =>
          refine Or.inl ⟨i, j, k, rfl, rfl, rfl, ?_⟩
          have hred : extractConstraint names
              { name := Ident.mk "bool_and"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = some (.boolAndSlot i j k) := by
            simp only [extractConstraint, hx, hy, hz]
          rw [hred] at hres
          have hcdc : dc' = .boolAndSlot i j k :=
            (Option.some.inj hres).symm
          rw [hcdc] at hcc
          exact (Except.ok.inj hcc).symm
        | none =>
          exfalso
          have hred : extractConstraint names
              { name := Ident.mk "bool_and"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = none := by
            simp only [extractConstraint, hx, hy, hz]
          exact absurd (hred.symm.trans hres) (by simp)
      | none =>
        exfalso
        have hred : extractConstraint names
            { name := Ident.mk "bool_and"
            , args := [.basic (.ident x), .basic (.ident y),
              .basic (.ident z)]
            , anns := [] } = none := by
          simp only [extractConstraint, hx, hy]
        exact absurd (hred.symm.trans hres) (by simp)
    | none =>
      exfalso
      have hred : extractConstraint names
          { name := Ident.mk "bool_and"
          , args := [.basic (.ident x), .basic (.ident y),
            .basic (.ident z)]
          , anns := [] } = none := by
        simp only [extractConstraint, hx]
      exact absurd (hred.symm.trans hres) (by simp)
  · -- the fallback arm: `bool_and`'s gate fires (the name and the
    -- three-element args are concrete); the do-block runs over the
    -- three identifiers' compileArgVals
    rw [if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_plus")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_le")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_lt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_gt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "int_ge")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_and" : String) = "bool_not")
        (by decide)),
      if_pos ⟨rfl, rfl⟩] at hcc
    -- the do-block over the three identifier argOfs (rfl-reduced: the
    -- bang reads of the concrete three-element list are the
    -- identifiers themselves)
    have hcc2 : ((do
        let _a0 ← (Except.ok (.ident x) : Except String BasicExpr)
        let _a1 ← (Except.ok (.ident y) : Except String BasicExpr)
        let _a2 ← (Except.ok (.ident z) : Except String BasicExpr)
        match compileArgVal env names (.ident x),
            compileArgVal env names (.ident y),
            compileArgVal env names (.ident z) with
        | .ok (.slotRef i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.slotRef _i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .ok (.litVal (.bool true)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .ok (.litVal (.bool false)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool false))
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ =>
            .error "unsupported bool_and argument shapes" :
        Except String DomConstraint)) = .ok dc := hcc
    split at hcc2
    · next i k hc0 hc1 hc2 =>
        exact Or.inr (Or.inl ⟨i, k, cav_slotRef hc0, cav_slotRef hc2,
          (cav_litVal_bool hc1).1, (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inl ⟨_, k, cav_slotRef hc0,
          cav_slotRef hc2, (cav_litVal_bool hc1).1,
          (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩))
    · next j k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨j, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨_, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    all_goals exact absurd hcc2 (by intro hc; injection hc)
/-- The successful compile of a 3-identifier `bool_or` piece: the
    honest five-way disjunction of the possible compiled forms (the
    extraction arm's `boolOrSlot` when all three names resolve, or
    `bool_or`'s fallback arm — a parameter-resolved operand compiles
    to `constEq k true`/`eqSlot i k` over the resolved positions). -/
theorem compileConstraint_bool_or3_inv {env : Store} {names : List String}
    {x y z : Ident} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "bool_or"
        , args := [.basic (.ident x), .basic (.ident y), .basic (.ident z)]
        , anns := [] } = .ok dc) :
    (∃ i j k, nameIndex names x.name = some i ∧
      nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      dc = .boolOrSlot i j k) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool true) ∧ dc = .constEq k (.bool true)) ∨
    (∃ i k, nameIndex names x.name = some i ∧
      nameIndex names z.name = some k ∧
      nameIndex names y.name = none ∧
      env y = some (.bool false) ∧ dc = .eqSlot i k) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool true) ∧ dc = .constEq k (.bool true)) ∨
    (∃ j k, nameIndex names y.name = some j ∧
      nameIndex names z.name = some k ∧
      nameIndex names x.name = none ∧
      env x = some (.bool false) ∧ dc = .eqSlot j k) := by
  unfold compileConstraint at hcc
  split at hcc
  · -- the extraction arm
    rename_i dc' hres
    cases hx : nameIndex names x.name with
    | some i =>
      cases hy : nameIndex names y.name with
      | some j =>
        cases hz : nameIndex names z.name with
        | some k =>
          refine Or.inl ⟨i, j, k, rfl, rfl, rfl, ?_⟩
          have hred : extractConstraint names
              { name := Ident.mk "bool_or"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = some (.boolOrSlot i j k) := by
            simp only [extractConstraint, hx, hy, hz]
          rw [hred] at hres
          have hcdc : dc' = .boolOrSlot i j k :=
            (Option.some.inj hres).symm
          rw [hcdc] at hcc
          exact (Except.ok.inj hcc).symm
        | none =>
          exfalso
          have hred : extractConstraint names
              { name := Ident.mk "bool_or"
              , args := [.basic (.ident x), .basic (.ident y),
                .basic (.ident z)]
              , anns := [] } = none := by
            simp only [extractConstraint, hx, hy, hz]
          exact absurd (hred.symm.trans hres) (by simp)
      | none =>
        exfalso
        have hred : extractConstraint names
            { name := Ident.mk "bool_or"
            , args := [.basic (.ident x), .basic (.ident y),
              .basic (.ident z)]
            , anns := [] } = none := by
          simp only [extractConstraint, hx, hy]
        exact absurd (hred.symm.trans hres) (by simp)
    | none =>
      exfalso
      have hred : extractConstraint names
          { name := Ident.mk "bool_or"
          , args := [.basic (.ident x), .basic (.ident y),
            .basic (.ident z)]
          , anns := [] } = none := by
        simp only [extractConstraint, hx]
      exact absurd (hred.symm.trans hres) (by simp)
  · -- the fallback arm: `bool_or`'s gate fires; the do-block runs
    -- over the three identifiers' compileArgVals
    rw [if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_plus")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_le")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_lt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_gt")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "int_ge")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "bool_not")
        (by decide)),
      if_neg (fun hc => absurd (hc.1 : ("bool_or" : String) = "bool_and")
        (by decide)),
      if_pos ⟨rfl, rfl⟩] at hcc
    -- the do-block over the three identifier argOfs (rfl-reduced)
    have hcc2 : ((do
        let _a0 ← (Except.ok (.ident x) : Except String BasicExpr)
        let _a1 ← (Except.ok (.ident y) : Except String BasicExpr)
        let _a2 ← (Except.ok (.ident z) : Except String BasicExpr)
        match compileArgVal env names (.ident x),
            compileArgVal env names (.ident y),
            compileArgVal env names (.ident z) with
        | .ok (.slotRef _i), .ok (.litVal (.bool true)), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.slotRef i), .ok (.litVal (.bool false)), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot i k)
        | .ok (.litVal (.bool true)), .ok (.slotRef _j), .ok (.slotRef k) =>
            .ok (DomConstraint.constEq k (.bool true))
        | .ok (.litVal (.bool false)), .ok (.slotRef j), .ok (.slotRef k) =>
            .ok (DomConstraint.eqSlot j k)
        | .error e, _, _ => .error e
        | _, .error e, _ => .error e
        | _, _, .error e => .error e
        | _, _, _ =>
            .error "unsupported bool_or argument shapes" :
        Except String DomConstraint)) = .ok dc := hcc
    split at hcc2
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inl ⟨_, k, cav_slotRef hc0, cav_slotRef hc2,
          (cav_litVal_bool hc1).1, (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)
    · next i k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inl ⟨i, k, cav_slotRef hc0,
          cav_slotRef hc2, (cav_litVal_bool hc1).1,
          (cav_litVal_bool hc1).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩))
    · next k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    · next j k hc0 hc1 hc2 =>
        exact Or.inr (Or.inr (Or.inr (Or.inr ⟨j, k, cav_slotRef hc1,
          cav_slotRef hc2, (cav_litVal_bool hc0).1,
          (cav_litVal_bool hc0).2, by
          have := (Except.ok.inj hcc2); exact this ▸ rfl⟩)))
    all_goals exact absurd hcc2 (by intro hc; injection hc)
/-- The successful compile of a slot-identifier/bool-literal
    `bool_not` piece (through the fallback) gives the slot's
    resolution and the negated constEq form. -/
theorem compileConstraint_bool_not_lit_inv {env : Store} {names : List String}
    {x : Ident} {b : Bool} {dc : DomConstraint}
    (hcc : compileConstraint env names
        { name := Ident.mk "bool_not"
        , args := [.basic (.ident x), .basic (.lit (.bool b))]
        , anns := [] } = .ok dc) :
    ∃ i, nameIndex names x.name = some i ∧
      dc = .constEq i (.bool (!b)) := by
  -- the extraction rejects this shape (bool_not with a literal)
  have hex : extractConstraint names
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } = none := by
    simp only [extractConstraint]
  -- the compile reduces to the fallback; the name gates select
  -- bool_not
  unfold compileConstraint at hcc
  rw [hex] at hcc
  simp only [hex] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_neg (by intro hc; exact absurd hc.1 (by simp))] at hcc
  rw [if_pos ⟨trivial, rfl⟩] at hcc
  -- the do-block reduces (argOf on the literal args)
  have ha0 : argOf
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } 0 = .ok (.ident x) := rfl
  have ha1 : argOf
      { name := Ident.mk "bool_not"
      , args := [.basic (.ident x), .basic (.lit (.bool b))]
      , anns := [] } 1 = .ok (.lit (.bool b)) := rfl
  rw [ha0, ha1] at hcc
  -- case on x's resolution: a slot (the success) or an env value/error
  cases hx : nameIndex names x.name with
  | some i =>
      -- the slot arm: the first match arm fires
      have hc0 : compileArgVal env names (BasicExpr.ident x)
          = .ok (ArgVal.slotRef i) := by
        rw [compileArgVal, hx]
      have hc1 : compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b))
          = .ok (ArgVal.litVal (Value.bool b)) := by
        rw [compileArgVal]
      -- the do-binds reduce definitionally; restate hcc in the
      -- reduced match form
      have hcc' : (match compileArgVal env names (BasicExpr.ident x),
          compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b)) with
        | Except.ok (ArgVal.slotRef i), Except.ok (ArgVal.litVal (Value.bool b)) =>
            Except.ok (DomConstraint.constEq i (Value.bool !b))
        | Except.ok (ArgVal.litVal (Value.bool b)), Except.ok (ArgVal.slotRef j) =>
            Except.ok (DomConstraint.constEq j (Value.bool !b))
        | Except.error e, _ => Except.error e
        | _, Except.error e => Except.error e
        | _, _ =>
            Except.error "unsupported bool_not argument shapes") = .ok dc := hcc
      rw [hc0, hc1] at hcc'
      refine ⟨i, ?_, ?_⟩
      · rw [← hx]
      · exact (Except.ok.inj hcc').symm
  | none =>
      -- x is not a slot: it resolves through env or errors; either
      -- way the match's first arm (slotRef, litVal) cannot fire with
      -- a slotRef for a0 — the compile either errors (contradiction)
      -- or produces a constEq over a LITERAL-resolved position,
      -- which is impossible (the arm requires a slotRef)
      exfalso
      have hc0 : compileArgVal env names (BasicExpr.ident x)
          = match env x with
          | some v => .ok (ArgVal.litVal v)
          | none => .error s!"unresolved argument '{x.name}'" := by
        rw [compileArgVal, hx]
        rfl
      -- restate hcc in the reduced match form and rewrite
      have hcc' : (match compileArgVal env names (BasicExpr.ident x),
          compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b)) with
        | Except.ok (ArgVal.slotRef i), Except.ok (ArgVal.litVal (Value.bool b)) =>
            Except.ok (DomConstraint.constEq i (Value.bool !b))
        | Except.ok (ArgVal.litVal (Value.bool b)), Except.ok (ArgVal.slotRef j) =>
            Except.ok (DomConstraint.constEq j (Value.bool !b))
        | Except.error e, _ => Except.error e
        | _, Except.error e => Except.error e
        | _, _ =>
            Except.error "unsupported bool_not argument shapes") = .ok dc := hcc
      rw [hc0] at hcc'
      -- case on env x: a value (litVal arm mismatch) or an error
      cases henv : env x with
      | some v =>
          -- the first argument compiles to a litVal; the match arms
          -- require a slotRef — the error arm
          have hc1 : compileArgVal env names (BasicExpr.lit (BasicLiteral.bool b))
              = .ok (ArgVal.litVal (Value.bool b)) := by
            rw [compileArgVal]
          rw [hc1] at hcc'
          simp only [henv] at hcc'
          cases hcc'
      | none =>
          simp only [henv] at hcc'
          cases hcc'

end LeanFzn.Solver.Direct
