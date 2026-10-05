/-
File: solver/Direct/Proofs/CompileAux2c.lean

Purpose:
  The auxiliary-slot expansion layer, part 2c: the per-shape name
  inversions and the per-piece successful-compile inversions (the
  aux-slot linker's payoff). Split from CompileAux2 (P1c) to bound
  elaboration memory; the statements are unchanged.

DAG:
  CompileCore -> CompileAux1 -> CompileAux2a -> CompileAux2b
    -> CompileAux2c -> Compile (shell)
-/

import solver.Direct.Proofs.CompileAux2b

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core
/-- The timesRK shape's name inversion: the classification's int_times
    branch fired, so the constraint's name is `int_times`. -/
theorem auxShapeOf_timesRK_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesRK x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.int k))] := auxShapeOf_timesRK_args h
  rw [auxShapeOf, hargs] at h
  split at h
  next heq1 => exact heq1
  all_goals exact absurd h (by simp)

/-- The timesKR shape's name inversion. -/
theorem auxShapeOf_timesKR_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
    .basic (.ident y)] := auxShapeOf_timesKR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  next heq1 => exact heq1
  all_goals exact absurd h (by simp)

/-- The timesKR' shape's name inversion. -/
theorem auxShapeOf_timesKR'_name {c : ConstraintItem} {x y : Ident} {k : Int}
    (h : auxShapeOf c = some (AuxShape.timesKR' x y k)) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
    .basic (.ident y)] := auxShapeOf_timesKR'_args h
  rw [auxShapeOf, hargs] at h
  split at h
  next heq1 => exact heq1
  all_goals exact absurd h (by simp)

/-- The timesRKK shape's name inversion. -/
theorem auxShapeOf_timesRKK_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesRKK x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.ident x), .basic (.lit (.int k)),
    .basic (.lit (.int k'))] := auxShapeOf_timesRKK_args h
  rw [auxShapeOf, hargs] at h
  split at h
  next heq1 => exact heq1
  all_goals exact absurd h (by simp)

/-- The timesKRR shape's name inversion. -/
theorem auxShapeOf_timesKRR_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKRR x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.ident x),
    .basic (.lit (.int k'))] := auxShapeOf_timesKRR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  next heq1 => exact heq1
  all_goals exact absurd h (by simp)

/-- The timesKKR shape's name inversion. -/
theorem auxShapeOf_timesKKR_name {c : ConstraintItem} {x : Ident} {k k' : Int}
    (h : auxShapeOf c = some (AuxShape.timesKKR x k k')) :
    c.name.name = "int_times" := by
  have hargs : c.args = [.basic (.lit (.int k)), .basic (.lit (.int k')),
    .basic (.ident x)] := auxShapeOf_timesKKR_args h
  rw [auxShapeOf, hargs] at h
  split at h
  next heq1 => exact heq1
  all_goals exact absurd h (by simp)

/-- The andTrue shape's name inversion. -/
theorem auxShapeOf_andTrue_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andTrue x y)) :
    c.name.name = "bool_and" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool true))] := auxShapeOf_andTrue_args h
  rw [auxShapeOf, hargs] at h
  split at h
  all_goals first
    | next heq1 => exact heq1
    | exact absurd h (by simp)

/-- The andFalse shape's name inversion. -/
theorem auxShapeOf_andFalse_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.andFalse x y)) :
    c.name.name = "bool_and" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool false))] := auxShapeOf_andFalse_args h
  rw [auxShapeOf, hargs] at h
  split at h
  all_goals first
    | next heq1 => exact heq1
    | exact absurd h (by simp)

/-- The orTrue shape's name inversion. -/
theorem auxShapeOf_orTrue_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orTrue x y)) :
    c.name.name = "bool_or" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool true))] := auxShapeOf_orTrue_args h
  rw [auxShapeOf, hargs] at h
  split at h
  all_goals first
    | next heq1 => exact heq1
    | exact absurd h (by simp)

/-- The orFalse shape's name inversion. -/
theorem auxShapeOf_orFalse_name {c : ConstraintItem} {x y : Ident}
    (h : auxShapeOf c = some (AuxShape.orFalse x y)) :
    c.name.name = "bool_or" := by
  have hargs : c.args = [.basic (.ident x), .basic (.ident y),
    .basic (.lit (.bool false))] := auxShapeOf_orFalse_args h
  rw [auxShapeOf, hargs] at h
  split at h
  all_goals first
    | next heq1 => exact heq1
    | exact absurd h (by simp)


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
