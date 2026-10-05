/-
File: solver/Direct/Proofs/CompileAux2b.lean

Purpose:
  The auxiliary-slot expansion layer, part 2b: the remaining argument
  inversions (two-literal times, and/or shapes) and the aux-slot
  linker's premise chains. Split from CompileAux2 (P1c) to bound
  elaboration memory; the statements are unchanged.

DAG:
  CompileCore -> CompileAux1 -> CompileAux2a -> CompileAux2b
    -> CompileAux2c -> Compile (shell)
-/

import solver.Direct.Proofs.CompileAux2a

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core

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


end LeanFzn.Solver.Direct
