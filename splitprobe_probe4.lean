/-
File: solver/Direct/Proofs/CompileAux2.lean

Purpose:
  The auxiliary-slot expansion layer of the compiler-correspondence
  proofs, part 2: the per-shape semantic bridges (SAT and coverage),
  the extended read chains, and the per-piece successful-compile
  inversions. Split from Compile.lean (P1c) to bound elaboration
  memory; the statements are unchanged.

Dependencies:
  - solver.Direct.Proofs.CompileAux1 (the expansion layer part 1
    and, through it, the core correspondence layer).

DAG:
  solver.Direct.Compile -> CompileCore -> CompileAux1 -> CompileAux2
    -> Compile (re-export shell) -> Exact / Fam.AllDiff
-/

import solver.Direct.Proofs.CompileAux1

namespace LeanFzn.Solver.Direct

open LeanFzn LeanFzn.Globals LeanFzn.Solver LeanFzn.Solver.Core
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

end LeanFzn.Solver.Direct
