/-
File: solver/Emit.lean

Purpose:
  Output-only rendering of an already-proved solver result as FlatZinc text.

Dependencies:
  - solver.Emit.Basic: stable executable API and implementation proof.

DAG:
  solver.Domain -> solver.Emit.Basic -> solver.Emit -> CLI output
-/

import solver.Emit.Basic
