/-
File: solver/Emit.lean

Purpose:
  Public executable solution-emission module. The evolving round-trip proof
  stack is deliberately not re-exported from this stable boundary.

Dependencies:
  - solver.Emit.Basic: stable executable API and implementation proof.

DAG:
  solver.Domain -> solver.Emit.Basic -> solver.Emit
                                  \-> solver.Emit.Roundtrip (explicit opt-in)
-/

import solver.Emit.Basic
