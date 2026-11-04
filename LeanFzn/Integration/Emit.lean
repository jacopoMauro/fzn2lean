/-
File: LeanFzn/Integration/Emit.lean

Purpose:
  Output-only rendering of an already-proved LeanFzn.Solver result as FlatZinc text.

Dependencies:
  - LeanFzn.Integration.Emit.Basic: stable executable API and implementation proof.

DAG:
  LeanFzn.Compiler.Domain -> LeanFzn.Integration.Emit.Basic -> LeanFzn.Integration.Emit -> CLI output
-/

import LeanFzn.Integration.Emit.Basic
import LeanFzn.Integration.Emit.Model
open LeanFzn.Compiler.Domains
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Compiler LeanFzn.Integration

