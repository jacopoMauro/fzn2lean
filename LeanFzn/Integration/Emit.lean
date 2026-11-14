/-
File: LeanFzn/Integration/Emit.lean

Purpose:
  Rendering of certified solver results, with a verified solution-text round trip.

Dependencies:
  - LeanFzn.Integration.Emit.Basic/Model: stable executable rendering API.
  - LeanFzn.Integration.Emit.RoundTrip: independent grammar, parsing and value correspondence.

DAG:
  LeanFzn.Compiler.Domain -> LeanFzn.Integration.Emit.Basic -> LeanFzn.Integration.Emit -> CLI output
-/

import LeanFzn.Integration.Emit.Basic
import LeanFzn.Integration.Emit.Model
import LeanFzn.Integration.Emit.RoundTrip
open LeanFzn.Compiler.Domains
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Compiler LeanFzn.Integration

