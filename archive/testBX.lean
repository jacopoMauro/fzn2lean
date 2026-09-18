/-
File: testBX.lean

Purpose:
  Minimal scratch example exercising `omega` and `trivial` via
  `FznGlobals.Common`.

Dependencies:
  LeanFzn.FznGlobals.Common.

Why:
  Quick build-time sanity check that the common helpers import
  cleanly. Not part of any build target.

DAG:
  FznGlobals.Common -> testBX.lean (standalone, no dependents)
-/

import LeanFzn.FznGlobals.Common
example (a b : Int) : True ∧ True := by
  refine ⟨by omega, ?_⟩
  · trivial
