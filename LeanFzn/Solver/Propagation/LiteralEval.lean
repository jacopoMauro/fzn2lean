/-
File: LeanFzn/Solver/Propagation/LiteralEval.lean

Purpose:
  `Literal.valueHolds`: evaluate a signed atom directly on a single slot
  value (the predicate the structural filters consume).  Kept in a small
  module so both the compact-domain filter and `FrameFilter` can use it
  without a `CompactDomain` <-> `FrameFilter` import cycle.

Dependencies: LeanFzn.Solver.Propagation.Operations (`Value.intView`,
`Literal`, `Atom`).
DAG: Operations -> LiteralEval -> CompactDomain/FrameFilter.
-/
import LeanFzn.Solver.Propagation.Operations

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Semantics LeanFzn.Solver.Core

/-- Evaluate a literal on the value of its referenced slot. -/
def Literal.valueHolds (l : Literal) (v : Value) : Bool :=
  let b := match l.atom with
    | .boolEq _ expected => match v with
      | .bool actual => some (actual == expected)
      | _ => none
    | .intLe _ upper => v.intView.map fun actual => decide (actual ≤ upper)
    | .intNe _ forbidden => v.intView.map fun actual => decide (actual ≠ forbidden)
  (b.map fun x => if l.positive then x else !x) == some true

end LeanFzn.Solver.Propagation
