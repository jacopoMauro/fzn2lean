/-
File: solver/Direct/Types.lean

Purpose:
  Defines the data passed between the direct solver's compiler, search
  algorithm, and output boundary. Contains no correctness proofs.

Dependencies:
  - solver.Core.Types: shared problem, domain, assignment, and state vocabulary.
  - LeanFzn.FznGlobals: source models, stores, and full semantics.

DAG:
  solver.Core.Types + LeanFzn.FznGlobals -> solver.Direct.Types
-/

import solver.Core.Types
import LeanFzn.FznGlobals

namespace LeanFzn.Solver.Direct

open LeanFzn

/-- A finite problem ready for direct search, extending the shared core
problem container with its source model and store reconstruction.

The constraint language is a parameter: the certified fragment
instantiates it with `DomConstraint` (whose `satisfiedB` leaf
evaluation is proved equivalent to its declarative semantics,
`DomConstraint.satisfiedB_iff`), so the compiled problem is exactly
the kind the LCG layer and the exhaustive reference search consume.

`toStore` is part of the compiled representation, not a checker: it maps a
complete internal assignment directly to the semantic store returned on SAT.
-/
structure CompiledProblem (C : Type) extends
    LeanFzn.Solver.Core.Problem C Unit where
  source : Model
  toStore : LeanFzn.Solver.Core.Assignment → Store

/-- Public outcomes of the directly verified solver. -/
inductive Result where
  | sat (store : Store)
  | unsat
  | unsupported (reason : String)
  | unknown

end LeanFzn.Solver.Direct
