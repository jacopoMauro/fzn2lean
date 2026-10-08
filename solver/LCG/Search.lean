/-
File: solver/LCG/Search.lean

Purpose:
  The executable LCG search entry point over the FUEL-FREE
  chronological frontier (kernel-checked termination by the
  `frontierCost` measure; no search budget, no `unknown` verdict on
  accepted models). Its chronological frontier tracks unused value
  alternatives explicitly; propagator arguments are retained for API
  compatibility and a later proved propagation refinement.

Dependencies:
  - solver.LCG.Engine: the search loop.
  - solver.LCG.Propagate: `propagatorsOf` for `DomConstraint`s.

DAG:
  solver.LCG.Engine + solver.LCG.Propagate -> solver.LCG.Search
-/

import solver.LCG.Engine
import solver.LCG.Propagate

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver (DomConstraint)

/-- The generic LCG search entry point: the fuel-free chronological
    frontier over the supplied constraint semantics. The propagator
    parameter remains available for a future coverage-preserving
    frontier refinement. -/
def solve (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (propagators : List Propagator) : SearchResult :=
  lcgSearch problem constraintHoldsB propagators

/-- LCG search over a problem whose constraints are `DomConstraint`s. -/
def solveDom (problem : Problem DomConstraint Objective)
    (propagators : List Propagator) : SearchResult :=
  lcgSearch problem DomConstraint.satisfiedB propagators

/-- The historical fuel-bounded entry point, retained as an explicitly
    named diagnostic reference (budget exhaustion reports `unknown`).
    NOT the normal solver. -/
def solveBounded (fuel : Nat)
    (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (propagators : List Propagator) : SearchResult :=
  lcgSearchBounded fuel problem constraintHoldsB propagators

end LeanFzn.Solver.LCG
