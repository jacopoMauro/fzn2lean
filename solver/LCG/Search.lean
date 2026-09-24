/-
File: solver/LCG/Search.lean

Purpose:
  The executable LCG search entry point: instantiates the engine
  (`lcgSearch`) with the standard propagators of the compiled
  constraint list.

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

/-- Default fuel: 10 000 decision/conflict iterations. Exhaustion
    reports `unknown`, never `unsat`. -/
def defaultFuel : Nat := 10000

/-- The generic LCG search entry point: the engine loop with default
    fuel over the supplied constraint semantics and propagators. -/
def solve (problem : Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (propagators : List Propagator) : SearchResult :=
  lcgSearch defaultFuel problem constraintHoldsB propagators

/-- LCG search over a problem whose constraints are `DomConstraint`s. -/
def solveDom (fuel : Nat)
    (problem : Problem DomConstraint Objective)
    (propagators : List Propagator) : SearchResult :=
  lcgSearch fuel problem DomConstraint.satisfiedB propagators

end LeanFzn.Solver.LCG
