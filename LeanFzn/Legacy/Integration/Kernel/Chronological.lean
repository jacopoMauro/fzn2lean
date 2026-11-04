/- Public chronological domain solving with certified propagation and learning. -/
import LeanFzn.Legacy.Solver.Propagation.DomPruningKit
import LeanFzn.Legacy.Solver.Chronological.Search
open LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

/-- Public domain LeanFzn.Solver: uses registered proved propagators and learned clauses.
The historical propagator argument is retained for source compatibility; arbitrary
unproved callbacks are never admitted to the certified pruning kit. -/
def solveDom (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Objective) (_props : List Propagator) : SearchResult :=
  solve problem DomConstraint.satisfiedB
    (problem.constraints.filterMap propagatorOfProved)
    (domPruningKit (feasibilityProblem problem))

/-- Same public domain algorithm with observable, non-limiting work counters. -/
def solveDomWithStats (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Objective) : SearchResult × SearchStats :=
  solveWithStats problem DomConstraint.satisfiedB
    (problem.constraints.filterMap propagatorOfProved)
    (domPruningKit (feasibilityProblem problem))

/-- **The NAMED CHRONOLOGICAL REFERENCE (D1b)**: the original source-LeanFzn.Solver
route (engine + certified pruning kit over `analyzedSolve`), kept callable
under an explicit name so the new driver route can be compared against it.
Its statement is that of `solveDom` unchanged; it is an alias, not a
restatement. -/
def solveChronological (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Objective)
    (props : List Propagator) : SearchResult :=
  solveDom problem props

end LeanFzn.Integration
