/-
Purpose: fuel-free search through a proof-carrying propagation and learning kit.
The public driver is `analyzedSolve`: the chronological frontier plus
nonchronological pruning of survivor frames against the learned clause
database (PLAN P1.D/E). It is the same measure-checked, fuel-free
traversal — pruning only removes frames, so `frontierCost` still strictly
decreases — and it is certified by `analyzedSolve_sat_leaf` /
`analyzedSolve_unsat_excludes`. The chronological-only `prunedSolve`
remains available as the reference traversal.
Dependencies: Engine supplies leaf semantics, AnalysisDriver supplies the
public driver, and Propagate supplies the legacy propagator API retained
for compatibility.
-/

import LeanFzn.Solver.Propagation.EngineCore
import LeanFzn.Solver.Reference.Engine
import LeanFzn.Solver.Propagation.Propagate
import LeanFzn.Solver.Chronological.Pruned
import LeanFzn.Solver.Chronological.AnalysisDriver
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference


namespace LeanFzn.Solver.Chronological
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference

/-- Execute a proof-carrying pruning kit and expose search statistics.
The public driver is the analysed one: after every completed branch the
surviving pending frames are pruned against the learned clause database
(`pruneFrames`), which is the plan's nonchronological step. -/
def solveWithStats (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (_propagators : List Propagator)
    (kit : PruningKit (chronologicalLeaf problem constraintHoldsB) := identityPruningKit _) :
    SearchResult × SearchStats :=
  let r := analyzedSolve (chronologicalLeaf problem constraintHoldsB) kit
    [(problem.domains, [])] problem.clauses {}
  (match r.1 with | .sat a => .sat a | .unsat => .unsat, r.2)

/-- Generic fuel-free LeanFzn.Solver with a coverage-preserving pruning kit. -/
def solve (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (propagators : List Propagator)
    (kit : PruningKit (chronologicalLeaf problem constraintHoldsB) := identityPruningKit _) :
    SearchResult :=
  (solveWithStats problem constraintHoldsB propagators kit).1

/-- Generic domain entry point; specialized public callers provide their kit. -/
def solveDomReference (problem : LeanFzn.Solver.Propagation.Problem DomConstraint Objective)
    (propagators : List Propagator) : SearchResult :=
  solve problem DomConstraint.satisfiedB propagators

/-- The historical fuel-bounded entry point, retained as an explicitly
    named diagnostic reference (budget exhaustion reports `unknown`).
    NOT the normal LeanFzn.Solver. -/
def solveBounded (fuel : Nat)
    (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (constraintHoldsB : Constraint → Assignment → Bool)
    (propagators : List Propagator) : SearchResult :=
  lcgSearchBounded fuel problem constraintHoldsB propagators

end LeanFzn.Solver.Chronological
