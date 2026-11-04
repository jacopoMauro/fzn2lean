/-
File: LeanFzn/Solver/Propagation/Proofs/FallbackRaw.lean

Purpose:
  The `hconfraw` discharge for the raw-conflict-clause learning
  (PLAN.md §5 item 4's residual): when `analyzeConflict` returns `none`
  on a NONEMPTY conflict clause, the engine now LEARNS the conflict
  clause itself (normalized) before the chronological retreat. The
  master theorem `go_unsat_entry_invariant` (Proofs/Run.lean) demands
  the new premise `hconfraw` — every reported nonempty conflict clause
  at a conflict-free RunInv entry whose analysis fails is ENTITLED
  (true at every internal solution).

  The route is the SAME state-free entitlement the `hconfent` premise
  (the analysis arm's `AnalysisReady` seed) already consumes:
  `propagatorsOfProved_conflictEntitled` (Proofs/Reason.lean) — the
  loop-level induction over the propagation origins (scan arm: the
  reported clause is an entitled database clause; unit arm:
  conflict-clear recursion; sweep arm: the per-family state-free
  conflict entitlement), gated on the clause's nonemptiness.

  The analyze-none and trail-distinctness premises are IGNORED in
  the proof — the entitlement holds for every reported nonempty
  clause regardless of whether the analysis resolves; they are
  carried only to match the engine's observable at the learning
  site.

Dependencies:
  - LeanFzn.Solver.Propagation.Proofs.Reason: `propagatorsOfProved_conflictEntitled`
    (the state-free loop-level conflict entitlement over the proved
    propagator registration).

DAG:
  Theory + Propagators + Run -> Reason -> FallbackRaw (a leaf;
  consumed by Certified.lean's wide front door)
-/

import LeanFzn.Legacy.Solver.Propagation.Proofs.Reason
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference

/-- **THE `hconfraw` DISCHARGE for the proved propagators** (the raw
    conflict-clause learning's entitlement): at every conflict-free
    RunInv entry whose engine-fuel propagation run reports a NONEMPTY
    conflict clause on which the conflict analysis fails, the reported
    clause is ENTITLED — true at every internal problem solution —
    so the engine's learned-clause insertion preserves
    `RunInv.learnedEntailed`.

    The proof is `propagatorsOfProved_conflictEntitled` (the `hconfent`
    route) under the learning site's observables: the analyze-none
    and trail-distinctness premises are not consumed (the entitlement
    is state-free and analysis-independent); the conclusion is
    packaged as `Clause.EntitledBy`. -/
theorem propagatorsOfProved_conflictraw
    {problem : Problem DomConstraint Unit}
    (hview : IntViewedDoms problem.domains)
    (hshape : DomsShapeTyped problem.domains)
    {props : List Propagator}
    (hprops : ∀ p ∈ props, ∃ dc ∈ problem.constraints,
      propagatorOfProved dc = some p)
    (hlin : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linLe coeffs is b → coeffs.length = is.length)
    (hlinE : ∀ dc ∈ problem.constraints, ∀ coeffs is b,
      dc = .linEq coeffs is b → coeffs.length = is.length)
    (_hsolvable : ∃ b, ProblemSolution problem
      DomConstraint.SatisfiedBy b)
    (hdb : ∀ c ∈ problem.clauses, ∀ a,
      ProblemSolution problem DomConstraint.SatisfiedBy a →
        ∃ l ∈ c, l.eval a = some true) :
    ∀ (st : State), st.conflict = none →
      RunInv problem DomConstraint.SatisfiedBy props st →
      TrailDistinct st.trail →
      ∀ cc, (propagateLoop (engineFuel st) props st).conflict
          = some cc →
        analyzeConflict (propagateLoop (engineFuel st) props st) = none →
        cc ≠ [] →
        Clause.EntailedBy problem DomConstraint.SatisfiedBy cc := by
  intro st hnone hinv _hdist cc hrep _hanalyze hccne
  exact propagatorsOfProved_conflictEntitled hview hshape
    (problem := problem) (props := props)
    _hsolvable hprops hlin hlinE hdb st hnone hinv cc hrep hccne

#print axioms LeanFzn.Solver.Propagation.propagatorsOfProved_conflictraw

end LeanFzn.Solver.Propagation
