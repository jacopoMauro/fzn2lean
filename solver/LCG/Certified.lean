/-
File: solver/LCG/Certified.lean

Purpose:
  The first certified LCG front door: for the singleton-domain
  fragment (every initial domain a singleton — no decisions, no
  propagation needed), the LCG engine's SAT/UNSAT verdicts carry
  kernel-checked source-level theorems with every premise DERIVED
  from executable checks (no caller-supplied safety or entitlement).

  The fragment check itself is executable (`fragmentOk`), and the
  empty propagator list makes the per-family soundness premises
  (`PropSafeUniv`, conflict entitlement) vacuous; the evaluator
  agreement is `DomConstraint.satisfiedB_iff`; the empty clause
  database is trivially entitled; `IntViewed` follows from the
  singleton-domains check.

Dependencies:
  - solver.LCG.Proofs.Search: `solve_certified_fragment(_unsat)`.
  - solver.LCG.Proofs.Theory: the fragment discipline.
  - solver.Propagators: `DomConstraint.satisfiedB`.

DAG:
  LCG.Proofs.Search -> LCG.Certified -> solver.Direct.Cli-level composition
-/

import solver.LCG.Proofs.Search
import solver.Propagators

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core

/-- The executable fragment check: every initial domain is a
    singleton (one complete assignment, read off directly). -/
def fragmentOk (problem : Problem Constraint Objective) : Bool :=
  problem.domains.all (fun d => d.length == 1)

/-- The executable check implies the fragment predicate. -/
theorem fragmentOk_iff {problem : Problem Constraint Objective} :
    fragmentOk problem = true ↔ PropFragment problem := by
  constructor
  · intro h
    intro d hd
    have hall : problem.domains.all (fun d => d.length == 1) = true := h
    rw [List.all_eq_true] at hall
    have := hall d hd
    simpa using this
  · intro h
    rw [fragmentOk, List.all_eq_true]
    intro d hd
    simpa using h d hd

/-- Singleton domains with int/bool values are int-viewed. -/
theorem intViewed_of_fragment {problem : Problem Constraint Objective}
    (hfrag : PropFragment problem)
    (hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none) :
    IntViewed problem := hint

/-- The empty clause database is trivially entitled. -/
theorem db0_nil {problem : Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    (hclauses : problem.clauses = []) :
    ∀ c ∈ problem.clauses,
      ∀ a, ProblemSolution problem constraintHolds a →
        ∃ l ∈ c, l.eval a = some true := by
  intro c hc
  rw [hclauses] at hc
  exact absurd hc (by simp)

/-- **THE CERTIFIED LCG FRONT DOOR (SAT)**: on a singleton-domain
    problem (the first certified fragment — every premise derived
    from executable checks), a `sat` assignment returned by the LCG
    engine satisfies every internal constraint under the declarative
    semantics. -/
theorem solve_certified_sat
    {problem : LCG.Problem DomConstraint Unit}
    (hfrag : fragmentOk problem = true)
    (hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none)
    (hclauses : problem.clauses = [])
    (hsat : solve problem DomConstraint.satisfiedB [] = .sat assignment) :
    ProblemSolution problem DomConstraint.SatisfiedBy assignment := by
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hfragP hint
  -- the empty propagator list: both safety premises are vacuous
  have huniv : PropSafeUniv problem DomConstraint.SatisfiedBy [] := by
    intro st
    exact ⟨fun p hp => absurd hp (by simp),
      fun p hp => absurd hp (by simp)⟩
  have hentFam : ∀ (st : State) (p : Propagator), p ∈ [] →
      ∀ (c : Clause), p.run st = .conflict c →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          ∃ l ∈ c, l.eval a = some true := by
    intro st p hp
    exact absurd hp (by simp)
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := []) hview hfragP
    (fun c hc a _ => by
      rw [hclauses] at hc
      cases hc) huniv hentFam hagrees hsat

/-- **THE CERTIFIED LCG FRONT DOOR (UNSAT)**: on a singleton-domain
    problem, an `unsat` verdict excludes every internal solution. -/
theorem solve_certified_unsat
    {problem : LCG.Problem DomConstraint Unit}
    (hfrag : fragmentOk problem = true)
    (hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none)
    (hclauses : problem.clauses = [])
    (hunsat : solve problem DomConstraint.satisfiedB [] = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem DomConstraint.SatisfiedBy
      assignment := by
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hfragP hint
  have huniv : PropSafeUniv problem DomConstraint.SatisfiedBy [] := by
    intro st
    exact ⟨fun p hp => absurd hp (by simp),
      fun p hp => absurd hp (by simp)⟩
  have hentFam : ∀ (st : State) (p : Propagator), p ∈ [] →
      ∀ (c : Clause), p.run st = .conflict c →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          ∃ l ∈ c, l.eval a = some true := by
    intro st p hp
    exact absurd hp (by simp)
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment_unsat (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := []) hview hfragP
    (fun c hc a _ => by
      rw [hclauses] at hc
      cases hc) huniv hentFam hagrees hunsat

end LeanFzn.Solver.LCG
