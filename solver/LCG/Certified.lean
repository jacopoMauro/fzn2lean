/-
File: solver/LCG/Certified.lean

Purpose:
  The first certified LCG front door: for the singleton-domain
  fragment (every initial domain a singleton — no decisions, no
  propagation needed) of a successfully compiled model, the LCG
  engine's SAT/UNSAT verdicts carry kernel-checked theorems with
  every premise DERIVED from compiler success and executable checks
  (no caller-supplied safety, entitlement, or int-view premises).

  The fragment check itself is executable (`fragmentOk`); the empty
  propagator list makes the per-family soundness premises
  (`PropSafeUniv`, conflict entitlement) vacuous; the evaluator
  agreement is `DomConstraint.satisfiedB_iff`; the empty clause
  database is trivially entitled; and `IntViewed` follows from the
  compiler's domain construction (`domains_intViewed`: `varDomain`
  produces only `.intDom`/`.boolDom`, so every compiled domain value
  is `.int`/`.bool`).

Dependencies:
  - solver.LCG.Proofs.Search: `solve_certified_fragment(_unsat)`.
  - solver.LCG.Proofs.Theory: the fragment discipline.
  - solver.Propagators: `DomConstraint.satisfiedB`.

DAG:
  LCG.Proofs.Search -> LCG.Certified -> solver.Direct.Cli-level composition
-/

import solver.LCG.Proofs.Search
import solver.Propagators
import solver.Direct.Proofs.Exact

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

/-- A problem whose domain values all have integer views is
    int-viewed. (The premise holds for every compiled problem by
    `domains_intViewed`; singleton-ness is not what carries it.) -/
theorem intViewed_of_fragment {problem : Problem Constraint Objective}
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
  cases hc

/-- **THE CERTIFIED LCG FRONT DOOR (SAT)**: on the LCG problem of a
    successfully compiled model (singleton-domain fragment — every
    premise derived from compiler success and executable checks, no
    caller-supplied premises), a `sat` assignment returned by the
    LCG engine satisfies every internal constraint under the
    declarative semantics. -/
theorem solve_certified_sat
    {m : LeanFzn.Model} {problem : LCG.Problem DomConstraint Unit}
    {compiled : LeanFzn.Solver.Direct.CompiledProblem DomConstraint}
    (hc : LeanFzn.Solver.Direct.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hsat : solve problem DomConstraint.satisfiedB [] = .sat assignment) :
    ProblemSolution problem DomConstraint.SatisfiedBy assignment := by
  -- the int-view premise, DERIVED from compiler success (the
  -- compiler's slot extraction only produces int/bool values)
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Solver.Direct.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
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

/-- **THE CERTIFIED LCG FRONT DOOR (UNSAT)**: on the LCG problem of a
    successfully compiled model (singleton-domain fragment), an
    `unsat` verdict excludes every internal solution. -/
theorem solve_certified_unsat
    {m : LeanFzn.Model} {problem : LCG.Problem DomConstraint Unit}
    {compiled : LeanFzn.Solver.Direct.CompiledProblem DomConstraint}
    (hc : LeanFzn.Solver.Direct.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hunsat : solve problem DomConstraint.satisfiedB [] = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem DomConstraint.SatisfiedBy
      assignment := by
  -- the int-view premise, DERIVED from compiler success
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Solver.Direct.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
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
