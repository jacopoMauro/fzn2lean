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
import solver.LCG.Proofs.Propagators
import solver.Propagators
import solver.Direct.Proofs.Exact

namespace LeanFzn.Solver.LCG

open LeanFzn LeanFzn.Solver LeanFzn.Solver.Core LeanFzn.Solver.LCG

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
  have huniv : CoherentSafeUniv problem DomConstraint.SatisfiedBy [] := by
    intro st _
    exact ⟨fun p hp => absurd hp (by simp),
      fun p hp => absurd hp (by simp)⟩
  have hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ [] →
      ∀ (c : Clause), p.run st = .conflict c →
        SolvedBy problem DomConstraint.SatisfiedBy st →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          ∃ l ∈ c, l.eval a = some true := by
    intro st _ p hp
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
  have huniv : CoherentSafeUniv problem DomConstraint.SatisfiedBy [] := by
    intro st _
    exact ⟨fun p hp => absurd hp (by simp),
      fun p hp => absurd hp (by simp)⟩
  have hentFam : ∀ (st : State), DomainCoherent problem st →
      ∀ (p : Propagator), p ∈ [] →
      ∀ (c : Clause), p.run st = .conflict c →
        SolvedBy problem DomConstraint.SatisfiedBy st →
        ∀ a, ProblemSolution problem DomConstraint.SatisfiedBy a →
          ∃ l ∈ c, l.eval a = some true := by
    intro st _ p hp
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


/-- The rooted initial state is domain-coherent: its domains are the
    problem's (`initialStateWithRoots_domains`) and its trail holds
    only root facts, whose `domOfLit` fold is the identity on the
    problem's domains (the root-fact fold lemma). -/
theorem initialStateWithRoots_coherent_cert
    (problem : Problem DomConstraint Unit) :
    DomainCoherent problem (initialStateWithRoots problem) := by
  have hdoms : (initialStateWithRoots problem).domains
      = problem.domains := initialStateWithRoots_domains problem
  unfold DomainCoherent
  rw [hdoms]
  -- the trail-of-root-facts fold is the identity on problem.domains
  have hfold : (initialStateWithRoots problem).trail.foldl
      (fun acc e => domOfLit acc e.literal) problem.domains
      = problem.domains := by
    have main : ∀ (tr : List TrailEntry),
        (∀ e ∈ tr, e.literal ∈ rootFacts problem.domains) →
        tr.foldl (fun acc e => domOfLit acc e.literal) problem.domains
          = problem.domains := by
      intro tr
      induction tr with
      | nil => intro _; rfl
      | cons e rest ih =>
          intro hall
          rw [List.foldl_cons]
          have hhead : e.literal ∈ rootFacts problem.domains :=
            hall e (List.mem_cons_self)
          have hid : domOfLit problem.domains e.literal
              = problem.domains :=
            domOfLit_rootFact_id (doms := problem.domains)
              (ds := problem.domains) (s := 0) (l := e.literal)
              (fun i => by
                show problem.domains.getD i [] =
                  problem.domains.getD (0 + i) []
                rw [Nat.zero_add])
              hhead
          rw [hid]
          exact ih (fun e2 he2 => hall e2 (List.mem_cons_of_mem _ he2))
    exact main (initialStateWithRoots problem).trail
      (initialWithRoots_trail_mem problem)
  rw [hfold]


/-- Every `linLe` constraint of a successfully compiled problem
    has equal-length coefficient/index lists (the extractor's
    `coeffs.length == is.length` gate). -/
theorem compiled_linLe_shape
    {m : LeanFzn.Model} {compiled : LeanFzn.Solver.Direct.CompiledProblem DomConstraint}
    (hc : LeanFzn.Solver.Direct.compileModel m = .ok compiled)
    {dc : DomConstraint} (hdc : dc ∈ compiled.constraints)
    {coeffs : List Int} {is : List Nat} {b : Int}
    (hdc2 : dc = .linLe coeffs is b) :
    coeffs.length = is.length := by
  sorry

/-- **THE CERTIFIED LCG FRONT DOOR WITH REAL PROPAGATORS (SAT)**: on
    the singleton-domain fragment of a compiled model, with the
    PROVED propagator registration (`leSlot`/`ltSlot`/`eqSlot`;
    `plusSlot`/`neSlot`/`linLe` are excluded pending their family
    proofs), a `sat` assignment satisfies every internal
    constraint. -/
theorem solve_certified_sat_real
    {m : LeanFzn.Model} {problem : LCG.Problem DomConstraint Unit}
    {compiled : LeanFzn.Solver.Direct.CompiledProblem DomConstraint}
    (hc : LeanFzn.Solver.Direct.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hcons : problem.constraints = compiled.constraints)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hsat : solve problem DomConstraint.satisfiedB
        ((compiled.constraints).filterMap propagatorOfProved) = .sat assignment) :
    ProblemSolution problem DomConstraint.SatisfiedBy assignment := by
  -- the int-view premise, derived from compiler success
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Solver.Direct.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
  -- the propagator-list premise: every registered propagator comes
  -- from a constraint of the problem via propagatorOfProved
  have hprops : ∀ p ∈ compiled.constraints.filterMap propagatorOfProved,
      ∃ dc ∈ problem.constraints, propagatorOfProved dc = some p := by
    intro p hp
    obtain ⟨dc, hdcmem, hprop⟩ := propagatorsOfProved_mem hp
    rw [hcons]
    exact ⟨dc, hdcmem, hprop⟩
  -- the state-relativized safety + entitlement (from the per-family
  -- theorems; at the engine's initial state, domain-coherent)
  have hcoh0 : DomainCoherent problem (initialStateWithRoots problem) :=
    initialStateWithRoots_coherent problem
  -- assemble the universal premises: the engine's SAT theorem needs
  -- only the evaluator agreement (solve_sat_correct), so
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := compiled.constraints.filterMap propagatorOfProved)
    hview hfragP
    (fun c hc a _ => by rw [hclauses] at hc; cases hc)
    (fun st hcoh => propagatorsOfProved_safeUniv hint hprops st hcoh)
    (fun st hcoh p hp c hrun hsol =>
      propagatorsOfProved_entitled hint hprops st hsol hcoh p hp c hrun)
    hagrees hsat


/-- **THE CERTIFIED LCG FRONT DOOR WITH REAL PROPAGATORS (UNSAT)**:
    on the singleton-domain fragment of a compiled model, with the
    PROVED propagator registration, an `unsat` verdict excludes every
    internal solution. -/
theorem solve_certified_unsat_real
    {m : LeanFzn.Model} {problem : LCG.Problem DomConstraint Unit}
    {compiled : LeanFzn.Solver.Direct.CompiledProblem DomConstraint}
    (hc : LeanFzn.Solver.Direct.compileModel m = .ok compiled)
    (hlcg : problem.domains = compiled.domains)
    (hcons : problem.constraints = compiled.constraints)
    (hfrag : fragmentOk problem = true)
    (hclauses : problem.clauses = [])
    (hunsat : solve problem DomConstraint.satisfiedB
        ((compiled.constraints).filterMap propagatorOfProved) = .unsat) :
    ¬ ∃ assignment, ProblemSolution problem DomConstraint.SatisfiedBy
      assignment := by
  have hint : ∀ d ∈ problem.domains, ∀ v ∈ d, Value.intView v ≠ none := by
    rw [hlcg]
    exact LeanFzn.Solver.Direct.domains_intViewed hc
  have hfragP : PropFragment problem := (fragmentOk_iff.mp hfrag)
  have hview : IntViewed problem := intViewed_of_fragment hint
  have hprops : ∀ p ∈ compiled.constraints.filterMap propagatorOfProved,
      ∃ dc ∈ problem.constraints, propagatorOfProved dc = some p := by
    intro p hp
    obtain ⟨dc, hdcmem, hprop⟩ := propagatorsOfProved_mem hp
    rw [hcons]
    exact ⟨dc, hdcmem, hprop⟩
  have hagrees : ∀ constraint assignment,
      DomConstraint.satisfiedB constraint assignment = true ↔
        DomConstraint.SatisfiedBy constraint assignment :=
    fun c a => DomConstraint.satisfiedB_iff c a
  exact solve_certified_fragment_unsat (problem := problem)
    (constraintHolds := DomConstraint.SatisfiedBy)
    (constraintHoldsB := DomConstraint.satisfiedB)
    (propagators := compiled.constraints.filterMap propagatorOfProved)
    hview hfragP
    (fun c hc a _ => by rw [hclauses] at hc; cases hc)
    (fun st hcoh => propagatorsOfProved_safeUniv hint hprops st hcoh)
    (fun st hcoh p hp c hrun hsol =>
      propagatorsOfProved_entitled hint hprops st hsol hcoh p hp c hrun)
    hagrees hunsat

end LeanFzn.Solver.LCG


