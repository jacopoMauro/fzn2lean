/- Contracts for the public chronological search strategy. -/
import LeanFzn.Solver.Chronological.Search
import LeanFzn.Solver.Propagation.Proofs.Frontier
import LeanFzn.Solver.Chronological.Proofs.Pruned
import LeanFzn.Solver.Chronological.Proofs.AnalysisDriver
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Chronological LeanFzn.Solver.Reference


namespace LeanFzn.Solver.Chronological
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-- SAT soundness for every proof-carrying pruning kit. -/
theorem solve_pruned_sat_correct
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator} {assignment : Assignment}
    {kit : PruningKit (chronologicalLeaf problem constraintHoldsB)}
    (hagrees : ∀ c a, constraintHoldsB c a = true ↔ constraintHolds c a)
    (hsolve : solve problem constraintHoldsB propagators kit = .sat assignment) :
    ProblemSolution problem constraintHolds assignment := by
  unfold solve solveWithStats at hsolve
  cases hr : (analyzedSolve (chronologicalLeaf problem constraintHoldsB) kit
      [(problem.domains, [])] problem.clauses {}).1 with
  | sat a =>
    simp only [hr, Prod.fst, SearchResult.sat.injEq] at hsolve
    subst assignment
    have hl := analyzedSolve_sat_leaf _ kit _ _ _ a hr
    rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true] at hl
    exact ⟨fitsB_iff.mp hl.1, fun c hc =>
      (hagrees c a).mp (List.all_eq_true.mp hl.2.1 c hc)⟩
  | unsat => simp [hr] at hsolve

/-- UNSAT soundness for every pruning kit, with original-clause entailment. -/
theorem solve_pruned_unsat_correct
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator}
    {kit : PruningKit (chronologicalLeaf problem constraintHoldsB)}
    (hagrees : ∀ c a, constraintHoldsB c a = true ↔ constraintHolds c a)
    (hdb : ∀ c ∈ problem.clauses, ∀ a, ProblemSolution problem constraintHolds a →
      ∃ l ∈ c, l.eval a = some true)
    (hsolve : solve problem constraintHoldsB propagators kit = .unsat) :
    ¬ ∃ a, ProblemSolution problem constraintHolds a := by
  rintro ⟨a,hfit,hcons⟩
  have he : EntailedDB (chronologicalLeaf problem constraintHoldsB) problem.clauses := by
    intro c hc b hb
    rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true] at hb
    exact hdb c hc b ⟨fitsB_iff.mp hb.1, fun d hd =>
      (hagrees d b).mp (List.all_eq_true.mp hb.2.1 d hd)⟩
  have ht : chronologicalLeaf problem constraintHoldsB a = true := by
    rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true]
    refine ⟨fitsB_iff.mpr hfit, List.all_eq_true.mpr (fun c hc => (hagrees c a).mpr (hcons c hc)), ?_⟩
    apply List.all_eq_true.mpr
    intro c hc
    obtain ⟨l,hl,hev⟩ := hdb c hc a ⟨hfit,hcons⟩
    exact List.any_eq_true.mpr ⟨l,hl,decide_eq_true hev⟩
  unfold solve solveWithStats at hsolve
  cases hr : (analyzedSolve (chronologicalLeaf problem constraintHoldsB) kit
      [(problem.domains, [])] problem.clauses {}).1 with
  | sat b => simp [hr] at hsolve
  | unsat =>
    have hf := analyzedSolve_unsat_excludes _ kit _ _ _ he hr a
      ⟨(problem.domains,[]), List.mem_singleton_self _, a,
        frontier_fits_mem_allAssigns _ _ hfit, by simp⟩
    rw [ht] at hf
    cases hf

/-- Every pruning kit has a total SAT/UNSAT verdict without fuel. -/
theorem solve_total (problem : LeanFzn.Solver.Propagation.Problem Constraint Objective)
    (holdsB : Constraint → Assignment → Bool) (props : List Propagator)
    (kit : PruningKit (chronologicalLeaf problem holdsB) := identityPruningKit _) :
    solve problem holdsB props kit ≠ .unknown := by
  unfold solve solveWithStats
  cases hr : (analyzedSolve (chronologicalLeaf problem holdsB) kit
    [(problem.domains, [])] problem.clauses {}).1 <;> simp [hr]

/-- A SAT result is an internal problem solution. -/
theorem solve_sat_correct
    {problem : LeanFzn.Solver.Propagation.Problem Constraint Objective}
    {constraintHolds : Constraint → Assignment → Prop}
    {constraintHoldsB : Constraint → Assignment → Bool}
    {propagators : List Propagator}
    {kit : PruningKit (chronologicalLeaf problem constraintHoldsB)} {assignment : Assignment}
    (hagrees : ∀ constraint assignment,
      constraintHoldsB constraint assignment = true ↔
        constraintHolds constraint assignment)
    (hsolve : solve problem constraintHoldsB propagators kit = .sat assignment) :
    ProblemSolution problem constraintHolds assignment := by
  exact solve_pruned_sat_correct hagrees hsolve


end LeanFzn.Solver.Chronological
