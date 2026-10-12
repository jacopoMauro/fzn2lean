/- Certified shared domain propagation kit. -/
import LeanFzn.Solver.Propagation.Proofs.BoxPropagators
import LeanFzn.Solver.Propagation.Proofs.Pruning
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

/-- The only extra administrative gate checks existing propagator proof hypotheses. -/
def domPruningOkB (problem : Problem DomConstraint Unit) : Bool :=
  problem.domains.all (fun d => d.all (fun v => v.intView != none)) &&
    problem.constraints.all (fun c => match c with
      | .linLe cs is _ | .linEq cs is _ => cs.length == is.length
      | _ => true)

theorem domPruningOk_view {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) : IntViewedDoms problem.domains := by
  rw [domPruningOkB, Bool.and_eq_true] at h
  have hd := h.1
  intro d hdmem v hvmem
  have hv := List.all_eq_true.mp (List.all_eq_true.mp hd d hdmem) v hvmem
  simpa using hv

theorem domPruningOk_lin {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    (∀ c ∈ problem.constraints, ∀ cs is b,
      c = .linLe cs is b → cs.length = is.length) ∧
    (∀ c ∈ problem.constraints, ∀ cs is b,
      c = .linEq cs is b → cs.length = is.length) := by
  rw [domPruningOkB, Bool.and_eq_true] at h
  have hc := h.2
  constructor <;> intro c hmem cs is b heq <;> subst c
  all_goals simpa using List.all_eq_true.mp hc _ hmem

theorem frameViewedB_view {f : BranchFrame} (h : frameViewedB f = true) :
    IntViewedDoms (frameState f).domains := by
  intro d hd v hv
  have hh := List.all_eq_true.mp (List.all_eq_true.mp h d hd) v hv
  simpa using hh

theorem domLeaf_solution {problem : Problem DomConstraint Unit} {a : Assignment}
    (h : chronologicalLeaf problem DomConstraint.satisfiedB a = true) :
    ProblemSolution problem DomConstraint.SatisfiedBy a := by
  rw [chronologicalLeaf, Bool.and_eq_true, Bool.and_eq_true] at h
  obtain ⟨hf, hc, _⟩ := h
  refine ⟨fitsB_iff.mp hf, ?_⟩
  intro c hmem
  exact (DomConstraint.satisfiedB_iff c a).mp
    (List.all_eq_true.mp hc c hmem)

/-- All pruning and explanation entailment comes from the existing family proofs. -/
theorem domPropagationContract (problem : Problem DomConstraint Unit)
    (h : domPruningOkB problem = true) :
    PropagationContract (chronologicalLeaf problem DomConstraint.satisfiedB)
      (problem.constraints.filterMap propagatorOfProved) := by
  have hp : ∀ p ∈ problem.constraints.filterMap propagatorOfProved,
      ∃ c ∈ problem.constraints, propagatorOfProved c = some p := by
    intro p hmem
    exact List.mem_filterMap.mp hmem
  have hv := domPruningOk_view h
  have hl := domPruningOk_lin h
  constructor
  · intro f hfv p hpm l r hr a ha hfa
    exact (boxPropagators_safe hv hp hl.1 hl.2 (frameState f)
      (frameViewedB_view hfv)).1 p hpm l r hr a (domLeaf_solution ha) hfa.fits
  · intro f hfv p hpm c hr a ha hfa
    exact (boxPropagators_safe hv hp hl.1 hl.2 (frameState f)
      (frameViewedB_view hfv)).2 p hpm c hr a (domLeaf_solution ha) hfa.fits
  · intro f _hfv p hpm l r hr a ha
    exact (boxPropagators_reasons hv hp hl.1 hl.2 (frameState f) p hpm l r hr).1.1
      a (domLeaf_solution ha)
  · intro f _hfv p hpm c hr hne a ha
    exact boxPropagators_conflicts hv hp hl.1 hl.2 (frameState f) p hpm c hr hne
      a (domLeaf_solution ha)

/-- Registered proved CP propagators plus lazy explanation clauses. Ill-shaped
internal problems still receive safe clause propagation, without CP deductions. -/
def domPruningKit (problem : Problem DomConstraint Unit) :
    PruningKit (chronologicalLeaf problem DomConstraint.satisfiedB) :=
  if h : domPruningOkB problem = true then
    pruningKit _ problem.clauses (problem.constraints.filterMap propagatorOfProved)
      (domPropagationContract problem h)
  else
    pruningKit _ problem.clauses []
      { implied := by intros; contradiction
        conflict := by intros; contradiction
        reason := by intros; contradiction
        conflictReason := by intros; contradiction }

/-- Objective erasure changes no feasibility semantics. -/
def feasibilityProblem (problem : Problem DomConstraint Objective) : Problem DomConstraint Unit :=
  { names := problem.names, domains := problem.domains, constraints := problem.constraints,
    objective := (), clauses := problem.clauses }

end LeanFzn.Solver.Propagation
