/- Certified shared domain propagation kit. -/
import LeanFzn.Solver.Propagation.Proofs.BoxPropagators
import LeanFzn.Solver.Propagation.Proofs.Pruning
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.Reference


open LeanFzn.Solver.Propagation.DomainFiltering

namespace LeanFzn.Solver.Propagation
open LeanFzn LeanFzn.Solver.Core LeanFzn.Solver

/-- The only extra administrative gates check existing propagator proof
hypotheses: int-viewed domains, linear arity, the reified-`linLe`
operand range (PLAN L1b), the `all_different` operand range (PLAN L8,
consumed by the value eliminations' state-free reason obligation), and
(for the explained `neSlot`/`allDiff` conflict clauses) shape-typed
domains - every domain holds only integers or only Booleans. -/
def domPruningOkB (problem : Problem DomConstraint Unit) : Bool :=
  (problem.domains.all (fun d => d.all (fun v => v.intView != none)) &&
    problem.constraints.all (fun c => match c with
      | .linLe cs is _ | .linEq cs is _ => cs.length == is.length
      | .linLeReif cs is _ _ =>
          (is.all (fun i => decide (i < problem.domains.length)))
            && cs.length == is.length
      | .allDiff is =>
          is.all (fun i => decide (i < problem.domains.length))
      | _ => true)) &&
  problem.domains.all (fun d =>
    d.all (fun v => match v with | .int _ => true | _ => false) ||
    d.all (fun v => match v with | .bool _ => true | _ => false))

private theorem domPruningOk_core {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    (problem.domains.all (fun d => d.all (fun v => v.intView != none)) &&
    problem.constraints.all (fun c => match c with
      | .linLe cs is _ | .linEq cs is _ => cs.length == is.length
      | .linLeReif cs is _ _ =>
          (is.all (fun i => decide (i < problem.domains.length)))
            && cs.length == is.length
      | .allDiff is =>
          is.all (fun i => decide (i < problem.domains.length))
      | _ => true)) = true := by
  rw [domPruningOkB, Bool.and_eq_true] at h
  exact h.1

theorem domPruningOk_view {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) : IntViewedDoms problem.domains := by
  have h0 := domPruningOk_core h
  rw [Bool.and_eq_true] at h0
  have hd := h0.1
  intro d hdmem v hvmem
  have hv := List.all_eq_true.mp (List.all_eq_true.mp hd d hdmem) v hvmem
  simpa using hv

theorem domPruningOk_shape {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) : DomsShapeTyped problem.domains := by
  rw [domPruningOkB, Bool.and_eq_true] at h
  intro d hd
  have hs := List.all_eq_true.mp h.2 d hd
  rw [Bool.or_eq_true] at hs
  rcases hs with hs | hs
  · refine Or.inl fun v hv => ?_
    have := List.all_eq_true.mp hs v hv
    cases v <;> simp_all
  · refine Or.inr fun v hv => ?_
    have := List.all_eq_true.mp hs v hv
    cases v <;> simp_all

theorem domPruningOk_lin {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    (∀ c ∈ problem.constraints, ∀ cs is b,
      c = .linLe cs is b → cs.length = is.length) ∧
    (∀ c ∈ problem.constraints, ∀ cs is b,
      c = .linEq cs is b → cs.length = is.length) := by
  have h0 := domPruningOk_core h
  rw [Bool.and_eq_true] at h0
  have hc := h0.2
  constructor <;> intro c hmem cs is b heq <;> subst c
  all_goals simpa using List.all_eq_true.mp hc _ hmem

/-- PLAN L1b: the compiled reified-`linLe` shape - the operand slots of
    every `.linLeReif` are in range of the problem's box (the bounds arm's
    state-free reason obligation consumes exactly this fact). -/
theorem domPruningOk_lreif {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    ∀ dc ∈ problem.constraints, ∀ coeffs is b r,
      dc = .linLeReif coeffs is b r →
        ∀ i ∈ is, i < problem.domains.length := by
  have h0 := domPruningOk_core h
  rw [Bool.and_eq_true] at h0
  have hc := h0.2
  intro c hmem coeffs is b r heq i hi
  subst heq
  have h1 := List.all_eq_true.mp hc _ hmem
  rw [Bool.and_eq_true] at h1
  exact of_decide_eq_true (List.all_eq_true.mp h1.1 i hi)

/-- PLAN L8: the compiled `all_different` shape - the operand slots of
    every `.allDiff` are in range of the problem's box (the value
    eliminations' state-free reason obligation consumes exactly this
    fact). -/
theorem domPruningOk_lad {problem : Problem DomConstraint Unit}
    (h : domPruningOkB problem = true) :
    ∀ dc ∈ problem.constraints, ∀ is, dc = .allDiff is →
      ∀ i ∈ is, i < problem.domains.length := by
  have h0 := domPruningOk_core h
  rw [Bool.and_eq_true] at h0
  have hc := h0.2
  intro c hmem is heq i hi
  subst heq
  exact of_decide_eq_true (List.all_eq_true.mp
    (List.all_eq_true.mp hc _ hmem) i hi)

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
  have hr := domPruningOk_lreif h
  have hr2 := domPruningOk_lad h
  constructor
  · intro f hfv p hpm l r hr' a ha hfa
    exact (boxPropagators_safe hv hp hl.1 hl.2 (frameState f)
      (frameViewedB_view hfv)).1 p hpm l r hr' a (domLeaf_solution ha) hfa.fits
  · intro f hfv p hpm c hr' a ha hfa
    exact (boxPropagators_safe hv hp hl.1 hl.2 (frameState f)
      (frameViewedB_view hfv)).2 p hpm c hr' a (domLeaf_solution ha) hfa.fits
  · intro f _hfv p hpm l r hr' a ha
    exact (boxPropagators_reasons hv hp hl.1 hl.2 hr hr2 (frameState f) p hpm
      l r hr').1.1
      a (domLeaf_solution ha)
  · intro f _hfv p hpm c hr' hne a ha hfaith
    exact boxPropagators_conflicts hv hp hl.1 hl.2 (frameState f) p hpm c hr' hne
      a (domLeaf_solution ha) hfaith

/-- Registered proved CP propagators plus lazy explanation clauses. Ill-shaped
internal problems still receive safe clause propagation, without CP deductions. -/
def domPruningKit (problem : Problem DomConstraint Unit) :
    PruningKit (chronologicalLeaf problem DomConstraint.satisfiedB) :=
  if h : domPruningOkB problem = true then
    pruningKit _ problem.clauses (problem.constraints.filterMap propagatorOfProved)
      (domPropagationContract problem h) problem.domains
      (fun _ a ha =>
        frameFaithful_of_domSub (domPruningOk_view h) (domPruningOk_shape h)
          (domLeaf_solution ha).1 (DomSub.refl _))
  else
    pruningKit _ problem.clauses []
      { implied := by intros; contradiction
        conflict := by intros; contradiction
        reason := by intros; contradiction
        conflictReason := by intros; contradiction }
      problem.domains (fun hne => absurd rfl hne)

/-- Objective erasure changes no feasibility semantics. -/
def feasibilityProblem (problem : Problem DomConstraint Objective) : Problem DomConstraint Unit :=
  { names := problem.names, domains := problem.domains, constraints := problem.constraints,
    objective := (), clauses := problem.clauses }

end LeanFzn.Solver.Propagation
