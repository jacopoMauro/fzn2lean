/-
Purpose: Legacy chronological instance of the generic optimizer interface.
Dependencies: Shared Optimization.Basic and the preserved legacy source solver.
DAG: generic optimization + legacy solve -> legacy optimizer adapters.
-/
import LeanFzn.Integration.Optimization.Basic
import LeanFzn.Legacy.Integration.Solve.Certified

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Compiler
open LeanFzn.Semantics.Globals LeanFzn.Solver.Propagation LeanFzn.Solver.Core LeanFzn.Compiler.Domains
open LeanFzn.Solver.Propagation.DomainFiltering

/-! ## The chronological certified solver as a `CertSolver` -/

/-- The verdict of the certified chronological solver on a compiled
    problem. -/
def chronVerdict (p : CompiledProblem DomConstraint) : CertVerdict :=
  if LeanFzn.Solver.Propagation.gateOk (toLCG p) then
    match LeanFzn.Solver.Chronological.solve (toLCG p) DomConstraint.satisfiedB
        (p.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
        (LeanFzn.Solver.Propagation.domPruningKit (toLCG p)) with
    | .sat a => .sat a
    | .unsat => .unsat
    | .unknown => .fail
  else .fail

theorem chronVerdict_sat {p : CompiledProblem DomConstraint} {a : List Value}
    (h : chronVerdict p = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold chronVerdict at h
  split at h
  · split at h
    · rename_i a' hsolve
      cases h
      have hps := LeanFzn.Solver.Chronological.solve_sat_correct
        (fun c a => DomConstraint.satisfiedB_iff c a) hsolve
      obtain ⟨hfits, hcholds⟩ := hps
      exact ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns hfits,
        List.all_eq_true.mpr (fun c hc2 =>
          (DomConstraint.satisfiedB_iff c a).mpr (hcholds c hc2))⟩
    · cases h
    · cases h
  · cases h

theorem chronVerdict_unsat {p : CompiledProblem DomConstraint}
    (h : chronVerdict p = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold chronVerdict at h
  split at h
  · split at h
    · cases h
    · rename_i hsolve
      have hnone := LeanFzn.Solver.Chronological.solve_pruned_unsat_correct
        (fun c a => DomConstraint.satisfiedB_iff c a)
        (fun c hc a hsol => LeanFzn.Compiler.seedClauses_satisfiedBy
          (fun dc hdc => hsol.2 dc hdc) c hc) hsolve
      intro b hb
      cases hacc : accepts p b with
      | false => rfl
      | true =>
          exfalso
          apply hnone
          refine ⟨b, ?_, fun c hc2 => ?_⟩
          · exact LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb
          · exact (DomConstraint.satisfiedB_iff c b).mp
              (List.all_eq_true.mp hacc c hc2)
    · cases h
  · cases h

/-- The certified chronological solver as a `CertSolver`.  It has no
    solution-guided presentation, so `solveWith` ignores the previous
    incumbent. -/
def chronSolver : CertSolver where
  solve := chronVerdict
  solveWith := fun _ p => chronVerdict p
  gate p := LeanFzn.Solver.Propagation.gateOk (toLCG p)
  sat_sound := fun _ _ h => chronVerdict_sat h
  solveWith_sat := fun _ _ _ h => chronVerdict_sat h
  unsat_complete := fun _ h => chronVerdict_unsat h
  solveWith_unsat := fun _ _ h => chronVerdict_unsat h
  gate_add := fun _ _ => rfl
  total := by
    intro p hg hfail
    unfold chronVerdict at hfail
    simp only [hg, if_true] at hfail
    split at hfail
    · cases hfail
    · cases hfail
    · rename_i hu
      exact LeanFzn.Solver.Chronological.solve_total (toLCG p) DomConstraint.satisfiedB
        (p.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
        (LeanFzn.Solver.Propagation.domPruningKit (toLCG p)) hu
  solveWith_total := by
    intro p prev hg hfail
    unfold chronVerdict at hfail
    simp only [hg, if_true] at hfail
    split at hfail
    · cases hfail
    · cases hfail
    · rename_i hu
      exact LeanFzn.Solver.Chronological.solve_total (toLCG p) DomConstraint.satisfiedB
        (p.constraints.filterMap LeanFzn.Solver.Propagation.propagatorOfProved)
        (LeanFzn.Solver.Propagation.domPruningKit (toLCG p)) hu


end LeanFzn.Integration
