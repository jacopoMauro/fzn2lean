/-
File: LeanFzn/Integration/LcgOptimize.lean
Purpose: certified branch-and-bound using fuel-free LCG solving with certified fallback.
Dependencies: Optimize supplies the generic certified optimization driver; Lcg supplies
compiled SAT/UNSAT soundness and totality. The gate depends only on domains, so adding
objective improvement constraints preserves it even when the selected solver route changes.
DAG: Optimize + Lcg -> LcgOptimize -> CLI and optimization fixtures.
-/
import LeanFzn.Integration.Optimize
import LeanFzn.Integration.Lcg
import LeanFzn.Integration.LcgHeur

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering

/-- Map the compiled LCG result into the generic optimization interface. -/
def lcgVerdict (p : CompiledProblem DomConstraint) : CertVerdict :=
  match LcgHeur.solveCompiledLcgHeur p with
  | .sat a => .sat a
  | .unsat => .unsat
  | .unknown => .fail

theorem lcgVerdict_sat {p : CompiledProblem DomConstraint} {a : List Value}
    (h : lcgVerdict p = .sat a) : a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold lcgVerdict at h
  split at h
  · rename_i a' hs
    cases h
    exact LcgHeur.solveCompiledLcgHeur_sat hs
  · cases h
  · cases h

theorem lcgVerdict_unsat {p : CompiledProblem DomConstraint}
    (h : lcgVerdict p = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold lcgVerdict at h
  split at h
  · cases h
  · rename_i hs
    exact LcgHeur.solveCompiledLcgHeur_unsat hs
  · cases h

/-- LCG with certified fallback implements the certified optimizer's solver interface. -/
def lcgSolver : CertSolver where
  solve := lcgVerdict
  gate p := gateOk (lcgProblem p)
  sat_sound := fun _ _ h => lcgVerdict_sat h
  unsat_complete := fun _ h => lcgVerdict_unsat h
  gate_add := fun _ _ => rfl
  total := by
    intro p _ hfail
    unfold lcgVerdict at hfail
    split at hfail
    · cases hfail
    · cases hfail
    · rename_i hs
      exact LcgHeur.solveCompiledLcgHeur_verdict p hs

/-- The LCG-backed certified optimizer uses the shared fuel-free branch-and-bound loop. -/
def optimizeLcg (m : LeanFzn.Model) :
    Except String (CompiledProblem DomConstraint × OptRun) :=
  optimizeCertified lcgSolver m

end LeanFzn.Integration
