/-
Purpose: Backend-independent sound partial search interface for branch-and-bound.
Dependencies: Optimization.Basic supplies verdicts and the existing optional-completeness interface.
DAG: shared compiler semantics -> partial oracle -> Core optimization.
The adapter explicitly supplies no completeness gate; all old generic theorems
remain unchanged, and completed runs retain their certified guarantees.
-/
import LeanFzn.Integration.Optimization.Basic

namespace LeanFzn.Integration
open LeanFzn LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation.DomainFiltering

/-- Sound SAT/UNSAT answers without an assumption that search always decides. -/
structure PartialCertSolver where
  solveWith : Option (List Value) → CompiledProblem DomConstraint → CertVerdict
  sat_sound : ∀ p prev a, solveWith prev p = .sat a →
    a ∈ allAssigns p.domains ∧ accepts p a = true
  unsat_sound : ∀ p prev, solveWith prev p = .unsat →
    ∀ b ∈ allAssigns p.domains, accepts p b = false

/-- Reuse the generic optimizer without claiming its optional completeness gate.
The false gate means exactly that no no-failure guarantee is provided. The
optimizer still runs, retains incumbents on failure, and certifies completed runs. -/
def PartialCertSolver.asCertSolver (S : PartialCertSolver) : CertSolver where
  solve := S.solveWith none
  solveWith := S.solveWith
  gate _ := false
  sat_sound := fun p a h => S.sat_sound p none a h
  solveWith_sat := S.sat_sound
  unsat_complete := fun p h => S.unsat_sound p none h
  solveWith_unsat := S.unsat_sound
  gate_add := fun _ _ => rfl
  total := by intro p h; simp at h
  solveWith_total := by intro p prev h; simp at h


end LeanFzn.Integration
