/-
File: LeanFzn/Integration/Optimization/Kernel.lean
Purpose: certified branch-and-bound using fuel-free LCG solving with certified fallback.
Dependencies: Optimize supplies the generic certified optimization driver; Lcg supplies
compiled SAT/UNSAT soundness and totality. The gate depends only on domains, so adding
objective improvement constraints preserves it even when the selected solver route changes.
DAG: Optimize + Lcg -> LcgOptimize -> CLI and optimization fixtures.
-/
import LeanFzn.Integration.Optimization.Basic
import LeanFzn.Legacy.Integration.Optimization.Chronological
import LeanFzn.Legacy.Integration.Kernel.Annot
import LeanFzn.Legacy.Integration.Kernel.Lcg

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering

/-- Map the compiled LCG result into the generic optimization interface. -/
def lcgVerdict (p : CompiledProblem DomConstraint) (o : SearchConfig := {}) :
    CertVerdict :=
  match solveSearchConfig p o with
  | .sat a => .sat a
  | .unsat => .unsat
  | .unknown => .fail

/-- The phase-aware variant: the previous round's incumbent is passed to the
    F3 solution-guided value presentation. -/
def lcgVerdictWith (prev : Option (List Value))
    (p : CompiledProblem DomConstraint) (o : SearchConfig := {}) :
    CertVerdict :=
  match solveSearchConfigWith p o prev with
  | .sat a => .sat a
  | .unsat => .unsat
  | .unknown => .fail

theorem lcgVerdict_sat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    {a : List Value} (h : lcgVerdict p o = .sat a) : a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold lcgVerdict at h
  split at h
  · rename_i a' hs
    cases h
    exact solveSearchConfig_sat hs
  · cases h
  · cases h

theorem lcgVerdict_unsat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    (h : lcgVerdict p o = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold lcgVerdict at h
  split at h
  · cases h
  · rename_i hs
    exact solveSearchConfig_unsat hs
  · cases h

theorem lcgVerdictWith_sat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    {prev : Option (List Value)} {a : List Value}
    (h : lcgVerdictWith prev p o = .sat a) :
    a ∈ allAssigns p.domains ∧ accepts p a = true := by
  unfold lcgVerdictWith at h
  split at h
  · rename_i a' hs
    cases h
    exact solveSearchConfigWith_sat hs
  · cases h
  · cases h

theorem lcgVerdictWith_unsat {o : SearchConfig} {p : CompiledProblem DomConstraint}
    {prev : Option (List Value)}
    (h : lcgVerdictWith prev p o = .unsat) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  unfold lcgVerdictWith at h
  split at h
  · cases h
  · rename_i hs
    exact solveSearchConfigWith_unsat hs
  · cases h

theorem lcgVerdictWith_fail_free {o : SearchConfig} {p : CompiledProblem DomConstraint}
    {prev : Option (List Value)} (h : lcgVerdictWith prev p o = .fail) : False := by
  unfold lcgVerdictWith at h
  split at h
  · cases h
  · cases h
  · rename_i hs
    exact solveSearchConfigWith_verdict p o prev hs

/-- LCG with certified fallback implements the certified optimizer's solver
    interface, for any heuristic options `o`. -/
def lcgSolver (o : SearchConfig := {}) : CertSolver where
  solve p := lcgVerdict p o
  solveWith prev p := lcgVerdictWith prev p o
  gate p := gateOk (lcgProblem p)
  sat_sound := fun _ _ h => lcgVerdict_sat h
  solveWith_sat := fun _ _ _ h => lcgVerdictWith_sat h
  unsat_complete := fun _ h => lcgVerdict_unsat h
  solveWith_unsat := fun _ _ h => lcgVerdictWith_unsat h
  gate_add := fun _ _ => rfl
  total := by
    intro p _ hfail
    unfold lcgVerdict at hfail
    split at hfail
    · cases hfail
    · cases hfail
    · rename_i hs
      exact solveSearchConfig_verdict p o hs
  solveWith_total := by
    intro p prev _ hfail
    exact lcgVerdictWith_fail_free hfail

/-- The LCG-backed certified optimizer uses the shared fuel-free branch-and-bound loop. -/
def optimizeLcg (m : LeanFzn.Model) (o : SearchConfig := {}) :
    Except String (CompiledProblem DomConstraint × OptRun) :=
  optimizeCertified (lcgSolver o) m

end LeanFzn.Integration
