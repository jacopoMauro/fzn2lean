/-
File: LeanFzn/Solver/UIP/Proofs/BudgetRun.lean

Purpose (PLAN F5): a FUEL-BUDGETED prefix of the certified phase driver.
`runPhaseBudget k fuel cfg` runs the SAME kernel step as
`runSupportedPhase` for at most `fuel` steps and reports

* `.sat w` / `.unsat` when the certified step reaches that terminal result,
* `.exhausted` when the budget runs out before a terminal result.

The budget is an OBSERVATION on the number of certified steps, not a second
search: the definition pattern-matches on `k.step` exactly like
`runSupportedPhase`, and its successor is the kernel's successor.  The two
soundness theorems `runPhaseBudget_sat` / `runPhaseBudget_unsat` prove that
every terminal result the budgeted prefix reports is the result of the
complete certified driver at the same configuration (using the kernel's
`reach` field only in the proof, never in the executable).  Hence a budgeted
restart that reports SAT/UNSAT keeps the caller's certified claim; an
`exhausted` budget supports no claim.

`runPhaseBudget_mono` records the driver fact the restart/portfolio
schedules consume: once a budget long enough to finish reports a terminal
result, every longer budget reports the same terminal result.

DAG: SupportedPhaseRun -> this file -> Integration budget/restart wrappers.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedPhaseRun

namespace LeanFzn.Solver.UIP

open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering

/-- The outcome of a fuel-budgeted certified run. `exhausted` is a summary of
the prefix, never a SAT/UNSAT claim. -/
inductive BudgetResult (leaf : Assignment → Bool) where
  /-- The certified step reached a satisfying assignment. -/
  | sat (w : Assignment)
  /-- The certified step closed the root box. -/
  | unsat
  /-- The budget ran out before a terminal result. -/
  | exhausted
  deriving Repr

variable {orig : List Domain} {original : List Clause} {props : List Propagator}
  {leaf : Assignment → Bool}

/-- Run at most `fuel` steps of the certified phase kernel. The recursion is
structural on the fuel; each step is the kernel's own `step` and successor,
so the prefix is a genuine certified run. At fuel 0 an already-terminal
configuration still reports its terminal result (no step is consumed). -/
def runPhaseBudget (k : SupportedPhaseKernel orig original props leaf) :
    Nat → SchedulerConfig leaf → BudgetResult leaf
  | 0, cfg =>
      match k.step cfg with
      | .sat w => .sat w
      | .unsat => .unsat
      | _ => .exhausted
  | n + 1, cfg =>
      match k.step cfg with
      | .sat w => .sat w
      | .unsat => .unsat
      | .propagate next => runPhaseBudget k n next
      | .decide next _ => runPhaseBudget k n next
      | .analyzeConflict next _ => runPhaseBudget k n next
      | .learnBackjumpAssert next _ _ => runPhaseBudget k n next
      | .localExclude next => runPhaseBudget k n next
      | .chronologicalFallback next => runPhaseBudget k n next

/-- The zero-fuel equation, definitional: an immediately terminal
configuration is still observed. -/
theorem runPhaseBudget_zero (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) :
    runPhaseBudget k 0 cfg =
      (match k.step cfg with
       | .sat w => .sat w
       | .unsat => .unsat
       | _ => .exhausted) := rfl

/-- The successor-fuel equation, definitional. -/
theorem runPhaseBudget_succ (k : SupportedPhaseKernel orig original props leaf)
    (n : Nat) (cfg : SchedulerConfig leaf) :
    runPhaseBudget k (n + 1) cfg =
      (match k.step cfg with
       | .sat w => .sat w
       | .unsat => .unsat
       | .propagate next => runPhaseBudget k n next
       | .decide next _ => runPhaseBudget k n next
       | .analyzeConflict next _ => runPhaseBudget k n next
       | .learnBackjumpAssert next _ _ => runPhaseBudget k n next
       | .localExclude next => runPhaseBudget k n next
       | .chronologicalFallback next => runPhaseBudget k n next) := rfl

/-- **SAT SOUNDNESS**: a budgeted prefix that reports `.sat w` reports the
complete certified driver's own result. -/
theorem runPhaseBudget_sat (k : SupportedPhaseKernel orig original props leaf)
    (fuel : Nat) (cfg : SchedulerConfig leaf)
    (hreach : SupportedReach orig original props cfg) (w : Assignment)
    (h : runPhaseBudget k fuel cfg = .sat w) :
    runSupportedPhase k cfg hreach = .sat w := by
  induction fuel generalizing cfg with
  | zero =>
      cases hstep : k.step cfg with
      | sat w' =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
          exact runSupportedPhase_sat k cfg hreach w hstep
      | unsat =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | propagate next =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | decide next l =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | analyzeConflict next c =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | learnBackjumpAssert next p an =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | localExclude next =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | chronologicalFallback next =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
  | succ n ih =>
      cases hstep : k.step cfg with
      | sat w' =>
          rw [runPhaseBudget_succ, hstep] at h
          cases h
          exact runSupportedPhase_sat k cfg hreach w hstep
      | unsat =>
          rw [runPhaseBudget_succ, hstep] at h
          cases h
      | propagate next =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_propagate k cfg hreach next hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | decide next l =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_decide k cfg hreach next l hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | analyzeConflict next c =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_analyzeConflict k cfg hreach next c hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | learnBackjumpAssert next p an =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_learnBackjumpAssert k cfg hreach next p an hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | localExclude next =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_localExclude k cfg hreach next hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | chronologicalFallback next =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_chronologicalFallback k cfg hreach next hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h

/-- **UNSAT SOUNDNESS**: a budgeted prefix that reports `.unsat` reports the
complete certified driver's own result. -/
theorem runPhaseBudget_unsat (k : SupportedPhaseKernel orig original props leaf)
    (fuel : Nat) (cfg : SchedulerConfig leaf)
    (hreach : SupportedReach orig original props cfg)
    (h : runPhaseBudget k fuel cfg = .unsat) :
    runSupportedPhase k cfg hreach = .unsat := by
  induction fuel generalizing cfg with
  | zero =>
      cases hstep : k.step cfg with
      | sat w' =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | unsat =>
          rw [runPhaseBudget_zero, hstep] at h
          exact runSupportedPhase_unsat k cfg hreach hstep
      | propagate next =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | decide next l =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | analyzeConflict next c =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | learnBackjumpAssert next p an =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | localExclude next =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
      | chronologicalFallback next =>
          rw [runPhaseBudget_zero, hstep] at h
          cases h
  | succ n ih =>
      cases hstep : k.step cfg with
      | sat w' =>
          rw [runPhaseBudget_succ, hstep] at h
          cases h
      | unsat =>
          rw [runPhaseBudget_succ, hstep] at h
          exact runSupportedPhase_unsat k cfg hreach hstep
      | propagate next =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_propagate k cfg hreach next hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | decide next l =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_decide k cfg hreach next l hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | analyzeConflict next c =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_analyzeConflict k cfg hreach next c hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | learnBackjumpAssert next p an =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_learnBackjumpAssert k cfg hreach next p an hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | localExclude next =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_localExclude k cfg hreach next hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h
      | chronologicalFallback next =>
          rw [runPhaseBudget_succ, hstep] at h
          rw [runSupportedPhase_chronologicalFallback k cfg hreach next hstep]
          exact ih next (k.reach cfg next hreach (by rw [hstep]; rfl)) h

/-- One more unit of fuel preserves an already-terminal result (the prefix is
deterministic and has already stopped). -/
theorem runPhaseBudget_succ_terminal (k : SupportedPhaseKernel orig original props leaf)
    {fuel : Nat} {cfg : SchedulerConfig leaf} {r : BudgetResult leaf}
    (hterm : r ≠ .exhausted)
    (h : runPhaseBudget k fuel cfg = r) :
    runPhaseBudget k (fuel + 1) cfg = r := by
  induction fuel generalizing cfg with
  | zero =>
      rw [runPhaseBudget_zero] at h
      rw [runPhaseBudget_succ]
      cases hstep : k.step cfg with
      | sat w =>
          rw [hstep] at h
          simpa using h
      | unsat =>
          rw [hstep] at h
          simpa using h
      | propagate next =>
          rw [hstep] at h
          cases h
          exact (hterm rfl).elim
      | decide next l =>
          rw [hstep] at h
          cases h
          exact (hterm rfl).elim
      | analyzeConflict next c =>
          rw [hstep] at h
          cases h
          exact (hterm rfl).elim
      | learnBackjumpAssert next p an =>
          rw [hstep] at h
          cases h
          exact (hterm rfl).elim
      | localExclude next =>
          rw [hstep] at h
          cases h
          exact (hterm rfl).elim
      | chronologicalFallback next =>
          rw [hstep] at h
          cases h
          exact (hterm rfl).elim
  | succ n ih =>
      rw [runPhaseBudget_succ] at h
      rw [runPhaseBudget_succ]
      cases hstep : k.step cfg with
      | sat w =>
          rw [hstep] at h
          simpa using h
      | unsat =>
          rw [hstep] at h
          simpa using h
      | propagate next =>
          rw [hstep] at h
          simpa using ih h
      | decide next l =>
          rw [hstep] at h
          simpa using ih h
      | analyzeConflict next c =>
          rw [hstep] at h
          simpa using ih h
      | learnBackjumpAssert next p an =>
          rw [hstep] at h
          simpa using ih h
      | localExclude next =>
          rw [hstep] at h
          simpa using ih h
      | chronologicalFallback next =>
          rw [hstep] at h
          simpa using ih h

/-- A terminal result is stable under a larger fuel budget: once the budgeted
prefix reports `.sat` or `.unsat`, every larger budget reports the same. -/
theorem runPhaseBudget_mono (k : SupportedPhaseKernel orig original props leaf)
    {fuel : Nat} {cfg : SchedulerConfig leaf} {r : BudgetResult leaf}
    (hterm : r ≠ .exhausted)
    (h : runPhaseBudget k fuel cfg = r) :
    ∀ extra : Nat, runPhaseBudget k (fuel + extra) cfg = r := by
  intro extra
  induction extra with
  | zero => simpa using h
  | succ extra ih =>
      rw [show fuel + (extra + 1) = (fuel + extra) + 1 by omega]
      exact runPhaseBudget_succ_terminal k hterm ih

end LeanFzn.Solver.UIP
