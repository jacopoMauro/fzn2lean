/-
File: LeanFzn/Integration/Optimization/KernelSeedBudget.lean

Purpose (PLAN F5): the FUEL-BUDGETED seeded LCG entry.  `lcgSeedRunBudget p s hg
prio actBump fuel` is `BudgetRun.runPhaseBudget` instantiated at the EXACT
kernel and initializer of `LcgSeed.lcgSeedRun`:

* the kernel is `LcgPhaseKernel.supportedPhaseKernel` on the seeded clause base
  `seedClauses p.constraints ++ s.clauses` and the same `lcgProps p`;
* the initializer is `SchedulerConfig.init` with the same priority vector and
  activity-bump toggle.

Hence the budgeted run is a prefix of the deterministic certified seeded solve,
not a second search.  `lcgSeedRunBudget_sat_run` / `_unsat_run` identify every
terminal budget result with the complete run's verdict, and
`lcgSeedRunBudget_sat` / `_unsat` state the problem-level consequences that the
budgeted solver instance needs (`SeedCertSolver.sat_sound_db` /
`unsat_complete_db`).  An `.exhausted` result supports NO claim.

DAG: LcgSeed + LcgSeedConfig + UIP BudgetRun -> this file -> OptimizeBudget.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Integration.Optimization.KernelSeed
import LeanFzn.Legacy.Integration.Optimization.KernelSeedConfig
import LeanFzn.Legacy.Solver.UIP.Proofs.BudgetRun

namespace LeanFzn.Integration
open LeanFzn.Semantics LeanFzn.Compiler LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.LcgSeedClauses LeanFzn.Solver.UIP.LcgPhaseRunDb
open LeanFzn.Solver.UIP.LcgCanonicalClauses

/-! ## §1 The seeded kernel and initializer (shared with `lcgSeedRun`) -/

/-- The mixed-kit frame gate of the seeded problem.  This is the same term
`lcgSeedRun` hands to `solveCfg`. -/
theorem lcgSeedFrameGate {p : CompiledProblem DomConstraint} {s : SeedDb p.domains}
    (hg : lcgRouteGateMixed p = true) :
    ∀ {cfg : SchedulerConfig (lcgLeafSeed p s)},
      SupportedReach p.domains (seedClauses p.constraints ++ s.clauses)
        (lcgProps p) cfg → FrameNonempty cfg :=
  lcgFrameGate_of_routeGate (original := seedClauses p.constraints ++ s.clauses)
    (props := lcgProps p) hg

/-- The kernel of the seeded run: exactly the kernel `lcgSeedRun` uses through
`LcgPhaseRunDb.solveCfg`. -/
def lcgSeedKernel (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) :
    SupportedPhaseKernel p.domains (seedClauses p.constraints ++ s.clauses)
      (lcgProps p) (lcgLeafSeed p s) :=
  LcgPhaseKernel.supportedPhaseKernel p.domains
    (seedClauses p.constraints ++ s.clauses) (lcgProps p) (lcgSeedFrameGate hg)

/-- The initializer of the seeded run: exactly `SchedulerConfig.init` at the
seeded clause base. -/
def lcgSeedInit (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (prio : List Nat := []) (actBump : Bool := false) :
    SchedulerConfig (lcgLeafSeed p s) :=
  SchedulerConfig.init p.domains (seedClauses p.constraints ++ s.clauses)
    (lcgProps p) prio actBump

/-- The seeded kernel dispatches by the real phase function: the budgeted
recursion consumes the certified `phaseNext` step, never a copy of it. -/
theorem lcgSeedKernel_step (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) :
    (lcgSeedKernel p s hg).step = phaseNext :=
  LcgPhaseKernel.supportedPhaseKernel_step _ _ _ _

/-- The initializer is supported-reachable from the seeded clause base
(entailment of the appended base is the seeded leaf's own conjunct). -/
theorem lcgSeedInit_reach (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (prio : List Nat := []) (actBump : Bool := false) :
    SupportedReach p.domains (seedClauses p.constraints ++ s.clauses) (lcgProps p)
      (lcgSeedInit p s prio actBump) :=
  SupportedReach.init (lcgLeafSeed_entailed p s)

/-! ## §2 The budgeted seeded run -/

/-- **THE FUEL-BUDGETED SEEDED RUN.**  `runPhaseBudget` at the same kernel and
initializer as `lcgSeedRun`: the returned `.sat`/`.unsat` is a terminal result
of the deterministic seeded solve (the complete run reaches the same state
after the same steps), and `.exhausted` is only a prefix summary. -/
def lcgSeedRunBudget (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true)
    (prio : List Nat := []) (actBump : Bool := false) (fuel : Nat) :
    BudgetResult (lcgLeafSeed p s) :=
  runPhaseBudget (lcgSeedKernel p s hg) fuel (lcgSeedInit p s prio actBump)

/-- Unfolding: the budgeted seeded run is `runPhaseBudget` at the seeded
kernel and initializer, definitionally. -/
theorem lcgSeedRunBudget_unfold (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) (prio : List Nat := []) (actBump : Bool := false)
    (fuel : Nat) :
    lcgSeedRunBudget p s hg prio actBump fuel =
      runPhaseBudget (lcgSeedKernel p s hg) fuel (lcgSeedInit p s prio actBump) := rfl

/-- A terminal budgeted result is the COMPLETE seeded run's verdict (the
budgeted recursion is the complete run's prefix). -/
theorem lcgSeedRunBudget_sat_run (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) (prio : List Nat := []) (actBump : Bool := false)
    {fuel : Nat} {w : Assignment}
    (hrun : lcgSeedRunBudget p s hg prio actBump fuel = .sat w) :
    (lcgSeedRun p s hg prio actBump).1 = .sat w := by
  have hreach := lcgSeedInit_reach (p := p) (s := s) prio actBump
  have hterm := runPhaseBudget_sat (lcgSeedKernel p s hg) fuel
    (lcgSeedInit p s prio actBump) hreach w hrun
  have hfst := runSupportedPhaseDb_fst (lcgSeedKernel p s hg)
    (lcgSeedInit p s prio actBump) hreach
  rw [lcgSeedRun, solveCfg]
  exact hfst.trans hterm

/-- A terminal budgeted UNSAT result is the COMPLETE seeded run's verdict. -/
theorem lcgSeedRunBudget_unsat_run (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) (prio : List Nat := []) (actBump : Bool := false)
    {fuel : Nat}
    (hrun : lcgSeedRunBudget p s hg prio actBump fuel = .unsat) :
    (lcgSeedRun p s hg prio actBump).1 = .unsat := by
  have hreach := lcgSeedInit_reach (p := p) (s := s) prio actBump
  have hterm := runPhaseBudget_unsat (lcgSeedKernel p s hg) fuel
    (lcgSeedInit p s prio actBump) hreach hrun
  have hfst := runSupportedPhaseDb_fst (lcgSeedKernel p s hg)
    (lcgSeedInit p s prio actBump) hreach
  rw [lcgSeedRun, solveCfg]
  exact hfst.trans hterm

/-- **SAT SOUNDNESS OF A BUDGETED SEEDED RUN**: a terminal `.sat w` is an
accepted assignment of the compiled box with the reported witness. -/
theorem lcgSeedRunBudget_sat (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) (prio : List Nat := []) (actBump : Bool := false)
    {fuel : Nat} {w : Assignment}
    (hrun : lcgSeedRunBudget p s hg prio actBump fuel = .sat w) :
    w ∈ allAssigns p.domains ∧ accepts p w = true := by
  have hsatrun := lcgSeedRunBudget_sat_run p s hg prio actBump hrun
  have hsolve : LcgPhaseKernel.solve p.domains
      (seedClauses p.constraints ++ s.clauses) (lcgProps p)
      (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump = .sat w := by
    rw [lcgSeedRun, solveCfg] at hsatrun
    exact (runSupportedPhaseDb_fst (lcgSeedKernel p s hg)
      (lcgSeedInit p s prio actBump)
      (lcgSeedInit_reach (p := p) (s := s) prio actBump)).symm.trans hsatrun
  have hdb : (solveDb (leaf := lcgLeafSeed p s) p.domains
      (seedClauses p.constraints ++ s.clauses) (lcgProps p)
      (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump).1 = .sat w :=
    (solveDb_fst (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump).trans hsolve
  have hsol := solveDb_sat_solution_of_kit_mixed (lcgKitSeed (s := s) hg)
    (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump hdb
  have hcons : (p.constraints.all fun c => c.satisfiedB w) = true := by
    have h := hsol.1
    simp only [lcgLeafSeed, chronologicalLeaf, lcgProblemSeed, Bool.and_eq_true] at h
    exact h.2.1
  exact ⟨LeanFzn.Solver.UIP.fits_mem_allAssigns hsol.2, hcons⟩

/-- **UNSAT COMPLETENESS OF A BUDGETED SEEDED RUN**: a terminal `.unsat`
excludes every accepted assignment of the box, given that the carried database
is entailed at the problem's own leaf. -/
theorem lcgSeedRunBudget_unsat (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) (prio : List Nat := []) (actBump : Bool := false)
    {fuel : Nat} (hrun : lcgSeedRunBudget p s hg prio actBump fuel = .unsat)
    (hseed : LearnedEntailed (lcgLeaf p) s.clauses) :
    ∀ b ∈ allAssigns p.domains, accepts p b = false := by
  intro b hb
  by_cases hacc : accepts p b = true
  · have hunsatrun := lcgSeedRunBudget_unsat_run p s hg prio actBump hrun
    have hsolve : LcgPhaseKernel.solve p.domains
        (seedClauses p.constraints ++ s.clauses) (lcgProps p)
        (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump = .unsat := by
      rw [lcgSeedRun, solveCfg] at hunsatrun
      exact (runSupportedPhaseDb_fst (lcgSeedKernel p s hg)
        (lcgSeedInit p s prio actBump)
        (lcgSeedInit_reach (p := p) (s := s) prio actBump)).symm.trans hunsatrun
    have hdb : (solveDb (leaf := lcgLeafSeed p s) p.domains
        (seedClauses p.constraints ++ s.clauses) (lcgProps p)
        (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump).1 = .unsat :=
      (solveDb_fst (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump).trans hsolve
    have hex := solveDb_unsat_excludes_of_kit_mixed (lcgKitSeed (s := s) hg)
      (lcgLeafSeed_entailed p s) (lcgSeedFrameGate hg) prio actBump hdb
    have hleaves : OriginalLeaves (lcgLeafSeed p s) p.domains b :=
      ⟨lcgLeafSeed_of_accepts hseed hb hacc,
        LeanFzn.Solver.Propagation.allAssigns_fits p.domains b hb⟩
    exact (hex b hleaves).elim
  · cases hh : accepts p b with
    | false => rfl
    | true => exact absurd hh hacc

/-- A terminal budgeted result is stable under a larger budget: once the
prefix reaches SAT/UNSAT, more fuel reports the same result.  This is the
restart/portfolio stability fact (a probe that finishes is the answer). -/
theorem lcgSeedRunBudget_mono (p : CompiledProblem DomConstraint) (s : SeedDb p.domains)
    (hg : lcgRouteGateMixed p = true) (prio : List Nat := []) (actBump : Bool := false)
    {fuel : Nat} {r : BudgetResult (lcgLeafSeed p s)} (hterm : r ≠ .exhausted)
    (h : lcgSeedRunBudget p s hg prio actBump fuel = r) :
    ∀ extra : Nat, lcgSeedRunBudget p s hg prio actBump (fuel + extra) = r := by
  intro extra
  exact runPhaseBudget_mono (lcgSeedKernel p s hg) hterm h extra

end LeanFzn.Integration
