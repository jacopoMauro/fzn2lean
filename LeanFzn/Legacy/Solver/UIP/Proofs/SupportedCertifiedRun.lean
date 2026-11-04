/-
File: LeanFzn/Solver/UIP/Proofs/SupportedCertifiedRun.lean

Purpose: the computable SUPPORTED entry point and its verdict transfers.
This composes the S2 pieces into the shape D0/D1 consume, on exactly one
supported run:

  §1 `SupportedPhasePremises (orig) (original) (props) (leaf)` — the
     explicit SELF-INDEXED premise bundle (`halignDB`, `hdb`, `hbr`).
  §2 `supportedPhaseKernelOf` — the sorted supported kernel built from a
     premise bundle (via `supportedPhaseProgressSorted_of_premises`).
  §3 `solveSupportedPhase` — the computable entry at the run's real
     initializer (`SchedulerConfig.init orig original props`,
     `SupportedReach.init`).
  §4 `solveSupportedPhase_sat_solution` / `_unsat_excludes` / `_total` —
     the verdict transfers via the `runSupportedPhase` lifts, with the
     supported terminal obligations as explicit hypotheses (the D0-level
     residual: they become theorems once B2b/B3b/B4/C1 produce the gate
     record and the run assembly's site wrappers are ported).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedCertifiedRun` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedPhaseRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference
open LeanFzn.Solver.UIP.P4 (PhaseRankSorted)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C3b

/-! ## §1 The supported premise bundle -/

/-- The explicit premise bundle of ONE supported run: database-side literal
pool alignment (C1), novelty of the recorded analysis (restated by R1c from the unfalsified database, C1/S5), branch reachability
(B4 via `supportedHbr_of_gates`). All self-indexed, so each has a producer
for the run. -/
structure SupportedPhasePremises (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop where
  halignDB : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool orig
  hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
    ReachableState leaf orig cfg.branch
  /-- S0 §3.5 frame-shape gate (owner D1/runtime): no reachable branch's
  box has an empty domain, so the S1 decide/skip rank decrease holds. -/
  hgate : ∀ {cfg : SchedulerConfig leaf},
    SupportedReach orig original props cfg →
    ∀ e ∈ cfg.branch.frame.doms, Dom.enum e ≠ []

/-! ## §2 The sorted supported kernel -/

/-- The sorted supported kernel of a premise bundle. -/
def supportedPhaseKernelOf {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf) :
    SupportedPhaseKernel orig original props leaf :=
  supportedPhaseKernelSorted
    (supportedPhaseProgressSorted_of_premises orig original props
      P.halignDB P.hbr P.hgate)

/-! ## §3 The computable supported entry -/

/-- **THE SUPPORTED COMPUTABLE ENTRY**: the ranked driver over the sorted
supported kernel, started at the run's real initializer. No fuel, no axiom;
the kernel's proof fields are erased. -/
def solveSupportedPhase {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf)
    (hent : LearnedEntailed leaf original) : DriverResult leaf :=
  runSupportedPhase (supportedPhaseKernelOf P)
    (SchedulerConfig.init (leaf := leaf) orig original props)
    (SupportedReach.init hent)

/-! ## §4 The verdict transfers -/

/-- **SUPPORTED SAT TRANSFER**: a `.sat` verdict of the supported entry is a
solution witness of the run's box/leaf. The terminal obligation is the
supported phase-level obligation (D0's residual, produced by the run
assembly once the gate record exists). -/
theorem solveSupportedPhase_sat_solution {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf)
    (hent : LearnedEntailed leaf original)
    (hterm_sat : ∀ (cfg : SchedulerConfig leaf) (w : Assignment),
      SupportedReach orig original props cfg → cfg.orig = orig →
        (supportedPhaseKernelOf P).step cfg = .sat w →
          SolutionWitness leaf orig w)
    {w : Assignment} (hrun : solveSupportedPhase P hent = .sat w) :
    SolutionWitness leaf orig w :=
  runSupportedPhase_sat_solution (supportedPhaseKernelOf P) hterm_sat
    (SchedulerConfig.init (leaf := leaf) orig original props)
    (SupportedReach.init hent) hrun

/-- **SUPPORTED UNSAT TRANSFER**: a `.unsat` verdict of the supported entry
excludes every leaf solution of the run's box. -/
theorem solveSupportedPhase_unsat_excludes {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf)
    (hent : LearnedEntailed leaf original)
    (hterm_unsat : ∀ (cfg : SchedulerConfig leaf),
      SupportedReach orig original props cfg → cfg.orig = orig →
        (supportedPhaseKernelOf P).step cfg = .unsat →
          ∀ a, OriginalLeaves leaf orig a → False)
    (hrun : solveSupportedPhase P hent = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False :=
  runSupportedPhase_unsat_excludes (supportedPhaseKernelOf P) hterm_unsat
    (SchedulerConfig.init (leaf := leaf) orig original props)
    (SupportedReach.init hent) hrun

/-- **TOTALITY**: the supported entry returns a verdict on every premise
bundle — pure well-founded recursion, no fuel and no runtime contract. -/
theorem solveSupportedPhase_total {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf)
    (hent : LearnedEntailed leaf original) :
    ∃ r : DriverResult leaf, solveSupportedPhase P hent = r :=
  ⟨_, rfl⟩

/-- The entry's kernel steps by the REAL phase dispatcher (definitional). -/
theorem supportedPhaseKernelOf_step {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (P : SupportedPhasePremises orig original props leaf) :
    (supportedPhaseKernelOf P).step = phaseNext := rfl

end LeanFzn.Solver.UIP
