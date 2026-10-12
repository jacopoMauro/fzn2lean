/-
File: LeanFzn/Solver/UIP/Proofs/SupportedRunAssembly.lean

Purpose: the supported-run terminal wrappers — the D0 layer's site theorem
shapes at S1's root-indexed execution. Everything is indexed by
`SupportedReach orig original props`, so each hypothesis is a fact about
exactly one run (no all-roots quantification):

  §1 `SupportedDeadEvidence` — the dead-site evidence of one supported run
     (the supported counterpart of `RunAssembly.ReachableDeadEvidence`).
  §2 `supportedPhaseNext_sat_solution` — a supported `.sat` outcome is a
     solution witness of the run's box (via the supported branch invariant).
  §3 `supportedPhaseNext_unsat_excludes` — a supported `.unsat` outcome
     excludes every leaf solution of the run's box: the exhausted-frontier
     sites by the supported invariant discipline + dead evidence, the
     level-0 conflict route by `rootConflictExcludes_of_terminalEvent` from
     the ACTUAL terminal event.

These are exactly the terminal obligations
`SupportedCertifiedRun.solveSupportedPhase_{sat_solution,unsat_excludes}`
consume (with `(supportedPhaseKernelOf P).step = phaseNext` definitionally).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedRunAssembly` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedArms
import LeanFzn.Solver.UIP.Proofs.SchedulerRunAssembly
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C2d
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.RunAssembly

/-! ## §1 The supported dead-site evidence -/

/-- The dead-site evidence of ONE supported run: a dead configuration has
no leaf solution inside its frame. (Producer: the B3b dead-site
infrastructure at the supported index.) -/
def SupportedDeadEvidence (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop :=
  ∀ {d : SchedulerConfig leaf}, SupportedReach orig original props d →
    d.status = .dead →
      ∀ a, leaf a = true → FrameCovers d.branch.frame a → False

/-! ## §2 The supported SAT terminal -/

/-- **SUPPORTED SAT TERMINAL**: a `.sat` outcome of the phase dispatcher at
a supported configuration is a solution witness of the run's box. -/
theorem supportedPhaseNext_sat_solution {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hpres : SupportedArmsPreserveReach orig original props leaf)
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : SupportedReach orig original props cfg)
    (hsat : phaseNext cfg = .sat w) : SolutionWitness leaf orig w := by
  have hst := RunAssembly.schedulerNext_eq_sat_imp (phaseNext_eq_sat_imp hsat)
  have hstate : ReachableState leaf cfg.orig cfg.branch := by
    rw [SupportedReach.orig_eq hreach]
    exact supportedReachableBranch_of_preserve hpres hreach
  have hs : SolutionWitness leaf cfg.orig w :=
    arm_sat_solution hstate (stableStep_sat_of_guarded hst)
  rwa [SupportedReach.orig_eq hreach] at hs

/-! ## §3 The supported UNSAT terminal -/

/-- **SUPPORTED UNSAT TERMINAL**: a `.unsat` outcome of the phase dispatcher
at a supported configuration excludes every leaf solution of the run's box.
The exhausted-frontier sites are refuted by the supported invariant
discipline + coverage + dead evidence; the level-0 conflict route is closed
by `rootConflictExcludes_of_terminalEvent` from the ACTUAL terminal conflict
event plus the concrete run premises (`hbr`, `hbridge`, `hlent`, `hc`). -/
theorem supportedPhaseNext_unsat_excludes {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hinv : ∀ (cfg : SchedulerConfig leaf),
      SupportedReach orig original props cfg → SchedulerInvariant cfg)
    (hdead : SupportedDeadEvidence orig original props leaf)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch)
    (hbridge : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      RootFactsBridge leaf cfg.branch)
    (hlent : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      LearnedEntailed leaf cfg.branch.learned)
    (hc : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ClosureContract leaf orig cfg.original cfg.props)
    {cfg : SchedulerConfig leaf} (hreach : SupportedReach orig original props cfg)
    (hunsat : phaseNext cfg = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False := by
  have exhausted : ∀ {d : SchedulerConfig leaf},
      SupportedReach orig original props d →
      d.pending = [] → d.status = .dead →
        ∀ a, OriginalLeaves leaf orig a → False := by
    intro d hd hp hstat a ha
    have hda : OriginalLeaves leaf d.orig a := by
      rw [SupportedReach.orig_eq hd]; exact ha
    rcases (hinv d hd).coverage a hda with ⟨f, hf, hcov⟩ | ⟨c, hc', hnc⟩
    · unfold SchedulerConfig.frontier at hf
      rw [hp] at hf
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
      rw [hf] at hcov
      exact hdead hd hstat a ha.1 hcov
    · exact hnc ((hinv d hd).learned_entailed c hc' c
        (List.mem_singleton_self c) a ha.1)
  rcases phaseNext_unsat_cases hunsat with hbare |
    ⟨n, hn_orig, hn_pend, hn_dead, hn_succ⟩ |
    ⟨n, d, hn_orig, hd_orig, hd_pend, hd_dead, hn_succ, hd_succ⟩
  · rcases schedulerNext_eq_unsat_cases hbare with ⟨hp, hstat⟩ |
      ⟨hconf, hact, hlv, bs, cs, learned, hne, ht⟩
    · exact exhausted hreach hp hstat
    · exact rootConflictExcludes_of_terminalEvent (hbr hreach)
        (hbridge hreach) (hlent hreach) (hc hreach) ht
  · exact exhausted (SupportedReach.step hreach hn_succ) hn_pend hn_dead
  · exact exhausted (SupportedReach.step (SupportedReach.step hreach hn_succ)
      hd_succ) hd_pend hd_dead

/-! ## §4 The composed supported terminals from the B4 record -/

/-- The SAT terminal from the supported residual gate record (via the B4
assembly). -/
theorem supportedSat_of_core {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hc : SupportedArmInvGatesCore orig original props leaf)
    {cfg : SchedulerConfig leaf} {w : Assignment}
    (hreach : SupportedReach orig original props cfg)
    (hsat : phaseNext cfg = .sat w) : SolutionWitness leaf orig w :=
  supportedPhaseNext_sat_solution
    (supportedArmsPreserveReach_of_gates hc.coreGates) hreach hsat

end LeanFzn.Solver.UIP
