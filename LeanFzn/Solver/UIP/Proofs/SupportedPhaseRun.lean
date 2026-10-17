/-
File: LeanFzn/Solver/UIP/Proofs/SupportedPhaseRun.lean

Purpose: the S2 CORE. Every quantifier here is indexed by
`SupportedReach orig original props` (S1's root-indexed execution), never by
raw `SchedulerReachable`, so each premise is a fact about exactly one
supported run and its producer can be built from the compiled initializer.

Contents:

  §1 `SupportedReach.phaseNext_succ` — supported execution is closed under
     the phase dispatcher (via the raw-chain classification, so no arm is
     re-analysed).
  §2 `SupportedPhaseProgressSorted` + its `_of_premises` instance: the
     sorted-rank progress at the FIXED triple `(orig, original, props)`,
     with SELF-INDEXED premises (`halignDB`, `hdb`, `hbr` over the supported
     run). The per-arm decreases instantiate at `orig` directly because
     every supported configuration carries that exact triple.
  §3 `SupportedPhaseKernel` + `supportedPhaseKernelSorted` + the computable
     driver `runSupportedPhase` (a `termination_by k.rank` recursion, same
     X1 pattern as X2's `runPhase`).
  §4 The whole-run lifts `runSupportedPhase_sat_solution` /
     `runSupportedPhase_unsat_excludes`: well-founded induction over the
     kernel's rank, with the supported index carried through every arm; the
     fixed-input `cfg.orig = orig` side conditions of W1's raw lifts are
     FREE here (`SupportedReach.orig_eq`).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedPhaseRun` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean`.
-/

import LeanFzn.Solver.UIP.Proofs.SupportedRun
import LeanFzn.Solver.UIP.Proofs.SchedulerReachClosure
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference
open LeanFzn.Solver.UIP.P3 (PhaseLt phaseLt_of_inst phaseLt_wf)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference
open LeanFzn.Solver.UIP.P4 (PhaseRankSorted)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C3b

/-! ## §1 Supported execution is closed under phase steps -/

theorem SupportedReach.phaseNext_succ {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {cfg cfg' : SchedulerConfig leaf}
    (h : SupportedReach orig original props cfg)
    (hsucc : (phaseNext cfg).successor = some cfg') :
    SupportedReach orig original props cfg' := by
  suffices ∀ {a b : SchedulerConfig leaf}, RawReach a b →
      SupportedReach orig original props a → SupportedReach orig original props b from
    this (phaseNext_successor_rawReach hsucc) h
  intro a b hr
  induction hr with
  | refl c => exact id
  | step hs _ ih => exact fun hc => ih (SupportedReach.step hc hs)

/-! ## §2 The supported sorted progress -/

/-- The supported-run version of C2's sorted obligation: every phase
successor of a supported configuration strictly decreases the sorted rank
of the run's own triple. -/
def SupportedPhaseProgressSorted (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg cfg' : SchedulerConfig leaf),
    SupportedReach orig original props cfg →
    (phaseNext cfg).successor = some cfg' →
      PhaseLt (PhaseRankSorted orig cfg') (PhaseRankSorted orig cfg)

/-- **THE S2 SORTED-PROGRESS INSTANCE**: the sorted obligation on the
supported run from the SELF-INDEXED premises — `halignDB` (literal-pool
alignment at the run's own box), `hbr`
(branch reachability over the run's own box). All per-arm decreases
instantiate at the run's `orig`; the recorded-analysis falsification is
produced from the forgetting map (`SupportedReach.reachable`). -/
theorem supportedPhaseProgressSorted_of_premises {leaf : Assignment → Bool}
    (orig : List Domain) (original : List Clause) (props : List Propagator)
    (halignDB : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch) :
    SupportedPhaseProgressSorted orig original props leaf :=
  P5.reachablePhaseProgress_of_arms (leaf := leaf)
    (R := SupportedReach orig original props)
    (Rstep := fun h hs => SupportedReach.step h hs)
    (fun cfg => PhaseRankSorted orig cfg)
    (fun cfg d => P4.phaseRankSorted_lt_propagate orig cfg d)
    (fun cfg v vs doms l hsplit =>
      P4.phaseRankSorted_lt_decide orig cfg v vs doms l hsplit)
    (fun cfg v vs doms l hsplit =>
      P4.phaseRankSorted_lt_decideSkip orig cfg v vs doms l hsplit)
    (fun hp h => P4.phaseRankSorted_lt_consume orig hp h)
    (fun hpe hlt hsucc => P5.phase_compose_consume_generic hpe hlt hsucc)
    (fun hp h => P4.fallback_then_consume_sorted orig hp h)
    (fun hp h => P4.localExclude_then_consume_sorted orig hp h)
    (fun cfg c learned n =>
      P4.phaseRankSorted_analyzeConflictCounted_stutter orig cfg c learned n)
    (fun c0 cp ev an restored hreach hconf hana hperf =>
      P4.phaseLtSorted_stepLearnBackjumpAssert
        (hreach.orig_eq ▸ P4.sortedNovelty_of_not_repeats
          (reachable_analysis_novel hreach.reachable hconf hana))
        hperf (planMatchesAnalysis_ofCheckpoint cp c0.branch an))

/-- The OLD discharge of the novelty premise (kept by R1c): at supported
sites whose learned database is unfalsified, the recorded analysis has sorted
novelty. It does NOT hold at routed (database-sourced) sites, which is why
`supportedPhaseProgressSorted_of_premises` now takes the novelty itself. -/
theorem supportedSortedNovelty_of_dbUnfalsified_site {leaf : Assignment → Bool}
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    (halignDB : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool orig)
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hreach : SupportedReach orig original props cfg)
    (hdb : DatabaseUnfalsified cfg.branch)
    (hbr : ReachableState leaf orig cfg.branch)
    (hconf : cfg.conflict = some ev) (hana : ev.analysis = some an) :
    P4.SortedNovelty orig cfg.branch.learned an :=
  P4.sortedNovelty_of_unfalsified (halignDB hreach) hdb
    (recordedAnalysis_normFalsified (bs := cfg.branch) rfl hbr
      hreach.reachable hconf hana)

/-! ## §3 The supported kernel and computable driver -/

/-- A recursion kernel over the SUPPORTED run: the driver's step, its
agreement with the real dispatcher, closure of the supported index, the
rank, and the rank decrease — every field indexed by `SupportedReach`. -/
structure SupportedPhaseKernel (orig : List Domain) (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) where
  step : SchedulerConfig leaf → SchedulerTransition leaf
  step_eq : ∀ cfg, SupportedReach orig original props cfg → step cfg = phaseNext cfg
  reach : ∀ cfg cfg', SupportedReach orig original props cfg →
    (step cfg).successor = some cfg' → SupportedReach orig original props cfg'
  rank : SchedulerConfig leaf → Nat × Nat × Nat × Nat
  decrease : ∀ cfg cfg', SupportedReach orig original props cfg →
    (step cfg).successor = some cfg' → PhaseLt (rank cfg') (rank cfg)

/-- The SORTED supported kernel from the S2 progress instance. -/
def supportedPhaseKernelSorted {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (h : SupportedPhaseProgressSorted orig original props leaf) :
    SupportedPhaseKernel orig original props leaf where
  step := phaseNext
  step_eq := fun _ _ => rfl
  reach := fun _ _ hreach hsucc => hreach.phaseNext_succ hsucc
  rank := fun cfg => PhaseRankSorted orig cfg
  decrease := h

/-- **THE COMPUTABLE SUPPORTED DRIVER**: well-founded recursion on the
kernel's rank function, following X1's exact `termination_by` +
`decreasing_by` pattern. The supported index and the kernel's proof fields
are erased arguments: the runtime carries no proofs. -/
def runSupportedPhase {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (cfg : SchedulerConfig leaf)
    (hreach : SupportedReach orig original props cfg) : DriverResult leaf :=
  match hstep : k.step cfg with
  | .sat w => .sat w
  | .unsat => .unsat
  | .propagate n => runSupportedPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .decide n _ => runSupportedPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .analyzeConflict n _ => runSupportedPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .learnBackjumpAssert n _ _ => runSupportedPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .localExclude n => runSupportedPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .chronologicalFallback n => runSupportedPhase k n (k.reach cfg n hreach (by rw [hstep]; rfl))
termination_by k.rank cfg
decreasing_by
  all_goals exact phaseLt_of_inst (k.decrease cfg n hreach (by rw [hstep]; rfl))

/-- The supported index is a proof-irrelevant argument. -/
theorem runSupportedPhase_reach_congr
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (p1 p2 : SupportedReach orig original props cfg) :
    runSupportedPhase k cfg p1 = runSupportedPhase k cfg p2 :=
  congrArg (runSupportedPhase k cfg) (Subsingleton.elim p1 p2)

/-! ## §4 Equation lemmas for the supported driver -/

theorem runSupportedPhase_sat
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (w : Assignment) (h : k.step cfg = .sat w) :
    runSupportedPhase k cfg hreach = .sat w := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

theorem runSupportedPhase_unsat
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (h : k.step cfg = .unsat) :
    runSupportedPhase k cfg hreach = .unsat := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

theorem runSupportedPhase_propagate
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .propagate n) :
    runSupportedPhase k cfg hreach
      = runSupportedPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

theorem runSupportedPhase_decide
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (l : Literal) (h : k.step cfg = .decide n l) :
    runSupportedPhase k cfg hreach
      = runSupportedPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

theorem runSupportedPhase_analyzeConflict
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (c : Clause) (h : k.step cfg = .analyzeConflict n c) :
    runSupportedPhase k cfg hreach
      = runSupportedPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

theorem runSupportedPhase_learnBackjumpAssert
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (p : BackjumpPlan leaf) (an : ConflictAnalysis)
    (h : k.step cfg = .learnBackjumpAssert n p an) :
    runSupportedPhase k cfg hreach
      = runSupportedPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

theorem runSupportedPhase_localExclude
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .localExclude n) :
    runSupportedPhase k cfg hreach
      = runSupportedPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

theorem runSupportedPhase_chronologicalFallback
    {orig : List Domain} {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool} (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .chronologicalFallback n) :
    runSupportedPhase k cfg hreach
      = runSupportedPhase k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhase]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhase_reach_congr k _ _ _)

/-! ## §5 The whole-run lifts on supported runs -/

/-- **S2 SAT LIFT**: `.sat w` reported by the supported driver is a solution
witness of the run's own box/leaf. Well-founded induction on the kernel's
rank; every arm carries the supported index to its successor, the terminal
arm is the lifted obligation (`hterm_sat`). The fixed-input side condition
`c.orig = orig` is FREE here (`SupportedReach.orig_eq`). -/
theorem runSupportedPhase_sat_solution {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf)
    (hterm_sat : ∀ (cfg : SchedulerConfig leaf) (w : Assignment),
      SupportedReach orig original props cfg → cfg.orig = orig →
        k.step cfg = .sat w → SolutionWitness leaf orig w)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    {w : Assignment} (hrun : runSupportedPhase k cfg hreach = .sat w) :
    SolutionWitness leaf orig w := by
  have main : ∀ (c : SchedulerConfig leaf),
      (hc : SupportedReach orig original props c) →
        runSupportedPhase k c hc = .sat w → SolutionWitness leaf orig w := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => (hc : SupportedReach orig original props c) →
        runSupportedPhase k c hc = .sat w → SolutionWitness leaf orig w) ?_
    intro c ih hc hrun
    cases hstep : k.step c with
    | sat w' =>
        rw [runSupportedPhase_sat k c hc w' hstep] at hrun
        cases hrun
        exact hterm_sat c w hc (SupportedReach.orig_eq hc) hstep
    | unsat =>
        rw [runSupportedPhase_unsat k c hc hstep] at hrun
        cases hrun
    | propagate n =>
        rw [runSupportedPhase_propagate k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | decide n l =>
        rw [runSupportedPhase_decide k c hc n l hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | analyzeConflict n c' =>
        rw [runSupportedPhase_analyzeConflict k c hc n c' hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | learnBackjumpAssert n p an =>
        rw [runSupportedPhase_learnBackjumpAssert k c hc n p an hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | localExclude n =>
        rw [runSupportedPhase_localExclude k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | chronologicalFallback n =>
        rw [runSupportedPhase_chronologicalFallback k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
  exact main cfg hreach hrun

/-- **S2 UNSAT LIFT**: `.unsat` reported by the supported driver excludes
every leaf solution of the run's own box. -/
theorem runSupportedPhase_unsat_excludes {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf)
    (hterm_unsat : ∀ (cfg : SchedulerConfig leaf),
      SupportedReach orig original props cfg → cfg.orig = orig →
        k.step cfg = .unsat →∀ a, OriginalLeaves leaf orig a → False)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (hrun : runSupportedPhase k cfg hreach = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False := by
  have main : ∀ (c : SchedulerConfig leaf),
      (hc : SupportedReach orig original props c) →
        runSupportedPhase k c hc = .unsat →
          ∀ a, OriginalLeaves leaf orig a → False := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => (hc : SupportedReach orig original props c) →
        runSupportedPhase k c hc = .unsat →
          ∀ a, OriginalLeaves leaf orig a → False) ?_
    intro c ih hc hrun
    cases hstep : k.step c with
    | sat w' =>
        rw [runSupportedPhase_sat k c hc w' hstep] at hrun
        cases hrun
    | unsat =>
        rw [runSupportedPhase_unsat k c hc hstep] at hrun
        exact hterm_unsat c hc (SupportedReach.orig_eq hc) hstep
    | propagate n =>
        rw [runSupportedPhase_propagate k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | decide n l =>
        rw [runSupportedPhase_decide k c hc n l hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | analyzeConflict n c' =>
        rw [runSupportedPhase_analyzeConflict k c hc n c' hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | learnBackjumpAssert n p an =>
        rw [runSupportedPhase_learnBackjumpAssert k c hc n p an hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | localExclude n =>
        rw [runSupportedPhase_localExclude k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
    | chronologicalFallback n =>
        rw [runSupportedPhase_chronologicalFallback k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl)) hrun
  exact main cfg hreach hrun

/-- TOTALITY of the supported driver on a supported configuration. -/
theorem runSupportedPhase_total {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (k : SupportedPhaseKernel orig original props leaf) (cfg : SchedulerConfig leaf)
    (hreach : SupportedReach orig original props cfg) :
    ∃ r : DriverResult leaf, runSupportedPhase k cfg hreach = r :=
  ⟨_, rfl⟩

end LeanFzn.Solver.UIP
