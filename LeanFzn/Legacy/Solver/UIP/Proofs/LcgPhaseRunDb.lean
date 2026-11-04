/-
File: LeanFzn/Solver/UIP/Proofs/LcgPhaseRunDb.lean

Purpose (PLAN B2): the DB-producing twin of the fuel-free supported driver of
`LcgPhaseKernel`/`SupportedPhaseRun`. `runSupportedPhaseDb` runs the same
recursion as `runSupportedPhase` but returns, besides the verdict, the
TERMINAL `SchedulerConfig` of the run; its first component agrees with
`runSupportedPhase` (`runSupportedPhaseDb_fst`) and its terminal configuration
is supported-reachable (`runSupportedPhaseDb_reach`).

`solveCfg`/`solveDb` instantiate that driver at the concrete LCG phase kernel,
so the verdict agrees with `LcgPhaseKernel.solve` (`solveDb_fst`) and the
verdict-soundness transfers of `LcgMixedPhaseTerminal` apply verbatim
(`solveDb_sat_solution_of_kit_mixed` / `solveDb_unsat_excludes_of_kit_mixed`).
`solveDb_spec_mixed` proves the returned clause database is canonical,
pool-aligned and entailed at the leaf along every mixed kit run — exactly the
facts needed to seed the NEXT solve (`SchedulerConfig.init` already puts the
seed into `learned`, so the returned database includes the seed).

DAG: LcgPhaseKernel + LcgMixedRunStep + LcgMixedPhaseTerminal -> this file
-> Integration seeded solve.
NO `sorry`, NO custom axiom.
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgPhaseKernel
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedRunStep
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgMixedPhaseTerminal

namespace LeanFzn.Solver.UIP.LcgPhaseRunDb
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation
open LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.UIP.P3 (PhaseLt phaseLt_of_inst phaseLt_wf)
open LeanFzn.Solver.UIP.LcgMixedGood
open LeanFzn.Solver.UIP.LcgMixedRunState
open LeanFzn.Solver.UIP.LcgMixedRunStep
open LeanFzn.Solver.UIP.LcgPhaseTerminal
open LeanFzn.Solver.UIP.LcgCanonicalClauses

variable {orig : List Domain} {original : List Clause} {props : List Propagator}
  {leaf : Assignment → Bool}

/-! ## §1 The DB-producing supported driver -/

/-- The supported driver that also returns the TERMINAL configuration (the
configuration at which the verdict was produced). Identical recursion and rank
decrease as `runSupportedPhase`; the verdict is its first component (`_fst`),
the terminal configuration is supported-reachable (`_reach`), and the terminal
LEARNED DATABASE is `snd.branch.learned`. -/
def runSupportedPhaseDb (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg) :
    DriverResult leaf × SchedulerConfig leaf :=
  match hstep : k.step cfg with
  | .sat w => (.sat w, cfg)
  | .unsat => (.unsat, cfg)
  | .propagate n => runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .decide n _ => runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .analyzeConflict n _ => runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .learnBackjumpAssert n _ _ => runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .localExclude n => runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [hstep]; rfl))
  | .chronologicalFallback n => runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [hstep]; rfl))
termination_by k.rank cfg
decreasing_by
  all_goals exact phaseLt_of_inst (k.decrease cfg n hreach (by rw [hstep]; rfl))

/-- The supported index is a proof-irrelevant argument. -/
theorem runSupportedPhaseDb_reach_congr
    (k : SupportedPhaseKernel orig original props leaf) (cfg : SchedulerConfig leaf)
    (p1 p2 : SupportedReach orig original props cfg) :
    runSupportedPhaseDb k cfg p1 = runSupportedPhaseDb k cfg p2 :=
  congrArg (runSupportedPhaseDb k cfg) (Subsingleton.elim p1 p2)

/-- Equation lemma, terminal `.sat` arm. -/
theorem runSupportedPhaseDb_sat (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (w : Assignment) (h : k.step cfg = .sat w) :
    runSupportedPhaseDb k cfg hreach = (.sat w, cfg) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- Equation lemma, terminal `.unsat` arm. -/
theorem runSupportedPhaseDb_unsat (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (h : k.step cfg = .unsat) :
    runSupportedPhaseDb k cfg hreach = (.unsat, cfg) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- Equation lemma, `.propagate` arm. -/
theorem runSupportedPhaseDb_propagate (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .propagate n) :
    runSupportedPhaseDb k cfg hreach
      = runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- Equation lemma, `.decide` arm. -/
theorem runSupportedPhaseDb_decide (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (l : Literal) (h : k.step cfg = .decide n l) :
    runSupportedPhaseDb k cfg hreach
      = runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- Equation lemma, `.analyzeConflict` arm. -/
theorem runSupportedPhaseDb_analyzeConflict (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (c : Clause) (h : k.step cfg = .analyzeConflict n c) :
    runSupportedPhaseDb k cfg hreach
      = runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- Equation lemma, `.learnBackjumpAssert` arm. -/
theorem runSupportedPhaseDb_learnBackjumpAssert
    (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (p : BackjumpPlan leaf) (an : ConflictAnalysis)
    (h : k.step cfg = .learnBackjumpAssert n p an) :
    runSupportedPhaseDb k cfg hreach
      = runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- Equation lemma, `.localExclude` arm. -/
theorem runSupportedPhaseDb_localExclude (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .localExclude n) :
    runSupportedPhaseDb k cfg hreach
      = runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- Equation lemma, `.chronologicalFallback` arm. -/
theorem runSupportedPhaseDb_chronologicalFallback
    (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg)
    (n : SchedulerConfig leaf) (h : k.step cfg = .chronologicalFallback n) :
    runSupportedPhaseDb k cfg hreach
      = runSupportedPhaseDb k n (k.reach cfg n hreach (by rw [h]; rfl)) := by
  rw [runSupportedPhaseDb]
  split <;> rename_i heq <;> first
    | rfl
    | (cases heq.symm.trans h <;> first | rfl |
        exact runSupportedPhaseDb_reach_congr k _ _ _)

/-- **VERDICT AGREEMENT**: the DB-producing driver returns the verdict of the
plain supported driver on the same kernel and configuration. -/
theorem runSupportedPhaseDb_fst (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg) :
    (runSupportedPhaseDb k cfg hreach).1 = runSupportedPhase k cfg hreach := by
  have main : ∀ (c : SchedulerConfig leaf),
      (hc : SupportedReach orig original props c) →
        (runSupportedPhaseDb k c hc).1 = runSupportedPhase k c hc := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => (hc : SupportedReach orig original props c) →
        (runSupportedPhaseDb k c hc).1 = runSupportedPhase k c hc) ?_
    intro c ih hc
    cases hstep : k.step c with
    | sat w =>
        rw [runSupportedPhaseDb_sat k c hc w hstep, runSupportedPhase_sat k c hc w hstep]
    | unsat =>
        rw [runSupportedPhaseDb_unsat k c hc hstep, runSupportedPhase_unsat k c hc hstep]
    | propagate n =>
        rw [runSupportedPhaseDb_propagate k c hc n hstep,
          runSupportedPhase_propagate k c hc n hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | decide n l =>
        rw [runSupportedPhaseDb_decide k c hc n l hstep,
          runSupportedPhase_decide k c hc n l hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | analyzeConflict n c' =>
        rw [runSupportedPhaseDb_analyzeConflict k c hc n c' hstep,
          runSupportedPhase_analyzeConflict k c hc n c' hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | learnBackjumpAssert n p an =>
        rw [runSupportedPhaseDb_learnBackjumpAssert k c hc n p an hstep,
          runSupportedPhase_learnBackjumpAssert k c hc n p an hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | localExclude n =>
        rw [runSupportedPhaseDb_localExclude k c hc n hstep,
          runSupportedPhase_localExclude k c hc n hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | chronologicalFallback n =>
        rw [runSupportedPhaseDb_chronologicalFallback k c hc n hstep,
          runSupportedPhase_chronologicalFallback k c hc n hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
  exact main cfg hreach

/-- **TERMINAL SUPPORTED-REACHABILITY**: the returned terminal configuration is
supported-reachable from the same initializer (so every run invariant carrying
along supported execution holds at the terminal configuration). -/
theorem runSupportedPhaseDb_reach (k : SupportedPhaseKernel orig original props leaf)
    (cfg : SchedulerConfig leaf) (hreach : SupportedReach orig original props cfg) :
    SupportedReach orig original props (runSupportedPhaseDb k cfg hreach).2 := by
  have main : ∀ (c : SchedulerConfig leaf),
      (hc : SupportedReach orig original props c) →
        SupportedReach orig original props (runSupportedPhaseDb k c hc).2 := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => (hc : SupportedReach orig original props c) →
        SupportedReach orig original props (runSupportedPhaseDb k c hc).2) ?_
    intro c ih hc
    cases hstep : k.step c with
    | sat w => rw [runSupportedPhaseDb_sat k c hc w hstep]; exact hc
    | unsat => rw [runSupportedPhaseDb_unsat k c hc hstep]; exact hc
    | propagate n =>
        rw [runSupportedPhaseDb_propagate k c hc n hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | decide n l =>
        rw [runSupportedPhaseDb_decide k c hc n l hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | analyzeConflict n c' =>
        rw [runSupportedPhaseDb_analyzeConflict k c hc n c' hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | learnBackjumpAssert n p an =>
        rw [runSupportedPhaseDb_learnBackjumpAssert k c hc n p an hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | localExclude n =>
        rw [runSupportedPhaseDb_localExclude k c hc n hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
    | chronologicalFallback n =>
        rw [runSupportedPhaseDb_chronologicalFallback k c hc n hstep]
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl))
          (k.reach c n hc (by rw [hstep]; rfl))
  exact main cfg hreach

/-! ## §2 The concrete LCG entry -/

/-- The concrete DB-producing LCG entry: the same initializer and kernel as
`LcgPhaseKernel.solve`, additionally returning the terminal configuration. -/
def solveCfg (orig : List Domain) (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult leaf × SchedulerConfig leaf :=
  runSupportedPhaseDb (LcgPhaseKernel.supportedPhaseKernel orig original props hgate)
    (SchedulerConfig.init orig original props prio actBump) (SupportedReach.init hent)

/-- The terminal learned clause database of `solveCfg`.  The optional
priority vector and activity-bump toggle are heuristic-only: every proof
below holds for all of them (the kernel's coverage/soundness does not read
`prio` or `actBump`). -/
def solveDb (orig : List Domain) (original : List Clause) (props : List Propagator)
    (hent : LearnedEntailed leaf original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DriverResult leaf × List Clause :=
  let r := solveCfg orig original props hent hgate prio actBump
  (r.1, r.2.branch.learned)

/-- **VERDICT AGREEMENT WITH `LcgPhaseKernel.solve`**: the DB-producing entry
decides exactly what the plain fuel-free entry decides. -/
theorem solveDb_fst (hent : LearnedEntailed (leaf := leaf) original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    (solveDb (leaf := leaf) orig original props hent hgate prio actBump).1
      = LcgPhaseKernel.solve orig original props hent hgate prio actBump :=
  runSupportedPhaseDb_fst _ _ _

/-- The terminal configuration of the concrete entry is supported-reachable. -/
theorem solveCfg_reach (hent : LearnedEntailed (leaf := leaf) original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    SupportedReach orig original props
      (solveCfg (leaf := leaf) orig original props hent hgate prio actBump).2 :=
  runSupportedPhaseDb_reach _ _ _

/-- **THE RETURNED DATABASE**: along a mixed kit run the terminal learned
database of the DB-producing entry is canonical, pool-aligned with the box and
entailed at the leaf — the three facts a consumer needs to re-seed the next
solve (the initializer already puts the seed into `learned`, so the returned
database includes the seed). -/
theorem solveDb_spec_mixed {dcs : List DomConstraint} {raw : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    (hent : LearnedEntailed leaf original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false) :
    DatabaseCanonical (solveDb (leaf := leaf) orig original props hent hgate prio actBump).2 ∧
    DatabaseAligned orig (solveDb (leaf := leaf) orig original props hent hgate prio actBump).2 ∧
    LearnedEntailed leaf (solveDb (leaf := leaf) orig original props hent hgate prio actBump).2 :=
  let h := lcgMixedRunState_of_supportedRun K
    (solveCfg_reach (leaf := leaf) hent hgate prio actBump)
  ⟨h.canonical.db, h.good.db, h.core.reach.learned_ent⟩

/-- The verdict-soundness transfer of `solve` carries over verbatim: a SAT
verdict of the DB-producing entry is a solution witness of the run's own
box/leaf. -/
theorem solveDb_sat_solution_of_kit_mixed {dcs : List DomConstraint}
    {raw : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    (hent : LearnedEntailed leaf original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    {w : Assignment}
    (prio : List Nat := []) (actBump : Bool := false)
    (hrun : (solveDb (leaf := leaf) orig original props hent hgate prio actBump).1 = .sat w) :
    SolutionWitness leaf orig w :=
  LcgMixedPhaseTerminal.solve_sat_solution_of_kit_mixed K hent hgate
    (solveDb_fst (leaf := leaf) (orig := orig) (original := original)
      (props := props) hent hgate prio actBump ▸ hrun)

/-- The verdict-soundness transfer of `solve` carries over verbatim: an UNSAT
verdict of the DB-producing entry excludes every original leaf solution. -/
theorem solveDb_unsat_excludes_of_kit_mixed {dcs : List DomConstraint}
    {raw : List Propagator}
    (K : MixedLcgKit leaf orig original dcs raw props)
    (hent : LearnedEntailed leaf original)
    (hgate : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg → FrameNonempty cfg)
    (prio : List Nat := []) (actBump : Bool := false)
    (hrun : (solveDb (leaf := leaf) orig original props hent hgate prio actBump).1 = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False :=
  LcgMixedPhaseTerminal.solve_unsat_excludes_of_kit_mixed K hent hgate
    (solveDb_fst (leaf := leaf) (orig := orig) (original := original)
      (props := props) hent hgate prio actBump ▸ hrun)

end LeanFzn.Solver.UIP.LcgPhaseRunDb
