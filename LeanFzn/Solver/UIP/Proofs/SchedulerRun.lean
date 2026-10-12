/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerRun.lean

Purpose (W1): whole-run verdict correctness for the fuel-free phase driver.

  * the recursive lift: `runPhase_sat_solution` / `runPhase_unsat_excludes`
    are proved by WELL-FOUNDED INDUCTION over the kernel's rank function
    (`InvImage.wf k.rank phaseLt_wf`, rank-generic since C2/G1), consuming
    X2's per-arm equation lemmas. Every
    recursive phase arm transfers the obligation to its successor; the
    terminal arms are the lifted phase-level obligations below. This is
    NOT the trivial `∃ r, run cfg = r` statement and NOT a restatement of
    S5's terminal-arm lemmas: the content added here is the induction over
    the phase recursion plus the preserved initial-problem identity.
    The ranked entry wrappers are `run_sat_solution`/`run_unsat_excludes`;
    the SORTED-chain wrappers (D1's route) are
    `run_sat_solution_sorted`/`run_unsat_excludes_sorted`.
  * the preserved initial-problem identity: `schedulerNext_succ_orig`
    (one real dispatcher step preserves `orig`) and its lift
    `schedulerReachable_orig` over raw reachability from a fixed start.
  * `PhaseOrigFrame` — the named phase-level frame obligation (owner W1):
    the phase dispatcher's (one-or-two raw step) successors preserve
    `orig`. Its discharge path is `C2d.schedulerNext_cases` +
    `schedulerNext_succ_orig` + `stepConsume_orig` (the same route
    analysis P5 §4 performs for the rank); it is recorded here as a named
    predicate rather than silently assumed.
  * the terminal phase obligations with their discharge paths:
    `PhaseNextSatSolution` (discharge: `phaseNext`'s non-terminal arms
    never emit `.sat`, so a reachable `.sat` is `stableStep cfg = .sat w`;
    S5's `arm_sat_solution` then needs `ReachableState leaf cfg.orig
    cfg.branch` — the named residual `hbr` of P5 §6, owner S5/W1) and
    `PhaseUnsatTerminal` (discharge: P5 §4's route analysis lands
    `.unsat` exactly at a dead configuration with `pending = []`
    (`stepConsume_eq_none_iff`) reached from a `localExcluded`/fallback
    site; S5's `arm_unsat_coverage` / `arm_unsat_rootContradiction_evidence`
    at that configuration plus `SchedulerInvariant` (owner S4/S5) and the
    site's dead-region evidence (owner S4/P2) close it).
  * `runPhase_total` — totality on every reachable (hence every supported
    initialized) input, no runtime contract: `⟨_, rfl⟩` for the computable
    driver over any kernel, i.e. no fuel and no assumed decrease.

EXPLICIT NON-CLAIM: `runPhase_total` / terminal-arm lemmas / the mere
existence of a result are NOT the W1 result; the W1 content is the two
lift theorems plus the frame identity above.

No `sorry`, no custom axiom; the only noncomputability is X2's driver
(proof-erased kernel). RULES: build `lake build LeanFzn.Solver.UIP.Proofs.SchedulerRun`.
-/

import LeanFzn.Solver.UIP.Scheduler
import LeanFzn.Solver.UIP.Proofs.SchedulerStep
import LeanFzn.Solver.UIP.Proofs.SchedulerReachable
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.W1
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.X2
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.P3 (PhaseRank PhaseLt phaseRank_wf phaseLt_wf)
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.UIP.P5 (ReachablePhaseKernel ReachablePhaseProgressSelf
  ReachablePhaseProgressSorted reachablePhaseKernel reachablePhaseKernelSorted
  runReachable)

/-! ## §1 The preserved initial-problem identity

`orig` is written only at initialization; every raw dispatcher successor
keeps it. Proved from `C2d.schedulerNext_cases` + the successor equations
(the same route split P5 §4 performs for the rank). -/

/-- The consume site preserves `orig` on its successor. -/
theorem stepConsume_orig {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} (h : stepConsume cfg = some next) :
    next.orig = cfg.orig := by
  unfold stepConsume at h
  split at h <;> first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (cases h)

/-- The counted analyze site preserves `orig` on its successor. -/
theorem stepAnalyzeConflictCounted_orig {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause)
    (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).orig = cfg.orig := rfl

/-- The consume site preserves the run's OTHER static inputs (`original`
clauses, `props` propagators) as well. -/
theorem stepConsume_inputs {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} (h : stepConsume cfg = some next) :
    next.orig = cfg.orig ∧ next.original = cfg.original ∧
      next.props = cfg.props := by
  unfold stepConsume at h
  split at h <;> first
    | (simp only [Option.some.injEq] at h; subst h; exact ⟨rfl, rfl, rfl⟩)
    | (cases h)

/-- The counted analyze site preserves the static inputs. -/
theorem stepAnalyzeConflictCounted_inputs {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause)
    (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).orig = cfg.orig ∧
      (stepAnalyzeConflictCounted cfg c learned n).original = cfg.original ∧
      (stepAnalyzeConflictCounted cfg c learned n).props = cfg.props :=
  ⟨rfl, rfl, rfl⟩

/-- Successor extraction: a transition's successor, when present, is the
configuration the transition carries. -/
theorem successor_cases {leaf : Assignment → Bool}
    {t : SchedulerTransition leaf} {cfg' : SchedulerConfig leaf}
    (h : t.successor = some cfg') :
    (∃ w, t = .sat w) ∨ t = .unsat ∨
    (∃ n, t = .propagate n) ∨ (∃ n l, t = .decide n l) ∨
    (∃ n c, t = .analyzeConflict n c) ∨
    (∃ n p an, t = .learnBackjumpAssert n p an) ∨
    (∃ n, t = .localExclude n) ∨ (∃ n, t = .chronologicalFallback n) := by
  cases t with
  | sat w => exact Or.inl ⟨w, rfl⟩
  | unsat => exact Or.inr (Or.inl rfl)
  | propagate n => exact Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))
  | decide n l => exact Or.inr (Or.inr (Or.inr (Or.inl ⟨n, l, rfl⟩)))
  | analyzeConflict n c => exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, c, rfl⟩))))
  | learnBackjumpAssert n p an =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, p, an, rfl⟩)))))
  | localExclude n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨n, rfl⟩))))))
  | chronologicalFallback n =>
      exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨n, rfl⟩))))))

/-- ONE REAL DISPATCHER STEP PRESERVES THE ORIGINAL BOX: every successor of
`schedulerNext` carries the same `orig` as its predecessor. Proved from
`C2d.schedulerNext_cases` + the successor equations. -/
theorem schedulerNext_succ_orig {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (h : (schedulerNext cfg).successor = some cfg') :
    cfg'.orig = cfg.orig := by
  rcases C2d.schedulerNext_cases (leaf := leaf) cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- recorded evidence: backjumpStep
    rw [hnext] at h
    unfold backjumpStep at h
    split at h
    · -- no analysis → the fallback transition
      simp only [successor_chronologicalFallback, Option.some.injEq] at h
      subst h
      rfl
    · split at h
      · -- no checkpoint → the fallback transition
        simp only [successor_chronologicalFallback, Option.some.injEq] at h
        subst h
        rfl
      · -- checkpoint present: zeta-reduce the plan `let` first
        dsimp only at h
        split at h
        · -- perform rejected → the local exclusion transition
          simp only [successor_localExclude, Option.some.injEq] at h
          subst h
          rfl
        · -- the jump lands at the learn/backjump/assert successor
          simp only [successor_learnBackjumpAssert, Option.some.injEq] at h
          subst h
          rfl
  · -- dead branch: consumeStep
    rw [hnext] at h
    unfold consumeStep at h
    split at h
    · rename_i nx hcs
      simp only [successor_chronologicalFallback, Option.some.injEq] at h
      subst h
      exact (stepConsume_orig hcs).trans rfl
    · simp only [successor_unsat] at h
      exact absurd h (by simp)
  · -- active branch
    rcases hrest with ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ |
      ⟨bs, cs, learned, ht, hnext⟩ | ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- propagation
      rw [hnext] at h
      simp only [successor_propagate, Option.some.injEq] at h
      subst h
      rfl
    · -- stable (guarded): the witness arm has no successor; the split arms
      -- (fresh decision or redundant-pin skip) and the exclusion carry one
      rw [hnext] at h
      unfold stableStepGuarded at h
      split at h
      · -- a reported witness has no successor
        simp only [successor_sat] at h
        cases h
      · split at h
        · -- split data: fresh or redundant-pin skip, both `decide`
          split at h
          · simp only [successor_decide, Option.some.injEq] at h
            subst h
            rfl
          · simp only [successor_decide, Option.some.injEq] at h
            subst h
            rfl
        · -- no split data → the local exclusion successor
          simp only [successor_localExclude, Option.some.injEq] at h
          subst h
          rfl
    · -- recorded conflict dispatch
      rw [hnext] at h
      unfold conflictStep at h
      split at h
      · -- empty reported clause list → local exclusion
        simp only [successor_localExclude, Option.some.injEq] at h
        subst h
        rfl
      · split at h
        · -- level 0 → the root-contradiction emission (no successor)
          simp only [successor_unsat] at h
          cases h
        · -- recorded analysis → the counted analyze successor
          simp only [successor_analyzeConflict, Option.some.injEq] at h
          subst h
          rfl
    · -- local exclusion
      rw [hnext] at h
      simp only [successor_localExclude, Option.some.injEq] at h
      subst h
      rfl

/-- ONE REAL DISPATCHER STEP PRESERVES THE STATIC INPUTS: every successor of
`schedulerNext` carries the same original box, clause base and propagator
list as its predecessor (the `original`/`props` companion of
`schedulerNext_succ_orig`; same route split). This is the enabling fact for
transferring STATIC problem properties — in particular the closure
contract (`domExplainedContract`) — from the root to every reachable
configuration. -/
theorem schedulerNext_succ_inputs {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (h : (schedulerNext cfg).successor = some cfg') :
    cfg'.orig = cfg.orig ∧ cfg'.original = cfg.original ∧
      cfg'.props = cfg.props := by
  rcases C2d.schedulerNext_cases (leaf := leaf) cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- recorded evidence: backjumpStep
    rw [hnext] at h
    unfold backjumpStep at h
    split at h
    · -- no analysis → the fallback transition
      simp only [successor_chronologicalFallback, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
    · split at h
      · -- no checkpoint → the fallback transition
        simp only [successor_chronologicalFallback, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩
      · -- checkpoint present: zeta-reduce the plan `let` first
        dsimp only at h
        split at h
        · -- perform rejected → the local exclusion transition
          simp only [successor_localExclude, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl⟩
        · -- the jump lands at the learn/backjump/assert successor
          simp only [successor_learnBackjumpAssert, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl⟩
  · -- dead branch: consumeStep
    rw [hnext] at h
    unfold consumeStep at h
    split at h
    · rename_i nx hcs
      simp only [successor_chronologicalFallback, Option.some.injEq] at h
      subst h
      exact stepConsume_inputs hcs
    · simp only [successor_unsat] at h
      exact absurd h (by simp)
  · -- active branch
    rcases hrest with ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ |
      ⟨bs, cs, learned, ht, hnext⟩ | ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- propagation
      rw [hnext] at h
      simp only [successor_propagate, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩
    · -- stable (guarded): the witness arm has no successor; the split arms
      -- (fresh decision or redundant-pin skip) and the exclusion carry one
      rw [hnext] at h
      unfold stableStepGuarded at h
      split at h
      · -- a reported witness has no successor
        simp only [successor_sat] at h
        cases h
      · split at h
        · -- split data: fresh or redundant-pin skip, both `decide`
          split at h
          · simp only [successor_decide, Option.some.injEq] at h
            subst h
            exact ⟨rfl, rfl, rfl⟩
          · simp only [successor_decide, Option.some.injEq] at h
            subst h
            exact ⟨rfl, rfl, rfl⟩
        · -- no split data → the local exclusion successor
          simp only [successor_localExclude, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl⟩
    · -- recorded conflict dispatch
      rw [hnext] at h
      unfold conflictStep at h
      split at h
      · -- empty reported clause list → local exclusion
        simp only [successor_localExclude, Option.some.injEq] at h
        subst h
        exact ⟨rfl, rfl, rfl⟩
      · split at h
        · -- level 0 → the root-contradiction emission (no successor)
          simp only [successor_unsat] at h
          cases h
        · -- recorded analysis → the counted analyze successor
          simp only [successor_analyzeConflict, Option.some.injEq] at h
          subst h
          exact ⟨rfl, rfl, rfl⟩
    · -- local exclusion
      rw [hnext] at h
      simp only [successor_localExclude, Option.some.injEq] at h
      subst h
      exact ⟨rfl, rfl, rfl⟩

/-! ## §2 The named phase-level obligations (owner W1, discharge paths
recorded in the header) -/

/-- The phase dispatcher's successors preserve `orig` (owner W1; discharge:
`schedulerNext_cases` route analysis as in §1, one-or-two raw steps). The
parameter `_orig` names the run's original box for signature symmetry; the
statement is about `cfg'.orig = cfg.orig` along the step. -/
def PhaseOrigFrame (_orig : List Domain) (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
    (phaseNext cfg).successor = some cfg' → cfg'.orig = cfg.orig

/-- The phase dispatcher's successors preserve the run's OTHER static
inputs (`original` clause base and `props` propagator list) — the
companion of `PhaseOrigFrame` (producer: `phaseNextInputsFrame`). Together
the two frames say that every configuration of a run carries the SAME
static problem data, which is what transfers the closure contract
(`domExplainedContract`) from the root. -/
def PhaseInputsFrame (_original : List Clause) (_props : List Propagator)
    (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
    (phaseNext cfg).successor = some cfg' →
      cfg'.original = cfg.original ∧ cfg'.props = cfg.props

/-- The phase-level SAT terminal obligation (owner W1 terminal, semantic
content owner S5), FIXED-INPUT (A2): a reachable `.sat` outcome from a
configuration whose own `orig` IS the run's original box is a witness of
that box. Discharge: `phaseNext`'s intercept arms yield
`.chronologicalFallback`/`.unsat` only, so the outcome is
`schedulerNext cfg = .sat w`, hence `stableStep cfg = .sat w`, hence S5's
`arm_sat_solution` under `ReachableState leaf cfg.orig cfg.branch`
(P5 §6's named `hbr`, owner S5/W1). The `cfg.orig = orig` premise is
load-bearing: without it the shape quantifies over runs on OTHER boxes
(assembly §4). -/
def PhaseNextSatSolution (orig : List Domain) (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg : SchedulerConfig leaf) (w : Assignment), SchedulerReachable cfg →
    cfg.orig = orig → phaseNext cfg = .sat w → SolutionWitness leaf orig w

/-- The phase-level UNSAT terminal obligation (owner W1 terminal, semantic
content owner S5/S4/P2), FIXED-INPUT (A2): a reachable `.unsat` outcome
from a configuration whose own `orig` IS the run's original box excludes
every leaf solution of that box. Discharge: the `.unsat` outcomes arise
exactly at dead configurations with `pending = []` fed by a
`localExcluded`/checkpoint-rejection site; S5's `arm_unsat_coverage`
(frontier exhaustion) / `arm_unsat_rootContradiction_evidence` (level 0)
with `SchedulerInvariant` (owner S4/S5, `hbr`-family) and the site's
dead-region evidence (owner S4/P2); the level-0 route is A1's
`rootConflictExcludes_of_terminalEvent`. The `cfg.orig = orig` premise is
load-bearing (assembly §4). -/
def PhaseUnsatTerminal (orig : List Domain) (leaf : Assignment → Bool) : Prop :=
  ∀ (cfg : SchedulerConfig leaf), SchedulerReachable cfg → cfg.orig = orig →
    phaseNext cfg = .unsat → ∀ a, OriginalLeaves leaf orig a → False

/-! ## §3 The well-founded lift through every recursive phase arm -/

/-- **W1 SAT LIFT**: if the phase driver over `k` reports `.sat w` from a
reachable configuration whose `orig` is the run's original box, then `w` is
a solution of the ORIGINAL box/leaf. Proved by WELL-FOUNDED INDUCTION on
`PhaseRank orig` — every recursive arm (`propagate`, `decide`,
`analyzeConflict`, `learnBackjumpAssert`, `localExclude`,
`chronologicalFallback`) transfers the obligation to its successor through
the frame identity; the two terminal arms are discharged by the lifted
terminal obligations (`hterm_sat` for `.sat`, contradiction for `.unsat`). -/
theorem runPhase_sat_solution {orig : List Domain} {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf)
    (hframe : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (k.step cfg).successor = some cfg' → cfg'.orig = cfg.orig)
    (hterm_sat : ∀ (cfg : SchedulerConfig leaf) (w : Assignment),
      SchedulerReachable cfg → cfg.orig = orig → k.step cfg = .sat w →
        SolutionWitness leaf orig w)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (horig : cfg.orig = orig) {w : Assignment}
    (hrun : runPhase k cfg hreach = .sat w) :
    SolutionWitness leaf orig w := by
  have main : ∀ (c : SchedulerConfig leaf) (hc : SchedulerReachable c),
      c.orig = orig → runPhase k c hc = .sat w →
        SolutionWitness leaf orig w := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => ∀ (hc : SchedulerReachable c), c.orig = orig →
        runPhase k c hc = .sat w → SolutionWitness leaf orig w) ?_
    intro c ih hc hcor hrun
    cases hstep : k.step c with
    | sat w' =>
        rw [runPhase_sat k c hc w' hstep] at hrun
        cases hrun
        exact hterm_sat c w hc hcor hstep
    | unsat =>
        rw [runPhase_unsat k c hc hstep] at hrun
        cases hrun
    | propagate n =>
        rw [runPhase_propagate k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | decide n l =>
        rw [runPhase_decide k c hc n l hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | analyzeConflict n c' =>
        rw [runPhase_analyzeConflict k c hc n c' hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | learnBackjumpAssert n p an =>
        rw [runPhase_learnBackjumpAssert k c hc n p an hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | localExclude n =>
        rw [runPhase_localExclude k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | chronologicalFallback n =>
        rw [runPhase_chronologicalFallback k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
  exact main cfg hreach horig hrun

/-- **W1 UNSAT LIFT**: if the phase driver over `k` reports `.unsat` from a
reachable configuration whose `orig` is the run's original box, then no
solution of the ORIGINAL box/leaf exists. Proved by WELL-FOUNDED INDUCTION
on `PhaseRank orig`: every recursive arm transfers the exclusion obligation
AND the preserved input identity to its successor (`hframe`); the `.sat`
terminal arm is contradictory, the `.unsat` terminal arm is the lifted
terminal obligation `hterm_unsat` (S5's exhausted-frontier /
root-contradiction arms at the dead terminal configuration, fixed-input
shape). -/
theorem runPhase_unsat_excludes {orig : List Domain} {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf)
    (hframe : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (k.step cfg).successor = some cfg' → cfg'.orig = cfg.orig)
    (hterm_unsat : ∀ (cfg : SchedulerConfig leaf), SchedulerReachable cfg →
      cfg.orig = orig → k.step cfg = .unsat →
        ∀ a, OriginalLeaves leaf orig a → False)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (horig : cfg.orig = orig)
    (hrun : runPhase k cfg hreach = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False := by
  have main : ∀ (c : SchedulerConfig leaf) (hc : SchedulerReachable c),
      c.orig = orig → runPhase k c hc = .unsat →
        ∀ a, OriginalLeaves leaf orig a → False := by
    intro c
    refine WellFounded.induction (InvImage.wf k.rank phaseLt_wf) c
      (C := fun c => ∀ (hc : SchedulerReachable c), c.orig = orig →
        runPhase k c hc = .unsat → ∀ a, OriginalLeaves leaf orig a → False) ?_
    intro c ih hc hcor hrun
    cases hstep : k.step c with
    | sat w' =>
        rw [runPhase_sat k c hc w' hstep] at hrun
        cases hrun
    | unsat =>
        rw [runPhase_unsat k c hc hstep] at hrun
        exact hterm_unsat c hc hcor hstep
    | propagate n =>
        rw [runPhase_propagate k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | decide n l =>
        rw [runPhase_decide k c hc n l hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | analyzeConflict n c' =>
        rw [runPhase_analyzeConflict k c hc n c' hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | learnBackjumpAssert n p an =>
        rw [runPhase_learnBackjumpAssert k c hc n p an hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | localExclude n =>
        rw [runPhase_localExclude k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
    | chronologicalFallback n =>
        rw [runPhase_chronologicalFallback k c hc n hstep] at hrun
        exact ih n (k.decrease c n hc (by rw [hstep]; rfl)) _
          ((hframe c n hc (by rw [hstep]; rfl)).trans hcor) hrun
  exact main cfg hreach horig hrun

/-! ## §4 Instantiations at the REAL phase dispatcher (X2's
`reachablePhaseKernel`, whose `step` is `phaseNext` definitionally) -/

/-- W1 SAT at the real phase driver: `.sat w` from a reachable configuration
initialized with `orig` yields a solution of that original box/leaf. -/
theorem run_sat_solution {orig : List Domain} {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSelf (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg')
    (hframe : PhaseOrigFrame orig leaf)
    (hsat : PhaseNextSatSolution orig leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (horig : cfg.orig = orig) {w : Assignment}
    (hrun : runPhaseFrom h hclos cfg hreach = .sat w) :
    SolutionWitness leaf orig w :=
  runPhase_sat_solution (reachablePhaseKernel h hclos)
    (fun cfg cfg' hreach hsucc => hframe cfg cfg' hreach hsucc)
    (fun cfg w hreach horig hsucc => hsat cfg w hreach horig hsucc)
    cfg hreach horig hrun

/-- W1 SAT at the real phase driver, SORTED instance (C2/D1): `.sat w` from
a reachable configuration initialized with `orig` yields a solution of that
original box/leaf, for the `runPhaseFromSorted` entry. -/
theorem run_sat_solution_sorted {orig : List Domain} {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSorted (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg')
    (hframe : PhaseOrigFrame orig leaf)
    (hsat : PhaseNextSatSolution orig leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (horig : cfg.orig = orig) {w : Assignment}
    (hrun : runPhaseFromSorted h hclos cfg hreach = .sat w) :
    SolutionWitness leaf orig w :=
  runPhase_sat_solution (reachablePhaseKernelSorted h hclos)
    (fun cfg cfg' hreach hsucc => hframe cfg cfg' hreach hsucc)
    (fun cfg w hreach horig hsucc => hsat cfg w hreach horig hsucc)
    cfg hreach horig hrun

/-- W1 UNSAT at the real phase driver: `.unsat` from a reachable
configuration initialized with `orig` excludes every solution of the run's
original box. -/
theorem run_unsat_excludes {orig : List Domain} {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSelf (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg')
    (hframe : PhaseOrigFrame orig leaf)
    (hunsat : PhaseUnsatTerminal orig leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (horig : cfg.orig = orig)
    (hrun : runPhaseFrom h hclos cfg hreach = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False :=
  runPhase_unsat_excludes (reachablePhaseKernel h hclos)
    (fun cfg cfg' hreach hsucc => hframe cfg cfg' hreach hsucc)
    (fun cfg hreach horig hsucc => hunsat cfg hreach horig hsucc)
    cfg hreach horig hrun

/-- W1 UNSAT at the real phase driver, SORTED instance (C2/D1): `.unsat`
from a reachable configuration initialized with `orig` excludes every
solution of the run's original box, for the `runPhaseFromSorted` entry. -/
theorem run_unsat_excludes_sorted {orig : List Domain} {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSorted (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg')
    (hframe : PhaseOrigFrame orig leaf)
    (hunsat : PhaseUnsatTerminal orig leaf)
    (cfg : SchedulerConfig leaf) (hreach : SchedulerReachable cfg)
    (horig : cfg.orig = orig)
    (hrun : runPhaseFromSorted h hclos cfg hreach = .unsat) :
    ∀ a, OriginalLeaves leaf orig a → False :=
  runPhase_unsat_excludes (reachablePhaseKernelSorted h hclos)
    (fun cfg cfg' hreach hsucc => hframe cfg cfg' hreach hsucc)
    (fun cfg hreach horig hsucc => hunsat cfg hreach horig hsucc)
    cfg hreach horig hrun

/-! ## §5 Totality on supported initialized input (no runtime contract)

The driver is X2's plain `def` over P5's well-founded recursion: for every
kernel, every reachable configuration and every initialized input a result
exists — no fuel, no assumed decrease, no open runtime contract. -/

/-- TOTALITY of the computable driver on every reachable input. -/
theorem runPhase_total {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf) (cfg : SchedulerConfig leaf)
    (hreach : SchedulerReachable cfg) :
    ∃ r : DriverResult leaf, runPhase k cfg hreach = r :=
  ⟨_, rfl⟩

/-- TOTALITY at the real phase driver on supported initialized input: the
root configuration of any original box is reachable (`R1.init`), hence has
a result. -/
theorem runPhase_total_init {orig : List Domain} {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf) (original : List Clause)
    (props : List Propagator) :
    ∃ r : DriverResult leaf,
      runPhase k (SchedulerConfig.init orig original props)
        (SchedulerReachable.init orig original props) = r :=
  ⟨_, rfl⟩

end LeanFzn.Solver.UIP.W1
