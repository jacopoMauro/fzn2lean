/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerPhaseProgress.lean

THE REACHABLE-STATE `PhaseProgress` REPLACEMENT over the UNIFIED RANK.

Gate (PLAN.md P5): "Assemble a reachable-state `PhaseProgress` replacement
over the unified rank and all actual phase successors. Prove termination
without `JumpDecrease`, `DomJumpDiscipline`, an assumed decrease, or user
verdict fuel. Restrict recursion to the preserved execution state/invariant
as needed. Retain F1 as a regression against the old contract; no claim that
changing the rank makes arbitrary fabricated states safe."

Contents (G1/C2 scoped 2026-10-11; see INTERFACES.md §G1):
  §1 `ReachablePhaseProgressSelf` / `ReachablePhaseProgressSorted` — the
     new obligations, stated on `SchedulerReachable` configurations only
     (F1's fabricated witness is NOT claimed safe) and over each
     configuration's SELF rank (`selfRank cfg = PhaseRank cfg.orig cfg`).
  §1b self-rank bridge lemmas (step projections, consume, stutter).
  §2 consume-landing helpers for the NEW rank (the P3 composites without
     the vestigial `status` guard, plus the shared phase decomposition and
     the rank-generic `phase_compose_consume_generic`).
  §3 `ReachableJumpRanked` — the ONE named residual, stated exactly at
     the real jump site, PROVED from P4's
     `phaseLt_stepLearnBackjumpAssert_of_reachable` given P4's own named
     SELF-RELATIVE premises (list in §6).
  §4 `reachablePhaseProgressRanked_of_premises` /
     `reachablePhaseProgressSorted_of_premises` — the ASSEMBLIES: every
     `phaseNext` arm allocated, one rank-generic body.
  §5 the well-founded recursion driver over the kernel's rank field,
     restricted to reachable configurations via a kernel carrying the
     reachability-closure field (owner S5/W1), plus the totality statement.
  §6 the consumed-lemma citation list: no `JumpDecrease`, no
     `DomJumpDiscipline`, no fuel.

DAG: Proofs.SchedulerRank (P3) + Proofs.SchedulerJumpProgress (P4) +
     Proofs.SchedulerReachable (R1) -> this module (consumed by X2/W1).
-/

import LeanFzn.Solver.UIP.Proofs.SchedulerJumpProgress
import LeanFzn.Solver.UIP.Proofs.SchedulerReachable
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP.P5
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.P3
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.P4
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.P4

/-! ## §1 The obligation: progress on reachable execution over the SELF rank

**G1 SCOPING (2026-10-11).** The rank read by every premise below is the
configuration's OWN-box rank: `selfRank cfg = P3.PhaseRank cfg.orig cfg`
(the pool component is `clausePool cfg.orig`). This is what makes the
concrete premises PROVABLE on a run: every real step preserves `orig`
definitionally (`W1.schedulerNext_succ_orig`), so a reachable configuration
is only ever compared against its own box's clause pool — a fixed-`orig`
premise quantifying over runs on OTHER boxes was uninhabitable and has been
replaced (it is not stated, not assumed). The `orig`-indexed adapters for
consumers that DO fix a box live in `W1`/`RunAssembly` (the `cfg.orig = orig`
terminal forms) and are fed by these self-relative premises.

The reachability hypothesis is load-bearing: the F1 witness
(`Proofs/JumpDecrease`) refutes the unrestricted contract, so no universal
statement over `SchedulerConfig` is made. The statement is not vacuous
(`schedulerReachable_init`). -/

/-- The SELF rank of a configuration: the P3 rank read at the
configuration's own original box (`PhaseRank cfg.orig cfg`). All real steps
preserve `orig` definitionally, so this is the rank every per-arm decrease
lemma instantiates to without any equality bookkeeping. -/
def selfRank {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) :
    Nat × Nat × Nat × Nat :=
  PhaseRank cfg.orig cfg

/-- Bridge: a configuration whose `orig` agrees with `cfg`'s has its
`selfRank` read at `cfg.orig` (`≡ PhaseRank cfg.orig _`). -/
theorem selfRank_eq_phaseRank {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} (h : cfg'.orig = cfg.orig) :
    selfRank cfg' = PhaseRank cfg.orig cfg' := by
  rw [selfRank, h]

/-- **THE P5 OBLIGATION (G1 SCOPED)**: every successor of the phase
dispatcher at a REACHABLE configuration strictly decreases the
configuration's SELF rank. Every premise a concrete producer must supply is
self-relative (see §§3–4), so the obligation is provable from the run's own
data; the previous unscoped fixed-`orig` shape is retired (it was not
inhabitable), and the name is distinct from R1's `ReachablePhaseProgress`
(the historical C3a-rank consumer interface). -/
def ReachablePhaseProgressSelf {leaf : Assignment → Bool} : Prop :=
  ∀ (cfg cfg' : SchedulerConfig leaf),
    SchedulerReachable cfg → (phaseNext cfg).successor = some cfg' →
      PhaseLt (selfRank cfg') (selfRank cfg)

/-- The SELF rank at the order-insensitive component (C2): the P4 sorted
rank read at the configuration's own original box. -/
def selfRankSorted {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) :
    Nat × Nat × Nat × Nat :=
  PhaseRankSorted cfg.orig cfg

/-- The sorted-rank obligation, G1-scoped exactly like
`ReachablePhaseProgress`. -/
def ReachablePhaseProgressSorted {leaf : Assignment → Bool} : Prop :=
  ∀ (cfg cfg' : SchedulerConfig leaf),
    SchedulerReachable cfg → (phaseNext cfg).successor = some cfg' →
      PhaseLt (selfRankSorted cfg') (selfRankSorted cfg)

/-! ### §1b Self-rank bridges: every real step projects `.orig` definitionally

All step functions of the runtime dispatcher build their result by structure
update (`{ cfg with … }`), so `X.orig` reduces to `cfg.orig` by `rfl`. The
bridges below turn each P3/P4 per-arm decrease — stated at an arbitrary
fixed `orig` — into the SELF-rank statement the generic assembly consumes,
with no equality bookkeeping at the call sites. -/

theorem selfRankSorted_eq_phaseRankSorted {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} (h : cfg'.orig = cfg.orig) :
    selfRankSorted cfg' = PhaseRankSorted cfg.orig cfg' := by
  rw [selfRankSorted, h]

theorem selfRank_stepPropagate {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (d : ProductiveDeduction leaf cfg.branch) :
    selfRank (stepPropagate cfg d) = PhaseRank cfg.orig (stepPropagate cfg d) :=
  rfl

theorem selfRank_stepDecide {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (vs : Domain) (doms : List Domain)
    (l : Literal) :
    selfRank (stepDecide cfg v vs doms l)
      = PhaseRank cfg.orig (stepDecide cfg v vs doms l) := rfl

theorem selfRank_stepDecideSkip {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (v : Value) (doms : List Domain) :
    selfRank (stepDecideSkip cfg v doms)
      = PhaseRank cfg.orig (stepDecideSkip cfg v doms) := rfl

theorem selfRank_stepLearnBackjumpAssert {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    selfRank (stepLearnBackjumpAssert cfg p ev restored)
      = PhaseRank cfg.orig (stepLearnBackjumpAssert cfg p ev restored) := rfl

theorem selfRank_stepLocalExclude {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (learned : List Clause) (r : DeadRegion) :
    selfRank (stepLocalExclude cfg learned r)
      = PhaseRank cfg.orig (stepLocalExclude cfg learned r) := rfl

theorem selfRank_stepChronologicalFallback {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (r : DeadRegion) :
    selfRank (stepChronologicalFallback cfg r)
      = PhaseRank cfg.orig (stepChronologicalFallback cfg r) := rfl

/-- The consume site preserves `orig` (pure projection lemma; the same
fact as `W1.stepConsume_orig`, hosted here because the self-rank bridges
below need it inside P5). -/
theorem p5_stepConsume_orig {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} (h : stepConsume cfg = some next) :
    next.orig = cfg.orig := by
  unfold stepConsume at h
  split at h <;> first
    | (simp only [Option.some.injEq] at h; subst h; rfl)
    | (cases h)

theorem selfRank_stepConsume {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} (h : stepConsume cfg = some next) :
    selfRank next = PhaseRank cfg.orig next := by
  rw [selfRank_eq_phaseRank (p5_stepConsume_orig h)]

theorem selfRankSorted_stepConsume {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} (h : stepConsume cfg = some next) :
    selfRankSorted next = PhaseRankSorted cfg.orig next := by
  rw [selfRankSorted_eq_phaseRankSorted (p5_stepConsume_orig h)]

theorem selfRank_analyzeConflictCounted_stutter {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause) (n : Nat) :
    selfRank (stepAnalyzeConflictCounted cfg c learned n) = selfRank cfg := by
  rw [selfRank_eq_phaseRank (show
      (stepAnalyzeConflictCounted cfg c learned n).orig = cfg.orig from rfl),
    P3.phaseRank_analyzeConflictCounted_stutter, ← selfRank_eq_phaseRank
      (cfg := cfg) (cfg' := cfg) rfl]

theorem selfRankSorted_analyzeConflictCounted_stutter {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause) (n : Nat) :
    selfRankSorted (stepAnalyzeConflictCounted cfg c learned n)
      = selfRankSorted cfg := by
  rw [selfRankSorted_eq_phaseRankSorted (show
      (stepAnalyzeConflictCounted cfg c learned n).orig = cfg.orig from rfl),
    P4.phaseRankSorted_analyzeConflictCounted_stutter, ← selfRankSorted_eq_phaseRankSorted
      (cfg := cfg) (cfg' := cfg) rfl]

/-! ## §2 Consume-landing helpers for the new rank

The P3 composites `phaseRank_lt_fallback_then_consume` /
`phaseRank_lt_localExclude_then_consume` carry a vestigial `status = .active`
guard that their bodies do not use; the consume landings below reproduce
their kernel-checked proofs WITHOUT the guard (the guard is not available
at the recorded-evidence route). No other change. -/

/-- Fallback-then-consume composite for the new rank, unguarded. -/
theorem fallback_then_consume_ranked (orig : List Domain)
    {leaf : Assignment → Bool} {cfg next : SchedulerConfig leaf} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    PhaseLt (PhaseRank orig next) (PhaseRank orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := stepConsume_learned h
  have hwork : frontierCost next.frontier
      < frontierCost (stepChronologicalFallback cfg r).frontier := by
    show frontierCost (next.branch.frame :: next.pending)
      < frontierCost ((stepChronologicalFallback cfg r).branch.frame
          :: (stepChronologicalFallback cfg r).pending)
    rw [hframe, hpend, hp]
    exact frontierCost_cons _ _
  refine Or.inr ⟨?_, Or.inl ?_⟩
  · show absentCount next.branch.learned (clausePool orig) =
      absentCount cfg.branch.learned (clausePool orig)
    rw [hlearn, stepChronologicalFallback_learned_eq]
  · show frontierCost next.frontier < frontierCost cfg.frontier
    rwa [show frontierCost (stepChronologicalFallback cfg r).frontier
        = frontierCost cfg.frontier from rfl] at hwork

/-- LocalExclude-then-consume composite for the new rank, unguarded. -/
theorem localExclude_then_consume_ranked (orig : List Domain)
    {leaf : Assignment → Bool} {cfg next : SchedulerConfig leaf}
    {learned : List Clause} {r : DeadRegion}
    {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    PhaseLt (PhaseRank orig next) (PhaseRank orig cfg) := by
  obtain ⟨hframe, hpend⟩ := C3a.stepConsume_frame_of_pending_cons hp h
  have hlearn := stepConsume_learned h
  have hrem1 := absent_localExclude_le orig cfg learned r
  have hwork : frontierCost next.frontier
      < frontierCost (stepLocalExclude cfg learned r).frontier := by
    show frontierCost (next.branch.frame :: next.pending)
      < frontierCost ((stepLocalExclude cfg learned r).branch.frame
          :: (stepLocalExclude cfg learned r).pending)
    rw [hframe, hpend, hp]
    exact frontierCost_cons _ _
  rcases Nat.lt_or_eq_of_le hrem1 with hlt | heq
  · refine Or.inl ?_
    show absentCount next.branch.learned (clausePool orig)
      < absentCount cfg.branch.learned (clausePool orig)
    rw [hlearn]
    exact hlt
  · refine Or.inr ⟨?_, Or.inl ?_⟩
    · show absentCount next.branch.learned (clausePool orig) =
        absentCount cfg.branch.learned (clausePool orig)
      rw [hlearn]
      exact heq
    · show frontierCost next.frontier < frontierCost cfg.frontier
      rwa [show frontierCost (stepLocalExclude cfg learned r).frontier
          = frontierCost cfg.frontier from rfl] at hwork

/-- The single consume-landing decomposition shared by every composed
landing of `phaseNext`: the phase value at `cfg` IS the consume route of
the intermediate configuration `n`, so its successor is exactly
`stepConsume n`'s result and the site composite at `n` pays. -/
theorem phase_compose_consume_ranked {orig : List Domain} {leaf : Assignment → Bool}
    {cfg cfg' n : SchedulerConfig leaf}
    (hpe : phaseNext cfg =
      (match stepConsume n with
       | some next => (.chronologicalFallback next : SchedulerTransition leaf)
       | none => .unsat))
    (hlt : ∀ {f : BranchFrame} {rest : List BranchFrame} {next : SchedulerConfig leaf},
      n.pending = f :: rest → stepConsume n = some next →
        PhaseLt (PhaseRank orig next) (PhaseRank orig cfg))
    (hsucc : (phaseNext cfg).successor = some cfg') :
    PhaseLt (PhaseRank orig cfg') (PhaseRank orig cfg) := by
  cases hsc : stepConsume n with
  | none =>
      rw [hpe, hsc] at hsucc
      simp at hsucc
  | some next =>
      rw [hpe, hsc] at hsucc
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      cases hsucc
      cases hpend : n.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := n)).mpr hpend] at hsc
          cases hsc
      | cons f rest => exact hlt hpend hsc

/-- **THE RANK-GENERIC CONSUME-LANDING DECOMPOSITION** (G1/C2): the single
`phaseNext` consume composite, with the inner landing supplied at the SAME
rank FUNCTION. The fixed-`orig` instance is `phase_compose_consume_ranked`;
the self-rank instances use this one directly — the successor `cfg'` is the
`next` handed over by the forced consume, so the inner landing's conclusion
is already at the right rank and no `orig` conversion is needed here. -/
theorem phase_compose_consume_generic {leaf : Assignment → Bool}
    {rank : SchedulerConfig leaf → Nat × Nat × Nat × Nat}
    {cfg cfg' n : SchedulerConfig leaf}
    (hpe : phaseNext cfg =
      (match stepConsume n with
       | some next => (.chronologicalFallback next : SchedulerTransition leaf)
       | none => .unsat))
    (hlt : ∀ {f : BranchFrame} {rest : List BranchFrame} {next : SchedulerConfig leaf},
      n.pending = f :: rest → stepConsume n = some next →
        PhaseLt (rank next) (rank cfg))
    (hsucc : (phaseNext cfg).successor = some cfg') :
    PhaseLt (rank cfg') (rank cfg) := by
  cases hsc : stepConsume n with
  | none =>
      rw [hpe, hsc] at hsucc
      simp at hsucc
  | some next =>
      rw [hpe, hsc] at hsucc
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      cases hsucc
      cases hpend : n.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := n)).mpr hpend] at hsc
          cases hsc
      | cons f rest => exact hlt hpend hsc

/-! ## §3 The named jump residual, proved from P4

The residual is stated EXACTLY at the real jump site (recorded evidence,
successful `perform`, checkpoint plan). Its proof is P4's reachable-site
wrapper; the named premises P4 demands become the assembly theorem's
arguments (§4) with the owners listed in §6. -/

/-- The jump-site rank decrease at a reachable configuration with recorded
evidence and a successful checkpoint restore — G1 shape: the decrease is
read at the configuration's SELF rank (`selfRank`), so the premises below
(P4's `hpool`/`hdb`/`hbr`) are consumed at `c0.orig` only. -/
def ReachableJumpRanked {leaf : Assignment → Bool} : Prop :=
  ∀ (c0 : SchedulerConfig leaf) (cp : DecisionCheckpoint leaf)
    (ev : ConflictEvidence) (an : ConflictAnalysis) (restored : BranchState leaf),
    SchedulerReachable c0 →
    c0.conflict = some ev →
    ev.analysis = some an →
    (BackjumpPlan.ofCheckpoint cp c0.branch an.asserting an.learned).perform
        c0.branch c0.orig c0.original c0.props = some restored →
    PhaseLt (selfRank (stepLearnBackjumpAssert c0
        (BackjumpPlan.ofCheckpoint cp c0.branch an.asserting an.learned) ev restored))
      (selfRank c0)

/-- PROOF of the residual from P4 + the three named P4 premises, all
SELF-RELATIVE (G1): pool membership at the configuration's own box,
NOVELTY of the recorded analysis (RESTATED by R1c: this premise was
`DatabaseUnfalsified cfg.branch`, which conflict routing falsifies at
database-sourced sites; the unfalsified-database discharge is kept as
`jumpNovelty_of_dbUnfalsified_site`), branch reachability of the
configuration's own box. -/
theorem reachableJumpRanked_of_premises {leaf : Assignment → Bool}
    (hpool : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg → cfg.conflict = some ev →
        ev.analysis = some an →
          Clause.canonicalClause an.learned ∈ clausePool cfg.orig)
    (hnov : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg → cfg.conflict = some ev →
        ev.analysis = some an → JumpNovelty cfg.branch.learned an)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ReachableState leaf cfg.orig cfg.branch) :
    ReachableJumpRanked (leaf := leaf) := by
  intro c0 cp ev an restored hreach hconf hana hperf
  have h := P4.phaseLt_stepLearnBackjumpAssert_of_novelty (ev := ev)
    (hpool hreach hconf hana) hperf
    (planMatchesAnalysis_ofCheckpoint cp c0.branch an)
    (hnov hreach hconf hana)
  simpa only [selfRank, stepLearnBackjumpAssert_orig] using h

/-- The OLD discharge of the novelty premise (kept by R1c): on a reachable
recorded site whose learned database is unfalsified, the recorded analysis is
novel. Valid at the propagator-sourced sites; it does NOT hold at routed
(database-sourced) sites, which is why the rank theorems now take the
novelty itself. -/
theorem jumpNovelty_of_dbUnfalsified_site {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence} {an : ConflictAnalysis}
    (hdb : DatabaseUnfalsified cfg.branch)
    (hbr : ReachableState leaf cfg.orig cfg.branch)
    (hreach : SchedulerReachable cfg) (hconf : cfg.conflict = some ev)
    (hana : ev.analysis = some an) :
    JumpNovelty cfg.branch.learned an :=
  jumpNovelty_of_unfalsified hdb
    (recordedAnalysis_normFalsified (bs := cfg.branch) rfl hbr hreach hconf hana)

/-! ## §4 The assembly: every phase arm allocated

Route structure (same three-way split as the real dispatcher,
`C2d.schedulerNext_cases`); each leaf is discharged by a NAMED theorem:

| phase arm                                | allocated theorem                     |
| ---                                       | ---                                   |
| ARM 1 propagate                           | `P3.phaseRank_lt_propagate`           |
| ARM 2/3 decide                            | `P3.phaseRank_lt_decide`              |
| consume route (dead, no evidence)         | `P3.phaseRank_lt_consume`             |
| ARM 6 / stable-none / conflict-nil        | §2 `localExclude_then_consume_ranked` |
| fallback stutters (route 1, analyze-none) | §2 `fallback_then_consume_ranked`     |
| checkpoint rejection                      | §2 `localExclude_then_consume_ranked` |
| recorded jump (route 1)                   | §3 `ReachableJumpRanked` (P4)         |
| analyze-site jump (ARM 4)                 | §3 `ReachableJumpRanked` + P3 stutter |
| analyze recorder                          | `P3.phaseRank_analyzeConflictCounted_stutter` |
| `.sat`/`.unsat`/root contradiction        | terminal (no successor: vacuous)      | -/

/-- **THE P5 ASSEMBLY, RANK- AND INDEX-GENERIC**: every phase
arm allocated, with the per-arm decreases and the composite landings
supplied as hypotheses BOUND UNDER THE SAME NAMES as the concrete P3/P5
lemmas, so the body below is shared verbatim between the raw-reachability
instances (the SELF-rank instance `reachablePhaseProgressRanked_of_premises`,
frozen name; and the order-insensitive SELF-rank instance
`reachablePhaseProgressSorted_of_premises`, C2) and the SUPPORTED-run
instance (S2's `SupportedPhaseRun.supportedPhaseProgressSorted_of_premises`,
indexed by `SupportedReach`). The reachability index `R` is an explicit
parameter with its own step-closure `Rstep`; the rank function is an
explicit parameter; every other input is a per-arm decrease about THAT rank
function. -/
theorem reachablePhaseProgress_of_arms {leaf : Assignment → Bool}
    (R : SchedulerConfig leaf → Prop)
    (Rstep : ∀ {cfg cfg' : SchedulerConfig leaf}, R cfg →
      (schedulerNext cfg).successor = some cfg' → R cfg')
    (rank : SchedulerConfig leaf → Nat × Nat × Nat × Nat)
    (phaseRank_lt_propagate : ∀
      (cfg : SchedulerConfig leaf) (d : ProductiveDeduction leaf cfg.branch),
      PhaseLt (rank (stepPropagate cfg d)) (rank cfg))
    (phaseRank_lt_decide : ∀ (cfg : SchedulerConfig leaf)
      (v : Value) (vs : Domain) (doms : List Domain) (l : Literal),
      splitData cfg.branch.frame = some (l, v, vs, doms) →
        PhaseLt (rank (stepDecide cfg v vs doms l)) (rank cfg))
    (phaseRank_lt_decideSkip : ∀
      (cfg : SchedulerConfig leaf) (v : Value) (vs : Domain) (doms : List Domain)
      (l : Literal), splitData cfg.branch.frame = some (l, v, vs, doms) →
        PhaseLt (rank (stepDecideSkip cfg v doms)) (rank cfg))
    (phaseRank_lt_consume : ∀
      {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame},
      cfg.pending = f :: rest → stepConsume cfg = some next →
        PhaseLt (rank next) (rank cfg))
    (phase_compose_consume_ranked : ∀
      {cfg cfg' n : SchedulerConfig leaf},
      phaseNext cfg =
        (match stepConsume n with
         | some next => (.chronologicalFallback next : SchedulerTransition leaf)
         | none => .unsat) →
      (∀ {f : BranchFrame} {rest : List BranchFrame} {next : SchedulerConfig leaf},
        n.pending = f :: rest → stepConsume n = some next →
          PhaseLt (rank next) (rank cfg)) →
      (phaseNext cfg).successor = some cfg' → PhaseLt (rank cfg') (rank cfg))
    (fallback_then_consume_ranked : ∀
      {cfg next : SchedulerConfig leaf} {r : DeadRegion} {f : BranchFrame}
      {rest : List BranchFrame},
      (stepChronologicalFallback cfg r).pending = f :: rest →
      stepConsume (stepChronologicalFallback cfg r) = some next →
        PhaseLt (rank next) (rank cfg))
    (localExclude_then_consume_ranked : ∀
      {cfg next : SchedulerConfig leaf} {learned : List Clause}
      {r : DeadRegion} {f : BranchFrame} {rest : List BranchFrame},
      (stepLocalExclude cfg learned r).pending = f :: rest →
      stepConsume (stepLocalExclude cfg learned r) = some next →
        PhaseLt (rank next) (rank cfg))
    (phaseRank_analyzeConflictCounted_stutter : ∀
      (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause) (n : Nat),
      rank (stepAnalyzeConflictCounted cfg c learned n) = rank cfg)
    (hjump : ∀ (c0 : SchedulerConfig leaf) (cp : DecisionCheckpoint leaf)
      (ev : ConflictEvidence) (an : ConflictAnalysis)
      (restored : BranchState leaf),
      R c0 → c0.conflict = some ev → ev.analysis = some an →
      (BackjumpPlan.ofCheckpoint cp c0.branch an.asserting an.learned).perform
          c0.branch c0.orig c0.original c0.props = some restored →
        PhaseLt (rank (stepLearnBackjumpAssert c0
            (BackjumpPlan.ofCheckpoint cp c0.branch an.asserting an.learned) ev
            restored)) (rank c0)) :
    ∀ (cfg cfg' : SchedulerConfig leaf), R cfg →
      (phaseNext cfg).successor = some cfg' → PhaseLt (rank cfg') (rank cfg) := by
  intro cfg cfg' hreach hsucc
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (schedulerNext cfg = backjumpStep cfg ev)
    cases ha : ev.analysis with
    | none =>
        -- ARM 7a stutter → forced consume
        refine phase_compose_consume_ranked
          (n := stepChronologicalFallback cfg (branchRegion cfg))
          ?_ (fun hp h => fallback_then_consume_ranked hp h) hsucc
        simp only [phaseNext, hnext, backjumpStep, ha, hc]
        rfl
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            -- ARM 7b stutter (no saved checkpoint) → forced consume
            refine phase_compose_consume_ranked
              (n := stepChronologicalFallback cfg (branchRegion cfg))
              ?_ (fun hp h => fallback_then_consume_ranked hp h) hsucc
            simp only [phaseNext, hnext, backjumpStep, ha, hcp, hc]
            rfl
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                -- the assertion rejects the restored ancestor: localExclude
                -- stutter → forced consume
                refine phase_compose_consume_ranked
                  (n := stepLocalExclude cfg ev.learned (checkpointRegion cp))
                  ?_ (fun hp' h => localExclude_then_consume_ranked hp' h) hsucc
                simp only [phaseNext, hnext, backjumpStep, ha, hcp, hp]
                rfl
            | some restored =>
                -- the real jump: passed through; decrease = §3 (P4)
                have hpe : phaseNext cfg =
                    .learnBackjumpAssert
                      (stepLearnBackjumpAssert cfg
                        (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                          an.learned) ev restored)
                      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                        an.learned) an := by
                  simp only [phaseNext, hnext, backjumpStep, ha, hcp, hp]
                rw [hpe] at hsucc
                simp only [successor_learnBackjumpAssert, Option.some.injEq] at hsucc
                cases hsucc
                exact hjump cfg cp ev an restored hreach hc ha hp
  · -- ===== ROUTE 2: dead branch — the REAL consume route
    cases hsc : stepConsume cfg with
    | none =>
        have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
          simp only [phaseNext, hnext, consumeStep, hsc]
        rw [hpe] at hsucc
        simp at hsucc
    | some next =>
        have hpe : phaseNext cfg = .chronologicalFallback next := by
          simp only [phaseNext, hnext, consumeStep, hsc, hconf]
        rw [hpe] at hsucc
        simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
        cases hsucc
        cases hpend : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hsc
            cases hsc
        | cons f rest => exact phaseRank_lt_consume hpend hsc
  · -- ===== ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- ARM 1: propagate
      have hpe : phaseNext cfg = .propagate (stepPropagate cfg d) := by
        simp only [phaseNext, hnext]
      rw [hpe] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      cases hsucc
      exact phaseRank_lt_propagate cfg d
    · -- ARM 2 / ARM 3 / ARM 6: stableStepGuarded (B1: fresh or skip)
      cases hw : leafWitness leaf cfg with
      | some w =>
          have hpe : phaseNext cfg = (.sat w : SchedulerTransition leaf) := by
            simp only [phaseNext, hnext, stableStepGuarded, hw]
          rw [hpe] at hsucc
          simp at hsucc
      | none =>
          cases hsp : splitData cfg.branch.frame with
          | some q =>
              obtain ⟨l, v, vs, doms⟩ := q
              by_cases hred : TrailRedundant cfg.branch.trail l = true
              · -- ARM 2b (B1): the redundant-pin skip, rank decrease by the
                -- chronological component (ready lemma)
                have hs : schedulerNext cfg =
                    .decide (stepDecideSkip cfg v doms) l := by
                  rw [hnext]
                  simp only [stableStepGuarded, hw, hsp]
                  rw [if_pos hred]
                have hpe : phaseNext cfg =
                    .decide (stepDecideSkip cfg v doms) l := by
                  simp only [phaseNext, hs]
                rw [hpe] at hsucc
                simp only [successor_decide, Option.some.injEq] at hsucc
                cases hsucc
                exact phaseRank_lt_decideSkip cfg v vs doms l hsp
              · -- ARM 2a: the fresh decision
                have hred' : TrailRedundant cfg.branch.trail l = false := by
                  cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
                have hs : schedulerNext cfg =
                    .decide (stepDecide cfg v vs doms l) l := by
                  rw [hnext]
                  simp only [stableStepGuarded, hw, hsp]
                  rw [if_neg]
                  rw [hred']
                  simp
                have hpe : phaseNext cfg =
                    .decide (stepDecide cfg v vs doms l) l := by
                  simp only [phaseNext, hs]
                rw [hpe] at hsucc
                simp only [successor_decide, Option.some.injEq] at hsucc
                cases hsucc
                exact phaseRank_lt_decide cfg v vs doms l hsp
          | none =>
              -- ARM 6: localExclude stutter → forced consume
              refine phase_compose_consume_ranked
                (n := stepLocalExclude cfg [] (branchRegion cfg))
                ?_ (fun hp h => localExclude_then_consume_ranked hp h) hsucc
              simp only [phaseNext, hnext, stableStepGuarded, hw, hsp]
              rfl
    · -- ARM 8 / ARM 4 / ARM 6: conflictStep
      cases cs with
      | nil =>
          -- empty reported clause list: LOCAL exclusion → forced consume
          refine phase_compose_consume_ranked
            (n := stepLocalExclude cfg learned (branchRegion cfg))
            ?_ (fun hp h => localExclude_then_consume_ranked hp h) hsucc
          simp only [phaseNext, hnext, conflictStep]
          rfl
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · -- level 0: root contradiction (terminal, vacuous)
            have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
              simp only [phaseNext, hnext, conflictStep, if_pos hlv]
            rw [hpe] at hsucc
            simp at hsucc
          · -- ARM 4: the analyze site — resolved through the recorded route
            cases hev : (stepAnalyzeConflictCounted cfg c learned
                (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).conflict with
            | none =>
                simp [stepAnalyzeConflictCounted, stepAnalyzeConflict,
                  SchedulerConfig.countResolutions] at hev
            | some ev =>
                -- the recorded config is a REAL dispatcher successor
                have hsuccN : (conflictStep cfg (c :: rest) learned).successor =
                    some (stepAnalyzeConflictCounted cfg c learned
                      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) := by
                  simp only [conflictStep, if_neg hlv]
                  rfl
                have hreachN : R (stepAnalyzeConflictCounted cfg c
                    learned (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) :=
                  Rstep hreach (by rw [hnext]; exact hsuccN)
                have hstut := phaseRank_analyzeConflictCounted_stutter cfg c learned
                  (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)
                cases ha : ev.analysis with
                | none =>
                    refine phase_compose_consume_ranked
                      (n := stepChronologicalFallback
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                        (branchRegion (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))))
                      ?_ (fun hp h => ?_) hsucc
                    · simp only [phaseNext, hnext, conflictStep, if_neg hlv, hev,
                        backjumpStep, ha]
                      rfl
                    · have h' := fallback_then_consume_ranked hp h
                      simpa only [hstut] using h'
                | some an =>
                    have hstep_orig :
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).original
                          = cfg.original := rfl
                    have hstep_props :
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).props
                          = cfg.props := rfl
                    have hstep_dom :
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).orig
                          = cfg.orig := rfl
                    cases hcp : checkpointAt
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).checkpoints
                        an.backjumpLevel with
                    | none =>
                        refine phase_compose_consume_ranked
                          (n := stepChronologicalFallback
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                            (branchRegion (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))))
                          ?_ (fun hp h => ?_) hsucc
                        · simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                            hev, backjumpStep, ha, hcp]
                          rfl
                        · have h' := fallback_then_consume_ranked hp h
                          simpa only [hstut] using h'
                    | some cp =>
                        cases hp : (BackjumpPlan.ofCheckpoint cp
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                            an.asserting an.learned).perform
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                            cfg.orig
                            cfg.original cfg.props with
                        | none =>
                            -- checkpoint rejection → localExclude → consume
                            refine phase_compose_consume_ranked
                              (n := stepLocalExclude
                                (stepAnalyzeConflictCounted cfg c learned
                                  (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                                ev.learned (checkpointRegion cp))
                              ?_ (fun hp' h => ?_) hsucc
                            · simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                                hev, backjumpStep, ha, hcp, hstep_orig, hstep_props, hstep_dom, hp]
                              rfl
                            · have h' := localExclude_then_consume_ranked hp' h
                              simpa only [hstut] using h'
                        | some restored =>
                            -- the recorded jump: §3 at the counted config +
                            -- the P3 analyze stutter
                            have hpe : phaseNext cfg =
                                .learnBackjumpAssert
                                  (stepLearnBackjumpAssert
                                    (stepAnalyzeConflictCounted cfg c learned
                                      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                                    (BackjumpPlan.ofCheckpoint cp
                                      (stepAnalyzeConflictCounted cfg c learned
                                        (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                                      an.asserting an.learned) ev restored)
                                  (BackjumpPlan.ofCheckpoint cp
                                    (stepAnalyzeConflictCounted cfg c learned
                                      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).branch
                                    an.asserting an.learned) an := by
                              simp only [phaseNext, hnext, conflictStep,
                                if_neg hlv, hev, backjumpStep, ha, hcp,
                                hstep_orig, hstep_props, hstep_dom, hp]
                            rw [hpe] at hsucc
                            simp only [successor_learnBackjumpAssert,
                              Option.some.injEq] at hsucc
                            cases hsucc
                            simpa only [hstut] using hjump
                              (stepAnalyzeConflictCounted cfg c learned
                                (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                              cp ev an restored hreachN hev ha hp
    · -- ARM 6: localExcluded → localExclude stutter → forced consume
      refine phase_compose_consume_ranked
        (n := stepLocalExclude cfg learned (branchRegion cfg))
        ?_ (fun hp h => localExclude_then_consume_ranked hp h) hsucc
      simp only [phaseNext, hnext]
      rfl

/-! ## §4b The sorted consume landings (C2's rank components)

Proved here (not in P4) because they need `phaseNext`. The rank-agnostic
part (`phase_compose_consume_sorted`) mirrors the P5 original; the two
one-shot landings wrap P4's sorted composites. -/

/-- The single consume-landing decomposition at the sorted rank. -/
theorem phase_compose_consume_sorted {orig : List Domain}
    {leaf : Assignment → Bool} {cfg cfg' n : SchedulerConfig leaf}
    (hpe : phaseNext cfg =
      (match stepConsume n with
       | some next => (.chronologicalFallback next : SchedulerTransition leaf)
       | none => .unsat))
    (hlt : ∀ {f : BranchFrame} {rest : List BranchFrame} {next : SchedulerConfig leaf},
      n.pending = f :: rest → stepConsume n = some next →
        PhaseLt (PhaseRankSorted orig next) (PhaseRankSorted orig cfg))
    (hsucc : (phaseNext cfg).successor = some cfg') :
    PhaseLt (PhaseRankSorted orig cfg') (PhaseRankSorted orig cfg) := by
  cases hsc : stepConsume n with
  | none =>
      rw [hpe, hsc] at hsucc
      simp at hsucc
  | some next =>
      rw [hpe, hsc] at hsucc
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      cases hsucc
      cases hpend : n.pending with
      | nil =>
          rw [(stepConsume_eq_none_iff (cfg := n)).mpr hpend] at hsc
          cases hsc
      | cons f rest => exact hlt hpend hsc

/-- **THE P5 ASSEMBLY (frozen name, G1 SELF-RANK INSTANCE)**:
`ReachablePhaseProgress` holds from P4's three named inputs, all
SELF-RELATIVE: `hpool` (canonical-pool membership at the configuration's
own box), `hnov` (novelty of the recorded analysis, restated by R1c from the
unfalsified-database premise), `hbr` (branch reachability over the
configuration's own box). Derived from the generic rank-parameterized
assembly at `rank := selfRank cfg = PhaseRank cfg.orig cfg`, with every
per-arm decrease bridged from its P3 statement by the definitional `orig`
projection (`selfRank_*` bridges above). -/
theorem reachablePhaseProgressRanked_of_premises {leaf : Assignment → Bool}
    (hpool : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg → cfg.conflict = some ev →
        ev.analysis = some an →
          Clause.canonicalClause an.learned ∈ clausePool cfg.orig)
    (hnov : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SchedulerReachable cfg → cfg.conflict = some ev →
        ev.analysis = some an → JumpNovelty cfg.branch.learned an)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ReachableState leaf cfg.orig cfg.branch) :
    ReachablePhaseProgressSelf (leaf := leaf) :=
  reachablePhaseProgress_of_arms (leaf := leaf) (R := SchedulerReachable)
    (Rstep := fun h hs => SchedulerReachable.step rfl hs h) selfRank
    (fun cfg d => by
      show PhaseLt (PhaseRank cfg.orig (stepPropagate cfg d)) (PhaseRank cfg.orig cfg)
      exact phaseRank_lt_propagate cfg.orig cfg d)
    (fun cfg v vs doms l hsplit => by
      show PhaseLt (PhaseRank cfg.orig (stepDecide cfg v vs doms l))
        (PhaseRank cfg.orig cfg)
      exact phaseRank_lt_decide cfg.orig cfg v vs doms l hsplit)
    (fun cfg v vs doms l hsplit => by
      show PhaseLt (PhaseRank cfg.orig (stepDecideSkip cfg v doms))
        (PhaseRank cfg.orig cfg)
      exact P3.phaseRank_lt_decideSkip cfg.orig cfg v vs doms l hsplit)
    (fun {cfg next f rest} hp h => by
      rw [selfRank_stepConsume h]
      exact P3.phaseRank_lt_consume cfg.orig hp h)
    (fun hpe hlt hsucc => phase_compose_consume_generic hpe hlt hsucc)
    (fun {cfg next r f rest} hp h => by
      rw [selfRank_stepConsume h]
      exact fallback_then_consume_ranked cfg.orig hp h)
    (fun {cfg next learned r f rest} hp h => by
      rw [selfRank_stepConsume h]
      exact localExclude_then_consume_ranked cfg.orig hp h)
    (fun cfg c learned n =>
      selfRank_analyzeConflictCounted_stutter cfg c learned n)
    (fun c0 cp ev an restored =>
      reachableJumpRanked_of_premises hpool hnov hbr c0 cp ev an restored)

/-- **THE C2 SORTED SELF-RANK INSTANCE**: `ReachablePhaseProgressSorted`
holds from the order-insensitive components' SELF-RELATIVE premises —
`hnov` (sorted novelty of the recorded analysis; RESTATED by R1c from the
unfalsified-database premise `hdb`, which conflict routing falsifies at
database-sourced sites — the old discharge is
`P4.sortedNovelty_of_unfalsified`), `hbr` (branch reachability over the
configuration's own box), `halignDB` (database-side literal pool alignment
at the configuration's own box, no longer consumed by the jump arm but kept
as the pool-side premise of the bundle) — with the sorted jump decrease
`P4.phaseLtSorted_stepLearnBackjumpAssert` (no `hpool`, no sublist
ordering, no `AnalysisDiffersFromConflict`). -/
theorem reachablePhaseProgressSorted_of_premises {leaf : Assignment → Bool}
    (halignDB : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ∀ c ∈ cfg.branch.learned, ∀ q ∈ c, q.norm ∈ litPool cfg.orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg →
      ReachableState leaf cfg.orig cfg.branch) :
    ReachablePhaseProgressSorted (leaf := leaf) :=
  reachablePhaseProgress_of_arms (leaf := leaf) (R := SchedulerReachable)
    (Rstep := fun h hs => SchedulerReachable.step rfl hs h) selfRankSorted
    (fun cfg d => by
      show PhaseLt (PhaseRankSorted cfg.orig (stepPropagate cfg d))
        (PhaseRankSorted cfg.orig cfg)
      exact P4.phaseRankSorted_lt_propagate cfg.orig cfg d)
    (fun cfg v vs doms l hsplit => by
      show PhaseLt (PhaseRankSorted cfg.orig (stepDecide cfg v vs doms l))
        (PhaseRankSorted cfg.orig cfg)
      exact P4.phaseRankSorted_lt_decide cfg.orig cfg v vs doms l hsplit)
    (fun cfg v vs doms l hsplit => by
      show PhaseLt (PhaseRankSorted cfg.orig (stepDecideSkip cfg v doms))
        (PhaseRankSorted cfg.orig cfg)
      exact P4.phaseRankSorted_lt_decideSkip cfg.orig cfg v vs doms l hsplit)
    (fun {cfg next f rest} hp h => by
      rw [selfRankSorted_stepConsume h]
      exact P4.phaseRankSorted_lt_consume cfg.orig hp h)
    (fun hpe hlt hsucc => phase_compose_consume_generic hpe hlt hsucc)
    (fun {cfg next r f rest} hp h => by
      rw [selfRankSorted_stepConsume h]
      exact P4.fallback_then_consume_sorted cfg.orig hp h)
    (fun {cfg next learned r f rest} hp h => by
      rw [selfRankSorted_stepConsume h]
      exact P4.localExclude_then_consume_sorted cfg.orig hp h)
    (fun cfg c learned n =>
      selfRankSorted_analyzeConflictCounted_stutter cfg c learned n)
    (fun c0 cp ev an restored hreach hconf hana hperf => by
      show PhaseLt
        (PhaseRankSorted c0.orig (stepLearnBackjumpAssert c0
          (BackjumpPlan.ofCheckpoint cp c0.branch an.asserting an.learned) ev
          restored)) (PhaseRankSorted c0.orig c0)
      exact P4.phaseLtSorted_stepLearnBackjumpAssert
        (P4.sortedNovelty_of_not_repeats (reachable_analysis_novel hreach hconf hana))
        hperf (planMatchesAnalysis_ofCheckpoint cp c0.branch an))

/-- Sorted-rank FALLBACK-then-consume landing (alias of P4's). -/
theorem fallback_then_consume_sorted {orig : List Domain}
    {leaf : Assignment → Bool} {cfg next : SchedulerConfig leaf}
    {r : DeadRegion} {f : BranchFrame} {rest : List BranchFrame}
    (hp : (stepChronologicalFallback cfg r).pending = f :: rest)
    (h : stepConsume (stepChronologicalFallback cfg r) = some next) :
    PhaseLt (PhaseRankSorted orig next) (PhaseRankSorted orig cfg) :=
  P4.fallback_then_consume_sorted orig hp h

/-- Sorted-rank localExclude-then-consume landing (alias of P4's). -/
theorem localExclude_then_consume_sorted {orig : List Domain}
    {leaf : Assignment → Bool} {cfg next : SchedulerConfig leaf}
    {learned : List Clause} {r : DeadRegion} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : (stepLocalExclude cfg learned r).pending = f :: rest)
    (h : stepConsume (stepLocalExclude cfg learned r) = some next) :
    PhaseLt (PhaseRankSorted orig next) (PhaseRankSorted orig cfg) :=
  P4.localExclude_then_consume_sorted orig hp h

/-! ## §5 The well-founded recursion driver, restricted to reachable states

The recursion is `WellFounded.fix` over the rank stored in the kernel —
no fuel, no `partial`, no assumed decrease. Because progress is only proved
on reachable configurations (F1), the driver recurses on configurations
CARRIED WITH their reachability proof; the kernel therefore also carries
the reachability-closure field (owner S5/W1: the invariant that the actual
execution state is preserved by every phase successor). The rank function
is a kernel FIELD (C2/G1), so ONE driver serves the historical `PhaseRank`
instance and the sorted `PhaseRankSorted` instance. -/

/-- A RECURSION KERNEL over reachable configurations: the phase step, its
agreement with the real dispatcher (`step_eq`, immediate here), closure of
reachability (`reach`), the RANK FUNCTION the driver terminates on, and the
ranked decrease (P5's assembly) about that same function. -/
structure ReachablePhaseKernel (leaf : Assignment → Bool) where
  /-- the dispatcher used by the driver -/
  step : SchedulerConfig leaf → SchedulerTransition leaf
  /-- the driver runs the REAL phase dispatcher on reachable states -/
  step_eq : ∀ cfg, SchedulerReachable cfg → step cfg = phaseNext cfg
  /-- reachability is preserved by the driver's step (the invariant S5/W1
      owes; NOT derivable from `SchedulerReachable` alone, since a phase
      step may bundle two raw steps) -/
  reach : ∀ cfg cfg', SchedulerReachable cfg → (step cfg).successor = some cfg' →
    SchedulerReachable cfg'
  /-- the rank the driver recurses on -/
  rank : SchedulerConfig leaf → Nat × Nat × Nat × Nat
  /-- every driver step strictly decreases the kernel's rank -/
  decrease : ∀ cfg cfg', SchedulerReachable cfg → (step cfg).successor = some cfg' →
    PhaseLt (rank cfg') (rank cfg)

/-- The kernel induced by the P5 obligation plus the reachability-closure
field: on reachable states the driver's step IS `phaseNext`, and the rank
is the configuration's SELF rank (`selfRank`, G1-scoped). -/
def reachablePhaseKernel {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSelf (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg') :
    ReachablePhaseKernel leaf where
  step := phaseNext
  step_eq := fun _ _ => rfl
  reach := hclos
  rank := selfRank
  decrease := h

/-- The SORTED-rank kernel (C2): the same driver's step and closure, with
the order-insensitive self rank. -/
def reachablePhaseKernelSorted {leaf : Assignment → Bool}
    (h : ReachablePhaseProgressSorted (leaf := leaf))
    (hclos : ∀ (cfg cfg' : SchedulerConfig leaf), SchedulerReachable cfg →
      (phaseNext cfg).successor = some cfg' → SchedulerReachable cfg') :
    ReachablePhaseKernel leaf where
  step := phaseNext
  step_eq := fun _ _ => rfl
  reach := hclos
  rank := selfRankSorted
  decrease := h

/-- **THE FUEL-FREE DRIVER over reachable configurations**: well-founded
recursion on the kernel's rank function (inverse image of P3's
`phaseLt_wf`), restricted by the reachability index. No fuel parameter, no
`partial`, no assumed termination. -/
noncomputable def runReachable {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf) :
    (cfg : SchedulerConfig leaf) → SchedulerReachable cfg → DriverResult leaf :=
  WellFounded.fix (InvImage.wf k.rank phaseLt_wf) (fun cfg rec hreach =>
    match h : k.step cfg with
    | .sat w => .sat w
    | .unsat => .unsat
    | .propagate n =>
        rec n (k.decrease cfg n hreach (by rw [h]; rfl))
          (k.reach cfg n hreach (by rw [h]; rfl))
    | .decide n _ =>
        rec n (k.decrease cfg n hreach (by rw [h]; rfl))
          (k.reach cfg n hreach (by rw [h]; rfl))
    | .analyzeConflict n _ =>
        rec n (k.decrease cfg n hreach (by rw [h]; rfl))
          (k.reach cfg n hreach (by rw [h]; rfl))
    | .learnBackjumpAssert n _ _ =>
        rec n (k.decrease cfg n hreach (by rw [h]; rfl))
          (k.reach cfg n hreach (by rw [h]; rfl))
    | .localExclude n =>
        rec n (k.decrease cfg n hreach (by rw [h]; rfl))
          (k.reach cfg n hreach (by rw [h]; rfl))
    | .chronologicalFallback n =>
        rec n (k.decrease cfg n hreach (by rw [h]; rfl))
          (k.reach cfg n hreach (by rw [h]; rfl)))

/-- TOTALITY: on every reachable configuration the driver returns a result;
no fuel, no user verdict fuel, no assumed decrease. -/
theorem runReachable_total {leaf : Assignment → Bool}
    (k : ReachablePhaseKernel leaf) (cfg : SchedulerConfig leaf)
    (hreach : SchedulerReachable cfg) :
    ∃ r : DriverResult leaf, runReachable k cfg hreach = r :=
  ⟨_, rfl⟩

/-! ## §6 Consumed-lemma citation list (no refuted contract, no fuel)

Non-jump arms (P3, `Proofs/SchedulerRank.lean`):
  `phaseRank_lt_propagate`, `phaseRank_lt_decide`, `phaseRank_lt_consume`,
  `phaseRank_analyzeConflictCounted_stutter`, and §2's unguarded copies of
  `phaseRank_lt_fallback_then_consume` / `phaseRank_lt_localExclude_then_consume`.

Jump arm (P4, `Proofs/SchedulerJumpProgress.lean`):
  `phaseLt_stepLearnBackjumpAssert_of_reachable` (which consumes
  `recordedAnalysis_normFalsified` + `jumpNovelty_of_unfalsified` from P2).

Well-foundedness: `P3.phaseLt_wf`, `P3.phaseRank_wf` (P3 §3).

Named premises reaching the caller (owners):
  * `hpool` — canonical-clause pool closure of reachable recorded analyses
    (owner P2, obligation P1-a; NOTE: P4's file records that P1-a as
    currently stated erases duplicates — the canonical clause itself must
    be in the pool).
  * `hdb` — `DatabaseUnfalsified` on reachable branches (owner S4/S5
    successor-invariant extension; recorded in `LearningNovelty`).
  * `hbr` — `ReachableState` of a reachable configuration's branch (owner
    S5/W1; R1 found the trail/level coherence obligation here).
  * `hclos` (§5 only) — reachability closure of the phase step (owner
    S5/W1, the preserved execution state).

NOT used anywhere above (grep-verifiable in this file):
  `JumpDecrease`, `JumpDecreaseNaive`, `JumpDecreaseOfDebt`, `DebtDecrease`,
  `DomJumpDiscipline`, `domJumpDecrease`, `DispatcherProgressNaive`,
  `SchedulerRank`/`RankLt`, `solveWithEventsOfJump`, and no fuel parameter
  or `partial def`.

F1 regression: `ReachablePhaseProgressRanked` is restricted to
`SchedulerReachable`; the unrestricted shapes are the refuted-historical
contracts (`not_jumpDecrease`, `¬ DispatcherProgressNaive`), and
`ReachableExcludesF1WitnessShape` remains open (owner S2/S3) — no claim
here that the new rank makes fabricated states safe. -/

end LeanFzn.Solver.UIP.P5
