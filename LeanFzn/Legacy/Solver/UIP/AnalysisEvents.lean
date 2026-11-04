/-
File: LeanFzn/Solver/UIP/AnalysisEvents.lean

Purpose:
  O1 CLOSE-OUT — the event-accumulation half of the O1 gate: result
  equivalence (already proved at the analyzer level, see below) TOGETHER
  WITH correct event accumulation ACROSS COMPOSED PHASES.

  The analyzer-level content (`EventCounts`, `IsExpansion`/`IsScan`,
  `stepCounts`, `analyzeEvents`, `analyzeEventsExpansions`,
  `analyzeEvents_trace_of_events` / `analyzeEvents_of_trace` /
  `analyzeEvents_complete_of_reachable`, the RESULT-EQUIVALENCE theorem
  `analyzeEvents_result_eq_analyzeAtAllowance` and the completed
  multi-resolution fixture with its derived counts) lives in
  `LeanFzn/Solver/UIP/AnalysisEventsCore.lean`: that module deliberately sits
  BELOW the consumers (SchedulerStep imports it for
  `analyzeEventsExpansions`), so this file can sit ABOVE them.

  THIS module adds the composed-phase accounting:

  * per-step invariance: every NON-analyze transition leaves
    `events.reasonResolutions` unchanged (`stepPropagate_reasonResolutions`
    … `stepConsume_reasonResolutions`; most are `rfl` or `rw` of the
    existing `*_events` equations) — the UNCOUNTED `stepAnalyzeConflict`
    included, which is why the increment happens only through
    `SchedulerConfig.countResolutions`;
  * `resolutionIncrement` — the real per-SITE increment read off the
    dispatcher: the counted executed expansions at the `.analyzeConflict`
    site, `0` at every other site;
  * `schedulerNext_successor_reasonResolutions` / `phaseNext_successor_
    reasonResolutions` — one REAL step of either dispatcher adds exactly
    `resolutionIncrement cfg`: the analyze site's counted expansions at
    the analyze site (through `analyzeEventsExpansions`, the value the
    `conflictStep` arm actually passes), nothing anywhere else. The phase
    dispatcher only composes stutter arms with the counter-neutral
    consume step, so its increment is the same site value;
  * THE COMPOSITION LEMMA `StepPath.reasonResolutions_eq` (and its
    `schedulerNext` / `phaseNext` corollaries): along a list of
    configurations connected by REAL successors, the final
    `events.reasonResolutions` equals the initial one plus the sum
    `p.incrementSum resolutionIncrement` of the real per-site increments.

Dependencies:
  - LeanFzn.Solver.Propagation.AnalysisEventsCore: the analyzer-level module above
    (analyzer + counted run + fixture + result equivalence);
  - LeanFzn.Solver.UIP.Proofs.Scheduler: the REAL dispatchers `schedulerNext`
    (with `C2d`'s dispatch equations) and `C3b.phaseNext`.

DAG:
  AnalysisEventsCore -> SchedulerStep -> ... -> Proofs.Scheduler
    -> LeanFzn.Solver.UIP.AnalysisEvents (this module).
-/

import LeanFzn.Legacy.Solver.Propagation.AnalysisEventsCore
import LeanFzn.Legacy.Solver.UIP.Proofs.Scheduler
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## Per-step invariance: non-analyze transitions leave the counter alone

These are the "many are `rfl`" obligations: every constructor of the
dispatcher other than the counted analyze site leaves
`events.reasonResolutions` unchanged. `stepAnalyzeConflict` is the
UNCOUNTED recording site (`events` untouched); only
`countResolutions`/`stepAnalyzeConflictCounted` adds the executed run's
expansions. -/

@[simp] theorem stepPropagate_reasonResolutions {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (d : ProductiveDeduction leaf cfg.branch) :
    (stepPropagate cfg d).events.reasonResolutions
      = cfg.events.reasonResolutions := by
  rw [stepPropagate_events]

@[simp] theorem stepDecide_reasonResolutions {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) (vs : Domain)
    (l : Literal) :
    (stepDecide cfg k v vs l).events.reasonResolutions
      = cfg.events.reasonResolutions := by
  rw [stepDecide_events]

@[simp] theorem stepDecideSkip_reasonResolutions {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (k : Nat) (v : Value) :
    (stepDecideSkip cfg k v).events.reasonResolutions
      = cfg.events.reasonResolutions := by
  rw [stepDecideSkip_events]

@[simp] theorem stepAnalyzeConflict_reasonResolutions {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (c : Clause) (learned : List Clause) :
    (stepAnalyzeConflict cfg c learned).events.reasonResolutions
      = cfg.events.reasonResolutions := by
  rw [stepAnalyzeConflict_events]

@[simp] theorem stepLearnBackjumpAssert_reasonResolutions
    {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf)
    (p : BackjumpPlan leaf) (ev : ConflictEvidence)
    (restored : BranchState leaf) :
    (stepLearnBackjumpAssert cfg p ev restored).events.reasonResolutions
      = cfg.events.reasonResolutions := rfl

@[simp] theorem stepLocalExclude_reasonResolutions {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) (learned : List Clause) (r : DeadRegion) :
    (stepLocalExclude cfg learned r).events.reasonResolutions
      = cfg.events.reasonResolutions := by
  rw [stepLocalExclude_events]

@[simp] theorem stepChronologicalFallback_reasonResolutions
    {leaf : Assignment → Bool} (cfg : SchedulerConfig leaf) (r : DeadRegion) :
    (stepChronologicalFallback cfg r).events.reasonResolutions
      = cfg.events.reasonResolutions := by
  rw [stepChronologicalFallback_events]

/-- The consume step (sibling resume) is counter-neutral: it changes the
branch, pending and status, never `events`. -/
theorem stepConsume_reasonResolutions {leaf : Assignment → Bool}
    {cfg next : SchedulerConfig leaf} (h : stepConsume cfg = some next) :
    next.events.reasonResolutions = cfg.events.reasonResolutions := by
  cases hp : cfg.pending with
  | nil => simp [stepConsume, hp] at h
  | cons f rest =>
      simp only [stepConsume, hp, Option.some.injEq] at h
      rw [← h]

/-! ## The real per-site increment and the per-step law -/

/-- The real per-SITE resolution increment of the dispatcher at `cfg`: the
counted executed expansions (`analyzeEventsExpansions`, the value the
analyze arm passes) at the `.analyzeConflict` site, `0` at every other
site. -/
def resolutionIncrement {leaf : Assignment → Bool}
    (cfg : SchedulerConfig leaf) : Nat :=
  match schedulerNext cfg with
  | .analyzeConflict _ c =>
      analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c
  | _ => 0

/-- The consume dispatcher's successor is counter-neutral (it is the
`stepConsume` route or the empty-frontier `unsat`). -/
theorem consumeStep_successor_reasonResolutions {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (h : (consumeStep cfg).successor = some cfg') :
    cfg'.events.reasonResolutions = cfg.events.reasonResolutions := by
  cases hs : stepConsume cfg with
  | none => simp [consumeStep, hs, SchedulerTransition.successor] at h
  | some next =>
      simp only [consumeStep, hs, SchedulerTransition.successor,
        Option.some.injEq] at h
      rw [← h]
      exact stepConsume_reasonResolutions hs

/-- The recorded-conflict route (`backjumpStep`: jump, checkpoint
exclusion, chronological fallback) is counter-neutral: NONE of its three
landings touches `events.reasonResolutions` (the jump's
`recordBackjump` changes `backjumps`/levels, not resolutions). -/
theorem backjumpStep_successor_reasonResolutions {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} {ev : ConflictEvidence}
    (h : (backjumpStep cfg ev).successor = some cfg') :
    cfg'.events.reasonResolutions = cfg.events.reasonResolutions := by
  cases ha : ev.analysis with
  | none =>
      simp only [backjumpStep, ha, SchedulerTransition.successor,
        Option.some.injEq] at h
      rw [← h]
      exact stepChronologicalFallback_reasonResolutions cfg (branchRegion cfg)
  | some an =>
      cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
      | none =>
          simp only [backjumpStep, ha, hcp, SchedulerTransition.successor,
            Option.some.injEq] at h
          rw [← h]
          exact stepChronologicalFallback_reasonResolutions cfg (branchRegion cfg)
      | some cp =>
          cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
              an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
          | none =>
              simp only [backjumpStep, ha, hcp, hp, SchedulerTransition.successor,
                Option.some.injEq] at h
              rw [← h]
              exact stepLocalExclude_reasonResolutions cfg ev.learned
                (checkpointRegion cp)
          | some restored =>
              simp only [backjumpStep, ha, hcp, hp, SchedulerTransition.successor,
                Option.some.injEq] at h
              rw [← h]
              exact stepLearnBackjumpAssert_reasonResolutions cfg
                (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned)
                ev restored

/-- THE PER-STEP LAW: one REAL `schedulerNext` step adds EXACTLY
`resolutionIncrement cfg` to `events.reasonResolutions` — at the analyze
site the counted executed expansions the site passes, and nothing at
every other site. Proved by the `C2d` dispatch equations, one arm per
constructor. -/
theorem schedulerNext_successor_reasonResolutions {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (h : (schedulerNext cfg).successor = some cfg') :
    cfg'.events.reasonResolutions
      = cfg.events.reasonResolutions + resolutionIncrement cfg := by
  cases hconf : cfg.conflict with
  | some ev =>
      rw [C2d.schedulerNext_eq_backjump hconf] at h
      have hinc0 : resolutionIncrement cfg = 0 := by
        simp only [resolutionIncrement, C2d.schedulerNext_eq_backjump hconf]
        cases hb : backjumpStep cfg ev with
        | analyzeConflict n c =>
            exact absurd hb (fun hc => C3a.backjumpStep_not_analyzeConflict
              cfg ev ⟨n, c, hc⟩)
        | _ => rfl
      rw [hinc0, Nat.add_zero]
      exact backjumpStep_successor_reasonResolutions h
  | none =>
      cases hst : cfg.status with
      | dead =>
          rw [C2d.schedulerNext_eq_consume hconf hst] at h
          have hinc0 : resolutionIncrement cfg = 0 := by
            simp only [resolutionIncrement, C2d.schedulerNext_eq_consume hconf hst,
              consumeStep]
            cases hs : stepConsume cfg with
            | none => rfl
            | some next => rfl
          rw [hinc0, Nat.add_zero]
          exact consumeStep_successor_reasonResolutions h
      | active =>
          cases hd : explainedDeduction cfg.original cfg.props cfg.branch with
          | some d =>
              rw [C2d.schedulerNext_eq_deduction hconf hst hd] at h
              simp only [SchedulerTransition.successor, Option.some.injEq] at h
              have hinc0 : resolutionIncrement cfg = 0 := by
                simp only [resolutionIncrement,
                  C2d.schedulerNext_eq_deduction hconf hst hd]
              rw [hinc0, Nat.add_zero, ← h]
              exact stepPropagate_reasonResolutions cfg d
          | none =>
              cases ht : terminalResult cfg.orig cfg.original cfg.props cfg.branch with
              | stable bs =>
                  cases hw : leafWitness leaf cfg with
                  | some w =>
                      rw [C2d.schedulerNext_eq_stable_sat hconf hst hd ht hw] at h
                      simp [SchedulerTransition.successor] at h
                  | none =>
                      cases hsp : splitData cfg.branch.frame cfg.prio with
                      | some p =>
                          obtain ⟨l, k, v, vs⟩ := p
                          by_cases hred : TrailRedundant cfg.branch.trail l = true
                          · -- B1 skip arm: the redundant pin decides without
                            -- a trail entry; the counter is untouched.
                            rw [C2d.schedulerNext_eq_stable_decideSkip hconf hst hd
                              ht hw hsp hred] at h
                            simp only [SchedulerTransition.successor,
                              Option.some.injEq] at h
                            have hinc0 : resolutionIncrement cfg = 0 := by
                              simp only [resolutionIncrement,
                                C2d.schedulerNext_eq_stable_decideSkip hconf hst hd
                                  ht hw hsp hred]
                            rw [hinc0, Nat.add_zero, ← h]
                            simp
                          · -- fresh arm (as before)
                            have hred' : TrailRedundant cfg.branch.trail l = false := by
                              cases hh : TrailRedundant cfg.branch.trail l <;>
                                simp_all
                            rw [C2d.schedulerNext_eq_stable_decide hconf hst hd ht hw
                              hsp hred'] at h
                            simp only [SchedulerTransition.successor,
                              Option.some.injEq] at h
                            have hinc0 : resolutionIncrement cfg = 0 := by
                              simp only [resolutionIncrement,
                                C2d.schedulerNext_eq_stable_decide hconf hst hd ht hw
                                  hsp hred']
                            rw [hinc0, Nat.add_zero, ← h]
                            exact stepDecide_reasonResolutions cfg k v vs l
                      | none =>
                          rw [C2d.schedulerNext_eq_stable_localExclude hconf hst hd
                            ht hw hsp] at h
                          simp only [SchedulerTransition.successor,
                            Option.some.injEq] at h
                          have hinc0 : resolutionIncrement cfg = 0 := by
                            simp only [resolutionIncrement,
                              C2d.schedulerNext_eq_stable_localExclude hconf hst hd
                                ht hw hsp]
                          rw [hinc0, Nat.add_zero, ← h]
                          exact stepLocalExclude_reasonResolutions cfg []
                            (branchRegion cfg)
              | conflict bs cs learned =>
                  cases cs with
                  | nil =>
                      rw [C2d.schedulerNext_eq_conflict_local hconf hst hd ht] at h
                      simp only [SchedulerTransition.successor,
                        Option.some.injEq] at h
                      have hinc0 : resolutionIncrement cfg = 0 := by
                        simp only [resolutionIncrement,
                          C2d.schedulerNext_eq_conflict_local hconf hst hd ht]
                      rw [hinc0, Nat.add_zero, ← h]
                      exact stepLocalExclude_reasonResolutions cfg learned
                        (branchRegion cfg)
                  | cons c rest =>
                      by_cases hlv : cfg.branch.level = 0
                      · rw [C2d.schedulerNext_eq_conflict_unsat hconf hst hd ht
                          hlv] at h
                        simp [SchedulerTransition.successor] at h
                      · rw [C2d.schedulerNext_eq_conflict_analyze hconf hst hd ht
                          hlv] at h
                        simp only [SchedulerTransition.successor,
                          Option.some.injEq] at h
                        have hinc : resolutionIncrement cfg
                            = analyzeEventsExpansions cfg.orig cfg.branch.trail
                                cfg.branch.level c := by
                          simp only [resolutionIncrement,
                            C2d.schedulerNext_eq_conflict_analyze hconf hst hd ht
                              hlv]
                        rw [hinc, ← h, stepAnalyzeConflictCounted_reasonResolutions]
              | localExcluded bs lit reason learned =>
                  rw [C2d.schedulerNext_eq_localExcluded hconf hst hd ht] at h
                  simp only [SchedulerTransition.successor,
                    Option.some.injEq] at h
                  have hinc0 : resolutionIncrement cfg = 0 := by
                    simp only [resolutionIncrement,
                      C2d.schedulerNext_eq_localExcluded hconf hst hd ht]
                  rw [hinc0, Nat.add_zero, ← h]
                  exact stepLocalExclude_reasonResolutions cfg learned
                    (branchRegion cfg)

/-- THE PHASE PER-STEP LAW (composed phases): one REAL `C3b.phaseNext`
step adds exactly the same `resolutionIncrement cfg`. The phase step
composes each stutter arm with the counter-neutral consume step (and
resolves the recorded-evidence route directly), so no composed step can
add anything but the analyze site's counted expansions. -/
theorem phaseNext_successor_reasonResolutions {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (h : (C3b.phaseNext cfg).successor = some cfg') :
    cfg'.events.reasonResolutions
      = cfg.events.reasonResolutions + resolutionIncrement cfg := by
  cases hnext : schedulerNext cfg with
  | sat w => simp [C3b.phaseNext, hnext, SchedulerTransition.successor] at h
  | unsat => simp [C3b.phaseNext, hnext, SchedulerTransition.successor] at h
  | propagate next =>
      have hn : (schedulerNext cfg).successor = some next := by rw [hnext]; rfl
      have hp : C3b.phaseNext cfg = .propagate next := by
        simp only [C3b.phaseNext, hnext]
      rw [hp] at h
      simp only [SchedulerTransition.successor, Option.some.injEq] at h
      rw [← h]
      exact schedulerNext_successor_reasonResolutions hn
  | decide next l =>
      have hn : (schedulerNext cfg).successor = some next := by rw [hnext]; rfl
      have hp : C3b.phaseNext cfg = .decide next l := by
        simp only [C3b.phaseNext, hnext]
      rw [hp] at h
      simp only [SchedulerTransition.successor, Option.some.injEq] at h
      rw [← h]
      exact schedulerNext_successor_reasonResolutions hn
  | learnBackjumpAssert next p an =>
      have hn : (schedulerNext cfg).successor = some next := by rw [hnext]; rfl
      have hp : C3b.phaseNext cfg = .learnBackjumpAssert next p an := by
        simp only [C3b.phaseNext, hnext]
      rw [hp] at h
      simp only [SchedulerTransition.successor, Option.some.injEq] at h
      rw [← h]
      exact schedulerNext_successor_reasonResolutions hn
  | localExclude n =>
      have hn : (schedulerNext cfg).successor = some n := by rw [hnext]; rfl
      have h1 := schedulerNext_successor_reasonResolutions hn
      cases hs : stepConsume n with
      | some next =>
          have hp : C3b.phaseNext cfg = .chronologicalFallback next := by
            simp only [C3b.phaseNext, hnext, hs]
          rw [hp] at h
          simp only [SchedulerTransition.successor, Option.some.injEq] at h
          rw [← h, stepConsume_reasonResolutions hs]
          exact h1
      | none =>
          simp [C3b.phaseNext, hnext, hs, SchedulerTransition.successor] at h
  | chronologicalFallback n =>
      have hn : (schedulerNext cfg).successor = some n := by rw [hnext]; rfl
      have h1 := schedulerNext_successor_reasonResolutions hn
      cases hc : cfg.conflict with
      | none =>
          have hp : C3b.phaseNext cfg = .chronologicalFallback n := by
            simp only [C3b.phaseNext, hnext, hc]
          rw [hp] at h
          simp only [SchedulerTransition.successor, Option.some.injEq] at h
          rw [← h]
          exact h1
      | some ev =>
          cases hs : stepConsume n with
          | some next =>
              have hp : C3b.phaseNext cfg = .chronologicalFallback next := by
                simp only [C3b.phaseNext, hnext, hc, hs]
              rw [hp] at h
              simp only [SchedulerTransition.successor, Option.some.injEq] at h
              rw [← h, stepConsume_reasonResolutions hs]
              exact h1
          | none =>
              simp [C3b.phaseNext, hnext, hc, hs, SchedulerTransition.successor] at h
  | analyzeConflict n c =>
      have hn : (schedulerNext cfg).successor = some n := by rw [hnext]; rfl
      have h1 := schedulerNext_successor_reasonResolutions hn
      cases hc : n.conflict with
      | none =>
          have hp : C3b.phaseNext cfg = .analyzeConflict n c := by
            simp only [C3b.phaseNext, hnext, hc]
          rw [hp] at h
          simp only [SchedulerTransition.successor, Option.some.injEq] at h
          rw [← h]
          exact h1
      | some ev =>
          cases hb : backjumpStep n ev with
          | sat w =>
              simp [C3b.phaseNext, hnext, hc, hb, SchedulerTransition.successor] at h
          | unsat =>
              simp [C3b.phaseNext, hnext, hc, hb, SchedulerTransition.successor] at h
          | analyzeConflict n2 c2 =>
              exact absurd hb (fun hc2 => C3a.backjumpStep_not_analyzeConflict
                n ev ⟨n2, c2, hc2⟩)
          | propagate n2 =>
              have h2 := backjumpStep_successor_reasonResolutions
                (cfg := n) (cfg' := n2) (ev := ev) (by rw [hb]; rfl)
              have hp : C3b.phaseNext cfg = .propagate n2 := by
                simp only [C3b.phaseNext, hnext, hc, hb]
              rw [hp] at h
              simp only [SchedulerTransition.successor, Option.some.injEq] at h
              rw [← h, h2]
              exact h1
          | decide n2 l =>
              have h2 := backjumpStep_successor_reasonResolutions
                (cfg := n) (cfg' := n2) (ev := ev) (by rw [hb]; rfl)
              have hp : C3b.phaseNext cfg = .decide n2 l := by
                simp only [C3b.phaseNext, hnext, hc, hb]
              rw [hp] at h
              simp only [SchedulerTransition.successor, Option.some.injEq] at h
              rw [← h, h2]
              exact h1
          | learnBackjumpAssert n2 p an2 =>
              have h2 := backjumpStep_successor_reasonResolutions
                (cfg := n) (cfg' := n2) (ev := ev) (by rw [hb]; rfl)
              have hp : C3b.phaseNext cfg = .learnBackjumpAssert n2 p an2 := by
                simp only [C3b.phaseNext, hnext, hc, hb]
              rw [hp] at h
              simp only [SchedulerTransition.successor, Option.some.injEq] at h
              rw [← h, h2]
              exact h1
          | chronologicalFallback n' =>
              have h2 := backjumpStep_successor_reasonResolutions
                (cfg := n) (cfg' := n') (ev := ev) (by rw [hb]; rfl)
              cases hs : stepConsume n' with
              | some next =>
                  have hp : C3b.phaseNext cfg = .chronologicalFallback next := by
                    simp only [C3b.phaseNext, hnext, hc, hb, hs]
                  rw [hp] at h
                  simp only [SchedulerTransition.successor, Option.some.injEq] at h
                  rw [← h, stepConsume_reasonResolutions hs, h2]
                  exact h1
              | none =>
                  simp [C3b.phaseNext, hnext, hc, hb, hs,
                    SchedulerTransition.successor] at h
          | localExclude n' =>
              have h2 := backjumpStep_successor_reasonResolutions
                (cfg := n) (cfg' := n') (ev := ev) (by rw [hb]; rfl)
              cases hs : stepConsume n' with
              | some next =>
                  have hp : C3b.phaseNext cfg = .chronologicalFallback next := by
                    simp only [C3b.phaseNext, hnext, hc, hb, hs]
                  rw [hp] at h
                  simp only [SchedulerTransition.successor, Option.some.injEq] at h
                  rw [← h, stepConsume_reasonResolutions hs, h2]
                  exact h1
              | none =>
                  simp [C3b.phaseNext, hnext, hc, hb, hs,
                    SchedulerTransition.successor] at h

/-! ## THE COMPOSITION LEMMA (list of connected successors) -/

/-- A DISPATCHED SUCCESSOR PATH: a list of configurations whose elements
are connected by REAL successor steps of `step`. The source of every step
is kept, so the per-site increments can be summed. -/
inductive StepPath {leaf : Assignment → Bool}
    (step : SchedulerConfig leaf → SchedulerTransition leaf) :
    SchedulerConfig leaf → SchedulerConfig leaf → Type where
  /-- the empty path -/
  | refl (cfg : SchedulerConfig leaf) : StepPath step cfg cfg
  /-- one real successor step followed by the rest of the path -/
  | step {cfg next last : SchedulerConfig leaf}
      (h : (step cfg).successor = some next)
      (t : StepPath step next last) : StepPath step cfg last

/-- The sum of the real per-site increments along a dispatched path. -/
def StepPath.incrementSum {leaf : Assignment → Bool}
    {step : SchedulerConfig leaf → SchedulerTransition leaf}
    (inc : SchedulerConfig leaf → Nat) :
    {cfg last : SchedulerConfig leaf} → StepPath step cfg last → Nat
  | _, _, .refl _ => 0
  | cfg, _, .step _ t => inc cfg + t.incrementSum inc

/-- THE COMPOSITION LEMMA: for a path of configurations connected by REAL
successor steps, the final `events.reasonResolutions` equals the initial
one plus the sum of the real per-site increments. This is the generic
form; the `schedulerNext` and `phaseNext` instances below are the two
dispatchers the scheduler runs. -/
theorem StepPath.reasonResolutions_eq {leaf : Assignment → Bool}
    {step : SchedulerConfig leaf → SchedulerTransition leaf}
    {inc : SchedulerConfig leaf → Nat}
    (hstep : ∀ {cfg cfg' : SchedulerConfig leaf},
      (step cfg).successor = some cfg' →
      cfg'.events.reasonResolutions = cfg.events.reasonResolutions + inc cfg)
    {cfg last : SchedulerConfig leaf} (p : StepPath step cfg last) :
    last.events.reasonResolutions
      = cfg.events.reasonResolutions + p.incrementSum inc := by
  induction p with
  | refl cfg => simp [StepPath.incrementSum]
  | step h t ih =>
      simp only [StepPath.incrementSum]
      rw [ih, hstep h]
      omega

/-- O1 COMPOSITION, `schedulerNext` instantiation: along any list of
configurations connected by real dispatcher successors, the final
`events.reasonResolutions` is the initial counter plus the sum of the
analyze site's counted expansions taken along the way. -/
theorem reasonResolutions_sum_of_schedulerPath {leaf : Assignment → Bool}
    {cfg last : SchedulerConfig leaf}
    (p : StepPath schedulerNext cfg last) :
    last.events.reasonResolutions
      = cfg.events.reasonResolutions + p.incrementSum resolutionIncrement :=
  StepPath.reasonResolutions_eq (fun h => schedulerNext_successor_reasonResolutions h) p

/-- O1 COMPOSITION, `phaseNext` (composed phases) instantiation: along any
list of configurations connected by real PHASE successors, the final
`events.reasonResolutions` is the initial counter plus the sum of the
analyze site's counted expansions — the consume compositions add nothing.
-/
theorem reasonResolutions_sum_of_phasePath {leaf : Assignment → Bool}
    {cfg last : SchedulerConfig leaf}
    (p : StepPath C3b.phaseNext cfg last) :
    last.events.reasonResolutions
      = cfg.events.reasonResolutions + p.incrementSum resolutionIncrement :=
  StepPath.reasonResolutions_eq (fun h => phaseNext_successor_reasonResolutions h) p

/-! ## Kernel examples on the real dispatchers -/

/-- Two REAL `schedulerNext` steps compose: the final counter adds exactly
the two site increments. -/
example {leaf : Assignment → Bool} {cfg n1 n2 : SchedulerConfig leaf}
    (h1 : (schedulerNext cfg).successor = some n1)
    (h2 : (schedulerNext n1).successor = some n2) :
    n2.events.reasonResolutions
      = cfg.events.reasonResolutions
        + (resolutionIncrement cfg + resolutionIncrement n1) := by
  have h := reasonResolutions_sum_of_schedulerPath
    (StepPath.step h1 (StepPath.step h2 (StepPath.refl n2)) :
      StepPath schedulerNext cfg n2)
  simpa only [StepPath.incrementSum, Nat.add_zero] using h

/-- Two REAL `phaseNext` steps compose the same way (composed phases). -/
example {leaf : Assignment → Bool} {cfg n1 n2 : SchedulerConfig leaf}
    (h1 : (C3b.phaseNext cfg).successor = some n1)
    (h2 : (C3b.phaseNext n1).successor = some n2) :
    n2.events.reasonResolutions
      = cfg.events.reasonResolutions
        + (resolutionIncrement cfg + resolutionIncrement n1) := by
  have h := reasonResolutions_sum_of_phasePath
    (StepPath.step h1 (StepPath.step h2 (StepPath.refl n2)) :
      StepPath C3b.phaseNext cfg n2)
  simpa only [StepPath.incrementSum, Nat.add_zero] using h

end LeanFzn.Solver.UIP
