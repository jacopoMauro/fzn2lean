/-
File: LeanFzn/Solver/UIP/Proofs/SupportedLogSites.lean

Purpose: the L1 producer of `SupportedNewRegionsSound` (SupportedLog.lean):
every region REGISTERED by one real `schedulerNext` successor of a
supported configuration is `DeadRegion.Sound`. The run-level log induction
(`supportedLogSound_of_newRegions`) and the two registration helpers
(`newRegionsSound_of_regions_eq` for unchanged logs,
`newRegionsSound_of_register` for a single insertion) are already compiled
in `SupportedLog`; this module classifies EVERY real dispatcher arm against
them and derives each registration from the ACTUAL dead-site producers
(`SchedulerDeadSites`, `SupportedDead`, `HdeadCkpt`).

ARM TABLE (real dispatcher arm -> registered region -> producer -> residual
owner). "derived" = closed here from this module's premises; "rfl" = the log
is untouched. Residual owners are the families already assigned in the plan
(P1 closure contract, SupportedArms joint reachability, E1/J1 restoration).

| #  | dispatcher arm (guard)                              | registered region     | producer / route                                           | residual owner |
|----|-----------------------------------------------------|-----------------------|------------------------------------------------------------|----------------|
| 1  | `.propagate` (productive deduction)                 | none (log unchanged)  | `newRegionsSound_of_regions_eq` (rfl)                      | —              |
| 2  | `.decide` fresh (stable + splitData, pin fresh)     | none (log unchanged)  | `newRegionsSound_of_regions_eq` (rfl)                      | —              |
| 3  | `.decide` skip (stable + splitData, pin recorded)   | none (log unchanged)  | `newRegionsSound_of_regions_eq` (rfl)                      | —              |
| 4  | `.sat` (stable + leaf witness)                      | — (no successor)      | `successor_sat` refutes the successor equation             | —              |
| 5  | `.analyzeConflict` (conflict `c :: _`, level ≠ 0)   | none (log unchanged)  | `newRegionsSound_of_regions_eq` (rfl)                      | —              |
| 6  | `.learnBackjumpAssert` (`perform = some`)           | none (log unchanged)  | `newRegionsSound_of_regions_eq` (`stepLearnBackjumpAssert_log`) | —         |
| 7  | `.localExclude` stable-none site                    | `branchRegion cfg`    | `supportedBranchRegionSound_of_stableNone` (`hshape`+`hbr`) | derived (gate `hdeadStableNone`) |
| 8  | `.localExclude` conflict-nil site                   | `branchRegion cfg`    | `supportedBranchRegionSound_of_conflictNil` (`hclos`+`hbr`) | derived |
| 9  | `.localExclude` checkpoint-rejection site           | `checkpointRegion cp` | the `hdeadCkpt` premise (exact gates-field shape)          | E1 (`supportedHdeadCheckpointRegion_of_premises`; `hsurv` ← J1) |
| 10 | `.localExclude` localExcluded site                  | `branchRegion cfg`    | `supportedBranchRegionSound_of_localExcluded` (`hclos`+`hbr`) | derived |
| 11 | `.chronologicalFallback` analysis-none site         | `branchRegion cfg`    | `supportedBranchRegionSound_of_recordedEvidence` (`hclos`+`hbr`) | derived (gate `hdeadFallbackNone`) |
| 12 | `.chronologicalFallback` checkpoint-none site       | `branchRegion cfg`    | same as 11                                                 | derived (gate `hdeadFallbackNoCp`) |
| 13 | `.chronologicalFallback` consume site               | none (log unchanged)  | `newRegionsSound_of_regions_eq` (`stepConsume_some_shape`) | —              |
| 14 | `.unsat` (empty consume frontier / level-0 conflict)| — (no successor)      | successor refutations                                       | —              |

Premises of `supportedNewRegionsSound_of_premises` (the exact residual set,
all in the shapes of `SupportedDead` §5 / `SupportedArmInvGatesCore`):

  * `hshape` — `ShapeTypedDomains orig`, the run's shape discipline
    (`SupportedInput.shape`; D1's compiled input);
  * `hclos` — the per-configuration closure contract in the
    `cfg.original`/`cfg.props` spelling (P1's producer
    `supportedHclos_of_compiled`);
  * `hbr` — per-configuration branch reachability (the first component of
    the joint induction `supportedReachAndEvidence_of_premises`,
    SupportedArms §0);
  * `hdeadCkpt` — checkpoint-rejection region soundness, EXACTLY the
    `SupportedArmInvGatesCore.hdeadCheckpointRegion` field shape. Its
    producer is E1's `supportedHdeadCheckpointRegion_of_premises` (current
    residual: `hbr` + `hent` + `hsurv`, with `hsurv` owned by J1); the
    convenience producer `supportedNewRegionsSound_of_E1premises` below
    consumes that residual directly, and `supportedNewRegionsSound_of_coreGates`
    consumes an assembled `SupportedArmInvGatesCore`, so no gate field is
    re-assumed anywhere.

The §5 exports (`supportedLogSound_of_premises` /
`supportedLogSound_of_E1premises`) compose the dispatcher with the
compiled run induction `supportedLogSound_of_newRegions`, yielding the
supported run's `ExhaustionLog.Sound` WITHOUT any assumed log soundness —
the L1 deliverable consumed by R2 (`hnew` / predecessor `log_sound`).

NO `sorry`, NO custom axiom. Registration owes the umbrella import line
`LeanFzn.Solver.UIP.Proofs.SupportedLogSites` in `LeanFzn.Solver/LeanFzn.Solver.UIP.lean` (coordinator).
-/

import LeanFzn.Solver.UIP.Proofs.SupportedLog
import LeanFzn.Solver.UIP.Proofs.SupportedDead
import LeanFzn.Solver.UIP.Proofs.SchedulerDeadSites
import LeanFzn.Solver.UIP.Proofs.SupportedGates
import LeanFzn.Solver.UIP.Proofs.HdeadCkpt
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Solver.UIP.C2d

/-! ## §1 Shape bridges (dispatcher spelling ↔ producer spelling)

The dispatcher spells static inputs through the CONFIGURATION
(`cfg.original`, `cfg.props`); at a supported configuration those are the
run's `original`/`props` (`SupportedReach`), and the dead-site producers of
`SchedulerDeadSites` are stated at the run triple. The two bridges below
transport between the spellings so every site call is a direct application
with no per-site rewriting. -/

/-- The run triple's closure contract, transported from the
per-configuration spelling (`cfg.original`/`cfg.props` are the run's by
`SupportedReach`). Same conversion as `SupportedDead` §5's internal
`hclosF`. -/
theorem supportedClosureContract_runTriple {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    {cfg : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg) :
    ClosureContract leaf orig original props := by
  rw [← SupportedReach.original_eq hreach, ← SupportedReach.props_eq hreach]
  exact hclos hreach

/-- The dispatcher's terminal-event input at a supported configuration is
the run triple's: `terminalResult cfg.original cfg.props cfg.branch =
terminalResult original props cfg.branch`. -/
theorem supportedTerminalResult_runTriple {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    {cfg : SchedulerConfig leaf}
    (hreach : SupportedReach orig original props cfg) :
    terminalResult cfg.original cfg.props cfg.branch
      = terminalResult original props cfg.branch := by
  rw [SupportedReach.original_eq hreach, SupportedReach.props_eq hreach]

/-! ## §2 The per-site branch-region producers

Each producer's conclusion is `DeadRegion.Sound leaf (branchRegion cfg)`
(the registered region of the local-exclusion/fallback sites), derived
from the dead-site producers of `SchedulerDeadSites` and `SupportedDead`:
the region is the COMPUTABLE frame region (`branchRegion = byFrame`), and
the frame's deadness is the site's semantic content. -/

/-- **STABLE-NONE LOCAL-EXCLUSION SITE** (arm 7 of the table): the region
registered when a stable terminal result has no split data is sound.
Route: `SupportedDead` §2's producer (`hshape` + `hbr`), which refutes the
unsupported-head case from the run's shape discipline — no per-site
assumption. -/
theorem supportedBranchRegionSound_of_stableNone {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    (hreach : SupportedReach orig original props cfg)
    (ht : terminalResult cfg.original cfg.props cfg.branch = .stable bs)
    (hwit : leafWitness leaf cfg = none)
    (hsp : splitData cfg.branch.frame = none) :
    DeadRegion.Sound leaf (branchRegion cfg) :=
  branchRegion_sound
    (supportedHdeadStableNone_of_shape hshape hbr hreach ht hwit hsp)

/-- **RECORDED-EVIDENCE FALLBACK SITES** (arms 11/12): the region
registered by `stepChronologicalFallback cfg (branchRegion cfg)` when
recorded evidence has no asserting analysis or no saved checkpoint is
sound. Route: `SupportedDead` §1's producer (`hclos` + `hbr`) — the
recorded conflict's own terminal event excludes the frame; the analysis
and the checkpoint lookup are irrelevant. -/
theorem supportedBranchRegionSound_of_recordedEvidence {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
    (hreach : SupportedReach orig original props cfg)
    (hc : cfg.conflict = some ev) :
    DeadRegion.Sound leaf (branchRegion cfg) :=
  branchRegion_sound
    (supportedFrameDead_of_recordedEvidence hclos hbr hreach hc)

/-- **CONFLICT-NIL LOCAL-EXCLUSION SITE** (arm 8): the region registered
when the terminal event is a conflict with an EMPTY reported clause list
(a database refutation) is sound. Route:
`deadConflictNil_of_terminalEvent` (`hclos` + `hbr`): the closure
contract's `conflictExcludes` excludes every represented leaf solution. -/
theorem supportedBranchRegionSound_of_conflictNil {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {cs learned : List Clause}
    (hreach : SupportedReach orig original props cfg)
    (ht : terminalResult cfg.original cfg.props cfg.branch = .conflict bs cs learned)
    (hcs : cs = []) :
    DeadRegion.Sound leaf (branchRegion cfg) := by
  have htr : terminalResult original props cfg.branch = .conflict bs cs learned := by
    rw [← supportedTerminalResult_runTriple hreach]
    exact ht
  exact branchRegion_sound
    (deadConflictNil_of_terminalEvent
      (supportedClosureContract_runTriple hclos hreach) (hbr hreach) htr hcs)

/-- **LOCAL-EXCLUDED SITE** (arm 10): the region registered when the
terminal event is `.localExcluded` (the selected deduction's literal
failed to narrow the frame) is sound. Route:
`deadLocalExcluded_of_terminalEvent` (`hclos` + `hbr`). -/
theorem supportedBranchRegionSound_of_localExcluded {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    {cfg : SchedulerConfig leaf} {bs : BranchState leaf}
    {lit : Option Literal} {reason : Option Clause} {learned : List Clause}
    (hreach : SupportedReach orig original props cfg)
    (ht : terminalResult cfg.original cfg.props cfg.branch
      = .localExcluded bs lit reason learned) :
    DeadRegion.Sound leaf (branchRegion cfg) := by
  have htr : terminalResult original props cfg.branch
      = .localExcluded bs lit reason learned := by
    rw [← supportedTerminalResult_runTriple hreach]
    exact ht
  exact branchRegion_sound
    (deadLocalExcluded_of_terminalEvent
      (supportedClosureContract_runTriple hclos hreach) (hbr hreach) htr)

/-! ## §3 THE REGISTRATION-SITE DISPATCHER

`supportedNewRegionsSound_of_premises` classifies every real
`schedulerNext` successor (via `C2d.schedulerNext_cases` and the runtime's
own branch equations) and closes each registration arm with the §2
producers (or the E1 premise at the checkpoint-rejection site) and each
unchanged-log arm with `newRegionsSound_of_regions_eq`. No log-soundness
or invariant input is assumed; the premise set is exactly
`{hshape, hclos, hbr, hdeadCkpt}`. -/
theorem supportedNewRegionsSound_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    (hdeadCkpt : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp)) :
    SupportedNewRegionsSound orig original props leaf := by
  intro cfg cfg' hreach hsucc
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (backjumpStep)
    rw [hnext] at hsucc
    unfold backjumpStep at hsucc
    cases ha : ev.analysis with
    | none =>
        -- ARM 11: analysis = none → chronological fallback, branch region
        rw [ha] at hsucc
        simp only [] at hsucc
        simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
        subst hsucc
        exact newRegionsSound_of_register
          (stepChronologicalFallback_log cfg (branchRegion cfg))
          (supportedBranchRegionSound_of_recordedEvidence hclos hbr hreach hc)
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            -- ARM 12: no checkpoint at the target → same fallback site
            rw [ha] at hsucc
            simp only [] at hsucc
            rw [hcp] at hsucc
            simp only [] at hsucc
            simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
            subst hsucc
            exact newRegionsSound_of_register
              (stepChronologicalFallback_log cfg (branchRegion cfg))
              (supportedBranchRegionSound_of_recordedEvidence hclos hbr hreach hc)
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.original cfg.props with
            | none =>
                -- ARM 9: the checkpoint-rejection site registers the
                -- CHECKPOINT's region; the E1 premise supplies soundness
                rw [ha] at hsucc
                simp only [] at hsucc
                rw [hcp] at hsucc
                simp only [] at hsucc
                rw [hp] at hsucc
                simp only [] at hsucc
                simp only [successor_localExclude, Option.some.injEq] at hsucc
                subst hsucc
                exact newRegionsSound_of_register
                  (stepLocalExclude_log cfg ev.learned (checkpointRegion cp))
                  (hdeadCkpt hreach hc ha hcp hp)
            | some restored =>
                -- ARM 6: the performing jump leaves the log unchanged
                rw [ha] at hsucc
                simp only [] at hsucc
                rw [hcp] at hsucc
                simp only [] at hsucc
                rw [hp] at hsucc
                simp only [] at hsucc
                simp only [successor_learnBackjumpAssert, Option.some.injEq] at hsucc
                subst hsucc
                exact newRegionsSound_of_regions_eq
                  (by rw [stepLearnBackjumpAssert_log])
  · -- ===== ROUTE 2: dead branch (consumeStep)
    rw [hnext] at hsucc
    unfold consumeStep at hsucc
    split at hsucc
    · -- ARM 13: the consume step carries the log unchanged
      rename_i next hcs
      have hlog : next.log.regions = cfg.log.regions := by
        cases hpend : cfg.pending with
        | nil =>
            rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
            cases hcs
        | cons f rest =>
            rw [(stepConsume_some_shape hpend hcs).2.2.1]
      simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
      subst hsucc
      exact newRegionsSound_of_regions_eq hlog
    · -- ARM 14: the exhausted frontier has no successor
      simp only [successor_unsat] at hsucc
      cases hsucc
  · -- ===== ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- ARM 1: propagate — log unchanged
      rw [hnext] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      subst hsucc
      exact newRegionsSound_of_regions_eq rfl
    · -- ARMS 2/3/4/7: the guarded stable dispatch
      rw [hnext] at hsucc
      unfold stableStepGuarded at hsucc
      split at hsucc
      · -- ARM 4: the leaf witness is terminal — no successor
        simp only [successor_sat] at hsucc
        cases hsucc
      · -- name the witness-failure fact for the stable-none producer
        rename_i hwn
        split at hsucc
        · -- ARMS 2/3: the split arms (fresh pin / recorded pin) — log unchanged
          rename_i l v vs doms hsp
          split at hsucc
          · simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            exact newRegionsSound_of_regions_eq rfl
          · simp only [successor_decide, Option.some.injEq] at hsucc
            subst hsucc
            exact newRegionsSound_of_regions_eq rfl
        · -- ARM 7: the stable-none local-exclusion site, branch region
          rename_i hsp
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          exact newRegionsSound_of_register
            (stepLocalExclude_log cfg [] (branchRegion cfg))
            (supportedBranchRegionSound_of_stableNone hshape hbr hreach ht hwn hsp)
    · -- ARMS 5/8/14: the conflict dispatch
      rw [hnext] at hsucc
      cases cs with
      | nil =>
          -- ARM 8: the database-refutation site, branch region
          simp only [conflictStep] at hsucc
          simp only [successor_localExclude, Option.some.injEq] at hsucc
          subst hsucc
          exact newRegionsSound_of_register
            (stepLocalExclude_log cfg learned (branchRegion cfg))
            (supportedBranchRegionSound_of_conflictNil hclos hbr hreach ht rfl)
      | cons c rest =>
          by_cases hlv : cfg.branch.level = 0
          · -- ARM 14: the level-0 conflict is terminal — no successor
            simp only [conflictStep, if_pos hlv, successor_unsat] at hsucc
            cases hsucc
          · -- ARM 5: the recording site — log unchanged
            simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
              Option.some.injEq] at hsucc
            subst hsucc
            exact newRegionsSound_of_regions_eq rfl
    · -- ARM 10: the localExcluded site, branch region
      rw [hnext] at hsucc
      simp only [successor_localExclude, Option.some.injEq] at hsucc
      subst hsucc
      exact newRegionsSound_of_register
        (stepLocalExclude_log cfg learned (branchRegion cfg))
        (supportedBranchRegionSound_of_localExcluded hclos hbr hreach ht)

/-! ## §4 Convenience producers (E1 residual / core-gate record) -/

/-- **THE E1-RESIDUAL PRODUCER**: the dispatcher with the current
checkpoint-rejection residual consumed DIRECTLY through E1's
`supportedHdeadCheckpointRegion_of_premises` (its residual families:
`hbr` + `hent` + `hsurv`, where `hsurv` is J1's loose-bound survivor
premise). No gate record and no region-soundness premise is assumed: the
checkpoint region is derived from the actual rejection-site producer. -/
theorem supportedNewRegionsSound_of_E1premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned])
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail) :
    SupportedNewRegionsSound orig original props leaf :=
  supportedNewRegionsSound_of_premises hshape hclos hbr
    (supportedHdeadCheckpointRegion_of_premises hbr hent hsurv)

/-- **THE CORE-GATE PRODUCER**: the dispatcher from an assembled
`SupportedArmInvGatesCore` record plus the joint induction's branch
component. The `hclos` gate is transported to the dispatcher's
`cfg.original`/`cfg.props` spelling and `hdeadCheckpointRegion` is the
`hdeadCkpt` premise; the derived deadness gates
(`hdeadStableNone`/`hdeadFallbackNone`/`hdeadFallbackNoCp`) are not
consumed here — this module derives those sites from `hshape`/`hbr`/`hclos`
via the landed producers. -/
theorem supportedNewRegionsSound_of_coreGates {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    (hg : SupportedArmInvGatesCore orig original props leaf) :
    SupportedNewRegionsSound orig original props leaf :=
  supportedNewRegionsSound_of_premises hshape
    (fun {cfg} hreach => by
      rw [SupportedReach.original_eq hreach, SupportedReach.props_eq hreach]
      exact hg.hclos hreach)
    hbr
    hg.hdeadCheckpointRegion

/-! ## §5 The supported-run log theorem (the L1 export)

`supportedLogSound_of_newRegions` (SupportedLog.lean) is the compiled run
induction; feeding it the §3 dispatcher yields the supported run's log
soundness from the concrete premise set only — no `hnew`, no log-soundness
or invariant input, no assumed progress. This is the L1 deliverable the R2
consume integration consumes as `hnew`/predecessor `log_sound`. -/

/-- **THE SUPPORTED-RUN LOG THEOREM (L1)**: every configuration of the
supported run has a sound exhaustion log; premises are exactly
`{hshape, hclos, hbr, hdeadCkpt}`. -/
theorem supportedLogSound_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    (hdeadCkpt : ∀ {cfg : SchedulerConfig leaf} {cp : DecisionCheckpoint leaf}
      {ev : ConflictEvidence} {an : ConflictAnalysis},
      SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
      (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting an.learned).perform
          cfg.branch cfg.original cfg.props = none →
        DeadRegion.Sound leaf (checkpointRegion cp)) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
  supportedLogSound_of_newRegions
    (supportedNewRegionsSound_of_premises hshape hclos hbr hdeadCkpt)

/-- The supported-run log theorem with the checkpoint-rejection residual
consumed directly through E1's
`supportedHdeadCheckpointRegion_of_premises` (`hsurv` ← J1). -/
theorem supportedLogSound_of_E1premises {orig : List Domain}
    {original : List Clause} {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hclos : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ClosureContract leaf orig cfg.original cfg.props)
    (hbr : ∀ {cfg : SchedulerConfig leaf},
      SupportedReach orig original props cfg →
        ReachableState leaf orig cfg.branch)
    (hent : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis}, SupportedReach orig original props cfg →
      cfg.conflict = some ev → ev.analysis = some an →
        LearnedEntailed leaf [an.learned])
    (hsurv : ∀ {cfg : SchedulerConfig leaf} {ev : ConflictEvidence}
      {an : ConflictAnalysis} {cp : DecisionCheckpoint leaf},
      SupportedReach orig original props cfg → cfg.conflict = some ev →
      ev.analysis = some an →
      checkpointAt cfg.checkpoints an.backjumpLevel = some cp →
        ∀ e ∈ cfg.branch.trail, e.level ≤ an.backjumpLevel → e ∈ cp.trail) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ExhaustionLog.Sound leaf cfg.log :=
  supportedLogSound_of_newRegions
    (supportedNewRegionsSound_of_E1premises hshape hclos hbr hent hsurv)

end LeanFzn.Solver.UIP
