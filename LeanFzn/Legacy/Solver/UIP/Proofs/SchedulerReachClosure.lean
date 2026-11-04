/-
File: LeanFzn/Solver/UIP/Proofs/SchedulerReachClosure.lean

Purpose: close the DRIVER-PATH reachability premises that block a closed
`X2.runPhase` term (owners S5/W1 in the handoffs):

 1. `hclos` — phase-step reachability closure:
    `∀ cfg cfg', SchedulerReachable cfg → (C3b.phaseNext cfg).successor = some cfg'
       → SchedulerReachable cfg'`.
    Route: `phaseNext` either PASSES THROUGH a real `schedulerNext` transition
    or COMPOSES a stutter with `stepConsume` (see `Proofs/Scheduler.lean`'s
    `phaseNext` docstring). Both are finite chains of REAL dispatcher
    successors, so `RawReach` (§1) records exactly those chains and
    `phaseNext_successor_rawReach` (§2) classifies every phase successor
    into one. R1's `schedulerReachable_successor` then lifts the chain.
 2. `PhaseOrigFrame` (W1's residual) — `orig` preserved by every `phaseNext`
    successor: same chains, each raw link preserves `orig`
    (`W1.schedulerNext_succ_orig`), so the endpoint does too
    (`phaseNext_succ_orig`, `phaseNextOrigFrame`).
 3. `hbr` — branch-level `ReachableState` from config reachability. The
    needed shape is fixed here as the SELF-ORIG invariant
    `ReachableBranchInvariant leaf` (§4:
    `∀ cfg, SchedulerReachable cfg → ReachableState leaf cfg.orig cfg.branch`),
    with the root discharged by R1's `reachable_init` and the step reduced to
    the named per-arm successor-preservation premise `ReachableArmsPreserve`
    (S5's arm table content; the irreducible per-arm hypotheses are listed in
    the §4 header and reported with owners). The fixed-`orig` consumer form
    (`hbr` of P5 §6 / S5's `arm_sat_solution`) is the corollary
    `reachableState_of_reachable_orig`.

NO `sorry`, no custom axiom: §2 is a total case analysis over
`C2d.schedulerNext_cases` whose EVERY arm is a finite chain of the real
transition equations; the stutter sites pay the forced `stepConsume` link.

DAG: Proofs.SchedulerReachable (R1) + Proofs.SchedulerRun (W1) + the real
phase dispatcher (Proofs/Scheduler §phaseNext) -> this module (consumed by
X2/W1's `runPhaseFrom`/`run_sat_solution`). Registration owes the umbrella
line `import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerReachClosure`.
-/

import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerRun
import LeanFzn.Legacy.Solver.UIP.Proofs.SchedulerReachable
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core
open LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.UIP.C3b

/-! ## §1 Raw dispatcher-step chains

`phaseNext` composes stutter arms with their FORCED successor, so one phase
step is a finite chain of real `schedulerNext` successors (one, two, or
three links). `RawReach` is the closure of that relation; its two
consequences are exactly the premises the driver consumes. -/

/-- Finite chains of REAL dispatcher successors. -/
inductive RawReach {leaf : Assignment → Bool} :
    SchedulerConfig leaf → SchedulerConfig leaf → Prop where
  /-- the empty chain -/
  | refl (cfg : SchedulerConfig leaf) : RawReach cfg cfg
  /-- one real link: `schedulerNext` has this successor, then the rest -/
  | step {cfg c cfg' : SchedulerConfig leaf} :
      (schedulerNext cfg).successor = some c → RawReach c cfg' →
        RawReach cfg cfg'

/-- A single raw link. -/
theorem rawReach_of_step {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (h : (schedulerNext cfg).successor = some cfg') : RawReach cfg cfg' :=
  RawReach.step h (RawReach.refl cfg')

/-- `hclos` content: a raw chain starting at a reachable configuration ends
at a reachable configuration (R1's `schedulerReachable_successor` per link,
`Proofs/SchedulerReachable`). -/
theorem RawReach.reachable {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} (h : RawReach cfg cfg')
    (h₀ : SchedulerReachable cfg) : SchedulerReachable cfg' := by
  induction h with
  | refl => exact h₀
  | step hs _ ih => exact ih (SchedulerReachable.step rfl hs h₀)

/-- `PhaseOrigFrame` content: every raw link preserves `orig`
(`W1.schedulerNext_succ_orig`), hence so does a chain. -/
theorem RawReach.orig {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} (h : RawReach cfg cfg') :
    cfg'.orig = cfg.orig := by
  induction h with
  | refl => rfl
  | step hs _ ih => exact ih.trans (W1.schedulerNext_succ_orig hs)

/-- The static inputs (`orig`, `original`, `props`) are preserved by a raw
chain (`W1.schedulerNext_succ_inputs` per link) — the `PhaseInputsFrame`
content. -/
theorem RawReach.inputs {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} (h : RawReach cfg cfg') :
    cfg'.orig = cfg.orig ∧ cfg'.original = cfg.original ∧
      cfg'.props = cfg.props := by
  induction h with
  | refl => exact ⟨rfl, rfl, rfl⟩
  | step hs _ ih =>
      obtain ⟨h1, h2, h3⟩ := ih
      obtain ⟨g1, g2, g3⟩ := W1.schedulerNext_succ_inputs hs
      exact ⟨h1.trans g1, h2.trans g2, h3.trans g3⟩

/-- The generic composed landing: a stutter/fallback/exclusion site `n`
whose successor `n'` is dead and carries no evidence is followed by the
FORCED consume link, so `next` is raw-reachable from `n`. This is the
single shape of every composed `phaseNext` branch. -/
theorem rawReach_of_landing_consume {leaf : Assignment → Bool}
    {n n' next : SchedulerConfig leaf}
    (hland : (schedulerNext n).successor = some n')
    (hc : n'.conflict = none) (hd : n'.status = .dead)
    (hsc : stepConsume n' = some next) : RawReach n next :=
  RawReach.step hland (rawReach_of_step (by
    rw [schedulerNext_eq_consumeStep_of_dead (cfg := n') hc hd]
    simp only [consumeStep, hsc]
    rfl))

/-- Projection bridge for the counted analyze site: the runtime projection
set has `_orig`/`_props` but not `_original`, which the real `backjumpStep`
passes to `BackjumpPlan.perform`. Locally named to avoid a homonym with a
future runtime projection lemma. -/
theorem stepAnalyzeConflictCounted_original_rc (cfg : SchedulerConfig leaf)
    (c : Clause) (learned : List Clause) (n : Nat) :
    (stepAnalyzeConflictCounted cfg c learned n).original = cfg.original :=
  rfl

/-! ## §2 The master classification: every phase successor is a raw chain

One case analysis over the real dispatcher (`C2d.schedulerNext_cases`),
mirroring P5's rank assembly arm for arm. Each arm either passes a real
`schedulerNext` transition through (`| t => t`) or composes a landing with
`stepConsume`; in both shapes the successor is a chain of real successors.
The `.sat`/`.unsat` terminals have no successor and are closed by
contradiction. -/

/-- **EVERY `phaseNext` SUCCESSOR IS A FINITE CHAIN OF REAL DISPATCHER
SUCCESSORS.** This is the single fact from which both `hclos` and
`phaseNext_succ_orig` follow. -/
theorem phaseNext_successor_rawReach {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (hsucc : (phaseNext cfg).successor = some cfg') : RawReach cfg cfg' := by
  rcases C2d.schedulerNext_cases cfg with
    ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
  · -- ===== ROUTE 1: recorded evidence (schedulerNext cfg = backjumpStep cfg ev)
    cases ha : ev.analysis with
    | none =>
        cases hsc : stepConsume (stepChronologicalFallback cfg (branchRegion cfg)) with
        | none =>
            have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
              simp only [phaseNext, hnext, backjumpStep, ha, hc, hsc]
            rw [hpe] at hsucc
            simp at hsucc
        | some next =>
            have hpe : phaseNext cfg = .chronologicalFallback next := by
              simp only [phaseNext, hnext, backjumpStep, ha, hc, hsc]
            rw [hpe] at hsucc
            simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
            cases hsucc
            exact rawReach_of_landing_consume
              (by simp only [hnext, backjumpStep, ha, successor_chronologicalFallback])
              (stepChronologicalFallback_conflict cfg (branchRegion cfg))
              (stepChronologicalFallback_status cfg (branchRegion cfg)) hsc
    | some an =>
        cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
        | none =>
            cases hsc : stepConsume
                (stepChronologicalFallback cfg (branchRegion cfg)) with
            | none =>
                have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
                  simp only [phaseNext, hnext, backjumpStep, ha, hcp, hc, hsc]
                rw [hpe] at hsucc
                simp at hsucc
            | some next =>
                have hpe : phaseNext cfg = .chronologicalFallback next := by
                  simp only [phaseNext, hnext, backjumpStep, ha, hcp, hc, hsc]
                rw [hpe] at hsucc
                simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
                cases hsucc
                exact rawReach_of_landing_consume
                  (by simp only [hnext, backjumpStep, ha, hcp,
                    successor_chronologicalFallback])
                  (stepChronologicalFallback_conflict cfg (branchRegion cfg))
                  (stepChronologicalFallback_status cfg (branchRegion cfg)) hsc
        | some cp =>
            cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
            | none =>
                cases hsc : stepConsume
                    (stepLocalExclude cfg ev.learned (checkpointRegion cp)) with
                | none =>
                    have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
                      simp only [phaseNext, hnext, backjumpStep, ha, hcp, hp, hsc]
                    rw [hpe] at hsucc
                    simp at hsucc
                | some next =>
                    have hpe : phaseNext cfg = .chronologicalFallback next := by
                      simp only [phaseNext, hnext, backjumpStep, ha, hcp, hp, hsc]
                    rw [hpe] at hsucc
                    simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
                    cases hsucc
                    exact rawReach_of_landing_consume
                      (by simp only [hnext, backjumpStep, ha, hcp, hp,
                        successor_localExclude])
                      (stepLocalExclude_conflict cfg ev.learned (checkpointRegion cp))
                      (stepLocalExclude_status cfg ev.learned (checkpointRegion cp)) hsc
            | some restored =>
                -- the real jump: passed through verbatim
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
                exact rawReach_of_step (by
                  simp only [hnext, backjumpStep, ha, hcp, hp,
                    successor_learnBackjumpAssert])
  · -- ===== ROUTE 2: dead branch — the REAL consume route, passed through
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
        exact rawReach_of_step (by
          simp only [hnext, consumeStep, hsc, successor_chronologicalFallback])
  · -- ===== ROUTE 3: active branch
    rcases hrest with
      ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
        ⟨bs, lit, reason, learned, ht, hnext⟩
    · -- ARM 1: propagate (passed through)
      have hpe : phaseNext cfg = .propagate (stepPropagate cfg d) := by
        simp only [phaseNext, hnext]
      rw [hpe] at hsucc
      simp only [successor_propagate, Option.some.injEq] at hsucc
      cases hsucc
      exact rawReach_of_step (by simp only [hnext, successor_propagate])
    · -- ARM 2 / ARM 3 / ARM 6: stableStepGuarded (B1: fresh or skip)
      cases hw : leafWitness leaf cfg with
      | some w =>
          have hpe : phaseNext cfg = (.sat w : SchedulerTransition leaf) := by
            simp only [phaseNext, hnext, stableStepGuarded, hw]
          rw [hpe] at hsucc
          simp at hsucc
      | none =>
          cases hsp : splitData cfg.branch.frame cfg.prio with
          | some q =>
              obtain ⟨l, k, v, vs⟩ := q
              by_cases hred : TrailRedundant cfg.branch.trail l = true
              · -- ARM 2b: the redundant-pin skip
                have hs : schedulerNext cfg =
                    .decide (stepDecideSkip cfg k v) l := by
                  rw [hnext]
                  simp only [stableStepGuarded, hw, hsp]
                  rw [if_pos hred]
                have hpe : phaseNext cfg =
                    .decide (stepDecideSkip cfg k v) l := by
                  simp only [phaseNext, hs]
                rw [hpe] at hsucc
                simp only [successor_decide, Option.some.injEq] at hsucc
                cases hsucc
                exact rawReach_of_step (by rw [hs, successor_decide])
              · -- ARM 2a: the fresh decision
                have hred' : TrailRedundant cfg.branch.trail l = false := by
                  cases hh : TrailRedundant cfg.branch.trail l <;> simp_all
                have hs : schedulerNext cfg =
                    .decide (stepDecide cfg k v vs l) l := by
                  rw [hnext]
                  simp only [stableStepGuarded, hw, hsp]
                  rw [if_neg]
                  rw [hred']
                  simp
                have hpe : phaseNext cfg =
                    .decide (stepDecide cfg k v vs l) l := by
                  simp only [phaseNext, hs]
                rw [hpe] at hsucc
                simp only [successor_decide, Option.some.injEq] at hsucc
                cases hsucc
                exact rawReach_of_step (by rw [hs, successor_decide])
          | none =>
              -- ARM 6: localExclude stutter → forced consume
              cases hsc : stepConsume (stepLocalExclude cfg [] (branchRegion cfg)) with
              | none =>
                  have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
                    simp only [phaseNext, hnext, stableStepGuarded, hw, hsp, hsc]
                  rw [hpe] at hsucc
                  simp at hsucc
              | some next =>
                  have hpe : phaseNext cfg = .chronologicalFallback next := by
                    simp only [phaseNext, hnext, stableStepGuarded, hw, hsp, hsc]
                  rw [hpe] at hsucc
                  simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
                  cases hsucc
                  exact rawReach_of_landing_consume
                    (by simp only [hnext, stableStepGuarded, hw, hsp, successor_localExclude])
                    (stepLocalExclude_conflict cfg [] (branchRegion cfg))
                    (stepLocalExclude_status cfg [] (branchRegion cfg)) hsc
    · -- ARM 8 / ARM 4 / ARM 6: conflictStep
      cases cs with
      | nil =>
          -- empty reported clause list: LOCAL exclusion → forced consume
          cases hsc : stepConsume (stepLocalExclude cfg learned (branchRegion cfg)) with
          | none =>
              have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
                simp only [phaseNext, hnext, conflictStep, hsc]
              rw [hpe] at hsucc
              simp at hsucc
          | some next =>
              have hpe : phaseNext cfg = .chronologicalFallback next := by
                simp only [phaseNext, hnext, conflictStep, hsc]
              rw [hpe] at hsucc
              simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
              cases hsucc
              exact rawReach_of_landing_consume
                (by simp only [hnext, conflictStep, successor_localExclude])
                (stepLocalExclude_conflict cfg learned (branchRegion cfg))
                (stepLocalExclude_status cfg learned (branchRegion cfg)) hsc
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
                  simp only [conflictStep, if_neg hlv, successor_analyzeConflict]
                have h1 : (schedulerNext cfg).successor =
                    some (stepAnalyzeConflictCounted cfg c learned
                      (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)) := by
                  rw [hnext]; exact hsuccN
                refine RawReach.step h1 ?_
                cases ha : ev.analysis with
                | none =>
                    -- analyze-site fallback stutter → forced consume
                    cases hsc : stepConsume
                        (stepChronologicalFallback
                          (stepAnalyzeConflictCounted cfg c learned
                            (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                          (branchRegion (stepAnalyzeConflictCounted cfg c learned
                            (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)))) with
                    | none =>
                        have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
                          simp only [phaseNext, hnext, conflictStep, if_neg hlv, hev,
                            backjumpStep, ha, hsc]
                        rw [hpe] at hsucc
                        simp at hsucc
                    | some next =>
                        have hpe : phaseNext cfg = .chronologicalFallback next := by
                          simp only [phaseNext, hnext, conflictStep, if_neg hlv, hev,
                            backjumpStep, ha, hsc]
                        rw [hpe] at hsucc
                        simp only [successor_chronologicalFallback,
                          Option.some.injEq] at hsucc
                        cases hsucc
                        exact rawReach_of_landing_consume
                          (by simp only [schedulerNext, hev, backjumpStep, ha,
                            successor_chronologicalFallback])
                          (stepChronologicalFallback_conflict _ _)
                          (stepChronologicalFallback_status _ _) hsc
                | some an =>
                    cases hcp : checkpointAt
                        (stepAnalyzeConflictCounted cfg c learned
                          (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)).checkpoints
                        an.backjumpLevel with
                    | none =>
                        cases hsc : stepConsume
                            (stepChronologicalFallback
                              (stepAnalyzeConflictCounted cfg c learned
                                (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c))
                              (branchRegion (stepAnalyzeConflictCounted cfg c learned
                                (analyzeEventsExpansions cfg.orig cfg.branch.trail cfg.branch.level c)))) with
                        | none =>
                            have hpe : phaseNext cfg =
                                (.unsat : SchedulerTransition leaf) := by
                              simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                                hev, backjumpStep, ha, hcp, hsc]
                            rw [hpe] at hsucc
                            simp at hsucc
                        | some next =>
                            have hpe : phaseNext cfg = .chronologicalFallback next := by
                              simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                                hev, backjumpStep, ha, hcp, hsc]
                            rw [hpe] at hsucc
                            simp only [successor_chronologicalFallback,
                              Option.some.injEq] at hsucc
                            cases hsucc
                            exact rawReach_of_landing_consume
                              (by simp only [schedulerNext, hev, backjumpStep, ha, hcp,
                                successor_chronologicalFallback])
                              (stepChronologicalFallback_conflict _ _)
                              (stepChronologicalFallback_status _ _) hsc
                    | some cp =>
                        cases hp : (BackjumpPlan.ofCheckpoint cp
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail
                                cfg.branch.level c)).branch
                            an.asserting an.learned).perform
                            (stepAnalyzeConflictCounted cfg c learned
                              (analyzeEventsExpansions cfg.orig cfg.branch.trail
                                cfg.branch.level c)).branch
                            cfg.orig
                            cfg.original cfg.props with
                        | none =>
                            -- checkpoint rejection → localExclude → consume
                            cases hsc : stepConsume
                                (stepLocalExclude
                                  (stepAnalyzeConflictCounted cfg c learned
                                    (analyzeEventsExpansions cfg.orig cfg.branch.trail
                                      cfg.branch.level c))
                                  ev.learned (checkpointRegion cp)) with
                            | none =>
                                have hpe : phaseNext cfg =
                                    (.unsat : SchedulerTransition leaf) := by
                                  simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                                    hev, backjumpStep, ha, hcp,
                                    stepAnalyzeConflictCounted_original_rc,
                                    stepAnalyzeConflictCounted_props, stepAnalyzeConflictCounted_orig, hp, hsc]
                                rw [hpe] at hsucc
                                simp at hsucc
                            | some next =>
                                have hpe : phaseNext cfg =
                                    .chronologicalFallback next := by
                                  simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                                    hev, backjumpStep, ha, hcp,
                                    stepAnalyzeConflictCounted_original_rc,
                                    stepAnalyzeConflictCounted_props, stepAnalyzeConflictCounted_orig, hp, hsc]
                                rw [hpe] at hsucc
                                simp only [successor_chronologicalFallback,
                                  Option.some.injEq] at hsucc
                                cases hsucc
                                exact rawReach_of_landing_consume
                                  (by simp only [schedulerNext, hev, backjumpStep, ha,
                                    hcp, stepAnalyzeConflictCounted_original_rc,
                                    stepAnalyzeConflictCounted_props, stepAnalyzeConflictCounted_orig, hp,
                                    successor_localExclude])
                                  (stepLocalExclude_conflict _ _ _)
                                  (stepLocalExclude_status _ _ _) hsc
                        | some restored =>
                            -- the real jump at the analyze site: passed through
                            have hpe : phaseNext cfg =
                                .learnBackjumpAssert
                                  (stepLearnBackjumpAssert
                                    (stepAnalyzeConflictCounted cfg c learned
                                      (analyzeEventsExpansions cfg.orig cfg.branch.trail
                                        cfg.branch.level c))
                                    (BackjumpPlan.ofCheckpoint cp
                                      (stepAnalyzeConflictCounted cfg c learned
                                        (analyzeEventsExpansions cfg.orig cfg.branch.trail
                                          cfg.branch.level c)).branch
                                      an.asserting an.learned)
                                    ev restored)
                                  (BackjumpPlan.ofCheckpoint cp
                                    (stepAnalyzeConflictCounted cfg c learned
                                      (analyzeEventsExpansions cfg.orig cfg.branch.trail
                                        cfg.branch.level c)).branch
                                    an.asserting an.learned) an := by
                              simp only [phaseNext, hnext, conflictStep, if_neg hlv,
                                hev, backjumpStep, ha, hcp,
                                stepAnalyzeConflictCounted_original_rc,
                                stepAnalyzeConflictCounted_props, stepAnalyzeConflictCounted_orig, hp]
                            rw [hpe] at hsucc
                            simp only [successor_learnBackjumpAssert,
                              Option.some.injEq] at hsucc
                            cases hsucc
                            exact rawReach_of_step (by
                              simp only [schedulerNext, hev, backjumpStep, ha, hcp,
                                stepAnalyzeConflictCounted_original_rc,
                                stepAnalyzeConflictCounted_props, stepAnalyzeConflictCounted_orig, hp,
                                successor_learnBackjumpAssert])
    · -- ARM 6: localExcluded site → forced consume
      cases hsc : stepConsume (stepLocalExclude cfg learned (branchRegion cfg)) with
      | none =>
          have hpe : phaseNext cfg = (.unsat : SchedulerTransition leaf) := by
            simp only [phaseNext, hnext, hsc]
          rw [hpe] at hsucc
          simp at hsucc
      | some next =>
          have hpe : phaseNext cfg = .chronologicalFallback next := by
            simp only [phaseNext, hnext, hsc]
          rw [hpe] at hsucc
          simp only [successor_chronologicalFallback, Option.some.injEq] at hsucc
          cases hsucc
          exact rawReach_of_landing_consume
            (by simp only [hnext, successor_localExclude])
            (stepLocalExclude_conflict cfg learned (branchRegion cfg))
            (stepLocalExclude_status cfg learned (branchRegion cfg)) hsc

/-! ## §3 Premise 1 CLOSED (`hclos`) and premise 2 CLOSED (`PhaseOrigFrame`) -/

/-- **PREMISE 1 CLOSED (`hclos`)**: phase-step reachability closure. -/
theorem phaseNext_reachable_succ {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf} (h : SchedulerReachable cfg)
    (hsucc : (phaseNext cfg).successor = some cfg') :
    SchedulerReachable cfg' :=
  RawReach.reachable (phaseNext_successor_rawReach hsucc) h

/-- **PREMISE 2 (core)**: every `phaseNext` successor preserves `orig`. -/
theorem phaseNext_succ_orig {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (hsucc : (phaseNext cfg).successor = some cfg') :
    cfg'.orig = cfg.orig :=
  RawReach.orig (phaseNext_successor_rawReach hsucc)

/-- **PREMISE 2 CLOSED**: W1's `PhaseOrigFrame` holds at the real phase
dispatcher (no premise — the reachability hypothesis of the statement is
not needed by the chain proof, matching `schedulerNext_succ_orig`). -/
theorem phaseNextOrigFrame (orig : List Domain) (leaf : Assignment → Bool) :
    W1.PhaseOrigFrame orig leaf :=
  fun _ _ _ hsucc => phaseNext_succ_orig hsucc

/-- **THE STATIC-INPUTS FRAME**: every `phaseNext` successor preserves
`original` and `props` (the `orig` companion of `phaseNext_succ_orig`;
same raw-chain route). -/
theorem phaseNext_succ_inputs {leaf : Assignment → Bool}
    {cfg cfg' : SchedulerConfig leaf}
    (hsucc : (phaseNext cfg).successor = some cfg') :
    cfg'.original = cfg.original ∧ cfg'.props = cfg.props := by
  obtain ⟨-, h2, h3⟩ := RawReach.inputs (phaseNext_successor_rawReach hsucc)
  exact ⟨h2, h3⟩

/-- **CLOSED**: W1's companion frame for the static inputs holds at the
real phase dispatcher (no premise). -/
theorem phaseNextInputsFrame (original : List Clause)
    (props : List Propagator) (leaf : Assignment → Bool) :
    W1.PhaseInputsFrame original props leaf :=
  fun _ _ _ hsucc => phaseNext_succ_inputs hsucc

/-! ## §4 Premise 3 (`hbr`): the branch invariant, reduced to the arm table

The needed shape (P5 §6 / S5 `arm_sat_solution` consumer) is the self-orig
form: every reachable configuration's CURRENT BRANCH is a reachable branch
state OF ITS OWN original box. The root is R1's `reachable_init`; the step
is exactly S5's per-arm successor-invariant assembly. That assembly's
per-arm content is S5's `arm_*_invariant` table (propagate/decide/analyze
closed; the jump and the exclusion/fallback arms carry the named
irreducible hypotheses recorded by S5: `RestorationPreReachable`,
`SurvivorRestoration`, `RecordedAnalysisFalsified`, `LearnedEntailed`),
so the residual is fixed here as the single named preservation premise
`ReachableArmsPreserve` with that owner attribution. -/

/-- The exact `hbr` shape on reachable runs (self-orig form). -/
def ReachableBranchInvariant (leaf : Assignment → Bool) : Prop :=
  ∀ cfg : SchedulerConfig leaf,
    SchedulerReachable cfg → ReachableState leaf cfg.orig cfg.branch

/-- The named residual of premise 3: S5's per-arm successor-invariant
assembly in successor form. Owners: S5 (assembly) with the per-arm
hypotheses of S1/S3/S4 as recorded in S5's handoff. -/
def ReachableArmsPreserve (leaf : Assignment → Bool) : Prop :=
  ∀ {cfg cfg' : SchedulerConfig leaf},
    (schedulerNext cfg).successor = some cfg' →
    ReachableState leaf cfg.orig cfg.branch →
      ReachableState leaf cfg.orig cfg'.branch

/-- Premise 3 reduced to the arm table: `ReachableBranchInvariant` holds
as soon as `ReachableArmsPreserve` does — induction over reachability with
R1's root witness (`reachable_init`) and `orig` transported across each
raw step by `W1.schedulerNext_succ_orig`. -/
theorem reachableBranchInvariant_of_preservation {leaf : Assignment → Bool}
    (hpres : ReachableArmsPreserve leaf) : ReachableBranchInvariant leaf := by
  intro cfg h
  induction h with
  | init orig original props hent => exact reachable_seed leaf orig original hent
  | step hnext hsucc _hr ih =>
      have h' := hpres (hnext ▸ hsucc) ih
      rw [W1.schedulerNext_succ_orig (hnext ▸ hsucc)]
      exact h'

/-- The fixed-`orig` consumer form (`hbr` of P5 §6 / S5's
`arm_sat_solution`): a reachable configuration initialized with `orig` has
a reachable branch state over `orig`. -/
theorem reachableState_of_reachable_orig {leaf : Assignment → Bool}
    {orig : List Domain} (hpres : ReachableArmsPreserve leaf)
    {cfg : SchedulerConfig leaf} (h : SchedulerReachable cfg)
    (horig : cfg.orig = orig) : ReachableState leaf orig cfg.branch := by
  have hb := (reachableBranchInvariant_of_preservation hpres) cfg h
  rw [← horig]
  exact hb

/-- The `hbr` premise exactly as P5's assembly consumes it, packaged. -/
theorem hbr_of_preservation {leaf : Assignment → Bool} (orig : List Domain)
    (hpres : ReachableArmsPreserve leaf) :
    ∀ {cfg : SchedulerConfig leaf}, SchedulerReachable cfg → cfg.orig = orig →
      ReachableState leaf orig cfg.branch := by
  intro cfg h horig
  exact reachableState_of_reachable_orig (leaf := leaf) (orig := orig)
    hpres h horig

end LeanFzn.Solver.UIP
