/-
File: LeanFzn/Solver/UIP/Proofs/PendingRun.lean
pending-side invariant, its preservation along a supported run, and the
route-(b) consume consumer)

Purpose: close R2a's two remaining obligations on top of the per-arm
lemmas of `Proofs/PendingBacked.lean` §5:

  §1 `pendingSideInv_of_premises` — ONE joint induction over the
     supported run (`SupportedReach orig original props`) that maintains
     `PendingSideInv orig cfg` at every configuration, dispatching through
     the real `schedulerNext` leaf table (`C2d.schedulerNext_cases`) and
     consuming exactly the per-arm preservation lemmas of §5.5. The decide
     arm's `ReachableState` premise comes from the run-level branch
     invariant `hbr`; the jump arm's checkpoint membership comes from
     `checkpointAt_mem`. No domain `Nodup`, no density or depth premise:
     sparse domains and deep/shallow pending stacks go through the same
     lemmas.

  §2 the consume consumers at the run's own box:
     * `stepConsume_reachable_of_inv` — the single canonical route, with
       the head's backing DERIVED from `PendingSideInv.pending` (never
       assumed at the site), consuming `resumePending_reachable`;
     * `stepConsume_reachable_of_inv_missing_checkpoint` — compatibility
       wrapper (the checkpoint-absent premise is unused: every consume is
       the canonical resume);
     * `supportedHconsume_of_premises` — the run-level `hconsume` gate.

  §3 retired route-(a) audit: the old checkpoint-consulting
     `resumeSibling bs f cp` declarations were removed with the old
     signature (the runtime uses the single canonical route).

NO `sorry`, NO custom axiom. Registered in the umbrella
(`LeanFzn.Solver.lean`). -/

import LeanFzn.Legacy.Solver.UIP.Proofs.PendingBacked
import LeanFzn.Legacy.Solver.UIP.Proofs.SupportedRun
open LeanFzn.Solver.Propagation.DomainFiltering LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Propagation LeanFzn.Solver.UIP LeanFzn.Solver.Reference LeanFzn.Compiler


namespace LeanFzn.Solver.UIP
open LeanFzn.Semantics LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Reference LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn LeanFzn.Solver.Core

/-! ## §1 The run-level producer: `PendingSideInv` along a supported run -/

/-- **R2a STEP (pair-friendly form)**: one real supported successor
preserves `PendingSideInv`, consuming the PREDECESSOR's branch
reachability directly (only the fresh-decide arm needs it:
`PendingSideInv.stepDecide`'s reachability premise). This is the form a
joint induction over `ReachableState ∧ … ∧ PendingSideInv` calls — the
predecessor's reachability is the other component of its own induction
hypothesis. The jump arm's checkpoint membership comes from
`checkpointAt_mem`. -/
theorem pendingSideInv_supportedStep {orig : List Domain}
    {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    {cfg cfg' : SchedulerConfig leaf}
    (hbrPRE : ReachableState leaf orig cfg.branch)
    (hs : (schedulerNext cfg).successor = some cfg')
    (ih : PendingSideInv orig cfg) :
    PendingSideInv orig cfg' := by
      rcases C2d.schedulerNext_cases cfg with
        ⟨ev, hc, hnext⟩ | ⟨hconf, hdead, hnext⟩ | ⟨hconf, hact, hrest⟩
      · -- ===== ROUTE 1: recorded evidence (backjumpStep)
        rw [hnext] at hs
        unfold backjumpStep at hs
        cases ha : ev.analysis with
        | none =>
            -- no analysis → chronological fallback (stack and checkpoints kept)
            rw [ha] at hs
            simp only [] at hs
            simp only [successor_chronologicalFallback, Option.some.injEq] at hs
            subst hs
            exact ih.stepChronologicalFallback (r := branchRegion cfg)
        | some an =>
            cases hcp : checkpointAt cfg.checkpoints an.backjumpLevel with
            | none =>
                -- no checkpoint → chronological fallback
                rw [ha] at hs
                simp only [] at hs
                rw [hcp] at hs
                simp only [] at hs
                simp only [successor_chronologicalFallback, Option.some.injEq]
                  at hs
                subst hs
                exact ih.stepChronologicalFallback (r := branchRegion cfg)
            | some cp =>
                cases hp : (BackjumpPlan.ofCheckpoint cp cfg.branch an.asserting
                    an.learned).perform cfg.branch cfg.orig cfg.original cfg.props with
                | none =>
                    -- perform rejected → local exclusion (stack kept)
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_localExclude, Option.some.injEq] at hs
                    subst hs
                    exact ih.stepLocalExclude (learned := ev.learned)
                      (r := checkpointRegion cp)
                | some restored =>
                    -- the recorded jump: the selected checkpoint's prefix
                    -- discipline comes from the invariant's checkpoint
                    -- component (`checkpointAt_mem`)
                    rw [ha] at hs
                    simp only [] at hs
                    rw [hcp] at hs
                    simp only [] at hs
                    rw [hp] at hs
                    simp only [] at hs
                    simp only [successor_learnBackjumpAssert, Option.some.injEq]
                      at hs
                    subst hs
                    exact ih.stepLearnBackjumpAssert_ofCheckpoint
                      (checkpointAt_mem hcp) hp
      · -- ===== ROUTE 2: dead branch — the consume route
        rw [hnext] at hs
        unfold consumeStep at hs
        split at hs
        · -- resumed
          rename_i next hcs
          simp only [successor_chronologicalFallback, Option.some.injEq] at hs
          subst hs
          cases hpend : cfg.pending with
          | nil =>
              rw [(stepConsume_eq_none_iff (cfg := cfg)).mpr hpend] at hcs
              cases hcs
          | cons f rest => exact ih.stepConsume hpend hcs
        · -- frontier exhausted: no successor
          simp only [successor_unsat] at hs
          exact absurd hs (by simp)
      · -- ===== ROUTE 3: active branch
        rcases hrest with
          ⟨d, hd, hnext⟩ | ⟨bs, ht, hnext⟩ | ⟨bs, cs, learned, ht, hnext⟩ |
            ⟨bs, lit, reason, learned, ht, hnext⟩
        · -- ARM 1: propagate
          rw [hnext] at hs
          simp only [successor_propagate, Option.some.injEq] at hs
          subst hs
          exact ih.stepPropagate d
        · -- ARM 2 / ARM 3 / ARM 6: the guarded stable dispatch
          rw [hnext] at hs
          unfold stableStepGuarded at hs
          split at hs
          · -- witness: terminal, no successor
            simp only [successor_sat] at hs
            cases hs
          · split at hs
            · -- split data: fresh decision or redundant-pin skip
              rename_i l k v vs hsp
              split at hs
              · -- SKIP arm: stepDecideSkip (redundant pin)
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                exact ih.stepDecideSkip hsp
              · -- FRESH arm: stepDecide (the one arm needing predecessor reachability)
                simp only [successor_decide, Option.some.injEq] at hs
                subst hs
                exact ih.stepDecide hsp hbrPRE hshape
            · -- no split data: local exclusion with the empty payload
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact ih.stepLocalExclude (learned := []) (r := branchRegion cfg)
        · -- ARM 8 / ARM 4: the conflict dispatch
          cases cs with
          | nil =>
              -- empty clause list: local exclusion with the payload
              rw [hnext] at hs
              simp only [conflictStep] at hs
              simp only [successor_localExclude, Option.some.injEq] at hs
              subst hs
              exact ih.stepLocalExclude (learned := learned)
                (r := branchRegion cfg)
          | cons c rest =>
              by_cases hlv : cfg.branch.level = 0
              · -- level 0: root contradiction, no successor
                rw [hnext] at hs
                simp only [conflictStep, if_pos hlv, successor_unsat] at hs
                cases hs
              · -- recorded analyze site: branch unchanged
                rw [hnext] at hs
                simp only [conflictStep, if_neg hlv, successor_analyzeConflict,
                  Option.some.injEq] at hs
                subst hs
                exact ih.stepAnalyzeConflictCounted
        · -- ARM 6: localExcluded → local exclusion with the payload
          rw [hnext] at hs
          simp only [successor_localExclude, Option.some.injEq] at hs
          subst hs
          exact ih.stepLocalExclude (learned := learned) (r := branchRegion cfg)

/-- **R2a PRODUCER (run level)**: every configuration of a supported run
carries `PendingSideInv` — the current branch's prefix is pinned, every
pending alternative is backed, every saved checkpoint's frame prefix is
pinned. An induction over `SupportedReach` steered by the per-arm
`pendingSideInv_supportedStep`. External premises: the run box's typing
`hshape` and the run's branch reachability `hbr` (only the decide arm
consumes `hbr`). -/
theorem pendingSideInv_of_premises {orig : List Domain} {original : List Clause}
    {props : List Propagator} {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch) :
    ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      PendingSideInv orig cfg := by
  intro cfg hreach
  induction hreach with
  | init => exact PendingSideInv.init orig original props
  | step hrec hs ih => exact pendingSideInv_supportedStep hshape (hbr hrec) hs ih

/-! ## §2 The consume reachability consumer (single canonical route) -/

/-- **R2 CONSUMER — THE SINGLE CANONICAL ROUTE, UNCONDITIONAL**: any
consume of a backed pending head resumes a reachable branch. The
successor's branch is ALWAYS `resumePending` (the checkpoint-consulting
route is RETIRED — `resumeSibling_shadow_not_represents` refutes it on a
genuine reachable run), and its reachability is R1's
`resumePending_reachable` fed with the head's backing DERIVED from the
run-level stack invariant (`hpinv.pending`). No checkpoint case split, no
route-(a) premise. -/
theorem stepConsume_reachable_of_inv {leaf : Assignment → Bool}
    {orig : List Domain} {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next)
    (hreach : ReachableState leaf orig cfg.branch)
    (hpinv : PendingSideInv orig cfg) (horig : cfg.orig = orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    ReachableState leaf orig next.branch := by
  rw [← horig] at hreach hpinv hfits ⊢
  rw [stepConsume_branch hp h]
  exact resumePending_reachable hreach
    (hpinv.pending f (by rw [hp]; exact List.mem_cons_self ..)) hfits

/-- COMPATIBILITY WRAPPER (retained name): route (b) is no longer a route
— every consume is the canonical resume — so the old checkpoint-absent
premise is ignored. -/
theorem stepConsume_reachable_of_inv_missing_checkpoint {leaf : Assignment → Bool}
    {orig : List Domain} {cfg next : SchedulerConfig leaf} {f : BranchFrame}
    {rest : List BranchFrame}
    (hp : cfg.pending = f :: rest) (h : stepConsume cfg = some next)
    (_hcp : checkpointAt cfg.checkpoints f.level = none)
    (hreach : ReachableState leaf orig cfg.branch)
    (hpinv : PendingSideInv orig cfg) (horig : cfg.orig = orig)
    (hfits : ∀ a, leaf a = true → a.Fits orig) :
    ReachableState leaf orig next.branch :=
  stepConsume_reachable_of_inv hp h hreach hpinv horig hfits

/-- **THE SUPPORTED `hconsume` GATE PRODUCER** (R2 deliverable, route (a)
retired): at the supported index, every consume of a supported run
resumes a reachable branch. The stack invariant comes from
`pendingSideInv_of_premises`, the branch reachability from the run's
`hbr` component; NO route premise and NO checkpoint case split remain.
This is the `hconsume` field shape of the arm-gate records
(`SupportedArmInvGatesCore.hconsume`). -/
theorem supportedHconsume_of_premises {orig : List Domain}
    {original : List Clause} {props : List Propagator}
    {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    (hbr : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ReachableState leaf orig cfg.branch)
    (hfits : ∀ {cfg : SchedulerConfig leaf}, SupportedReach orig original props cfg →
      ∀ a, leaf a = true → a.Fits orig) :
    ∀ {cfg next : SchedulerConfig leaf} {f : BranchFrame}
      {rest : List BranchFrame},
      SupportedReach orig original props cfg → cfg.pending = f :: rest →
        stepConsume cfg = some next → ReachableState leaf orig next.branch :=
  fun hreach hp h =>
    stepConsume_reachable_of_inv hp h (hbr hreach)
      (pendingSideInv_of_premises hshape hbr hreach)
      (SupportedReach.orig_eq hreach) (hfits hreach)

/-! ## §3 Retired route-(a) audit

The former §3/§4 audit and refutation concerned the checkpoint-consulting
`resumeSibling` route (`resumeSibling bs f cp`), which the runtime no
longer uses: `stepConsume` is the single canonical `resumePending` route.
Those declarations were retired together with the old signature. The
run-level producer and the consume consumer above are the live content of
this module (sparse `PendingSideInv` vocabulary). -/

end LeanFzn.Solver.UIP
