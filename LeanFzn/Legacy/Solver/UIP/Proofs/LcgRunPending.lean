/-
File: LeanFzn/Solver/UIP/Proofs/LcgRunPending.lean
H2c (part 6): `PendingSideInv` one-step law with the decide arm taking `LcgReachableState`
(only `length_ok`/`full_fits` of the predecessor are consumed there).
-/
import LeanFzn.Legacy.Solver.UIP.Proofs.LcgRunCert
import LeanFzn.Legacy.Solver.UIP.Proofs.PendingRun
open LeanFzn.Semantics LeanFzn.Semantics.Evaluation LeanFzn.Solver.Core LeanFzn.Solver.Propagation LeanFzn.Solver.Propagation.DomainFiltering
open LeanFzn.Solver.UIP.LcgReachable LeanFzn.Solver.UIP

namespace LeanFzn.Solver.UIP.LcgRunPending

variable {leaf : Assignment → Bool}

theorem pendingBacked_decide_push' {orig : List Domain} {cfg : SchedulerConfig leaf} {l : Literal}
    {k : Nat} {v : Value} {vs : Domain}
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : LcgReachableState leaf orig cfg.branch)
    (hpins : PrefixPinned cfg.branch.frame)
    (hshape : ShapeTypedDomains orig) :
    PendingBacked orig (cfg.branch.frame.retire k vs) := by
  refine pendingBacked_split_sibling (splitData_spec hsplit).1
    (not_mem_order_of_split hsplit hpins) ?_
  exact ⟨hreach.length_ok, hpins, hreach.full_fits, hshape⟩

theorem stepDecide' {orig : List Domain}
    {cfg : SchedulerConfig leaf} {l : Literal} {k : Nat} {v : Value} {vs : Domain}
    (h : PendingSideInv orig cfg)
    (hsplit : splitData cfg.branch.frame cfg.prio = some (l, k, v, vs))
    (hreach : LcgReachableState leaf orig cfg.branch)
    (hshape : ShapeTypedDomains orig) :
    PendingSideInv orig (stepDecide cfg k v vs l) where
  branch := stepDecide_prefixPinned hsplit h.branch
  pending := by
    rw [stepDecide_pending]
    exact pendingBackedList_cons (pendingBacked_decide_push' hsplit hreach h.branch hshape) h.pending
  checkpoints := by
    intro cp hcp
    have hck : (LeanFzn.Solver.UIP.stepDecide cfg k v vs l).checkpoints
        = DecisionCheckpoint.ofBranch cfg.branch :: cfg.checkpoints := rfl
    rw [hck] at hcp
    rcases List.mem_cons.mp hcp with rfl | hcp
    · show PrefixPinned cfg.branch.frame
      exact h.branch
    · exact h.checkpoints cp hcp

theorem lcgPendingSideInv_step {orig : List Domain}
    {leaf : Assignment → Bool}
    (hshape : ShapeTypedDomains orig)
    {cfg cfg' : SchedulerConfig leaf}
    (hbrPRE : LcgReachableState leaf orig cfg.branch)
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
                exact stepDecide' ih hsp hbrPRE hshape
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

end LeanFzn.Solver.UIP.LcgRunPending
